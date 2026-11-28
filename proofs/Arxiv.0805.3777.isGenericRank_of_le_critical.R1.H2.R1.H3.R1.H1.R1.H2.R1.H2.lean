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

namespace TensorTwoSided.Seed21
def x : Array ℕ := #[5, 29, 32, 18, 44, 7, 60, 48, 14, 45, 53, 23, 8, 3, 38, 57, 55, 33, 24, 50, 9, 37, 63, 13, 40, 59, 22, 11, 52, 28, 61, 30, 26, 46, 49, 62, 27, 6, 20, 17, 25, 4, 2, 15, 21, 12, 56, 10, 34, 47, 42, 1, 41, 54, 39, 16, 35, 43, 58]
def y : Array ℕ := #[1110002, 795885, 116161, 722491, 2057015, 1809687, 635635, 1965698, 2093753, 709129, 188311, 431639, 1835300, 1742870, 1898270, 276226, 563069, 73962, 570525, 1473739, 1440201, 636014, 1066276, 146772, 1091301, 313461, 1292347, 1821187, 264940, 1708895, 126677, 1895692, 534558, 1019310, 605690, 1637758, 1084308, 534952, 115457, 1700452, 793874, 551508, 603158, 10288, 1040996, 1048316, 144033, 1552432, 1871565, 1729515, 845242, 1207252, 694814, 20033, 1071807, 1321392, 1950059, 2019421, 2084745]
def z : Array ℕ := #[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536, 131072, 262144, 524288, 1048576, 2097152, 493123, 1183418, 1735673, 3176963, 3074858, 364664, 1318436, 3487817, 1514155, 3395973, 1350207, 3963173, 1054347, 2047276, 2921437, 1106860, 2755385, 331373, 1958850, 2243348, 1622676, 3317994, 2996700, 130540, 1287644, 22300, 1264387, 3078495, 301237, 3808344, 4073716, 3885435, 786218, 335956, 834706, 2467063, 1011699]
private def whichChunkT0B0 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3b43b33b23b13b03af3ae3ad3ac3ab3aa3a93a83a73a63a53a43a33a23a13a039f39e39d
  | 1 => 0xa2d9d99859318dd8898357e178d7396e569163d5e95955414ed4994453f10000003b63b5
  | 2 => 0x4084074064054044034024014003ff3fe3fd3fc3fb3fa3f93f83f73f63f53f43f33f2a81
  | 3 => 0x9da9869328de88a8367e278e73a6e669263e5ea5965424ee49a4460003b740b00040a409
  | 4 => 0x45c45b45a45945845745645545445345245145044f44e44d44c44b44a449448447a82a2e
  | 5 => 0x9879338df88b8377e378f73b6e769363f5eb5975434ef49b00040c3b846045f45e45d000
  | 6 => 0x4b04af4ae4ad4ac4ab4aa4a94a84a74a64a54a44a34a24a14a049f49e49d49ca83a2f9db
  | 7 => 0x9348e088c8387e479073c6e86946405ec5985444f000046140d3b94b50004b44b34b24b1
  | 8 => 0x5045035025015004ff4fe4fd4fc4fb4fa4f94f84f74f64f54f44f34f24f1a84a309dc988
  | 9 => 0x8e188d8397e579173d6e96956415ed5995450004b646240e3ba00050a509508507506505
  | 10 => 0x55855755655555455355255155054f54e54d54c54b54a549548547546a85a319dd989935
  | 11 => 0x88e83a7e679273e6ea6966425ee59a00050b4b746340f3bb00055f55e55d55c55b55a559
  | 12 => 0x5ac5ab5aa5a95a85a75a65a55a45a35a25a15a059f59e59d59c59ba86a329de98a9368e2
  | 13 => 0x83b7e779373f6eb6976435ef00056050c4b84644103bc5b40005b35b25b15b05af5ae5ad
  | 14 => 0x6005ff5fe5fd5fc5fb5fa5f95f85f75f65f55f45f35f25f15f0a87a339df98b9378e388f
  | 15 => 0x7e87947406ec6986440005b556150d4b94654113bd000609608607606605604603602601
  | _ => 0

private def whichChunkT0B1 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x65465365265165064f64e64d64c64b64a649648647646645a88a349e098c9388e489083c
  | 1 => 0x7957416ed69900060a5b656250e4ba4664123be00065e65d65c65b65a659658657656655
  | 2 => 0x6a86a76a66a56a46a36a26a16a069f69e69d69c69b69aa89a359e198d9398e589183d7e9
  | 3 => 0x7426ee00065f60b5b756350f4bb4674133bf6b30006b26b16b06af6ae6ad6ac6ab6aa6a9
  | 4 => 0x6fc6fb6fa6f96f86f76f66f56f46f36f26f16f06efa8aa369e298e93a8e689283e7ea796
  | 5 => 0x6b466060c5b85645104bc4684143c07087077060007057047037027017006ff6fe6fd
  | 6 => 0x75074f74e74d74c74b74a749748747746745744a8ba379e398f93b8e789383f7eb797743
  | 7 => 0x6b566160d5b95655114bd4694153c175d75c00075b75a759758757756755754753752751
  | 8 => 0x7a47a37a27a17a079f79e79d79c79b79a799a8ca389e499093c8e88948407ec798000709
  | 9 => 0x66260e5ba5665124be46a4163c20007b27b17b07af7ae7ad7ac7ab7aa7a97a87a77a67a5
  | 10 => 0x7f87f77f67f57f47f37f27f17f07ef7eea8da399e599193d8e98958417ed00075e70a6b6
  | 11 => 0x60f5bb5675134bf46b4173c30008078068058048038028018007ff7fe7fd7fc7fb7fa7f9
  | 12 => 0x84c84b84a849848847846845844843a8ea3a9e699293e8ea8968420007b375f70b6b7663
  | 13 => 0x5bc5685144c046c4183c400085c85b85a85985885785685585485385285185084f84e84d
  | 14 => 0x8a089f89e89d89c89b89a899898a8fa3b9e799393f8eb8970008087b476070c6b8664610
  | 15 => 0x5695154c146d4193c58b18b00008af8ae8ad8ac8ab8aa8a98a88a78a68a58a48a38a28a1
  | _ => 0

private def whichChunkT0B2 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x8f48f38f28f18f08ef8ee8eda90a3c9e89949408ec00085d8097b576170d6b96656115bd
  | 1 => 0x5164c246e41a3c69060009059049039029019008ff8fe8fd8fc8fb8fa8f98f88f78f68f5
  | 2 => 0x948947946945944943942a91a3d9e99959410008b285e80a7b676270e6ba6666125be56a
  | 3 => 0x4c346f41b3c795b95a95995800095795695595495395295195094f94e94d94c94b94a949
  | 4 => 0x99c99b99a999998997a92a3e9ea9960009078b385f80b7b776370f6bb6676135bf56b517
  | 5 => 0x47041c3c89b00009af9ae9ad9ac9ab9aa9a99a89a79a69a59a49a39a29a19a099f99e99d
  | 6 => 0x9f09ef9ee9ed9eca93a3f9eb00095c9088b486080c7b87647106bc6686145c056c5184c4
  | 7 => 0x41d3c9000a05a04a03a02a01a009ff9fe9fd9fc9fb9fa9f99f89f79f69f59f49f39f29f1
  | 8 => 0xa44a43a42a41a94a400009b195d9098b586180d7b97657116bd6696155c156d5194c5471
  | 9 => 0x3ca000a5aa59a58a57a56a55a54a53a52a51a50a4fa4ea4da4ca4ba4aa49a48a47a46a45
  | 10 => 0xa98a97a96a95000a069b295e90a8b686280e7ba7667126be66a6165c256e51a4c647241e
  | 11 => 0xaaf000aaeaadaacaabaaaaa9aa8aa7aa6aa5aa4aa3aa2aa1aa0a9fa9ea9da9ca9ba9aa99
  | 12 => 0x2001000a5ba079b395f90b8b786380f7bb7677136bf66b6175c356f51b4c747341f3cb
  | 13 => 0x1901801701601501401301201101000f00e00d00c00b00a009008007006000005004003
  | 14 => 0x1aab0a5ca089b496090c8b88648107bc7687146c066c6185c457051c4c84744203cc000
  | 15 => 0x3000002f02e02d02c02b02a02902802702602502402302202102001f01e01d00001c01b
  | _ => 0

private def whichChunkT0B3 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xab1a5da099b596190d8b98658117bd7697156c166d6195c557151d4c94754213cd032031
  | 1 => 0x4904804704604504404304204104003f03e03d03c03b03a039038000037036035034033
  | 2 => 0xa5ea0a9b696290e8ba8668127be76a7166c266e61a5c657251e4ca4764223ce00004b04a
  | 3 => 0x6106005f05e05d05c05b05a05905805705605505405305205100005004f04e04d04cab2
  | 4 => 0xa0b9b796390f8bb8678137bf76b7176c366f61b5c757351f4cb4774233cf064063000062
  | 5 => 0x7907807707607507407307207107006f06e06d06c06b06a069000068067066065ab3a5f
  | 6 => 0x9b89649108bc8688147c076c7186c467061c5c85745204cc4784243d000007d07c07b07a
  | 7 => 0x9109008f08e08d08c08b08a08908808708608508408308208100008007f07eab4a60a0c
  | 8 => 0x9659118bd8698157c176d7196c567161d5c95755214cd4794253d1000096095094093092
  | 9 => 0xa90a80a70a60a50a40a30a20a10a009f09e09d09c00009b09a099098097ab5a61a0d9b9
  | 10 => 0x9128be86a8167c276e71a6c667261e5ca5765224ce47a4263d20af0ae0000ad0ac0ab0aa
  | 11 => 0xc10c00bf0be0bd0bc0bb0ba0b90b80b70b60b50b40000b30b20b10b0ab6a62a0e9ba966
  | 12 => 0x8bf86b8177c376f71b6c767361f5cb5775234cf47b4273d30000c80c70c60c50c40c30c2
  | 13 => 0xd90d80d70d60d50d40d30d20d10d00cf0ce0000cd0cc0cb0ca0c9ab7a63a0f9bb967913
  | 14 => 0x86c8187c477071c6c86746205cc5785244d047c4283d40e10e00df0de0000dd0dc0db0da
  | 15 => 0xf10f00ef0ee0ed0ec0eb0ea0e90e80e70e60000e50e40e30e2ab8a64a109bc9689148c0
  | _ => 0

private def whichChunkT0B4 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x8197c577171d6c96756215cd5795254d147d4293d50000fa0f90f80f70f60f50f40f30f2
  | 1 => 0x1091081071061051041031021011000ff0000fe0fd0fc0fbab9a65a119bd9699158c186d
  | 2 => 0x7c677271e6ca6766225ce57a5264d247e42a3d611300011211111010f10e10d10c10b10a
  | 3 => 0x12112011f11e11d11c11b11a119000118117116115114abaa66a129be96a9168c286e81a
  | 4 => 0x77371f6cb6776235cf57b5274d347f42b3d712c00012b12a129128127126125124123122
  | 5 => 0x13913813713613513413313200013113012f12e12dabba67a139bf96b9178c386f81b7c7
  | 6 => 0x7206cc6786245d057c5284d448042c3d814500014414314214114013f13e13d13c13b13a
  | 7 => 0x15115014f14e14d14c14b00014a149148147146abca68a149c096c9188c487081c7c8774
  | 8 => 0x6cd6796255d157d5294d548142d3d900015e15d15c15b15a159158157156155154153152
  | 9 => 0x16916816716616516416300016216116015fabda69a159c196d9198c587181d7c9775721
  | 10 => 0x67a6265d257e52a4d648242e3da00017717617517417317217117016f16e16d16c16b16a
  | 11 => 0x18118017f17e17d17c17b17a000179178abea6aa169c296e91a8c687281e7ca7767226ce
  | 12 => 0x6275d357f52b4d748342f3db19000018f18e18d18c18b18a189188187186185184183182
  | 13 => 0x199198197196195000194193192191abfa6ba179c396f91b8c787381f7cb7777236cf67b
  | 14 => 0x5d458052c4d84844303dc1a91a81a71a60001a51a41a31a21a11a019f19e19d19c19b19a
  | 15 => 0x1b11b01af1ae0001ad1ac1ab1aaac0a6ca189c497091c8c88748207cc7787246d067c628
  | _ => 0

private def whichChunkT0B5 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x58152d4d94854313dd0001c21c11c01bf1be1bd1bc1bb1ba1b91b81b71b61b51b41b31b2
  | 1 => 0x1c91c81c70001c61c51c41c3ac1a6da199c597191d8c98758217cd7797256d167d6295d5
  | 2 => 0x52e4da4864323de1db0001da1d91d81d71d61d51d41d31d21d11d01cf1ce1cd1cc1cb1ca
  | 3 => 0x1e11e01df1de0001dd1dcac2a6ea1a9c697291e8ca8768227ce77a7266d267e62a5d6582
  | 4 => 0x4db4874333df1f40001f31f21f11f01ef1ee1ed1ec1eb1ea1e91e81e71e61e51e41e31e2
  | 5 => 0x1f91f81f71f60001f5ac3a6fa1b9c797391f8cb8778237cf77b7276d367f62b5d758352f
  | 6 => 0x4884343e020d00020c20b20a2092082072062052042032022012001ff1fe1fd1fc1fb1fa
  | 7 => 0x21100021020f20eac4a70a1c9c89749208cc8788247d077c7286d468062c5d85845304dc
  | 8 => 0x4353e122622522422322222122000021f21e21d21c21b21a219218217216215214213212
  | 9 => 0x22a229228227ac5a71a1d9c99759218cd8798257d177d7296d568162d5d95855314dd489
  | 10 => 0x3e223f00023e23d23c23b23a23923823723623523423323223123022f22e22d22c22b000
  | 11 => 0x242241240ac6a72a1e9ca9769228ce87a8267d277e72a6d668262e5da5865324de48a436
  | 12 => 0x25800025725625525425325225125024f24e24d24c24b24a249248247246245244243000
  | 13 => 0x25a259ac7a73a1f9cb9779238cf87b8277d377f72b6d768362f5db5875334df48b4373e3
  | 14 => 0x27026f00026e26d26c26b26a26926826726626526426326226126025f25e00025d25c25b
  | 15 => 0x272ac8a74a209cc9789248d087c8287d478072c6d86846305dc5885344e048c4383e4271
  | _ => 0

private def whichChunkT0B6 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x28928828728628528428328228128027f27e27d27c27b27a279278277276275000274273
  | 1 => 0xac9a75a219cd9799258d187d8297d578172d6d96856315dd5895354e148d4393e500028a
  | 2 => 0x2a12a029f29e29d29c29b29a29929829729629529429329229129000028f28e28d28c28b
  | 3 => 0xa76a229ce97a9268d287e82a7d678272e6da6866325de58a5364e248e43a3e60002a32a2
  | 4 => 0x2b92b82b72b62b52b42b32b22b12b02af2ae2ad2ac2ab2aa2a90002a82a72a62a52a4aca
  | 5 => 0xa239cf97b9278d387f82b7d778372f6db6876335df58b5374e348f43b3e70002bc2bb2ba
  | 6 => 0x2d12d02cf2ce2cd2cc2cb2ca2c92c82c72c62c52c42c32c20002c12c02bf2be2bdacba77
  | 7 => 0x9d097c9288d488082c7d87847306dc6886345e058c5384e449043c3e82d50002d42d32d2
  | 8 => 0x2e92e82e72e62e52e42e32e22e12e02df2de2dd2dc2db2da2d92d82d72d6000acca78a24
  | 9 => 0x97d9298d588182d7d97857316dd6896355e158d5394e549143d3e90002ee2ed2ec2eb2ea
  | 10 => 0x3013002ff2fe2fd2fc2fb2fa2f92f82f72f62f52f40002f32f22f12f02efacda79a259d1
  | 11 => 0x92a8d688282e7da7867326de68a6365e258e53a4e649243e3ea307000306305304303302
  | 12 => 0x31931831731631531431331231131030f30e30d00030c30b30a309308acea7aa269d297e
  | 13 => 0x8d788382f7db7877336df68b6375e358f53b4e749343f3eb32031f31e31d31c31b00031a
  | 14 => 0x33133032f32e32d32c32b32a329328327326000325324323322321acfa7ba279d397f92b
  | 15 => 0x8848307dc7887346e068c6385e459053c4e84944403ec000339338337336335334333332
  | _ => 0

private def whichChunkT0B7 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x34934834734634534434334234134033f33e00033d33c33b33aad0a7ca289d498092c8d8
  | 1 => 0x8317dd7897356e168d6395e559153d4e94954413ed00035235135034f34e34d34c34b34a
  | 2 => 0x36136035f35e35d35c35b35a359358000357356355354353ad1a7da299d598192d8d9885
  | 3 => 0x7de78a7366e268e63a5e659253e4ea4964423ee00036b36a369368367366365364363362
  | 4 => 0x37937837737637537437337237100037036f36e36d36cad2a7ea2a9d698292e8da886832
  | 5 => 0x78b7376e368f63b5e759353f4eb4974433ef00038438338238138037f37e37d37c37b37a
  | 6 => 0x39139038f38e38d38c38b38a000389388387386385ad3a7fa2b9d798392f8db8878337df
  | 7 => 0x7386e469063c5e85945404ec4984443f000000039c39b39a399398397396395394393392
  | 8 => 0xad4a80a2c9d89849308dc8888347e078c
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
  | 7 => whichChunkT0B7 i
  | _ => 0

def which (i : ℕ) : ℕ := (whichChunk (i/24) >>> (12*(i%24)))%4096

private def denseT0B0 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x7a2653af775b7bf938d6c9641343e14920a81c5f91efb0d26b6c95d008e2ad3f8c644275ef7be9ddaf5e86cfcc975a49618e7b2daaea9aec8bb99208f6db3b0171bcf0f6bf7c52a3af30634987678080bf356959367c320766535a56eca246160c16348c98fcc9986c25680ddd503a777628473
  | 1 => 0x8887051418ed40a3d93ca7cbd00dc0bc6090b19b1c61cb89531bd02c5b2dc0baeb981cd3ec7ef7821ba1d8ed55973e172db83c5db7b2301ff92fd53c1e34e885316db22926e5f0f0032183559ab51ad340be44a227a4b233973333a9aefb6b2658096e179dcbf00b69b604186d5f11820287251
  | 2 => 0xe3fee027b444307ded58772c4e527c9f77e3a6b9918f4cc7a47ea55b75a225110cdc8f1d49f25a09ad65bf5c68b8aa3d9831a52a58c5979a5db230e80136fc362037d7a65035ef1ace1e051b401ee492a6d2002c2442ebb814d6925cd5e3b58f6519a2a65ba0fcbaa2e868477653be5a8170bc2
  | 3 => 0x628790d917b88e8b2c986858372ac8133e819a9828ab50340753259e0443043dc19113961977c1f882332c836f9acd4b61eeffdd5cdfbdec7500956ccfa86f3fe77e153a4c7bef4ae6359d6af03cc40e3ab87316840e250568b4d569a8aa47d809dccf6332da35a961aeaa40976392219aa38b5
  | 4 => 0xf1b4895176514b690f3b7a5fba1e13acada2e936847622d6d8c26384fd0f56c594f29b2936deb5cef29029557158a16d19949041d0e07385c371a8e18f70e3ab7979d512cd84ff3d587e1b23e42c5836b1377b9a073c75a59675b054c6da17dc08130e546ae0eb0106467f15204cba4cce14299
  | 5 => 0x229ebecd6cd2c6fa6d400c784e9b55bf353b1e4b710ee2459adb6e6b58b95f8b9d34194dccf62af10fc4ac5ea3bcc43c960c038af3b4d695a993d5c54e168aafd19373fe3654d26e05e624232c85f9edbe239d6e304c821fb32d83d3825291422d568eddad523ee3d6ea3c98253e00beb6d3214
  | 6 => 0xa2a92762b3c37e6f3a9757eebd7f03faa1b77a5dc671b0b67d159e08a215e5575050d502cfc40549395cc1cbc79c11df63f4d12ab09a7a08f21c273ea1da1f59737c0d9255e002ddbe083742ef1de31eeb08d1ca61399716010c0991dffe65809ba1343586c474ed4aeb4c896c04779e316374b
  | 7 => 0xd9563b88c7bfe84175ce1f1bfa80f1f83423f436d29840cbfb87908891c360925a550705cd76b2954986d6f993f65707259b048b3c9c03440435d5c2e5d6875e9a4eefdb10f76c3c6b2fff16eb9a919103d2d3c6758980c3ee0d49b3d4b101d2ad1aa9c1b36b2e6b778a280ab8e53d297bc7617
  | 8 => 0x22ee25b58425704684b7c037f840ac9e621c2e8277da069eb77ed4b80047025f45fcfda8bba03866049a57a700bf1c525ba1e3f644ae34aa3d3861e21a02a5ba6cbf358db89ab8909766b72548d713738e6071bed1d041c1ce801615fd690b0eb7c1f8461886c84ce2f81187aa840ffb7248867
  | 9 => 0xf488a7c9361bbe6af67e3882df1e39f66ca9baa1c76a93d6529b7141811695e03b108b8f85d976b09ca5fbce83693b7ba6b749456cf08552b0609cefcc157f73e4cbd9112c23d8511a4d38917e74935e50f69055a69e1a8865f22ad4c0f256ef51b4d5ab85d5e21e2955b72a3a269d28183add0
  | 10 => 0x561772ab429672a57fb5fc8a25a4ce8a8c959cd90b8af5c1525b6843279b2a85a1af8ace678af674b4bc900cd6d14dd86987d5558f8f2c8a3af6628f814dca313336c023bfb6a4535ef1d937fed02ad23dfe0381d12ca06d4d489044462a01407fb56e50f49615a452952573b1f9404d5eaafa2
  | 11 => 0x15bdcbcca7fd9f01dab8218ed6933663905a5a33777f4d2d2516531ca89e292d07729580c9cf13a98f8e4fa6bd1407230a269317e2670dc57bb390a97173497c4516b23cdf245775de84341d90a44f6ad921f45b92a739f83407c46d16a4ba565469085f9cf02e4465f98042c5cbd97f853f480
  | 12 => 0xa861aaaaf9833e969c24bad89379cb8b28d6f761a39982cc8dfc371fd3d11158a53eb8a217be24169cddc5e4cdafaf12626016ada1d643446b6a07d5461f9ad3dbf8e8c298d42a03bc7398bb9721722057b5dd156e6f06111b833276589a67db40105e59c8d6de7a636a4a7e36e58845b2ae553
  | 13 => 0x316e6367d73cd025e42a398756417fea89d7d8b196b046a0abee6a299db16c9851ce4e9971e7ec8c4e2dae2e3c3effded449d6d0f2bdc618152df70abc0bb44987e346e0f30705e111c73b044340c14892f2d54285577bb82112953e3edb50e5795bdaefd4daf730a8875c4b28e1e844100c3d3
  | 14 => 0xacc194694dc12cd63bbde03ff8815237b3555990344cfc250c181936e2635fa7058de46876218e3ae0d6743c65b7569350940a7b3b433876a80b33d362af907b26c370864373d7d82de66b1d107584c54651619558229f412387a1fd6464547eababffd511bcaff8ab89dec9904095487fee4b4
  | 15 => 0x21506571c1d9232ea30a32d723390a9a601fe11b6e9c667bad5efe213f8b6095f9dfefb8eed0c4f116bc7e888a10c6209fb96d4baa0dca02c4f71493ee5f7f51b06af90f36e8d965b0bef26c511cfb6a5f88967215c4f8e7c86a6608452e771c2fe3f852777fbc7bd7501c848e5bbd00d61d169
  | _ => 0

private def denseT0B1 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x6a2b3da2ce5f736b89b6f763cc1f26997cf23d679afd8ea57e9dd21d94a505262eea1dce6bc5f361c779606cc00e620c8278c84b75c33c923c3bbde6f0ffa98b79d681598145388f160754e94308129f6fe5bb538dd64ea90cbc4fa71885f027a63f926f2fa1a5be9822ac2cff081a4ed5d3391
  | 1 => 0xd6431a84207d671e5fd0873b9f4ad230acf3cc773c10b7c18832b482eb178e42793a2265a39e5657de458f865789ff4070bab65177d1a5897a9dfff2ee9218c2fea370217f3e8f49ef5577196895c0be18a98af54ea78d466a560a145b9b577d22518c9e20074215b6d5500232f7a66cac54704
  | 2 => 0x3b0757a10201d9632741d5a74b8850be27328a9128bec7eca5cd3bb751e6655036bf58a0d4a3e111de374af0296f9e4c5a4290def6321c467fb6dd0506fc147503b4bbe2b5c208fd16b90c7623939c42bec132d3f561790edda4ac742448a946beb1ad06c3c59c7d2d8ff6de55722a506bdcebe
  | 3 => 0x2e7311c7d5757a5c0eeb8a322aa0cc6a2b3859aebf19fc8cc87d74031aee9acfd43553674fe46c44cbba26ba63622054bf5da10f223f407703378069bf2ac0e1495cf7adaf5988960d68a25c80d8452259e70f47addd9b5e9274824233b70a575470b72bb3f7f77f67c44540412806d9dee696a
  | 4 => 0x377fc298938a06b89a6f68216dc1afd76f85ca2c7749e874ddb37d7937ec6145bee894ea5cdb6224c708ae2a89c7e88c64b5fc3e8ec37db18f59917b01d287c13ebf48b66b0096bab1b8edee38e4f0473a879bfb79ed355460af28e84defb71bffadb8e43df1c61dc28745002a46bf45654e34e
  | 5 => 0x3b29ac2a186379105fd28f282b9a51d0c1e971ba2a5febc8a5ef2197fb2ee94aa2df555701359123b458d68cda508cb356e43de1f0e87e261f4572c4851ad35f415caea73548f44dcec89bfbbf0d831e815e5cc4fd6919639ae16c4e2fc63aa6e3c0d4ef2b8dfd600d45bee4477fff75c021e04
  | 6 => 0x878ce82e1860f0cf6d5fceb97e6ba3661ba811c10a1a93707e955aa22508acc247aa2b9068a11312a2654c6ce1fa9def6cb04b50c91c4cebccc88bbc2edf364d500fa585c2076c94e1c0235c17a761cdbeb790c0dbb382ef4f47baf0f436709f4a3cd6f94f829626c2c82534b60550aec5911a1
  | 7 => 0x33ac4f9c88140ec718c9dd73db98190e6dcc3dbb2c2c9a99a8631f46b6b62e9ba7abf8f2708a6a8989c912a78b0feaa9f14ef3f1e36df56fcf6258f031f29bf9990e6b7fbc68e36f52200cf1c2db1b1f890f6a9b793fc49c3f0ea95ace374aae4ec7bb038c7a90dcf7d4905baaa2c43a64f594d
  | 8 => 0xae3b9d5e40ce170fd9969f5807d70bb22d16d9380f225436df5780f4415d877f428af0d4a5046fbe72c5abf08668a4a51404c869f2ac3bf11fd778dc11043cad9118c9ee3245a8b34334e9539e7219e76bfb2489897ff7aef8b66681f3934b93e2ce1ccf41e59e44c1dbfd83050392d2d9dcb9e
  | 9 => 0x26137b9aa2302042e900e7885cbef898a2846cf0eeed97c242abbf0b681dfcfe860f0fab75a49b38009e983fd5c6d38ef58609d7cb5518a85f8b439b9b7a115147bc8243e7203088b7cc327ccf1d2661953a23bccbda37c901fa246fc15574c5449821a94ad07eb093cf083d63f47e82b1ddbbe
  | 10 => 0x71edf9adcd61a8984956a7a9a62f136a7a58d013877450850bff02f61212ac7d2cd63ebb6b3080213988a853c08bb12ab28f7cf248c4a08fe2ac0155627903207a486191f9a0cda2ec57b5061115676cc65934bc4b9b3e1da66f26c206e68fc08fb97486d18c6b98b4a2f445764df6ef13cdd3a
  | 11 => 0x9cfba800d69c4cc72dc4a8c3e32599cc5c38a12553ecee8e9ef98853c4715d9827bd861cfbaebb83cf50f36346ce389a766391bb0ee8affe7db5a2404da3eeaf8747f6a2952eecd7d07c5f30f06c01b2d66618c449e0ca39f3c780073fecfa7810aa0ef6a0b5a4a17e1ff99ab4149a857854c1f
  | 12 => 0x354ab44b672ffbc11381be7aa165e543f73af40086a5e2978bd2e58972427f1c1f8bc43c60b656af965a28ca528ffdf8bae26cf311872eba5e3eaa0f5b80b2ff03412a0a695f3600916251209402b7b8d443e46d8c48fee49d43eeb81ebc58963d2650e31812c1be12688d7abaa99d3495dbac2
  | 13 => 0x7f1cf0c81e0e396be449bbfa9a8794bdf6f8b7422343445047e2d8797399cc83520ef8e110fba51ff210487a7600a8df14e25a3e0d4f01f67787316bc5fdb65ce77c50952061750dec8ceb3a14f7042165af52709a5fd9e8778339c956f6900c26f783a6d4ecaf87b0b495cf56eb08451ffde97
  | 14 => 0x981292106cde8d35130669f91012fcf6b1011dbec3ee73b7e8e303cb58cd85f81eade26811287537b4fdcf90b422038f21ff5fb11b510124498e35734bb866cd3dffad2de74ff66d46ee9f7bb90ce4aa19cc35db9c283a1934575aafdf4a9dbd238ff40899ccf32549bc38c60a891de2ee18210
  | 15 => 0x5db4f2c436449074bd1626a9d65984053f79246b2c7df12e1b1c9241561a9b6c5da0b466d77a279b05355e645906407136efe2c9be6e9397a6e6d1c1c9416663535a983cbe6cfb38d61a3bfceb4eeb12f2ec851653cdf48b9deb67bc5f1aa86d63fef0c38ffba198cffa8f5dfb774e410cca25f
  | _ => 0

private def denseT0B2 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x9e1a48e442a5532c017c18fdfcab4bbd9381cc90c5ebf5facd6055bade70b0b9c124f265008ac39ca12415a158ffe121a2350d57a4fdefad79ddecabcc7d17d72612395aa18c097b9756ac4bdda518a70a6b20af6a246652a2b19db825797dc48a97821cf296c97ca2322c201c8b878d8184914
  | 1 => 0xd2746f64edf953a805ca280f7c8a036b57c8ff29483e7805ff62b3f9c068bfaf1ea52258f01c992bf54a971d71abf5d3d5e80177eef9abf24b515bfe039b33a85975bbccc55f1a96014e5e7424d73650db7f1c2479360c1d92862c967697c1b906f1661095f4cbc18a6d506a5a5210ca55f0c46
  | 2 => 0xd1551ef8acf47a4096065c6f96fad8a49cd3a9964a036b384aab9fcfb1a62ba24c4c58a7acbf6ff4642448e417beef278134cc80649b5cc18937e9c67831e3415c400e6811584928472aa502bb915bc53dce132356806f31e74e90a01f2ace08816991d9951198aaf6226b1779487bc74705be1
  | 3 => 0x336512042fff10dfb6a900384a73f84205f322ec8c3c9d9517e4f79f139c46e6b77c7d6caf58e9bef44b886f32d548b76e523982c8f14b49c96138a349d558eb36a01c5464ea5a34eeaefa5d6c5424a99acda2d204c423c70192d73bd2d0b96a34dfad65a32c73d076f5cfd84bd1f50ce60ade4
  | 4 => 0x517867e4e2ce8084f1936b07c2cd0c498a4e65a0b8ba70629614a6e83b4e87b68c08049bae7f184258aab16a89752a639933ff7ba0964eaa86b26da08d083eecdf8dd27ae7ae87b0fe4a83f134a810734a80089fb4b0b0d2cc7062ead6065099bb569cbecc4683aa668593213abb830dd97b2a1
  | 5 => 0xf32d49d6b39eb21dcb177e162ffc31748dd8975148fe079f05a92e0480c4599dfb5de4f5b68becceac7f5b074154928d34ac207cd5b60aefe7391bee60331ddf459a09abb7e01857a9dcd0d079c028ee689fbb4541978e15145ab9f33ad0b9d6e3b4a842b522d0a00b47f0acb34126a9085c18e
  | 6 => 0xed715c2ea044f53d5d20fe0ad232a4e7a8f3fe6ccf2317b87afd818ab176ee949db75102bedcdf8f4e4e2951d583187489d474897cb9fec0c28baa29c13ba409842090f5ffe8f9bde3ca445771c160eb847dc7e76d534fcbbd24f8067bc693bd9e04497888fef307079bb094df18911302d935d
  | 7 => 0x72e4a34317b7393e62418a835838c28df010896ffd95f6e2a4cfe00621a0333200cf436824afa3af913eac738112b7d499ebd9c2a5a02461ed4d0f359588de4cc56411e30598a7637a699678ab003bc63bac099444cbe944372a85e5c9fa160de63dc916e0bd521a07143c07912f91820fa43d
  | 8 => 0x331166c0348cb1a70bb9109db6a6bedda69dbcaca1411d316a2aefdca991f89d806e83ef95c542ace0b6e8042006a8420a7396cba2076895a69a70b20ff778c41c43b9619493c2cbb4af51eed9bb21f6902cd20c87fc528b04016d233ad24bb2ad68c44e7fed20db7bb9b001e058053455dbf65
  | 9 => 0xd10a00c63bc0389d8f539959ed8f721e34e4a10768cd8e6f1b662024d310e47af8926ab78807f3e4964e43be8387d49eb08c39a587a899c499024383c146fb62028ef5cb323b3868e32a5ef3527f0d20029b4ee84f0e0b827384b90d3fabd061228a49feea052a132878d52ec075f0eb9b6fe73
  | 10 => 0x98f9794c2082de4bdb119c1f1dadf7bf166e609691b82777f115b908100e3e671da8bb9abc512f4b4ddcbde8c6d82c9dfb5c0da2ffd05f9db96382d683167035b76f531fdc0ceb191b249566f5d5903b8f3f51333e94341c927164167aa9d510b649862ce9a70a911f28f4adc418d9bcde9e32f
  | 11 => 0xbc47e66f518bcef8c074a04e1897d7e290e21c0ea3a8c1081abd23cd875b978372bdf8ee376483023c6ece072a269a56dfe118b3e94535db34ccb90165a1afff22c962e9c46ee58c6511e44a101c79e14a1801c18dffa220d476189b5c20c59aea3205bcc750f47ecac8581c2a4a42c20723ffd
  | 12 => 0x621df7de4515b98f36d123f97e76e78bc0444b009701d40bea93c6d05b8dbc9bfcf0749b64f3a967a4ebeaaee490e47f32dd4a62a618c325e5219a668bd0e9206c4eef46b9ad23d51ce17e1628538906e5c3b2bc2003a02752bde47e47fbfa103745148d0b3111ec76726f1bc38d2c33fe8d7b2
  | 13 => 0xa3d99914d87f47b6995607d909ffd4343c08f334dcbf7ad2efdb1c8c9e85f20efece9bdbda305bace5e93a56b5615b3df2d39e0fa112cf687a14f6fc2a2110475f60df52e4b9cf5b66268ecf2fa3db0b945fb9189f976f954f2166e419733a8f777df493b57257fa603a7c045a14b902b487e6e
  | 14 => 0x872a9bbf927f6ac4658662bf619cc7c0e0990a51c7685dfa9f9ea69c788393c01090bae4d94e056051ef0f0ab975f1d7145c133712c50f1749672aa0f3609bdf3fbb1bb8736a1fc5025d5f8bec77372de170c3d7ffb80718b1fd9ce7a5bef5fb2a87c0b8599355b3b76611f20e28adf574518a9
  | 15 => 0x593c8db5195f83b99ba2f376eae8bced74e78596cf08b1e3422cb87e66a2cf603f5bc0688688470327059d8ab38caff030b30dcb5fd37b3c2b29883a1f7ae5ab84d3fa9dc1cba837473c7bd5286868cd6fba800e7670bc79052050c1a994fe2a514bf062e5fd297a7c44902316bc211c1be7d07
  | _ => 0

private def denseT0B3 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1d35827b2b12f8db9d9496f926a805fa35eba3d461da384f8d6d14bb63d84b5fdec17f8dc31d4fd0757da6c448a57aa567841b178443edd31983c788b404b697654cbb8159608fb4518ae2e38d8b0851e3b013d593f9d2e255a14523f00b83d2e0c987a6492930895e54f0dc64f3dad3b05bb2
  | 1 => 0x45c7a6ce77f3a106e4d2135e9234b60e77f5c6b763c10f8f2102f4165c26774e5c9ce42e3b808b5ad18dec8e91b846b858857e0edbb4a05732fc16995d04a5cbbd90d0730ef06f10f20cd8ab1ec0307757832537778bcd01ac68d7b5483e8d3dc7774d7947a99aa1d2eb0183d8ad71ee6968798
  | 2 => 0x678b6e59b6e298a9003f2a8e6bbea4d39640f2f3685000fb05e1dfaf08c8b6f69b6e9cdbb3d5b6709ab190cfc5a2e4132effbe27f0988bbbf89c449784d12f0ce694f67eb83bf20c6a0863929b429dcbedfbdf5392bf2eae71789bebea910563c99d82ba6f8a7a5f78edf4f1c055017fa25b5fd
  | 3 => 0x12c8074759accc542664475ec37ee6b91a1953528980c219281373b011d131b2f1b33e8c01196e79164d67fc0895895686169e283fffe04db0fa0b0e66f69ee24bce8d57c97a475cac7280e664c73bdec54dbf1279e1c8716999faca377f94e75e1b4824d8c598b716794054d75cf022f70dd45
  | 4 => 0xb7e3d29d3d7e4f4974f60ac375e0e466b05eab51ab9ebc93ac5aec53966c01eba631bbe03279f5e9a32137ad4b2e5efcbf67296dce8884749ca5683546f15f8126b524742796aff0ddcf422708b2a9e08ae68259c9821136f213b8c2f3847cc650f7254e2ffc96deb98f500a047c7210eee8070
  | 5 => 0x2855bce052cb8f98f497af8f0e79c108809fb2ae1893c33fe5957744c8d243ff9c07ede5a7ffb8902745ddc40459c47f7ca1aefb2c7e8748b483a6ef983ed2fc1fa6e60458836387518c43570ccd67e4ee440db2abbc7e34c621855a647708e33abc6293fd5fd710c5772f8475bbc02fecac887
  | 6 => 0x2348d02e309e37cc1d43b2d5c48c0624aa48e397eab98b22e27b7f90e09764e580b413105f58cd7a21cdc6b5d282c49d9437f506e11a28565cb6cc63c8801cf46bb210b3cbd629c00be368fedb5a8af9509e1e21fa163f83209c1e1cdc9f225d25fbd044d0b49ecfb0c3808f16c33cdef91756e
  | 7 => 0x4edbe47563b0ebb32193ad3522ae96a926e5f4d41ee0df44779892eaf0bd578189b3b80579c070e932e8be90f89aa22047c7db4ef7d3576cb72c0e77ecc82927bab9b90159f6d3217cdd57a7804409239811986e2df6c8e7906d076540d3f0127d6bcc80cc9631a81e1eb3c08a28fd895c71996
  | 8 => 0xa9a0f74b4b284d4e0dc8a4583ff22d1a3b9206b704e7a97260ae4cb90ff4c1406af9cbd3a73abc9a0ef8ed423e6677433952e83e54851d779b50413fc7b7fc523298745331e377d6c7ad6b19bb974e6494d85f23caffbdc0a52f2316a8484e9c3333c4cc5acc91b128b9d3df4d98087d041c3ac
  | 9 => 0x5f1345680aa3c87b7b2c90296d1874dfbf4c5ad16bf920ec826cf753b3d9c4d8df36233f2871e28ef7113837ee4389e4d5d8f46531e5744ab2c1c3ca1e3fb869a393e304e6611fb4fa5f4e1e5fdc6d5e6d7b4c9073d2d05772b02d93dfc0bd5b986d8e9e7735f72dacc4675b1dca58c6b1af865
  | 10 => 0x2a2089ec009ee47e77d03ad5d7685f5142f142e13ed66f9a271da11ec07f1996a7140cfb3cad629d1da736997b68143f185faa44f26d8f5a922123a1ffbea5335aa9c621cda9d1e23956d905e165ef1f6843f8b8f35ab26ed81f52297ef66e9806bbbc7de393dc56e8afc676e3a064bfe0d3fad
  | 11 => 0x39d95c10cc2a0aff062c51710841a160875b6fe5855d2a7caa5f248d89c48fed3ca53b3c71c61983575b58dbd250afec04d4983f4b3f259d025c968adc545f1d9019eb79a60f90aa3f2428bcf1aeb11805eae807d655393ebd593a7848eb7f18963a4575ec16ea533a7af16dfe87f49900cd2c8
  | 12 => 0x29d705b3fff9b0e1015fd8d29335cd14ee055f5e2a1753b7af2296b47aec60da4d344d2410857bc41693f5bbbc7c458385610d69dba014e85fbfedccb9edfb95503050073a6c51c436ac13820b5c3feade73699fc3e2b01ebbe4315fe99be6a7d0cd2594851f1caca67afb84d6593275a69e0a9
  | 13 => 0xbcaa5724f7a5d874a7a14306b98be192f62580777f8d87ecf229810f8c8831a5398b6c99bd5a29ee7c0ac60af7858d9eb650a3877d776abc950ef6f7da28cdb479369a95fc1942ee6ba719fa5b798f1efb15cf0d791b2c2ff4a4b5e66ec291cf8caf3f42d7df7e996fa629d3ceba8296f6fa88
  | 14 => 0xd89ee3c7c73fd84b4984f9d06b538bf8870838bc84b86a9b5dce1e013662f7e6f1a4c3e8c638a6b49cddce7f3cf9807d8018c6a1b9a2469a9d528f77f54056bf7cda42828f0edecfe055bbd59e13c6cae311f72027e3db3afe5f4537d124c49cc561eb8120332a8402deacdc20bf957b901f1a3
  | 15 => 0xed7f81a89e0123a2120cd054c385fd29fddd016af9be905f5ffafdf1cbb0f8b74675aef31078e0b18e5e9d66f7846828313f6275280440fa210a4d49eb71456ed8fed73a2a7b056219d3b636b025d5fb826acdc73920702cb85279baeaad28f72ff0ed52d50a70d510c664ec356929ac341e481
  | _ => 0

private def denseT0B4 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xc974192daa45ee67f32f6a55fbbcdbfdae0da62349b99325927b29e675baa97aec059fad5ebabafa22873c38daadd0471bf57fefd0525f1410a350d375942330ad985d57292fbcfd186baba06cfc2cf31a52188751718eda31fbac4c7b78bafb3724eadb8a98282b6a17d5ac996453f4376f03a
  | 1 => 0x506ca24bcaebeedbcbf6811f3d9a13ec41ad02c961c40aee057b4cb61904a1a24bb59552bc9956df3e962204c76d6a8674e08007147e376ab5daabdadf530a7ad90e0e0d6c5de93aefd50b2cb44aa83c433d32997c13a0641da4a5e3055c7c5b4a1c60180960937140466020cfffc929234ac1f
  | 2 => 0x24a15e90c0d03da90f9d77679676273cb1074b159e7367554d090863060a315b8add170268db5f88aa3e6082b25861dd102a75c348e41cd3e5c956fd48c6b8693f9bd60c2e33d40d938903c02d14cf32b9249588454842750962b016eedd2d051f9a726c3aef9a7852102514e06e57c72df7e05
  | 3 => 0xe744a798836716610c65c3021db0ad494123022476c9f4446df0374ed922c88572c8774c23556f528e24f1634197e0adc797d5fe8b233eb4e01e9a2831d6cfe5a7b57f0231f5b3b7b10d7b422c0d294f585d12787e1b8a33e5c811b0f4e6e963f7a757d6996db8328c58958d76dbee473f3e1c6
  | 4 => 0x6be00a8576774e88a6906399b324cd924128b2257b2429958fdf40d75600b8887133e2ab5201ecf61451df19bcb16a7bf7c50bdf8bc7be5f4a133b71fb413dfffb2091792b6cfba75b4aebfbd8c50694b507743bbe9b69ddd7a9be4539e2a729f342d25891c8c53219f60175432e88c72c781b0
  | 5 => 0x7826c6e670ed6368c9a2cb6c1769648a898a1d7877c9b0a95af71d9f86edc34e3d2efe1e2ca6b16f306b8042aea36b4128d32244003b55ae439dd38beb8448910d19d59a696e7bf714a499f75a346f439ab60b1762ec5468aeb8b178490a86db3cc66906999085188f11fe0021fdd16a756f3da
  | 6 => 0x9a29f8ece15be0c6578a2fee123d9daa7e99c320787349cc8769dde180a602e05e6ccbabe83083990c28c7116630f0c5a54721a8856e7415bc0baf25c8805bfdcd696786520a9d7149a790d0f3f40b51e9c01038641a928b6317694fc7d8aa3ba416a626eb03eea332f269302945743dac4e38b
  | 7 => 0x62302265a41e143bb6d57d82f44052a6af8f147a994ebb5181c27ff4cdfd704226d1d0fb986ef840291644cf2ab3fdce7d2b5fcaf4154bd0d10195ecf528445cdfe5a545f69af962583466a9b597644e8c20ce642b488aa29c1bfb825138fbddf8f75497313ceb37fa7250aebd21e00a2abbf3
  | 8 => 0xe8b8a0375ddeff4b60acf00cf9a4c17767b2dbfa5a43515d4668e570132f64924cfdb83220529a5ab301473011c3df4ea83a947d5fb0d59d59863261dc0a44b50363a6bd27f85a25d61b2a30db4f943a1ca898361a47268f1a06ccd4115fe0c34b69a1fab9224f81a4a2384317433fae17b93ea
  | 9 => 0xbb37c63b17dcaf2c4f4c50e51ae5ceae3f2aafc49d61b939282d0eae7c3d3c789b60ce91a989a8be9a6328408173b3fcaabfe0d90810f1f2bb31a8cdc8813810915b69ee3df359a187767ec6c420d27dd404bb7c0347565f6c1a3d2129dfdb21a5253d83f4c7d99dd0a970f7992207f6f4873be
  | 10 => 0x361dbf43b3f414c467864c8e45c33ef192fde8f3320090c183e08805be27acc6dffc5e624b5dcf8f0df1ec82a15eb784903e40445d96297276cc87cee181177919411000023f05663347686b3195cde438b29813ac9840814acb3405e949f9c5b5048be369cbf3eed748af3d6e65765c96fad90
  | 11 => 0x8b6ef530d7131b8f948afc0b84acc73e627aab0220ee3ff893d1d2093543dfab6dbaf5e81081cd8d386099b7ca5948d3af095fb665ecd2445133e9447e57bd84e14667d6c9cd419ede071ecec1ff7d04c602eae8ccf32a5d408f72a9d4ddf497733dab6c3cd76b0e5ddb7a358122777e10903a9
  | 12 => 0x7c7910d5d35d9300b3b7c3acc6c6b31c6bc85d8210933b3b90d3f39d13135dadbdb1e103cb3b94a7abefd73202844af0d2969b4da61af46dd8b86dff8455afc346db8642c5fb28547695168a5c4806ee85bef846642f7977cbf5f8cb35bd849e6dd2ddd513655cfb82d6337ec1352a29a3891b
  | 13 => 0x4b4635c71b5ff6a9448ea4fffdb31889bc55b9b63a8c98cac80a007c8be261419ea3c14b4fb388dc6b25c22c89dc20f77f6f60557321fbfd8b165f068452bf7263fefd812325d414246aa64d0ba737f1989ba8fd21c2ec6842bede711fd08f9ba3454957d36ea77c128f7285b975473ba464007
  | 14 => 0x982e75db6582103feb7b6a35dc2666049ceb6f2d191aa3529eff0b4935172ab0820addf9d64df301ea15c81b0948b340d4e9d9eba7cd8304c3c2cb33e7f124251f03d2999e35ea9348d756a5429993d2dddafdb102273f5d055fcb27b394932674e88f2f604eebaa537b0e50a33883091406ebf
  | 15 => 0x90a09e7e42fe6523b060cdb6d813a05baf30e189b0282ce243620ef556a7815130b669cc0e3d8489c6255f81dee765ffef5da247a24492f809b60fb65fb38f900940219ea91beb86f1bac5be052c54799b1f61025b6cf5bef002c6d3729cfed812711f31a3679eedfdaa5fc56a858fbcea4acca
  | _ => 0

private def denseT0B5 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2e77d00ab824e8f11ad2837a8066640a3932851356392f069c57d4784e935f8ffe3a07adfb1f4867f27cc26452a1d118474786953685ce85197091ac6a7987b2230216d6c69be927cc4565c5a086be9dc765a471f43d4007fdb68d89a25a8e40721ae3080a3c1a04a600a2582294743f158ad5
  | 1 => 0x78e76f6e58df1c07edf719240204990ef9217c830ecf50717eb22a0abc7f0a4ab21e04cc5244331790005d13c94b9d2b720fc46ba44da3a36e09006d4f6a517dead079d3743a05c1f4c325277d35c636dd83158596b4ae468b01436e8a5473aabca3f4cb3c80dc91234134647db053a6c2e5dd3
  | 2 => 0x9731fd6d479f96ddf99767feb39d22c6768f30584edc886cfacaa50f8a4a133e35b6bf4c979faddde9c8aadbce764f7b69ec46ea7d5dc8c7a959194eaae0e27dded180067aed8579b055f0617bcf15cd63512cfc2e9b8ae1ce210593bdfbbeef9836629d5701fc6505c8ac52ec12a7af9b2a1df
  | 3 => 0x4172abb66df45516ba650177a7bdf76ba6854b47d7200524c2114569ca84bedfb9d344521660aa5fad7a4ab44f1249aa1057a4d3d928496a14b74fc7091de14bb517f990b5d4dad53ddba8703f3e7c9823094ea7866e776bd3500e08f036b0cb3f704917dc73ce47529c0f61110f2ee4843610e
  | 4 => 0x3674fb25a7b876dcd5e2d55ded55ee6e7731643eb76f94b2ca78ee43367f7e7facec96e6103c157a3953e969dd6b8edf148b3b4f2293f610bc615903172b0c5f9169b9eabb174b666c719ec14f8ea1a358a8c0ee8b86be11784d12f69a176a45af8b2ed59dc4a4ed017cfb43f91e2ca2bd4d63e
  | 5 => 0x6b3fda9634486424fda516c15403c6406471f682fedf722b9dd4cedf1fdda444bbb949ec1051ccfa0662e550576f2d838902a4a543cf86f7c00bd3af7d8affe95a0815b6da4193dfe3b1716b3747c20a39678319b9a778dfec8289394b181eba7bdc19c896ab1f55be8ae624c0b7431f4b6f533
  | 6 => 0x3bdf979bb0044ad1460fa7dc30192b596096c09f446d1e31124293af3b863004d084c298ea35123253dfa5f6a5743237bf8f4ad44dcbebcc3c4953c42b5a8c46266cd1c971cd45c4da37e8e8c7e60df36a03516e21072f5057cf7faaeface9468ded7a721fc13a452f90f334f0eaf34ec8bf7db
  | 7 => 0xb91c10973f86e922f6a3ddb4e8e57534209a73265d1f6fbd5c06739ba9291d2db80237fdc52cc233652749df5a16445ae4541934dcf6d004256ac4e513b5d4d85cb1be50234be9c45477c144d94c6d2219fd965c02d5b148cc8d516a8f599b19ab895e45a778d6b91e7c4b420556e86236fc5dc
  | 8 => 0xc17fdbc6bd553c0d98b381da5f61bb26dca0c80cc4065f49685ab33328feeb82343bd4b135327d69cb9b20b7da1bae91be48b4bcf7dfe4df9179c7266a49e336b7beac20035a58442efb61401baec65568e403267b80e2d505a317f2df45579637053dbd0bc979ba04edf16326577b5db2a1648
  | 9 => 0x1138f9dd607654ca259b3b288b10af4b12bc5b46c38b57b51868dd5f097f827d473914f24960f7547db1f2bcb0fb77fd0ffd73fb897b25d6c733155cf00932a4379048c43d28b6b6910921d3b720770e1daac64f4e7e851e76d7e330bf3df515746f52566efd74cd99498c66d06df4ca1f4039f
  | 10 => 0x78d6771a1ba6a0657b8fa5783db45130728c042d720abc1f289245700345a99cef5be9118c32e4ae20332cbce7b0df88e0d5e2a84bd142a5f1345aab9fc2e5fe0b634b49801e6b8f6188e5084c2a580d57261d0df884b12c4d161d5fccd92a2f7880888bbd89d41d27db353bff0871acf7df72b
  | 11 => 0xbbc507eb9a64f9461341e1b3aaae4842063bbb091894afd8ec697ae20fd1de01d5157c38f70aa63845afebc3c5cf046800d751eb110a030201595707a35a2c38af55095af177dc8fed9d1e889a5cfb7726f260790d628c3ad3e1ada02fa3679bfb3d9d19bd6721f643ea8736319ab69e0c4940e
  | 12 => 0xa615e3775cbcf57b58675ebef90049766357866bb3f432db5fcbb75c52929d2a6beca280d53a4064e37faee25723db9bda732288709a60e8d747930a35d6d1e92c5f943cf6439e2f0390d6f27ff484cae104839307ef77c97f0ffaf5b810eb7cb271fdba1cd161aa66abcc05978e5d3ecb20566
  | 13 => 0xd07f004bb59c62d50d57a3f9aaa456339e421d3ee55f89386190e8be6a52d78d775f692cbe39549ab4bbf2d593b44753dbc8b2776f34140ced82503b333ecc608e7499c5e3bf11d37ea002cce3c8fdec652f125969fd21781679489f967e91d20a60fc25e4d85599b226a45281929700b67ab23
  | 14 => 0xb6272b3cc88509087b2d09bbab01a7632c0a4a4cdec77622961b7b7bd06a604a3c1dc70a5d59b2488db7d0a5ef32c0049a57674d33197ca035878f16eb8b4bf1ffec782559bf90c69583351673fc9420d8cf48fa5eade4d0923cd26f5c0dfc0ffd2c2a6fc96c06086492ad12ad4816fa00b61c4
  | 15 => 0xd2132499e97d9e184d03520b1a09018389c4a9ed7cb925196c4cf9de65811f876375a5c894cc0aaf6495b5939c360b1b5bdfe6620943785733dc2b32ea693c405fff974db3a4109852cc24419baa6df45e966e476858a9eafa3d537904fb65e1e066936692ad0a6ab3cc6bc650867c4828ad5ab
  | _ => 0

private def denseT0B6 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x8950e24cad2a5873c8a0edd03fd6b1a83d2c9236ec78e9db4b535641b5a7c672d1ef2a8341cdf3588b22511faa0b5f7359df5a30bc9c65da444d80534093b343daaef9d70e32ccbf97d8810c1cfb0ab12a53ad7bd1f3b0b46427620f757563fe6a77886cd1211f244871739c1921045d866965e
  | 1 => 0x99b98769e1c705c99607a3a0816a00309f8d459ee13b300106f7768700dbfa4aaebba321367e03ecc06c5550768ea2d8ad33cf48a4df1e8d4b722d5629c2a07b218af6fab98ff824a8fcc834323d064d8d6ac77f4298205db42f90625cadb0cd8a52d5fad46cb19de36c62db564f20768bf2e9c
  | 2 => 0x4bd0228376bf21b02b90e96a1463eff4080de44befc20d8f6a1b7bbc59a2dda11e6470245bc1823f708ba2c0f47306a6f5f6d6272c3f08cf25b630e1d210afcd4a35ec3e51c859b957d8a3421e327e7ac209976397457a5f31fec1b68d486aabf5b27c46634195a2cad21c62d54d1e06c812a86
  | 3 => 0x862bd4c33781a50e739dd65e4d31acc493d9e9a92ce714eee6c42f38fb9cb2501a75475cd8103451359e2aaa060310e0fd5f13226be3db02b2e87fb301a8f1ad7c97f982cb566a743e24f4af367df6ee679c47aa777685e41d3ed9d3017b1f5350a68d525014e1b357f9eb81a01d7df5067e4cd
  | 4 => 0x1bbe9cc626418e7029b904495f60497d184494cb14538425fd506d3af4c72c8c76695bfe2798bcd0eb4f16f95be69781aabfbc1a79af337d2175d9f7f47c2c30310af9dde5d64d8292d8d07c4e495b69af205e27870a52324aeff880ddf64cace020420bbcf95e01e7891d85ccc9531f1e3f320
  | 5 => 0xd33571c43700226651726a4f8632c20820780b59f5b0721b9e6613bca217d258644cb5181b909a325da334c090ac81995669b7d358e2ffe81cccd29b02d4e65dc27de64f41eba793027928d624410c81879ae5a194a4d34561c57e4a2a9af1bb2d64b03b6ea7618b76f93a01d765ea140b1f694
  | 6 => 0x9d3ad192188ce5e31be0336ed51d2524c27bfeacedc48e3482e3d0b98bc210c27024816760cee7f0605936b7b7c348aca43ad7ffc959cfeb1044619584843015a01947ee9a1b40784f03309bb2bb836db50d3663e4d4d77c596642a2676edce6ae4b2fd34186efa1e6cdacfe1bda999390a11c4
  | 7 => 0x45cf86a8a947e17a3a08120a8ba4c53536542bc63b3298e7b60073c8d067290c7aba9bf72f6dad4dcc4c37476e7e6025c6c0cd23ced20024d365242d944155a6bba91e47bac8c49a5e3d27f8696f2ebd611aea34f18d0ded3810fe17e0ff459699b0a4605b54fc7e87e56d0815cf4a9b86af0c5
  | 8 => 0xc6b77865758487c8abf13cef510a47f8e3ca888e894615313716bb245a36f56ba4f5e263552416b0203a8d28bd80c80db1e87c0ce9775f160ff658b93c35e1c2aa3ba795c43c8009ff776fc3e2f5bef5d9358ec667ea3b7b7b857f7fd6f43aa42d89c0dab2328b63d7e82340fbc809bbaec852f
  | 9 => 0x2c71c52766b3cddc74761008fb1d374e0ee1d50dbc9255cc1b22ada86365452a2641634ae4b6b39a10bca7e86b15eb4a28f75cd0d9d8f97766d76a8c7c484755d2a1acb4a0e868971124563b3ea8a5df9fa9e270521dbbcb3e9b31e942b12c683abfb8fe681bb932d526216df267c8277b1734c
  | 10 => 0xc1818c9527f34c5ece1f416dc0106ed63d76b6f798469b7a0c479dbb9d7b2cf5070f659fa673ba266321f3e172b5d7f8160a5e7b3f5d7000b2a348336be07913a58102b1df4151ab816208291a0840848d0b46e3e7d34f289555b15eaaf4bfcc4189742b7e4dba22245e905fa22ad3ee4805b3c
  | 11 => 0x4b424bc09a67a04f30c248bb1ceac2fa990a8e89bab4a1341f5b87b5c57797a9408b1db2161e8fa98ac486848dc131bbdf213ae912ad2ab3dfb0db906435785dbedaa1a75447a35d0d74b9c0e3324202d29c1a8b86c5abd2339d65ca857cdc07f1718b78f89df8aa75b6434796197ed67a00e8b
  | 12 => 0x15c9c62c2798ba5db6585122e0e97ff7d3367570b24e70fe83724452b38db60e0d53d7f8aaec77c37081f2d9935ae124baa9ea5a7fb62e19aea9be778709f89cf02f400a9a879dd2adb48d4a058db4360cf6864fbb51fcca87bd27c6ffd0c43c45d4ee6762d4a1defcf660e6a6c10dabf702ba5
  | 13 => 0x39f02955282853e2d0dcb84a493e12ab15f11b7eb6baf9869f5aabaaceb69efb45f9ff597da3db940693336a5127646f3f2e5b1eaa9abe2d3763112a0389474b43e55b16122de1f1242f8e4db05bca6f5bcb3b8b13aa2d025f0b8ba0e2fc6164d9a1064cd51414396e03239ecfd260f7b5637d5
  | 14 => 0x25c0f2d97a23dec8db2f325324cf83518f2aacc6ff1fb730ef88119c323d3e06ec0d902e6c4824de7fc5f1b2b221f4d1d4dc23d19638fb619cfe40005dfb6d48482186988ab85bb6612b0186363c78d9971997aae27b5604e98a6b529263afd321be64d073fb8ddae02b287cd7b73691a332d7e
  | 15 => 0x8c4b3cf6f4e7c34fa03fe75e74850de3407f3e9c9d8e5261beecb690f5eefb7c60da4eb2482885e4a410671b2507ad7eeeebebb47a1bd25e31ed025ce7735c00e198cb81510d71442c8e313a3255bef7e7dbc056c3bdb533576c855e5e496bda9574011c1494158ad74e1320ca4dd269b20dcba
  | _ => 0

private def denseT0B7 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x53b7445b6147ac0a2857d5f704e8dbff51a21e3a0d61b9b9682f8d9d6f6f26bfb7bdfef788a68db63997fc4d163f5e8f71369d36ae7e1eee1a399f4dcdc056c6649d738c97e5135f18f3deb7a0300a09cb98e92d527ace2baecaf9a3d47ff3aea2af1764b3e75726812424c3e7ad3a52ce99893
  | 1 => 0x2582f0ec8661afd37894795dd3a766717b0fdaad2a358a58200a03343479cfbc066d60981427c3b815d2a7ea97b505d6c65c820d5adfa692cdd3b3cccb3932ec24364fd2577a88e7ef69e3f0c7103470d845062d41300db83bb6fd54b3daeb09bf81cfebf8460371b7ce39190345a4c659c0d51
  | 2 => 0x195b1383b338879e91f979d056e01af821bc91f5c1be7f228c31eb28247d90209a23d0813b26a8efa0bc1478435a245cb1e85a4957fc6a7e5ccf685a4123d45ff1f74faaca88f0be7b1c9482b20f197ce0b5bed97164ffca3a0e78e7c0fff723227419da731a2251fe412c8942e7ed20c0d64af
  | 3 => 0x9a34d2cbe4595ef74a694bfb10f7f059a8cad7fdd392a004b32d74c3fb3c35060be9c2c1c9c2df2ae9506a579742a821321a1ab8cd952875265b8a3b5cf1bb864882538ea5a8405d5e219f356ea10b1388f9b1c8839e6a3d1926425d538ad721f6168d88d1c2b4ddabde7e1d7299a1f28cdde32
  | 4 => 0xf5fc99588b97601356db9f38ba9db2c66973e5ad24a8df3c791e49fe34ec2657b3001d30c8723dab610edfb04e6378f8d4c912bbd82e053deb2aac1c8b52e83d175f92d5b83bfd55f14a195ba06ab90c701820dfeec57346a23edce92daab8698223fad0df2ece141be2036f2138008cd7171fa
  | 5 => 0xefe463a7ebff9832dbe48db0f0953d67e9e858df300148f1e5ed12eddb51c346780effdf50ea61a03e8dabe7c42ee2eaefbc40e742c4dc13b0ae373c916fdb3b0d6b4541a56c33eb06253a274575b5247b77f991467fe54f1dc313d1834130999dfee730487e8259535a56100a87e4971a9a7
  | 6 => 0x78d163d9febd5e16ff767bc041576a2282cd0ab383c20796bbb0a02a1dd311aa9bff70e25ae19b7d69557c0684b43c56b9458d17c26296a6beb88da459e093ddd7b59f4c301646253b4357ab3b1eb91888b2fed84155a1bd9b4f34f0d5805ee52300712c8756f077d0255fe2702b5f863079e58
  | 7 => 0xae29c9afdd31922d7895c7e525c9c1cff43bfd6dd06814fc683b55d26e2fb38aad019757f3d1156e2c9a5e90f4348addd56d42cf2a8744c08ffe2017eca49244973a6cd740fd9d47f9d9e0681f970d9cc1a6571ac826d70cbef3e2fa97d114a2914b9c8a905a218eeec66e73c60bbc99e7ebd76
  | 8 => 0x352900974fb02147eb9e52c1452b11a6cd84f247ef1afcbf04a2504a92559c9b9e10cff9a66fb9ad59c13ab62d7d6f59d13a3aeeffcbabb5ba0cee837bc3a1b98923e655171e2200466dd663763bad656f543cfd1a453039b34d6b5fdd0210fa762b74a9bb68e87072ff73555e96ddcbd880fdc
  | 9 => 0x43bf79fad7ff064c0ef9f2b0f6413c2ffaba09fa02860d7dfd5ea7f1197718c041bcbb0140bb75b5d3af43372fcaeb3049304cac14103ccfa28937873c97475bdab44f526010d4309f54141d5716a7b58ffd40251ae298b91dd5711cdaf6ee118cb7937b801cdaa7c6c716d9b737586b30c9b34
  | 10 => 0xea421f0d1e4c628c543cc4376cf278d64b1f010a115c38f7ff214701c692e76ad93ab48f194ef98ad7aca5b566cf4ea4ace092f9d892e6705ec592ba4f48a7ed5d948639450713f8b4b960b48cfa1700cdcc54c401cb85edd0567c2cfab296b443c4698f59cbc14d032f3ecc94c7274868873bc
  | 11 => 0x49b080cd4344864bb5cb7d19806d853930fd1d892a2fe0e29eee42ce0249cb03f65d9c78a8b8127bdb6759c1f394eb187a47cf72416063c97a716f81f6049566fbc4b123f1aa91a064e2ce4a6befc2c1b787ac0a1aeaeb94ab3362472864905ae557d08f1be8520fa2fb29a51eb04a83ea1526f
  | 12 => 0x5fc7c84388f2a591832ab052f47fca5638e5ec1974cf681db3a34c64aca985057bffa8d1ac17fa1bc82b08e8b2b87ffb00249c39149df7f3103cfa3490f3672c29192b2f7c529884cac29e898248afd21ab431293f3edd333426824cef28005be81cdf1be820bbecd4202c2baf1aa822b97a9e
  | 13 => 0xe8aef32903f88fd4af40d43b71429aaec8decbab82a874911f7242aaf4cfc017d21e7d7ee2de93156f4d53f435a0b70d631244625ff01812dd9524ba00b83eacfab77af83cdb80af8ffb33cd63af36867e2a7d6f195b45bea6d5ce921f2d85bb854936a78df74d049ac2b7b03f62d89021cfb8c
  | 14 => 0x7dd3bf381586613c1846464858d6f5de2bd366aa8f609a198886e81b7aab1422fb225f3a97e2d39634db79a805c175cab9c4b804f82deb5f0894db5b806e88d10651b82a9f11e8d0bdcaa531a1e32bec8efb618da2b8c21e75d5845acf2cf8fa765513e33c1354188c793db5441a3d75b8f6cb
  | 15 => 0x94b450e286a6da934540a0eb3fbe8379622d1ad466ab960c40bc744cf80141c96acd4110218e5cfee97c1c8f2d9fb7457d2d331cf191344f5dc4da101e75466106b0fa1385e9fc2ba93b201a738e44f154a71987773e353d9480476dc2054965956b58514febee2303d6604b22f1bffa7391d03
  | _ => 0

private def denseT0B8 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x4b4708073ef02956cc741ecb7548bc9b1d3f73c0ff4a61fef85db9d95c2e917611922927b25bf7f4f0019d07143540ee930efad63d60d3f17a73d83c086457059cc5747def4b21a8c47829722c0e975308133557430979213c655c46c9aff28e6004b7a948234b958fcb42d59a62a097b17f58b
  | 1 => 0xc6cdb7a9970b42982de8631126b5736dd90629c3225e15263fdd0dba31b114dc1696a0b460e7930cfbe08060c5c1fe9763701fe8a79a4f3b1b08471bf072daf9cfbc60ece26a4cca41c7dd67470c2a4254fef4f4240332b8cdd9fd8e0677f7fa534c09b2c5c4336b139473fade46f2ccf6acc08
  | 2 => 0xc92cbdc0b926f5659ba41880080a24e266ec551476c12a569a06416ec80fd390b7d01f7815faf9eeba7c35ed73b1578fa5e605a0a55bf6f69521509751eb4a62b167c7872e5f722aa58759ce3347baa3e8237c27f4f8b240aa5c9c638cf0ecb0ba27fa94d12a9b37c07056dd076a3a468747bbb
  | 3 => 0xa6c05a208a677a7820c162cdf3edd87a66997fa376c24fdbf839ff713ecf766749a195f4e40fb1bc52561cbdfd4e06c4a194f6368551ba5c8d4b29dbdb3e5a7c754b10d8b86cb4de6925479329ea73e3b46204f76c557700d55180b1ada7f6149242e0b9933ad85f9020cd0b93101ec19614c91
  | 4 => 0x90453b99b4686cece351b12d5d718568d30b1ca15c4c388152c3ea26b04454b5e5ff0601234977e654ca351903b2e814096ebe08f79335f0d587e8310f7b4c194967eeea5fed2e3f828a9acb7b43567c09089091d138bee8072b39681b04ef758df9df8bf1ac87b4b2192b59f67c30641a69d63
  | 5 => 0x6f57a044ce3b1c74f112116caaa44e4f06efcb43cc6c5926c8b177ad5cc7e828281de519124f74d647a14d00cd2a832ed5e06ff232e6f8836d2f7c1e76ac82d2b3e856c44187ca092591cdc88246a9046f7ad78e2103b471884c2620bfeb83c9b8224a4cc45e3da6540dcee4fa098a3a6f893dc
  | 6 => 0x372714008d3ed14f419442cc92dd55d504356bb184a47962a6f0a60ce862e1a9803fd7beb599589740f21d3884d0ff0869f2c454939fc9070e7438a0329ed68b3cef8863210ef13eb2f6affb42cfd819129310a6073479c382cb671fdde25a79c95e0d1a942d5e58dafdc82a23aa41e4be4e847
  | 7 => 0xd38811debf013a37d85891a76737888b7c818d5481f11054add25a79f256cd2543c4919fb23562a2f836cb52cb171d16607e2231d0a462bdccc6c52ee19ced374288003ade31a7a2e063ff4889931561cef0cb9590389e73846ff48c964db43142cb26451a6cd7a0cbb8503ba0088ff0777109d
  | 8 => 0x654372b59699dc035845692bb80f942b0cc88d95669132f75d2d833ab236a4924dfc4dbf0241c1980e31accaa38c25e3b06b10eebf9ef6bb64581211288e76ee043dcbd0fe135d5ce7f179d3586c3f5edf09e90519c4140fc43cccdbc06ebfc35a17d7543b20214dda12aa166e6aea197742181
  | 9 => 0x7818a7cf95ec811adb5aea5d4e2d6c4e031c6ea849744ece902bcc17228ebce568b3a2127cd1e447d07fda2bf9651a65a98f76ab37af6ceb240af02d513932c8cd19443ba54768deeb4620bfe7235b323e4ccd66b7c3f2fc0c0cdba581471b1ffb654f4626310083c1afe4d603f69e4869651ef
  | 10 => 0x4e4bd6f6ea311c5f4965306747def4fb4c1289df71107c975c9cc702740c02766b39988a875cf99be07d75b550ad180cc0811dd3ab4a4239e89c9c626a20de9a07b688066174532b3b679020698e7396749719b024b2acf2ff943451330f4f7c6d82b0c43769215f11f60b2c248117301bb309c
  | 11 => 0x12c965ce369638afe5f188f5dc32ab8dbe5425ba9ea81a1d31aeaeb272117196fa04179daf573d89506f47b5e7699f2d8e50e60563fb5392fe43b3b689dc7b1fd9ebb05eb3051af832c2ceccceccb5c794d893387b7034fb00e781ee12efe2a627f6d78023a78bfe96fab863513f2c3cd5ea17d
  | 12 => 0xd0634f331c4ba75354e58abee8846bdefcc4ef389c460d8862683281d86dbb46eca300307d7bd2cbe6ee105a1bbfb9f227381d69f66a972eec41a2337fe79a198c6bc0b9d114e4f59cf61429b1ca824782713829ec3cd1804c23ef3fc531f383e13dc177ecfa11b30199eca4a8c3dc154d463e5
  | 13 => 0x1d4e6cd95dd0525c168678066234098b768f25d471a4134a7b7d6034e768d0406ab204132cc89e1dc64751a8422291105b0867de3089580954639667cf58a006f128971f2a5ec1e6bd319d2e742643d65f99cdeb527841f874999792645a3978a0ee6a530b6d0386a8d2958421e91a6808d92be
  | 14 => 0x8d8ff81c7dc7973e13c007e3ee32fdfa22f43a150363c9c6be48ea5418854bd33d0b615d463b60d47b8c34f55888afddce1d11a5290d96d3a8d1732d23520cf0e57f14f0119a2cab5a3988a204c6246717028a9eb6db6c3871b9efaae749120601475f3e3ccbfbe3d2be043fe40eeb5770d3155
  | 15 => 0x987dde9f082838f83fb9bab680b5129f10f5f9ef3ca7c57e10119aadd86dd9fdd9a83af2463b0e05bd73e9cb5b88ecec7dbda83e5e4361379c2aadee30b5e583db46bad90f57019b54662e9bd94ffe053c844e9fe8e93924d90bfa2123d937d4845085718a326351ec6d84d2aee58ffe0c50023
  | _ => 0

private def denseT0B9 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x9883bac033ce053ff8ba35a4d2d655b1cad0b9db7961b54b3a7566ab62d783f9c3d7243382fb5c28c809e49f0c1124217557345e900f7228bffa62820285ae9720616713e1098402e64385157127ff6df3f476018166d77265cdebd86f93c3d0c2085d466999187d587176412db0070299f25b8
  | 1 => 0xf5d0807bae5773c6bac3daeb014aadec3ae0e92c04f899de52ea0fde306005f8f4d5a2ff6a1208fb7aa9215b6cada8dbac3ea0df239cbac896cab609952faeba26348f8102b9ec2f417e765e171a92796b5535af9736621874971cf951f107769e7a3c1b16211200113b3ca34f88f3c93723dc8
  | 2 => 0xb2a31fc8dbca051d9f79f2963a9ea7116d69e980d4987e37b0dd3a5dbfc971b4a79b132442cd9307103573b68a7e21dca5b2a806c7b29d8a29dc3f02cdeac1b6882192716450e56949ef5706f0442508b865bf7b013738fd1a1857940019d592aa5f81f0611b327ce0606005795d87daa6bf762
  | 3 => 0x19303fc8aa299d3e0b05fcbe94e5a40b633c963e678adf73df3dd6cea38d434866a31fead94722adfe3e70d898d533d1d6df9e481ea9fa2a92ba2f36cdc7cbf183def063aed23a762fbeb1c40177572a97f05bd4ca32d8ba8141bfd4933d35acf7bda38785482694aa7b2ce319af441779b187e
  | 4 => 0x9a4c54d902f6ae9dc84fefa8bf50dafc83d0b85f5dadee31a83c92e607e0105800fa6013314af06412772cd5d82bc6c12ed836941cdb7ed471b605acc1245474d224bf8e30b62eb2b781aae93716c62e6817a1c7701b1b9a40038e694f75d2094471c56965248094bdfe8f436f80d2f56a8e720
  | 5 => 0x245b116326e861fd239656b866e8f12035d6d9c23ab948e3c6c5fb38aa27a2be1b6f2547656463759ab4d81eceb146d0d2001a675b6382c28e9fae705ecab1ad81b42c186726f417df737e44ac639cd020e38e47909dc302da457234b941c42d6dcf1e64903f024594042af93993d2292da5fd5
  | 6 => 0x7684144073d5eec654b35d1a2da4aa075f691c7574b821bd02b748a9fe041576d5e4f23f4321dc6e5918dee2d7d4f8698b0c38939f6d5fe3e60d906301e2cd17c5801c761c486bc07c02f1af8d681aff06c742f265565f7c4016421d283a025cb948e60d9fb0b2acf9a8c8359e3025122d88ae6
  | 7 => 0x45e885ad8e3cb72bb5635cfd22795fe80a9037e624ffbdf158516910eae2aa33a35dce93fd0fc184a0262c0cf421f06795b1d08fe205a57427ea7dccb9ca67a6175ad3d5506f12d1fc57e28ebb2498e1ab113273ebbd3e73c2fed50f0cba4ecb66439018beae36d37fe94e7158c6657cdea204f
  | 8 => 0xaf32ca1ac56d8d85fef68ff9f1cadf065b83713e54b4aeb318043cfa0e4b02e483dff17bf1722499070c23a8b62ac61cbf8af74474a025146b78560b463f4df5a3f79653431ee48b13b1780b05ff23ddf429eb7372eb6252665c7b123371b4c5974f784225693f7126839ee416b83bc5b4fac5b
  | 9 => 0x3605155c025f99122b69f96245a75755bd4e5abda1c03f450996962bd87639ddcd2a1ec4cacec0575aaa6c7852d1cbce4407f311fc4d2edad80863b6a1113023098f26dbc059447891dc0aa31646f2650f8eea45177379937f22c1eb422080ca9b01adfedec307240724990677c42a04e73824
  | 10 => 0xd2a298a538a22a9c870b3f7dea2f59a2b2cbdb4c5df97223ff249d7db6418827c3df5233da02da7415cadff58ba148d1888b6d6c5af23554fcf7691727732c570e86b781b76e43423189b7d365d1ad795a3f99197686df482fdb1432cd54bf2a3cca60b73354c3f7bb1acfc46ceaba5f983f7eb
  | 11 => 0x92840b35283cead2f07b3cadcd721df8f0c284b6fa3e8e436d761215467512c724abdd78a96cabc8ca3fd82df7495b6536553d4ca33bbfb7eef296d913584898beeeb8427e14f841ca992cc5caeae82a7af2a9ac5f949c6bb9eb53554e59ef4765ad6ae6f2aa21e1b1170db58192e7e03abdad4
  | 12 => 0x4b1a2de191aa83e3aff73be43ab4a4c1b96eaf0d3febd62309f75ae4ff42ef8fe979190590c2188ad71a2d90755e37a77023603adfaa8b1d1b76dade39f0beab60f42be02af8bd6ecb501f9b35e53333493cba44d5c5dafbe29b53167a02db94caf561fe8e0bdb25fac838db28bccb8ac0e30f6
  | 13 => 0xdffdc9df4492ada65afa6c3fcd96d90a0e0e822ec1f52f8ad4d2353ddf235603619ec066366a4464612f504333c3a6292e91aba7aa160fe392857d43a3f224053fe9012a2052b95c54c22717c092fd20afcc17a9e41846103455a443bc0b3d62a7d3316f227e6c78f872d5153f4d2b61c8aab7e
  | 14 => 0x2d54bda3dd6e50d810be02cfef1f14b032283ba50b0176a2dc9e2bb609dd5cee53c1754385dcb53a39d7670ad7ed9d8478270ab9b24f8c6177f9f774f4cd879e2cd1618fa2d8648079dcadd462334cb53d141fdda9594172a1982e728082fb49465c7f4791b472993e0fc2030dbfa3acb31e94e
  | 15 => 0x44d5bdae80edd60b05f3cec86a71aea4ebf6d585c4533f1afda13a12e518acb481c8e82f33e62749bb0bc34e099c8aed39f86b8b053b0868f13e90596ea3775036743fbf562d68cad9255901e519fa72b5ef915fafdaacd3c59e14e76e37810b5f24b6f486cf50ddf4f82ca3cf8dae38683ecf5
  | _ => 0

private def denseT0B10 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x476613d099466eda69e60805383c2031a926b9c3bb27ef03a8c71ab73c2fb8999e029d22a4352b08a5f3dccc32a3f5a016567eb07202dc42ba9898175044485260c9e2f665494f3cf8aab21626826a34decaf8c78e7b2c4bfb225523f57a2d31bf33666709759da0eae045582d3832fd0ea4118
  | 1 => 0xd5314ec239f28238d172a07c00970a5a6e37ffc47de55b3cef9fb482f7c2493be3e43e8b4edeea8a941ed70faaad83b0b20faf82623baa57c9a64f2f32180975578250f1450a6905d1d2fc91cc3821e8df3279aad6f1e2dcd0764f1fc34f2905cd28f0ecfbbb9c8ae0f0577a3d0eb22842b039f
  | 2 => 0xdf60ac4611287d1230ee66518390dd769d6a25f3832c90b23c9dc0e04bf9a04312bb4225e5439c0d7bbc2b02c8939ed3081e0d9d2856d1f30dfbe8f8c6b32de367066108e26ae6cf16e40bdb109447c785f8924528884761c071c92416986afccbf607290d4b1191a8408ae35d78da0f6c088b6
  | 3 => 0x23c8617c1e2a79ea22ea3a9a2ba38aed26edb2de3cbca2710e87509bf7179904e2155402d0d6a56fe4f5cbec8d1f29b116d937290043edb190b89d1542e9ff08af3135fcde963add21097733730569bf19bf02a96ae1faf8a04bcae98cf822c39ca2d05d04e56e19833f17420b9b5d03ca24745
  | 4 => 0xd1daefed0aa543348dbdbf8dd776d7dae6f2edac23146ca317b83522aba99b7a01d580e20ec0a56b7762c1324bb30bc2647ca076ef96171d434aef55f50ca04c1b2d768d251a49e0fa923718ea31e3a78c555702b72c40b228991242532b2e6488ace92fe73706c7c91280d2e076bbf50be47a3
  | 5 => 0x8c80b9bb9706c92678c7626b520a0321899568032e6b42310e7ece8353c1d238d797b27ce8ec7c1dfb21f92c6b3757b3c933a91e56e31310b1576e439bcc76795786cb2881d12fd23ddf3b2a41e394f08b8cb3f58a86ea0c0072f26cb4a56773d0914df35973971dc04e4cc53e1171d55b61ee9
  | 6 => 0xec6efec899510c2994adc1b20a68ead2157a5c36887b69a6eee6996874faca03827c9a0889d2e9d1b0c0fb89f65bb5291133654d7109c90655269dc83bfaaa514fffe06acceb07d2045b04d9bc66f3641cb3f652d6bae9088dc61ff2a0d17cd48492a798f7e399ba7fdbfbb490af249c97d0241
  | 7 => 0x98d2d313a09fb06e3f2d15f3524c86a4ff3a19714a40a7491fe5a7e10e7c1032c0d95a6d3e2b2c5dcd0d0c3b762a4e1988a3af8f5e9cef67f5dfad3ad84e8a22b77163fc2588d095c2b37260f84f0374eb26dd071d45af5ad4a3dcd823d5b21553cb24e0897ed956beb9a89a6d1866fd52a91f1
  | 8 => 0xa36a1aa95ad18e34588c3029a7682979f30637cb4cafbdcb4a3f14dfbfb8609fe91a8c12b73a74ee1a0592e10491afb1a152df3d30c8e11d2f36eb38580aaecb8b1bd35e756aa6daeffb21b2bb4e8d76bfd49890e361575ecd115b6e1370c77e2d9248999573c4c7e14b25339749eddbe6dcc23
  | 9 => 0x3e4aa98713bba2e507d0816277402fd52a2394b6cc60c2dba0c74ddf6600e20637fa9ebaa237bf19acd02192c7357317d537f144728c722f50b40c41135b00b1c3586a1dcb43d66363f0ae34b6d417dd27585655aab79963bb073b39abbc088423667d477dd2d24895520b3f7e544e452054636
  | 10 => 0xf70e06aacad6351f4db1662339660e34f1d4077cccaf9264012815cb381355eed97f69527b1548ab70083afe685f366b5ca31a1a93c4a1e5d1d081123e50d7bd0eb9dad1d5781cda8f49914aea9a87cf1adf27c04fc9214390a5b7bb67bacefd9fb8b9db9d924261058b82dc98758b98540897c
  | 11 => 0xd002306f6f6087fd6a65b6d4f3b0030854e2da5d142bb6eb333d3e359d60861db4a5d4f42e9a795e816b1eb91ec50ff523c5ba5752f7c3b4eab0a76086b144a3acb69bdd9b92a1c3fdd4956a54663a39896259ba4e7c95d62b9835d65f801a80091163d81c84a27c373327212a0330e9cb801c8
  | 12 => 0xc65c2a0c9190f2ca9d23599c6449d395c1de4214723b98520b11cfddae0cf4991daa68928016722027ba133c40afb42677c6dbda92edf628563f2e394c0e91b10f13d18b5034f3dbdca37935205e447a4c8409235cf43d36396648a1f02aa8ad187457bd8dc38002cd901525013d2ca7f28130a
  | 13 => 0x39fde021706b21fb17cfa4ac3280d1de55a12bf077cd1ac9d309f328fad123d382a709d59565ee3c836b734e16f42e6eafc773e13744d9c180d7b23f18f7caf7364b009669edc89584d0b92d8f171f40ea45af70f0b693d58aaded8f46c455c2f8f5aec99a14a57295814704a213396b1edfaa0
  | 14 => 0xe50161a8bd1f9a82dff02f36c15d98293f173ec37cb0760377b2f2bcef6fcb5c234656d8a88071a3b28b4690d77b4c9159dd708e2d43228c72c02bc02596b1065f11f9bdbce6f78f55064c4d30dd402da2a57d8ba213a65022464f1f6470007aba25757db02ecc4ba15d901bf6d488e9aa59034
  | 15 => 0x8f0dd8eedb8a627ca381b477fe51b8e07e888f5ca509c81092ae032bf909d4114f7e3795005ef247bc4f045a0f5e1e336b709620acaa39c7444959462ce9ce8199c637562ad2079bd1b9a58071d95d01d19bbf6e84dd0fbe1a84db111bb4c287f8e9e4052e43df641ef82f31a7856c8ab387290
  | _ => 0

private def denseT0B11 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xa05acc53608badd86b61db23f26d6161788a221507b1d65d94d8ca6999fe7ec154d59ad271c4da1cdeefbb8a4798e18463c11bd8c69f65274eac99e2442f37f22b04460bcb4d9f8a3e26c3edb4f4bc9323f9114a181fd3a2969bf43dbb9ee084960a6440aaf8163f629cffbb00c1d976e27a196
  | 1 => 0x998d6a591d0a5807e2fc4d89b0142cb408996285894f70fb1a349df113a96a36356e04e8e67670eb69ddcf3edde534b5c9d1521d3d814615d6f6608b1d6f2639c18fe8460f10b9657fbf1e43b22ca67f42910e71d10fb9f4fce4ff85fcd6ad0d49cd407245939902ad3a77a6ef17d4edb0880cb
  | 2 => 0x98b20f741793c01ac1ce58a01f62470d2eae5ae65384fcf8a1a710979c15a12cea38a98fb8eea13b9db4ccc693d71b87fde9b3a0e509fa799f7d150ebf16da4be1283e6264bb59124aac04994f4884e4ed68fa70712e4e147fddc29426d8f1a8812e1c437286e3c343627091b5a119088c0f413
  | 3 => 0x4ad3ebadecfba6a9eaf358d86ef10b20bae8d79306c9d70c63dab0384d18b582454912a5bede47038eeb875caf030e28053798bebd79b7b0d12ecd7483466bcb95cdbd7fdbc926ae415eb9a092ff1d26cebb814068c36c149bbdcdbc88d9862b0bcc80dfe796dc58d41463d8a43aef5b3f6d9e7
  | 4 => 0x968185bf7ab201e3fe763ebeb4a5f1d5e75c9822760dfecd7508f59502d74420427cf9b78461f08eed600a3e1645c01ca172f7299946ea49ad2f986d365750dafec2689469f276a698800cf2b8d4fbc6fbe99ffe31c37e0abe9f55a9026e2136a5791504017a2f0ec6c4dcc503001aa5fe2f9ed
  | 5 => 0x3cd63fc81f0586340d5ec15ef56d3d3eacf0c09ab0cba4a1db4b07b74544cb08a030361b74a5563afdf7ebea45db03f5c99e674f7a19f2204f05c4f0d19e0f2997b5238a65155aec0857a2b7ab20f584b51e0e0694733ca6aed3e753fbaefb276b76688f3001d81ecfa738ec33be95a27338240
  | 6 => 0x82e9c3176abf2b33af8e0a83c31c211443ec68f6952f936911327be2cb28c51f60628eea9f929730da5580c4d69d6f9727da0446586532fbff2d3a1954746cf46d9ef17f5062d5203d6eda9d6b70266fbee86f2cb10ce4fb9e0ea3efd69363f03d14807badeb1493c581b78713ffd4e21d60494
  | 7 => 0x28bb89f596163c71a57787fcc50256d6b37bed5f767534836507635603b0d8999b94713f773005e8475b2a05a7b8d9a3e52b27d20ccad5b3fd36d55bfa38b56541fbf5356b7ae5d8e64f359a3a4ff5ad46e72848ebfb123a743c2de7620bd37c87a0ca96de8059b4a75706541ccd4bf3af77865
  | 8 => 0xc60541d4c7761944d502b8d9e7b7363021503ebdf9468ddfb655d9c5653790e9e1d983fa64904e05d89970548872ee98c18027968e94e65ee55dd008590ae84bd54497cf91c1280ddd7441c4ddeef1a6f52bf90720c398eb0c4de8d27b75d1cb1b784d81c279dd42b405f76f16adf2a9e0e923b
  | 9 => 0xad9d53037aa9e094c641c12af11ee29c416120bf3ff3aa934f7b715a22499e651d622703bca827b54bb5ec2a512efe42103c39ac8d8540c05994bf547263f699ba71f390f097df0cba51dd706730f87f4e94fc1d9f641c2fc90ea7fc065e83eaa3ce6849fc024fe2d8872be5f22c40f2f2a9b8b
  | 10 => 0x54cda30008f0b70949b830ee7c86c19e7ec2a8d47bbdf046ab6169e6f9fd596b4725c6bd775e3bf7df30a8facc8ef37a7630adb2155497516cf13de5ff491047dd6d03fa2caba94ad904ce9ca6ef52abdae20ec3e6e4c84f42bda050d8f10fe5b4013a7023fa11773fd50d9891698f9fd716a63
  | 11 => 0xedba4e3b56dd8bb8bd0eba7b1cdd8aa81877b96d278e9fd3a85eb8ee0b7f376aa4495b6765a9cb38d31b62244c8aba691fa9e17bfd1796a2ed0bb53013447e90cc64dc364e147a9c7a3f0b3bc17977125284aca1bf289ced6f441a07a6f6b28ff88354a4bede646349ef211464b9d9465f6b2e9
  | 12 => 0x7e0e957dfece90278528927b073fac61d043f73e03754c1233e1bea585acfec6b0d5eba8a67f14bdcc95e57cb7e25da888b8fed2df4021cee2853a8de168c136fdbbbbdbfdaf6bd6dd260e6e60ec8d74ec90003a53db93b9f5ce47357ae12312e6804a345b5d5efee7c0f6251c0c1211ddc2cd
  | 13 => 0xbe427fb3d4ec7f6b4b7e14dda4568a8bfdda156ccc395fce53dc58059fd66160d59abd9d96e4a63cc7b52b5b8637673b1af9cf430b92e390653963eefb3c39a50197bbe1484c95f128e23f001ad86b8d7be41e3ce0c750ea86619a767a9fd36056fbcf85c1e3aa19444cd2b2293504c1a4f6ca
  | 14 => 0x5250a72962abe889b25b582ee391924e29b01909c4140c68849458bb8e2bdbaf309f38fadaf3c63185de41a4b1be76df549e5c7e106178f8192fc88c8ab4de3b4668c6a37703d23428952ccc1c21b696ef245b3f5f6a20ee832e8edf9d9e95f6c7b6057eca1248d11cd57d7076186c91834190e
  | 15 => 0x2e7078e143a9a9c7f27517ce48888c97403c0bc9dbfb4ef3e53ee55e3803e27012c1bf069b7d4366ff79080ce9f432922add8c2bbcb77fdc2a041e01953f96b60645b7c5982f9c041af03ac13e99aeffcf8431786739412b90b5e7e3005b90f3c7d35bb17c110d03589f7b01e98dfb51e9814d2
  | _ => 0

private def denseT0B12 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x6e2f653440c53fa2538d9f90d4de814dcc7de37c3db889a81e9d562d2e36300e4c89be27809e954905c77e58383f196b7c02196c17afd86875da4a7967b744003112d2814ffacc21873c80bcfa0aee6e104f65c4be9f8950362dca1108c410b763079a29d83dfd2da001d9bc5e49450fcfa1e44
  | 1 => 0x423fdd57d7777e913ee6989fbe0f95addc80c1592147e7b76d6a7fceee762d86a8c5c06bb95d9360dd749730f5c3f91810e7f4d8076b652b48e83209d6a8f71eb4e12170775c5f0bf8b590bc37f59eff3319158e458c17f7baf108bf0ba43272b913e5da19ebb8f9fcd5a3be16073fff05ece44
  | 2 => 0xae9a5ac62cef4eb0e725b2efac5c212579a7b8d371e7d8fa98f01406477e9ebf7fd96de6de0a3747569324fb7ed5d6757e69cf8679b813c3563781675279039dd91fac95202cdb21ebea309e1b69b0546ba60f3767e828c1206748c803acd0d84e3f81cbe330e0708d5e9035187ec1bc2556c2a
  | 3 => 0x8290c6bf26d187b3261c75b774776eeec857fa552bc9cff88aab3c1beadad0dda3ab74650da4e7c095aff3b8d9d86fd8e056fef26af90f8210a44fa8d4fe67b35e6f0e709d9163b73c725811be3336114742e91479b1180b2c1a773888fa3fd985207e50b796fa8e69bca8663e7ac5a1e6dae2d
  | 4 => 0x3796a46754fbfca994f31823cb4350c655a1ed16b8fe526a932986a701a6db657b330b64c2ab1665b49bbb931762d8b312755d37b6589cbd0a0ef48a51c66b3c7865b22e92764770c24525215e0134c45824a1902888e61cccd31a162ed995e9c97145bf51c1f697aa4f7bc6dc04c92024fe94d
  | 5 => 0xdcce35cfd4810b2354bd0fa6f8e4ddacb4d155c572978a24f4d02e7db140ab49f90f787f8ac5e4996b3263786faa7bedb20ffd1a8c8408f5a6e9647d348f53b147b675ca50380d1382f4b2a0ae97b2c92b0fe32543e7e04ea287c7e1e4d90b31b8862577c36280f28b0803ab0d348e49a887f1c
  | 6 => 0xb73c80cfece1c4d59c88eecbb9498d5e358a09f7319fd67b75ab7d716766b973a77a92ac0a4524015ef29734ab65b5d3bc66d95c95603d02db9e8c9f11751f96c52e4a932dd5413d562e6383303c1b05aa4c60763057ec3eb91a63f468aa76e2a8c7f89d378be50660131f3ce565c6c0eecfeaf
  | 7 => 0xbbddadb0565b698428b7550de3de19d56a0fba43fbcc9e831368087b5bbb27767f83171706824a89a543e5a24e827996e1b8c8ee157fa3d644a78107a9b5a8d81c5c440d84b7bd8c697cef7cb61b850a309958d15cebfc358b87e74845c4ce2cf530bc115394affb106c4b3de0317c83decb3c3
  | 8 => 0x9eb1b40e951f3cae15e63675abd59a05086d5178efb10fdd975f7307186e9615aa6f915f583480cb0936f4cb2059b5cecb634c0f09351243b46daf2b0d1dd8ff4adbdbc9bf8b8289c250b7d6ba86a21cf540eaac42066b2d9145c4ad171b084fe093d392d030a7d3da633c93c0fa563fac52641
  | 9 => 0xde1dae91820a515467d6740ed42243f613958668c67dd6ed4cd518a6e8382c0fd23662eef12e62ef5110da5fa14ec4ffdf00e777f1e89089e4e3fa42eb5ce0443e76eb5b49e9febc23aa184e4b85916d32807ec6034fc731e31a86fac9a8c7f8d310b8ad1ce5533dccb0ab4d7ddd26b6f51df41
  | 10 => 0x78afe276ec8ef060c3f305c189bdcf94a0ea8ab5a0d2349d3995f9619398b6f29c9bad729f4a348df604f716662d0e62a50473139fdeb8258b54a4aa633c8bd28cd978581c451e7b94f756830b865d2e0879df97c643da0c03d5bb7e557a3b2a251e598c7a411cb058dcc0ed5f73105659a8180
  | 11 => 0xd2fcd4fdcbffc7701a324a6c47a42b8d87d5f25493c073d1523f6406b8977c16d1eb4bb0645e837425d9a6097d4dd445100e287666bdc3a2c7d1df10cb5c3617de273fab19f7096d0b95089d9986452a58cbf75a3a318d891e5f4a448404becc5ec32e83d85de0986dc1ed274e645970f0e18b4
  | 12 => 0x14940732c11d85c17416210e9b2c2af20112450113d247de33722a4105094295eb524b49315e59168411e158e53e8eb13dab3342738d1666b1a15c579406ec80e8122681084d1c33965346f6c84a66259bd2c815239b01e6123034cb648cfa4d08b34dac6033b85f59e4b7067e8fb3cda49c857
  | 13 => 0x9447c7ca57f983f082d24c1cf63da6219fe6b506ad505798b31d650d370c784e2e67b6d3c162e4fe57a77da71e8f0a4179c28c2987cb3d12c77337e07b05f1991cc432441b27be797f3a9d976244be4ec985eb37928d66540ea006883cd565876ac5c548992296e5a20a147c7f01b5e022f325f
  | 14 => 0x4a44143f91c21c8c865e94e34ed47b80faaaef3a940f7f4ddb7cbd3ba289f8f382e97bcf284a5dcbd9d8289211d0ef34be2c3c86818631e4d36ae92312503f150fbb2ca6d5cfe89a040bc5945adc496d499377b6794e553e4e3f4e566fb6b0faa31723b378781ab6d6c8af8111018933f381493
  | 15 => 0x7b03e611dc004b06d7e851d4d37fec41e00697633a95b311aa5edaf0c37e61cb54507060925f8ca0f9668a6567bd92914e1a7b79bd77235e01d2bccc8322df65da5bd4e6182e6b1b57a43610d90afe35a413f8f94762d558cfe4f5bebff4037b3a13e45caca40f5f4e802fdee97eec64959ce5f
  | _ => 0

private def denseT0B13 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xec09510aecb961d6421c1f26c41532916d9c8647c12accd37a2c4fcb0b741427aabcf606da1e8d97ddd44c8eecb6a1bac4dc1e7c407a1e126cac3c4c50f4b9be4043582dde7d96b4589f9a9e43030305b6e95032e331be63a5ba9a5676812b33c14278418f84b41c06a1c43bc698fac7d7f9929
  | 1 => 0xc599d254bd16abb7f6dbc89b6ee7fe21ebf3dc0f4791b87908a10bcdf57406c28eb3e62c4a419412db91af6465ab20dbabb1e80429e4b72f1117926fed204a6e4233db41fc0028ee8cd4588c9eece2f2e6c617b383d370470a633f43044ea6e716815540089193e56181fa4681f3974d279cffd
  | 2 => 0x8cbecdcbc014644a23c42d591dfa4c0edbd38245ac3c26d891be3b4582bcd5a0fa463864bf5f6bd821004acf223523c7ccab959397682604596d31e34a3eae74be626a7f7cf992e3454271829cc17984d2b3c483dc8b8c8e32905a64a582c71876bcaf68b4e22e9231efe450267d8aa357cbef9
  | 3 => 0x72958db61e4b6a905f6863a9808994b36888891e135028c35ec3f3831290563f45f819dc53e7d8fe0538c4ea24963911f3de3d950d9b09efecf0f90b7e5c204f5e23b9fafd20a11b19fcf179937cf03e57451d903d28d3996cbb707292d7083621e9f9c24c7e2c09f272f79c332b004cc0b04b5
  | 4 => 0xc91bdd50c085b5a70933ca3af18d5b10d35d7994a82dc3177a844b99ca4bc44fff8400d2facd429952f8a19679ed09d40b1f07727a86c841b1bc8782ebf6bd46d8a1a0db4860eef67d6fe4ffe97efff46dd500ef9346223a4f402678c16541f412265e97877d2ab1e15ea2bfaf95c564b980424
  | 5 => 0xda4b554e22762c02b0c512d4cfec40de81f2e673f387769b9693a1bf0e51d42322be88dff45507a916ec271ea7fee5476b07dbfa85950dabd268ab5a529236f7b3b8c853ec9d2c69d299910b667f64cac4cbc68d994faf220c6a0ea063f21072b6d378260037e095cea78fe41f77c3f940d02e7
  | 6 => 0x352d742d337b57b7ec92126cba5ba66d910d653ecc0d47ad3162699e72be076190489e92c9efbc4c5187eedd1a4ee7f85da55057a2366ee5ba4280d69ba6d160dab94fa642eb927c351d77ee6bb7f50bd7ce8760add88cf5266671decd857b37cf870fe97ecec04a4802fc5e7dac639e835e32
  | 7 => 0x490c15370d9cae26e02b437afc4c67e45e7fe7e2db1608696d36055d2c8c99de28bb515f5f0d51bfe7563ba89dbad8c80c7b39410841466a9f484bcc0a0d43b964a215af150b982560e353554b9c4b5aef97b993347f1ba0432d43e23021bd0e8d7fdaab145b7524f8d8a687aa8c177a62773bf
  | 8 => 0x944fd674e77b688e7f0844b3dc547f0805b4c0a6738583111ae2b139d877052628b7be347664e77cc293e18767d501283348d2f6ded8c0b0961fef06650958399282e4bebefdbafdf41178bf9e2e1e5bb79f65cf19cb0fd41c787a5f9ce7b1398f89fd5e5959e921e916f82233bfe79670e6140
  | 9 => 0xec399e800df282acb2492461b962753964105b7cf7a982c87b6b9f9b0bc89d2d83151ef73f94abbef015cd799fe7734a66de88cafe8867f1c88cab5eddc9e1fd86ea968bc1f0b6742401eb26d9e3bde63d8d14d21134052f356755d6f99b54c5787bb93ecbbc6c559d0986090d6d2895dfc28b3
  | 10 => 0x4fdc1889b761a7a9b9c95ca83eabc0f610b64810b08e819afe82c72602d8eddd13b2788b73ff7853b95c30d4c64c7541d59652e670e306c5c4029f09ae3f4e5ef6e88cf5f19e37c83040b6053e4e7513a8bb687966251f2cdeaf1fb7a22b459885926a6880481647326f7e87f918d2fb0f6a519
  | 11 => 0xfdaa64356468da2fd0017f2b913aef14fb29ace16036b556128d833177e4936af46b934e2122983467f7c3620e8cbf8359566b3e3a2a15ae8721ffca89d16be2abe09988ea419bf49ea91fb925d5af22f0ebd4fbc16e8b3a013fd2b58995d132bf70aa4e96b898c81fbd181befe8a3641d10706
  | 12 => 0x1fe2c265d16a662ae1967817c4810438d5f7ee06006e010b49f977849b67d449223e299ca5e0b81f06d6206ef6805b78a0b0501b711c1d7221b19696666a58f00b193bb6428dba7eb526540fe96573ec9f3de517e5328c5e9895a25c6d7ad2dae89ae7c010a7f182ab1ce474f171a73dc7645ec
  | 13 => 0x8b600347fbd3f8c9afc0a5155dbbcdd8d47e93a2359c1f6a493b8bc11773bcd0a6e74a0b4e1f9327ae7856e196fcf73a6add8dc1aed2afbf87991a8920f59d17f2224d79aa3acfb74fd21fb820e2d2e3f806d2902b73ea8648deffbfc5cce3096ef3c90bff10a6047099f05dadb20e0b3295769
  | 14 => 0x2cc4385e7ad51508e308c6326af038458bd7dd2d58032bd498e5229c212e9a46e4e6faccbbcbf61283d30eb90fde253675be3b542b86e311cfa131c51408bf2f3e7564e824bc33cef838669046d501cdf0a364f8e79a9b82204037be2f34e0a32fc3f50421145a3e110b0557b7171ebd042bb6f
  | 15 => 0xbff64258a64d2293dd9263de84a19af68e95939b6ffad4dddc62947cb98c7a955759a5d6f6e5163321923c69ae778965c506590168eac688bf49b927227b27f5da8dd1238635af60acad8809b34929ae3880b73473b5dde0acc06152b1a0b9c1c89d1552c2048278a1fc98c37d68fbf3f030e74
  | _ => 0

private def denseT0B14 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3836d99f4aec9d2ee2727474d09cda4d427f2c0aaaf005d9faedead3aa7def8e208ed0a4a321a56abab4ad5adae6b9e29160e2a0229abce9c364060c5687b666aea52ab45346dfebf1114a56171037edf2364fe5289c9520dae470ae87c522b3039fa7c87c6bd81294329271b8bd9ec84044669
  | 1 => 0x97741319e7dafe3a2965c9323759cb1d8b758f84d258df0291fbaca4060725ae9dd4cb627729907dbc172c170bca31d345fc565e3a5c06e286da7754100c7781382068a0591079f7e6e3188eb053b4751b74b60a93f138b322275724700580abd83eea68ea316c59ed23c3700726842610f5cdb
  | 2 => 0xc372ca574e3c0a4b89bcad1d59376b2e4527a664f481ef3bb6bd345e2a77db29a22820740d086aab1da188dac21bc4cc46f6f154acbee0bf6731eddab1ce39c826d018a3494a62f05e5e04a63daae7d8bcb73b889a61c6db2b1db4802f1a153b6466396c3dd5f22235945cd0f688298eed54ef6
  | 3 => 0x6dcdfcca446423cc8874efb3d67ce0ee7370ca0a5c5379ea7f1351596eee7634ad2d539c9827c591b9e61b9b42ef2b9e9f5ab7e5287a0a07d66bcdce8b56c71f3a6e96353cfc17a056ef712cbc745436c242cd3b40105ed16a4901ec149aef8024bccecd62f494773c916d11d5d74d7f4385388
  | 4 => 0xfb6a07f8ff24aacc30b51e0aaf9d4068113aea3b52a8d9ba7af676c04477ae13a211d03f2b4cc42205dba861ce50a759629795f28c7cb6b2e563628f033915cdc2daf737c84a7017168d12b4b44ba677247fcb0f95c073256f94d9146b38dade2273d227926e6788bd567d6e30abc8d2013a5c9
  | 5 => 0xa500acc4e899733cbf58c49348cf075375c2901d94b68e4c4769bbfd30c8a6ba5fb9e7fdf7c20a56ee5e85d3a5daff42827aec1e4f4ac1ebaca71b695be61e24f58add770d7e74b7bc476726368c4e75a604acd7b796ca8d6d00e3847a265fde0393e0f604191f26d6937c0bbebfc4338f952c9
  | 6 => 0xa1784ce22701b65f4462b3a40be355ddab04e336a6b7bcedfd5be1ac1daad4ab34048732976796cce8b6a6b2694236593cf9afb432b12e94a18e63971319570a5296d6cf9d2c345c2d9a2c29f8521be15e2d77b4b43d808c75bd3c5444721a59549251358776041147adf555edca3962f288f1b
  | 7 => 0x45a598406f37690d42f3a063afd48aaa2538c74384549b7c9232b45e369b56de52b09ad5642d9b46ad49ed637737fe168d8bd9a374ff3ad8e7e11d141de5263454b34aab124b2c529e36ae7bea7fffede21d7a1785eb30ae113802201ec0639fc848507bdd9c79500cb7fc0bc499a028dadf2fc
  | 8 => 0x33d73099f4401eec23c9bdbacbcd3d94ce02211143c58a495f6f7613e262ab3927872bdb36d5e6a8b438713aa1db0ecdfdf4a63070a85e32c96363c959132ac8eb6d14b4d35539eff88100a1165052efe2c41f7fda061cd411c02fe5a3828660bd3832c1e62b7049cd364fed690faf61335a791
  | 9 => 0x6ea4b54a968621fd8b4e2b28e94087da7b7d40002de9fc96085f946e899d3a54256c06884935c20b224e773a6e1e214871b05eb63baddc894d4c397a82f53d6a9e95866086e7372a33750ed2a79ef140dbfd8a6832c33b02f77b7af6c3501e3c1e65b16649fa6a0d96fafbc6994b0911366ec2
  | 10 => 0x1e6530384b83c51c6cf7d30952604fe6990114d710d8f303f00d8661f1408ad0b9a5ec4139f1cd6ce571a22553eb6a14fc97d5287c1c0680d884853dda62c738438b42b222ac3c21367a6c18ee0a0582c61971de7bc9067448d6474503f9faa4919ed6f3d7c3db8f8192f44b511f9a0b4769ea8
  | 11 => 0xb87d65cbfcea9304f4b239d9c4962b20afbb3125c4959b2c53eee530b0c91d13b8cadd11c7530d121cd688d6496529d460e852ee29fdbb9684e6c81691429d1242361f0890b3bf83c450b2c4fd9f7c19c537cb727fdbbf9e2699abbd50234fb24ac4968c7955496a042757b73c0b1ebd5a9efdb
  | 12 => 0x12224cd14b9d7c26d9092e519d9f388aa9e06e6f40d94be85701513d70ec431d49225edd8a666e819952320fc5cb758e84cc6431b2caef406816f217f51a8b4329a1d52de3fabff029c5e3b3878757b7a0e298c8ba94b45d05f108177e3a628b2867fd820f5cdaf84e76e6d727a77fedac03ce1
  | 13 => 0x824c649fcc509e77cf8cb6484ef0ffc3090de1a5e7027af49bf73f37dfa150d2c70190eed7013fa90eee0e3bf9557ffd68648f9c2dfd6a17d7a11257b6d85419a8184f8edc66615e7ecddf5116a38c5c8e459c069603602ebea22b52611a1a71ed80383c90f06f5db84066f5ba52d83f337acb9
  | 14 => 0x62735f68dc353ef3acdbae3001b3a533a6223141249fde97cae0b257a6373335b92d5bc53200b1132b353361e67a09b1b062710351442d4eac3eb43eb2ea6d6b5e75dd3edc9bc0823a80d63aea3e99552e1de4b6069a2656c823f938c472706498377b0a3871aaf60b32884f17a8a95ddeae3e9
  | 15 => 0xd5a683e227a5d12c3ad17a0386ab915da3da87e29f1ae334beb420e84a4bfe61bf9dae662df51a94ef650ea9c649311ceaf748a793a3dc2a5529895555195cb324c545bd7de5c74378fca623b25ebe60a8ab3ef95d6fc24fabeab8433701cd18a3bfce11df80226162a288dcedc24be7ce85964
  | _ => 0

private def denseT0B15 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x90de4656f805aa608dff0638edfcad14e61566a385990751c660bb38d95edf09b1efc6d41b1ccaaed135c94a0bf9c32f1d841d31bae65817c395752ecc9bc48fa1a838825a1b683699ded47605653e447e5808b64fb0d4b1aebaba97adf0a4c3750765468418b06bda259c74c395256bc87f0ca
  | 1 => 0x82ca0c7685054478390606d8b8dcacf3dd44dcc3959a4d3ab3fe07a829cc136ed19874ea66ffb5101c6c6735cf45bcb9f204fd7d153f1ecf8e66d1b5fe8cca0bc2178b2dd5ace28ddd1a9e7bfdbc6cebbb6614830e332fc319613bc16b1c60b0086acddd16a921d09e049f93582d19cd3b872b2
  | 2 => 0x4901b80cb578cbb283b32626ba9e10fba986496989f452231c2c6a08e54835f3301b7551cafb699a55fcf2d6720fa2117e6bcb52b272bc7357e792096e63e1d1969155e48d628e2b3a129214a9602797b18c497a1ea8393af28e7769cc4898e29e15cea3bfcacdc5e51224edbf681708bedd307
  | 3 => 0xb9fc7eb377dabea1080d38618ffb4c289a0a2f08a98002e044735ffe25f4438ffff624e1177aa70c6d26650db45c2fb5fbc8625ff856b4faa8ae57ec35f9c8769cf0eab7c2a00e1b6ab17f9b14f62869fd002172b95d0da093ad382c7ca3467ca3524a473ad6ab49b639775f02fbdf500db0249
  | 4 => 0xd55c3f1ed34866af10d743862d5f39a9dc42c9aadc6a178352e9fd3b6111ac8c9188d3120f73ed542248efe85231436ef169e024d660a1eda5cc4d16a237c66cff98d8b6b515f6315c90a1e05414c1fbbe18508d789f04ac4e6cd3b51b71a0e73083226f02dd1d940a2e05632bd13d8e7dd4fa6
  | 5 => 0x91a767e72c2b49ced6c32cfebd3c6d8265385b812eba2801ab653402d772dd8ce41168114357874b1d864a5ed679ea71116f293a75cd7ab3bcfc018a83d5e35dc7447d6ec50c555ad793a620eea52aacb9a28495099c9bac3e93d7abfe3cbca99bee215b46275ac6464a100752b3b84aed61c
  | 6 => 0xa7e52a03f86762b5996d275dfd8eb248f68489f4124dc2e8cc21dc51176eed0941580a6227c718dfb26d824e8cd025efda6c306aac0dfcf02f829661794cac3dc7b10ef89dbf83f73b4c08fdb958f2122c1cb2a0d01ade6965609f14faf3814cb787656038cad067d04846b2c123fbe9fab8145
  | 7 => 0xc3ff4e31ba2a452b1279d870de091533bb418c42a29f87dd5a9c34ece5ffd9f29bf840dba94078862312ca6ceebd33c224b7971862ee9e4d2a9426e41d9f1613fa6028c1c9bea701ff32a6550032136fdcb07b73e2d30194589f1d77fac8ba51dea0f613cf445b78d9a3b14cdd5521b7074073f
  | 8 => 0x30f7408bd612f6ccac0c0d191a22fbee5f94d434aed8eb358610d7d0c408111b209c82ec9f1ea41b877ff83713dd68e4188788a739fab91316aad7898da0e82b6f90f30a912fe900e96c9f7e1e752747d227f60566a35fb4e138b7d025f9631f8e643e09ccb073421f160b93a0d2e4f9da5aea6
  | 9 => 0xd81080563e4e0c6e8817eacd2da91d119aadff676b0ca0ebfc295cd01a9abb1d0129f463ad02ed041c8dd8c50ed2e6e723ea9e6569fcf9881863a009aa4963a6bb2c777ce8513e1d5089c53dac7e68f0d78e1ac5299be558cf3912f4e80eb5b78767759673a8b36b1fe5404b207bff602871874
  | 10 => 0x779c0bae78886a9da3a9c953d340024ca49702cba4b59b72556e7dde1858fb586952721bbceeb78a72e64f08bd61affa16735432bcae8d344bcdd6c541dbf36f2f47a8d503033dce443a2c2987fd179628fc0a532d56c062eb926816ff915e2aa2c2bce69786b5c220761ea910d57f6b8b39cd0
  | 11 => 0x49a36a6e1a3b59e35e39b644b56501131f1648a12bcc028bbead62107086baa8e982e88dde1097369afc1b72f1ed3ed109b7ecf5930350395d3425e43ae0dac45906baa26bc6e5d7b4036d00972001dab0ac401fae4734d657ee3d64b3ce85292a7594ed818d6095d2f3d621b7ea6b1e5facf36
  | 12 => 0x460860602635c4b9fd27015294eb70772ddeac3e2bd4064306e59636e1be3eea0528f1bb8b6d13f5ac10244f7be377ab5c4b68f9babac60c83a84216e8bd4650a285574e6e7b66e8e4a77c1048343827780c154179ae66c257a866b02a2fc0bad580c3a5b965cff020022b3d22a394c6bee6589
  | 13 => 0x39ac83c923cb0db58270de2af2e4244f7758c5437f924c153dae122c2c99f645dc1664fe1a96abd0a134b65fbe4a7c192f5db741e734d0f367e61f6e476e6a54be2bb2a433e12a56e8d4b66aeb6e9eb8e8023c0e5107049960dc11b5562061eabb9186b2e3920fb56d11615d127785f8739cc60
  | 14 => 0xabdf53fa11fad9fe2862daf073b08fcf9466ad7211dd38dc3758fd44b7e98a5bd558e665c3a1b55381ece565d71ca452d1adf8e8818fab675637044ccf72efdcbf98b625d1ec1dd871f37f17845a037f1354fd3c852d7c2d49324ba660bae2c680af3e08a0f318f3116e52b0104513a43cdba3f
  | 15 => 0xed1fcbe77b2d37210e6d9317d7107356ca5651dbf15561518cc5436daa43d218ad9d27fdfce9dcd2f3818a07f96153aa0e05ca2a53387d4268ea763589f7e24c7749724058f0ca494ebc7051809c7eb749ba8bf53871ff6c72640a04bfd86120fff1b7ef137a661d1b1c3ac54483ee1f8c792a7
  | _ => 0

private def denseT0B16 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb1e57341ae3fbdbc3a6bee551d2c213452ee1316d82e09198fd8b490f67b5dfe29de65c29bbcca66d472dbb23f9dfe5e8548670204cbe9c614e7d5d4fc8763e0518dde5dd49764b05dab2d7324a902e1c6b64106fa23498e881f1f205c09cfc72f379326adcd6068f303ea0ce36c58df7b36e01
  | 1 => 0xc22e3aad221318ffa5457fffe91a46b77f369a04a138d937e2f088ef10a7ea7a376cf82c9eb3d46d73cc651702163371ff8dd1c46fae88d5f350a1442378017f517adf8a70c51a2519c09bbfc92d9c0f9f1fbd55c22ed60c412b954f20713ca724ab61944a8360e4088b0730bd398027364cc5a
  | 2 => 0xe2e54e660e443f54235a5e0dd97a2949e27d1510bf929c13cfccef8b54feedec33935993d0f05646a04cb9962eeecf9574deeebd4b3c921d00362370065fe9c69b997f9d7d5cd48f0f73d4ddd1ca34f444db4816ca81e6776682f3b37399b3efdc4675026e7eda04fd56ffaf1432706332fff98
  | 3 => 0x9d472e8e5f2d23e2c6137eb82840236cfc178decd3b01326eb1b42b8d81a67ac81830ffddbd25e225e7b2daf64196db768e7535eec8987354e4555eec46e819279818b792a984508993f5a727863576abb92ca5edc9130c796a41f9013fb76b42b4c07ab24865edd7f289fcc3b71bc368771467
  | 4 => 0xae1950da4abb47d56d5f50558e506058371a4329423b924225ad366584caeb8623cfe86fe2c1ae354635019fbd789865be2d05cffc1f730dab10398570904f905b584919cc2d87552ddbd66d2d04608d8875e1bfa9c36ae294428df0789ed2c7b919f16d12787f8d986478948136a12647de0b5
  | 5 => 0x51d3ac4dd163416d1cd0d8dc93b1ecdc1f22054b0c8edba4a95fb9ccde29bba6242af3ab163c26e4363df4f4a660cae9978e74f018828851b451b6f34c6e30246637c3b113c964b4c39f9e724cd09debc4ccbdf8c5b19e0ad018c3257684b60d08d4f65c383ee76ebe85abfca544b751313e370
  | 6 => 0xc39c15a9e8dd4378a5e4ae0068794715919e6441a280a523a9e45b85892fd8c5052b34e03d7bd5787fbd2c8a605556aed128f742aa389f77dab1f405a1f85c6f42bf089cf74c671877434cd6ab307bd7eda09701cce91d38766d2c315b030339fe694969f2596eec2c1b70816b95ff832b009b
  | 7 => 0x811a32f3952915235a90a3c9830fca9e28f42936a02e6323ed447cd1c7d75af6c4fbd135e7ea1c7658af109a15dd8c330986b291888898eadb6306dfb226dc01f5f380da252fa2fc3e6d0c7e8e74f78806be1e6f9c90c3d2107b62739261ca6eacf8861ef4ef81a9b7e8414e6535bbe0e8eaad0
  | 8 => 0x9b6ce681f448ef29b93c135a2d429c8fda4882f454b18c37dbd6311aa3b5f9107c11d5f4f5712c1807d82d1af47a84680b09183e44b1882c1f59b31d9cb8a809cfbe48bb538d6327de39d2517f41adc9dd6f7b2bbeefd76f7955a3342cfa66f77c9951f2cbe6b817b7c410aadfdcc2f17f4f692
  | 9 => 0xa01bbc2119ceb12e525d38820e110d1bc2e9890a9fca71ef8ad80e373b5f5c353fc5304d99c4c7e9f5864c97de119e4dd86a713a028da5e732b17228f486150b57703163c96408e6835b80233430f8c77a7e65571090b9d67711148ffe1eca1e8cae50c3b6b87066f3574b35b153a09157fa078
  | 10 => 0x731e0f326f192239809bf4f6cd29e9f4b1b8d08c585d5cfef872974718c9d990574d52bb7c23bac9c5774c8841a06d6680d7fafe777749f03019194ce556645156b851438dd227fd7eb827143feeaf3866410c9c4494a27f126194744f474eb291a95b66e20b0a03afe4c7310a01adb22d4be28
  | 11 => 0xd64d6d5bbb74b605aea00692cbcb6c6e860a80479819adb55f306bf13cf348e7831e77a13eab36e2fd1d22124a61d437d1ba5e908255d82555abee8b1c92fe14fe25c17707fb3f80bc4fd7c5b687b0b50d0353659a22d1df8460848616c4566e57a8ca2f4c69c627c21f55c9235f2b73fb2c30f
  | 12 => 0x822e58654b07ad4a5607b01226ceac4ef60b3a098ae65af567298cbfd08587301ecfba18ec0549ba049bb303bec3e0dc9c20e4c10fc9dc43570a009a072ea5431a663adfe56ff7b1a4a1c0d8ff09b3613df9545c433d09ff612bd0ba6ea2e410563f2f9c4bde2a85df0486504e78997cfaa0310
  | 13 => 0xce869a10fb866568da04358c31c11a4967e818d2fe0e595b4093c72e86ba2fde989fdbc3721529be72379c9073520d016ddfb1d8c9725ab0b2b44505e93abeb5c23cf2ec35eb1bc8025214396669fb12f753cac6c704761257c08498041545831eba9df5f011d49e5546fc78db108c836e202bb
  | 14 => 0x4f2847e46fd1502d4b944494332157c5dbcba9845a12c84d6c14449ca3f4e07a42be8192c34aced1833f21ede62739d5d40b552f2ba856637f51f382c3ec8635440afe557c4726598c2e751cbb26313f219d2cd99412e3dd73c6509328f05fecd93a3c9d7f3bf60787b6713869a75909d51e679
  | 15 => 0xc0b8caaeb99014e8644fa4524f1b05acb551bc7ee392473803c5ba7553d53e37a25aa0e1abf42a6498a151bcd44f9f4051abc7ae3f76c0e8ff6aad821a9c7bbe8fd52d49b1b711b5a0fc96d8c39b4d3b0af0de0ea738245f03403f940af5ee4f7d5061cf092b8dd89991b1bf739bacf6cd7ad0b
  | _ => 0

private def denseT0B17 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xc584656139d999875aac6b656bd0353037f5761d1fde65d057c53f7c9da5a9df6c276363e7d4ae740aeb68dcfdf53eaba689166052c3de7af85263c3d7fe1a9ede0cd4abadc27244636cc58708a4d4bb5d7cbfd3204cf7880b947f6e0053e1139685827c0e9db248e7613ff3a1b514d14ba010b
  | 1 => 0xf8099f1c5109cfc4e5387b950ff3255327d028953ca3c7c2fcd850079747e0ce4cd945ff0a318579d6e6cbe9d9ebd4c3639b09f30a08af2206889c0a011bf1c808c3631a6bbd3c4b6740714b06223d070a99877a204c70a9057a9e8c169647a4aba7ce2f56b7955fb9968482bff0633e7ea37ee
  | 2 => 0x2fad3f5581f9574352cfd50a219bd732ef5340b1868e070db39f376b104741614dae3ffcac7ca09d18bcf72e355b05b377e44c82494184de4ad33394660fa1c9df3ef4196382e6bfab9c79b4b7c5ee7c19eddb88977dbf155218e719dfee51653446c45bf77b5dc2c38cb3cae7cd33f9f2a1f4d
  | 3 => 0x98161d6005a8780ab7072092132e64c55f8a09fa5b46beaf992e8b2eba5775a64891d48e596bae3a64343bb1d2b4bcbcf8087da69a8ac090d1b56f615e9edd90802b19a7e58293ebd919097b04f3677283a31666a7caf6f9374d9fe23d0c8bb6cfb2ee637528cf2a50705300349200057b4f7ff
  | 4 => 0x61e040567a51575bdd590df4075415b6cca665f9e666bed3fae5275d93ad7d2d076ef1ac47bbf499a56f7bd6580a7cb22cb9dabdaabab63e8a6916d817b751f39f0170e05069b2d1ec2136b9d922b7076cd199ae9eba0873ee5c42a4bf4b6c4a66aec624eb824a24a5b4b6499af756e9bf33d3c
  | 5 => 0x3992ea195227ce17141eac162bbaa829bd748f33d253dfcb550085e5a292d93bad268722ca83ed0ce48e6957827ffff832f9afccd53f66abac345d71d18f17ef2b7dc4aed2a31a17f53449af35c2d1fd76f845a64b390f531cd903dad7e53835c74fe623051b3d18a8fcee3abb105aa26c13001
  | 6 => 0x5d4a7f120c3a164db2e51f36bbd57437719619b4d36e531c94738b7e3db71fe5774a7393afc049f8e725c3a31ed23bc672250d83737cb8a65d7d5adc849147f4bbef8efff6f6f0970d18dcd064d2da6a040c0ba66d20443b76f8d89098d5917bd3f0c9c88b3a6bc20cc20fcdd4c73b84779245b
  | 7 => 0xc42fa2b8beb99e05f90e361f22d31f74b309c0317aa8019ed1f5d37eb6e0362a6efe4ea070f43d1ff1b19f097ff8cecaeb6a7aff350ac9a720ce18d139bf17a918c568f04e52c4df254c2acf097e9ce4facc42b2b85f96668547645ed8996b0947a18783b513b3d8b051b0241ccf375503839e5
  | 8 => 0xa4b6c5865aec945dd990ba71432fb889e462d37ee99cbc2acbb9a5c9cd29e8e27f1dcfa8213273d0c07246f1e640ffd080337f031dfa084ebaab49920796e3d37164be8959dbaa643d3dec6639f3744f968ee51921b6c8c0d6f06ffe36b42f2ac5b01a1d6abae59009d89c64135acb640da1bab
  | 9 => 0xc093de618cb701232791030072f3df2e3a0202578e014c29d3bee14dec87c47ce1af219958fb086444a567204b40da4ccf5928001a6e68989ef93b38184eef2f7208104f7d1b23b8f08285dc91db0805d62ca70637f168f3c0d69dbb941b72deb39527cc0a1b7da53a33a9bf102446b8e77c0a3
  | 10 => 0x25dad40f7847921e6aa62afd5d138cf9f2a5a7d468afefc69a754a3439e4b1d995de0cd5569f81665b84ec231192e47e4943f0bb7cd101241bf01f167c90a19969b5ba4b80b2f2e5496768b5f0797145e7d2fe0c5f7f4c9c60748aa45aad0fa843fb517b979d4e3602445cce379fc9a26f9709f
  | 11 => 0x826deeca11004a226d79c877e2b9abd0952717a4a00fb80ba1b63c11881f27cbf68b39095ca5b61b7f75855d77f805c48eab645c6cccea0c17f852129ee509a483c17263787e69956d4f79454393f47834ef73cb759313646eaa6a758e5268d5049680a1b5b3a9d91de8a28e20f9c2c6eb7da3f
  | 12 => 0x51970a18b3ba16a0fa140e23ee1d38bb1b947332daa1757cdabc5fe61935bc25ab44d1726613f6b598d4565be61e22568656737d810b34fc9cb0bc51db4fb2b3f361d34ba1563cffa429dfbd2dabf7e32219bcf357c641dfbad4ab53eb7fec3eeb06cc6ac407bfd271a5c630c538f5b1f81f369
  | 13 => 0x439a7e10d620651626fe7a3a1aa83d25fcfb7bcf6b1381059063b197a21b60cfc7b29b772ed3c2e59dc551a2184429a4af3e96a75a48d15f07833cbcc95f3f189785b223d36b245f23155ecd1b6b2f0111684221b56bc07025343e8c388a3e1421e57140b6f9e7ddf192ddc678205619eeaa5ab
  | 14 => 0x6cd1be057748e5d1d81558ccf1c4edb27beefcad56396abd02380a7b93789e15dca9601e2a5010bff9863fd7790ab99209d80da195eb0c18157681652cdb5145e5b67fe0599affbd76991b51174429b4eca8a5cd56351644ee0c0995530482e03c32da520da209d655bfea778cebdee76a41574
  | 15 => 0xcd66c9c7d84dcd791c13d51f09c2111d3d68ec9ad22d6c2cb38adcf041bf527b5c3c1749abbe24ae18aaa891028e0301a086ff2ad09bef80dbe8efaf720fe5e1d1f57f475b463f758325031b96d650f0793977bcd01df6820ab7a5c030affc370b368b0629e0332d1b264bcf2f499673819a70b
  | _ => 0

private def denseT0B18 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xe7320ddd8f217b6c942af6c913d49b0400b82f2b5c5e1ec61b18a755741beb7b1ce4d97f56e3306a7b5fcccabe6475543827c1e0635843b0986b8488f85b37e32daa906cf25a92f9a657857537f540f7e94ba9f5101908aa528af626e582e1b207e1b302ff54669b79443d18c7df155cb28aaac
  | 1 => 0x9be3d75432a4ed15d31d303b5f8297b6783aac3fa404edc7f033926ba00ef444e35561f28e60a2866bac00fb2f5da3a700ee6fb95f73b7d37ae5f34d24d4936361bf23dd28f62739653cd276a849b31e0434bcf40457c06b0b4903c55b2f304f7637ee0a654a71019034ccc3a402b6453cd4798
  | 2 => 0x128d0f875aafd31bf28411c718094746ddbb6d28a5c36858019138b3ab569a550aaf4af90edec5d6bffabaed4d247330b133717bea8ff80138e16bbab937a5cf52a1d2750275d8474c72128db516964fa68191526acb118817722e789178f60d2ec029008fb2d9a5e97661f1b4d68be58faa745
  | 3 => 0x3b0e31ec6006c5873b226251f9176bf3fdb8a0b08c868a3e11cd0be647e01fca92484f2cf50cfda96a262cac8c6b52d8725ec9dea57043460de6471bb0d999a7fc7b31188573b3251d79589d4b5f7ae5b59db98343e0ecdef20a56094a32d8245b110f2a82fec244930cb5b89a388179257e709
  | 4 => 0xcb3e5cc5a0b4c09ec3c780536a0031a7c38ef11be21c8417daca8c21459c52e38c73bbba362659350f4e711f5e02eaea164da84e712b9bced230d39c902fd64ff7cbcf28f50fd2a5150195f6db1fb84331b1a7708f797558323a91d002d3b86fab2361010c9ed68d4728e1f417f2394d6b21b9
  | 5 => 0xe023bb442b4af14e3436af9186ee875bf59d4df2c2f945666d2247888cf4d630bbbc79ef75111861cfbbb04e735914da253c9e531663ba49063f7805869e01cc982e218b3bb3becf65c2613acbb9b4cb2ac484f12f0641cd49d5d8fa223c7f2507016c449732ea724b2657824692b28c2d6fdc5
  | 6 => 0xff2bcf5eccd26d7d77effad09ba46f61af5f22c376365c8bc898df43f9ae0159b96a2cbed1cefa3246a5a6c1aeb36fbb4e877c269aa567b0550c7df77b67826689a50cc73997f2cab8d10a8d39954d8abf554cf77ce474893a5dc3a3dc3e1cc62e0c0f26f6dbfcb899a9f205dd25099ecde8d0c
  | 7 => 0x7a3d00de034d71a0d73bec914ea5ebba3c56b385e61e024a2272ac4ed85bcfac6e58131fa3f72583f66211bb311c1bf6e05e23601b04f4d68f2ed1a677a36c7ee742b2279e519b93edfe91e5287da69d6ab684844799f9d8e9dbd93312bfd5e43555852077972dbfeeaa4ec98ad3d005008cb46
  | 8 => 0xe8511054b515af6351ae443dc6c1cf10e85e70fc7e34d6d9b1a2fc23e85aaca591d424ab123ae6622c6393543e494d5a8c49b282e82d170e6b14c4b35e7e30cd0dd47b638ca3ee3a354aeb221734530d8d31c0d54d0fe65def1d8dc76fd0775e47f831db453e267aad35c7d1fac797c1f1e27cb
  | 9 => 0xc5858f303c3aa99c1cea78be7b7b759db20689e21c10aed27b5f0efc27aaeafeb19715d5546fc49cda578f5f643b0bb80e9a068d029afdb0ad70b1b688a629dd33a26d2163c38253902ad3ead27a0b75200b13d776ed26bb19eeb2339d5273f0c6be74661fa0f0bccb5190e9ac2ab9d51ffae9b
  | 10 => 0xe2195fa78155b7d6f71b127c0ca32fda3b5be2534981aa3ed762845ae7f6be38038fdb3e3c239f5c851b149f9700df3b9b9a677fde649e90c23105a140720a505b496b9b65dabafb8cf77e71148a2eda9a51a48f23bb324c67798e612b046e3187ab61eb9b17230a9a509a36d3107c48b9c1355
  | 11 => 0xd73d87d9ca10410241d7d270fe7457956fac04bb433860f8d43231d9a2104dc7b99f0cbfd2f349aa2a3ebb486bb9d7cfe92e1537408780f4740eba177a518f60b3aadda91e74b3ca7e7eb530eb0c6d7bfe7f05d8628b9622f9e3adc51a42e2d0187605d9a87f43de54db4303a38da6b09a481d0
  | 12 => 0x6728489a0a145df08e9f77fe08c3752569647997eccf4dd3fe86645e8af604b6b1dbf8f49d58da5ebc6dcfdbee3e1856d18a3fe8124a8501f42b3607a109e760e6e2c1a067d74952761ff1a08ba4dc2840083119a664cf2f99d0570d76747fdb4287eaf79471cfc73eacac48ecdd09f4eafdafa
  | 13 => 0x536c5b1824587e2e437e033419aac850784c11f40c072253276d31a9f7aa7526a00dc84990a94dafa2797cb4b2b9c485e29781b8c91efadf73e5c2a81ecae80eb8ebd5d1b8e29c110cd4043f54a89fb6fd707d335a1f63dc7ff50b3c6af795882eaa9c1ae4d0b39ceb8fba3f1791c53d14c085a
  | 14 => 0xde74c208437ead0aae1f69689492dc87843c8f03b5fa602480fe0b65a2581d8c48215e359f1445687d3940f107471fc847797f3bf52f96d1ac737119c9fce49b39e114c5369e1f6c434f2b5f0d7f9ad1b53c98305b42a3c2d9408ec423bb714d2550cf8af273009e5b89f7e4b40de38ea45cf4d
  | 15 => 0xc7a4ffa6b54f37e2d482b4e3a81f3d54016dd9d0bbff81bb5835fb05bcf8b28bd7823a27ad5f2fd346e138bbad69bdb3eb82e90950234628462a630508a80958673e5ec49f2ca1e80dd0befffc8c196c6fec77424e0f3b54dcb4151034b85469851da2b5a83675be464d53aeedfa9994a7aac1e
  | _ => 0

private def denseT0B19 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xd33fafbe8f689c69d362b535125be3a3bd1544d1db9d499044e5f557bd546a0b80ac6f12c0beb0ca2acd8cdc800b333d1a5336f15f6dd8f03839e5ceef206f22789be0cb19da74f663cf6e2ff3ca9b3fb334f90d9cf316f4d97a737dd7fe92b06d3783f24ea164b551b5008f20d5a215e7b3aa
  | 1 => 0xf54afb0b96d51ef446fd5d4568fa06f8d22d64206be79cb46c91027bef8b30e8330adf4ae84959d695c409acb7bff1692bfc2fda080daa2a2c203a3194aa5d23f137ab1735c176d00420ce76038bf60cfcd23b853938be7cfc32e1d3fc0d9e9a86d557761f7d5990776a41e95ca94bca687447f
  | 2 => 0xb8bd69a8f4df9f1441eb7c2888756936c269d8ebc17436c02d4774961541a1f22c583390d812880e040fc5002bee15bbeb4224d470c53513df49cafa32c95c5c83834bdce1f7e036bad4c3b6fc6b3a8eb254f7757822bd3a6d96add51339f8789f6f945f3c60abcc911e8724c65309f73b4ba1e
  | 3 => 0x40e1b3508f0e3142ae7931aee975a785071accf75578ed976462c70df9501020d4bcb418d9cb52ed5372d0721991b80d66be6e3e823f34a3da016f5b6ba129c58f01fa3a61977e0fc12717a7c70ee9d1a53866d37efd62a33b57426d4454a965e8f528768727e7ec325ae90598ffd0b49668c51
  | 4 => 0x7f1658e88bd34abb9a00248fd01151074f888905caf5f7ddd11c1c7ddc1172f6ba4d499493cd9ea8744057b704c006dd62f7af05851f7ca78f6bcf4d23714fc25e01914a88846d2bd98a67e52e0c0e7382e77d9369c82d3a9f68e7e540f46ae2ba22081124a358c8d40643e48eebf8f6e160586
  | 5 => 0x2b11051918b4b69a9b28d4710392590f1cd426af5caf466dabbc0efb41d8474f9c6e09db22a04e42792b15c7fecbfbd164ef89c1236472fded367da917dfe7cadad0e2f64c5f4eb7d0c9ff38bbb2649c6879f382507b3a72bed19ec0fa62b3c1d58a0d359b1578e2247c3a69e98b2fd295403f9
  | 6 => 0x69525de7891c3381d31883b19f132d0f1996c5bb9178d1d4623c3ba5cfc187429c839174e2d1f89593322e21e46d2d9fc5cb22f59c83688bd504f532c2567bdfbf0a43ee541138e1f19ec147a8ce6a3768cf32bc3d0754b6fbd495de2ca97301cc42615ea863ae1bc50800db7e0960f2e03be82
  | 7 => 0x3d7c0a21c50fd375fedc29a4b88e0e52a0f15a3d5cec590bdc95ae13e2fae2014b9e44c49e6eb8e590c8febfa353b018ae546801f1490a68ed687e8c43e26f2710adfb1ad91d06ae94e0e6d10d0a2f998061b38506757f990ef5a6b9280f437aed3fc509d46270702c14f91b546d7cb3f9534d
  | 8 => 0x670946dab258a2d03eddaafa56657fe92156fc7e7efac11e5855fecdced4a54f80fcf351e8dc976cd065a1e602c49b02382e51301269b82260120e09e4742e6b7f88006f8102048274c5506133e96fbe2b0d7154c4a27e5f9dc795276842f02fc44ccfbb2a9b86d59f77b3b174e931f2f74457a
  | 9 => 0xc6f09be62f4e2e614af4c1a7141e6aa92e8fa8e5cc7e51edb204456c52ac92d098bbe4ec2b8175bbf12150c11136fb5da38090f041000a311db25b6db45af713b1c2123ec18cebaf212bef490d1ae712edaa18222b5db683583442c911980fc3f123d9de09460c7284c5ec5def4d24ce1b89994
  | 10 => 0x69c38afd5318b9499047353d13ed27443f261b3d53c89ef4f1e78f04f7c25a9a900396d4d8f3785e63187eddea522cb693918b79a7c0924c6e894f24d72eb85d3427fc310d2d9f955d44292ec893ae46f01455ebb301df102ba6d6f25c531675c5ddb4ab0a7a579d72bbd4bc8dcda89132a83f4
  | 11 => 0x744822699ccc1978f44f9bf9339cec641c944e3aaadc2a3cf1118111740aaf6d5704934e4b3c6bb0d8b1e55d13a3b09f9e1bd64b44000d6776e50b81bf8ae118721330a2eff5ae2ac77e2c2b647b4574b34a169828a3a39e0d11fcc457223f4e43392a089f75b971c92a54d3ee847f2905b0cb9
  | 12 => 0xd5dc9959933c355bb70a1e46f752cb665c131bf772dbe39d208793e4762b45728cdf5ae64082a3d46e01ca461377b7023f508b6bbfb5391b464bc1d235e30a4b0470f58d0427e7888df31d2570b21f14c2c954c074fdf7e29d9dd41e07dc30345dc42c2bc5662f9f4eb4da963b481d2f254657e
  | 13 => 0x7d8358c30768d0b887fc0fbe7b4b01f4f3a9f68e43b3ad115fdff5fb8965ea4d3345b8fdf1bb41ff976125e1e03fd5625a458ba487ec8a49d19328ffe4544f503300fb037d1d62c0720e146ac747f5e151a23fb67914671848e9674849fd7635bbb3db7616b64403a1f81a9c4d9f4c54f4629c3
  | 14 => 0x5d7af22d8bfda78cce381fb6ebf2ae5f640044845155dd0eeb04db78b00a2d8b3957955f84656445dd2b5cb70aa551b2d9a80880f795edba994c48f53d9e9cc4361680e46343f1ba2d500caa8ef7fffe0b3c75ca64447c55cc1c0abd3bf74a9d09b2a15161ad3a0852631ce8f643781438ffea5
  | 15 => 0x5ab69835a788258b0b70b254cd74019bc23055988de08275312f670bc2ce3967b8f29122660aeb6522d49dd834673d47eab5f2921aa1665c940cb08b1668754b8c655ad6c6acb9f43b70a02237891383b2445835fd4ceee32a3336b17dd1f23d030910cf3cc4d23c81a57e48038ec09c6ecb98d
  | _ => 0

private def denseT0B20 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xf6a347e9c2bb5b96a262d1e2898cc3ef0ea00fb4d34d34635c061b895468df7629562be424f58ac8f0d4c9c6f2cf8fd8a80d9d4bc5a10d22ff44d090a60f20e0d8a1b776b6e819863a217eefe5a0f6cdfa858fe4b569304af06eb082b2b63c5d638a04397d264ee2d301b645d3ce1844878ba42
  | 1 => 0x3b0e6e28399bb40f56c8fd5c25600c4c37c1d2672d455d51e423a25b9a6531b59badc88e1352b84ac227f11fde1c6ccc3805780e85252a77513b851189e013e8a647780080be6b491e519f29eb27e426d0da603163a603f29d8a6fbe9e95b0e6b34388ad15bfee911db564d882c3dd200c2cec0
  | 2 => 0x7256feebd4a8c0c77139f783c615630055374e84c48ea0b63e53c4bf283902816368def86d2f17723c589b2b688095f96ce0b3dd05bd813f7c61462e76d2c0beb8e1fcc89365ccc1273cc6cd691fb7b9207a2c687bd81233d684b048c5aa299598c36e007b6da16f319fa180d47738c418b5a3c
  | 3 => 0x3b64705e0d52e3e63c8dfdf920e8208a0c7defc7aead771fb47c9bf2ab4e90cf0067eacac571938e3541a651f837c4885e8df1f02ae1eab707ac18fe96e8c93bc87a2f15e88dc3563956beacc4fd8371731992807d35e57e7f17c053e48d475efef415380d5fedaf6d63ddb461bcbad814d96e6
  | 4 => 0xd3fe16da9856063ad59b49a93ea38e1475b6e0ded193ec198e9054d009c2e8c6b8eb2ed58085f59c1f18931758302193331f5c4d3f7c29d08fa3e9e16f30495a39ad2161ad1d57b57795abd098d7b96bf04c338cbc0ae78c61f7394ef2eb1342e454817a366d510aee5a3769d40d233abff817c
  | 5 => 0xddaf965a3d02ab22af2dd922bb921ff714e4845c2b97b9c9c46044ae0ea4bfc6d78c13db5260825365317fba232933f5ecde5162379aa614dbf16640aac7816cf2f7ba9ca77353ff2319a08ad2524d70f33579a3311c767b01f6e4cfc3ae1381e446a12438c19912249661e6fdc36452ca497f4
  | 6 => 0xc8f3c7b4c28ae124e0e19f7f398c6aa808f5acffcb58223c62023f7aab091f26e19e90f823e85cd1c6f0be2b0ffd2f26fdef6c3725113ced97e5f0e6fb850ffce10919578701e15141ffb32c54f58da8ad0dbf047ab99c48eaa3528e2620bd41a3a2c4ea6989d961ad6f0773c849302714caa79
  | 7 => 0xe1f5522fa3e8677160f6d2c010d940d5ce4e7a99421173f11250b6dd0afd962e7ea310e39474b8ebb41fb473af1ef4e073b737c32d3a3e98e7818f22d4c31d51dff38058f3ee283a1c8d72fc3e40e1001985700d813f800eb969bb8902b74f1b1d1bd48f991d702c68f9a2bb07cd137f8ad7b7b
  | 8 => 0xe1bea26a6c4b3f6b56f89f0e0578f7640cd4cc85f5ee90b4eafbc9337d0cea581c186105a3745b8746d8369aa54480e9df2e2789fa04f8db828af68088834273dd182328bea5fe9a9c70e241447341ae05970e49a9815f871515b2169b1777ed6745d13de5eedfc6f1e87ba61c09462655a9266
  | 9 => 0x334dd2f632530d3ea939c9c617c74158509741e81f505c74818ec405073ba68ac589261bcabeef7f496249ac820533d932c5119d5002b41ce8905566a606078ec11f772ded9bc58b942f902750113ea6664cffce53df4ad501848d7e05435dcc75364cd5df266e6a8531f4babedc672c4e6bedf
  | 10 => 0xfb2c333edd9a2f76cee04b4f8c1c8cba8626f03a41dbe0d7a4098a9f768045112212eb802cb8baea53a231fa9e00426b7cdfebc72e5427ed539bcca2f7c457e4207ca80c7849ffec9af0c83d9ace77f151697d6b973b4364b1619b0709e521611067a6005c065aa7b8186f915e1750c1f164115
  | 11 => 0x94cf58f237903087a1a35021172319f2e0007f0bb9d89d370ba71705722bdddd0c51d3cb397e6296d3377cdba18d4ce591b6add85586f95651275f8990aa7628697de4445ad469227647efff65dd621170508200316251c392d145d40a74a402ea15f3ec6e3b12366980466311fa90de905b414
  | 12 => 0x5ebe77b4f5f3c6b423b48464ee8b378e805e2b786aedbd5bfd266463e5b253170133868aebc164ab769c06ae40d39eafd8074b23077c6a0f37cd4f2b30796162c8b28be84625c880fd2a1a1d854c1ada4539b7a28a0675c8b1844168c9ac2e03c0ebe89cedcdfe7527f59b9700ba2e0861b2b4f
  | 13 => 0xc3772c8f81892b9e11d157465baa56e854df7f097c388e868b57503f05c5bf6d0a803409f2a6bf160e172ebaf4f9c6bd869391d3aab4481587430211d225bb2e9090714086f8cac20c678f66a89ff3e1dabb9a5ebae0969106cef9669d80af87ea4003c4c9200fb0fb02607c371eb552b6f2257
  | 14 => 0xe444793e93b8ab4129debb35a96db71c0b910524c379fe3f6e21212076967bc65f48700b8d8995bf0c7ef8958b3d325fcde93a1672662ca76f71f48d04e6baf9063b63589ba1827e65947a9f3ad061160020a2974ba825aa203f7c8d3cb6a20ba07d1c6844f16c45b3ae50aeba5a15635601af6
  | 15 => 0xcc88f7546f685520c81c5da63bff57beb0a52b342fda9454795d8e34986c386d6b65d352da1954e2cc24d63a40ec80227738eee4b629a1b82b4addaf2047d25e5aa0ec45b7f14b24d3543393fa0fd1e927913a8063660402092a28f03b3757cc5d25297ed07999de6e792fd8d3f94e55cd7952a
  | _ => 0

private def denseT0B21 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb788f0475b0f944e5ad00d9c1dd1e8d1abf4f0af1afd27557480988288653b9d90b045fbf791deed1c02df3052ecaac6ddb530d6848af744708cd9a01db51b6d645bda3fb1d3d70a584f86782fc48f99a38ca6f69fe580bd6282f6a4a98560a4f7ac0aa880f08ce2c41ec3580371b24ad61aa49
  | 1 => 0x5b41d8d8dd14d6c1ee3b0ee355d967851e9047961f5b2d9da24d790fccc3d5ee3c9fc81c459e48faa25ab5fda17d06003f91385a32ab02b75f7a97f29f91997e870186d1d9adc94a9171d4959801cf7f3a018ee285556676af0260666158477544602248c9d6a9490293f2525e65d624cb6407c
  | 2 => 0xaa22f177c4dc033f3d2e34abcf5783dff256a82b11ffd000dd88de17f07d97e46347c21278b0f63626252db5acc9349aa1f94c0d69681e937bc6148ea5660dadc6b056863cc3c19af697524e172358f0c4122a005b3d397a421119a2c59e5f42447243af32feb4970745dd1b5ccdfb6007e8e9f
  | 3 => 0x4429cf6a4154ef3bc00943b7c33f5b997a03a75d998de08a6b6a331a37154cebb97edf9e0284c9ed61bd2d8e6a8ae89119cb2cc66a4a7bab0298771ec4b1bf9aec18d10983e84596796ccac3c7d3ede99ec9b4115c84cfe46c0351dcb683374dddbace093780d9029f3d8ffe8204d6d869ca9ea
  | 4 => 0x80cde415c3015c3a05022ee3c6083f404be18990a45d39c142f6d8e983c66442be39906a0f53b0e2da02f3dca4f8b84339801de174a906d3c34b312f67445c22dceff2ae6d2b043fb6d384f70d1baa951c193ed202a50267c3f14f2f2055b7c9914d48d4d1b968a1489e9735584d846df347258
  | 5 => 0x2633c59862df326405b91472756f4e069c26e911b925ea05e03944cc7b41574205d435841b97b1bc827fef218600a9283a271c87e036bdf828cdd24bd5f3392b2fb3296250c0dd6e09ab4a909136127e77bd0ee2f8080551da80502882a1ae6fb2aff3c82a743e56d4043cf8c5ff33eeccfdb59
  | 6 => 0x7b1b7da4f4d37afb985d2692d19efef868e08078a8cc2a385076d6ff282d877422be477a0c72954ac92400fa37d35765fb95e4e3480203f77e1176aaa5b564463660156a577a950bc1ec00320ed61e52ce4838b7b82e813be24c0cc8b448abb93004c2347936d9a1bf876076a6d9570a1944117
  | 7 => 0x767cd05df2ff1aa49797d5d5cffbf98f9acbe95ad94e128f1e8c4a9527a953895a2a93e07018049e229b13b0a8ed8f4a95e39e5ee9a4f4189edf17e7ccfca438d0768bfe0dde72b66ac3d95e1135df634873dd22f793dee6456cedf93e58c0f7764632de1db44299e491d472df0b6e4ef7cbd68
  | 8 => 0xe4183111e6c98312ff8f74c45c50fe5d53d542f706e861a26058fbf3a49fdace07f5fb8e9db290b8fd2eac6dc4a70db85cd9c137a86d18ce8b4fd541340a462f4dcfd4c6ba6a8c3a7edc7240aba2883bbe4a446e3581767afd3456449dc4da817ffe895210943f9c68269864f21deed2c978105
  | 9 => 0xc43f6529e379f22f2235be277cc406349717f6068ffd34034d9d708e3aca8afb47bb810977cd24c036b5b426817602e415741f6cdfc2d8ebbdec47f8ba93e13e5e0a7c2791016b0dbcbdd9038d45bcbbf4c1c9f6dac71baaa158fa72a509a55422ce80560698abc9791ab74cf06ca62df255ef2
  | 10 => 0x96b102ce8cb44433ffff169f813bf5b19aed66f96da10a21cd1f83a2dc05e1eaa4b37287493a5d6feff0c7d057645ad70a13ac7e44b9dd0b29ffb0eb59b2a4e8ee0004b882ec6b26c69116892280af057244598c83a02180495bb87689d750316d2fdc5c857f89667e5924e9ed2b9d1ed584f2f
  | 11 => 0x7a3a18c3ff835c5f7b77d1a492480e671000ba280ea6d0772081770ebdc63bc041cd8ef22b17166e93f92c083e2dca7ce74e0ab15075e1188a9af113fdcb223064c94555f389687dfcf03b49456c5727e1a16ac4d0d1ae61791d494f21f2d17197f4399d324736020cdffdd41a44a5cd518223d
  | 12 => 0xa4f878ef1ead878dc88dba3c037edb70a39d261b3b467091c25ce4afd67ab454bb09dc81a34b736c6991a419ae85dd349adb6800709959c1d6de0643bb02ab383da227912ce00cdf1d9a404ce01fc5fc64e6b95d71264af967902c04bf0f862613d0d6c230ec536a407ee18929b379629ab3f20
  | 13 => 0xcaee04ae6f8985e2e54ccdb3416b6648af1d91fd4f6eb8baaa52ced00cbc3c88855640fe27d73b1cdecf4fb67336ec7e7c41616cfeba49279ee9b9c34154357da3cc5e07e9c0e60d88fb2ed2120fd2c751f05a14c71e9a61e4c6b3152effe98b516a3406a8d2681f136140261710946bef70ba2
  | 14 => 0x20b4cead372b383db7761d27e00e67e9d8ff1ef5f08015893021d874ea051d66468707be5704b003e8c9062ae4e7954931d6c2307c8803de724205f44b2f4bbe63f1e5020e80d86c2a8a4b85b8496ac06ef904995ce6b0ad992a8b14b292e8d6db4c9eaf20b1f92d0c79b2a83e9b4d624051c69
  | 15 => 0xaf5d0ac30abc3804bd58f74c3b9c4aa4dabfd3bf9498d25f8e17ee03bc567ba51eab92c2f11e6e1e43f28d4a4cd6f390720e75f7f7d81e09bdc7b79d7e0839a87738798d555448d25bc14c68a1b670ac7a8aa07c30924c9965c1488fd8953dd1fc77892c8f8dfd345b6c11b62699564982146f
  | _ => 0

private def denseT0B22 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xd174bc4c797f558fe82b693abf3151ecb5194758caae892741326e1ef5ae2f5e3ebcf873f4d2768d3d8ec628e4cedd9242c85419ad8557ac0555d6876a0db8c5dfc1d9be20b979b9507108ef972d3e11c6a3f1c7417598300314e0fe27c08155ecfa8d667d7da9ab8a1d6383bf7ad8ac5a6b097
  | 1 => 0x450e775f3e5e0dc170dff985174c566fd94b6b91efbf3b023dd6f510b952f9626ba4bed0a624f9eb115e883e432b7e50d12ca61103bb6f5c49f0581440772e16ac01f9003ec109a1aea51d012e2db0ffd6d93f6e5afcf732bdf8e7638cb29a1e139d8f0f10284f116a56431ccc0a1e0a0200a07
  | 2 => 0x39054f3628f182e3874acde7f52dc7406128c37ca0a36a317a852d296ac46e8a1350eb11aa70dc54e13d3daefdc17ef94dc1d84d8210b6858c592e6351a6a66e626e18e7cc5f37855f7ecc9bef332458ba9535329c1d3161a5dbd32c58a15adbfa7526101a4574cfc972f8458c14f5b103639d4
  | 3 => 0x74c8b390bcca5b2ee99d96c845e75b4baa812fe6699d9f0edf745fab33e524d87ddf4159991fdc5937d6c3735ab668274bd206eaf8ddb34cdcd83a76cf5a08740b5561b2cc9db7e6eba5d8abe8803eacf35e0bde892f7c1bd89ba4bd68df5e4d5065d64d675da2edc201db5c79d85de302b82bc
  | 4 => 0xb4399f3380c559b456aff672baa3b44ce7bcc23ee5bdc3b60ee22e5483e7bec468a2d23f55deb122e54762d5448e3ddef44805de5389e3caf62517548881ca8b04eaa11e827513e6f9883ec39d0fa2701d400a648c177bfa2bec08c32ecaf9791a89d42b98bafaa07f0168b213d925591606949
  | 5 => 0x90a1449f1376dd6b08f98b345be21de5c781062041cdde251c0cd29333aed56f178bab924f884d464ae38aee0d18bef965cadfa513eea9dc523bdaa3015402f5756c4e3a10728d25776894eb7ec6948710aaef08cc2071f55885d7794aef97869cb1feccb0ea9a0030e3cc020bfb57f6e993967
  | 6 => 0xb0b4a9df480fb500848de3325a9983d637e7f1199d15839f08e72b1abae1d43cea485a5368373e0fbba16814bd33731f1687af9bdac0b1338a57bd465705e1c288c50a50402943a28f025092d4829115236129018d035c86b5051f03214ea42bfd1b56d771a0d118114fd739bb1a2023516f182
  | 7 => 0x895b340e05cef24a2f788811431a27c3d34cced84ffb77f652a9f8285f7fdabfbdb9aa8ae73b215048f3372f25b013b09be44a6b64493ce7af5350f99ae85cc053ac0682c25fb91b65acaf26d338572cdefdf989a15ca7b3d71528e8f65f2c1f49c4d636552a70e2680071bc625519ec35ec37d
  | 8 => 0x1bad8d78732102b6faf051cb6f4fc6f6d81b8eeb0604a707a645374cb6b1bcb62f69185e85d01893d7a2cce013d6cb3a8fb3d7f415efd0b01482efb2cfd70dd19bd986eb8267268b89105cd42079d1cbc209567316a26c1087c5a058d71c566ae442b2ebb27bb06a85e6cf63cd1b4f8b103faf6
  | 9 => 0x3ed8263d66bf4115eb36176ac54fabb15d5607575673fe13e924e3ddff9f637dae09ce6c2eafebed90ed0c393c388111354a39aec4c1ca6d8a4d31c7c49aeae5e222b6a7a3c37ff733e222f3c7fe88f68de8c61984bf1cbb222a58373185a1fdd884d148be7761801ea72629594664d716d1907
  | 10 => 0x797ebaabc72dfd07ea5101d36043122e3960eeecfc036a86c9a13b2686dd0ed3981f470b201d368b0375d98047efdb2a8847474e16a24c195d6e2910bd3a9460623ca87262a3966f248f8490b24f3f748425fcaea60dafa6495da410605aa8ee7d1020a5f2e0f639720c9f163f33ecc69a02f77
  | 11 => 0xb990b6955af816d635adefba8de3c473ceef759a69d6abeadd4cc8e2ac9d2b60ee0ba0a74a00f873aa524db9bc0a6f303a82479b2881725363ade980f49beec62243e415ce3118a79df43d04835cdfcc7cac067e5d076c70fa573f1ead086160938b9f57d29f80e6cd2112fab4be24fd62328d1
  | 12 => 0xec36092701ac5d3b95844bf75ca7710ef2079422c2c6cad8a0ac777ecec2e9586000f4ad4920b191ca1dc75713e49fc0f890266ca0e189ff578ab6d8869774900d7abdd23e3893d4b80160710eaa3151015cf296ce4134ce043708632f23c866ed7cf9192a06182dfbf034f31a7138d23679f28
  | 13 => 0x10e1c0a119411bd74da570b07998c8b0a1637db17724cf5be08cce44f6bc5489174b885e9450508c5b2bb09493431ae73084e287d66ad62fecce7d879403107efd04f62ba98f3ec50a0eea790d53a0d0fafe4e7a741ed0a2dd237153f7ef2e05ffdc3bee8a4f467bc2e78e2751ce55518b4adce
  | 14 => 0x6db1a79717c2b88facaafcbe36b76e91a238f8049327f97ffa2880e34115d1eacf179391c8ae9ae63e8aed402203a364add49197aedbf907a770bf72c65c0fde36a41f7313e35fdf6849e2a7ee8331ed4ee5a5accd3cedc16ce65ac1be92b4d218bf176338ae5e6f317d3a091f2854d9e87dc03
  | 15 => 0x43c5a2288dfbac4d064dae597af1ba16a207a6d9378c67fcd66c615e336217210352af0a4bf1cc7809dc9c81ac9a6525161af8446c9cd2d51e28be0aa3e169935893250c6adbaf80a51d41785e39e68b094afb4b733c918e516a7f99b2a464581db809c45f769ecf3d732a3d652ae652c91c072
  | _ => 0

private def denseT0B23 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x9035f7b009a27fe58bd389eb5862930964224db5f587925fa59e60e4212edf77fd719b4dacb223c9162ecf40c4cc4c2622e8f633102f419af71d609b588efdf5b10cb3a15120398f7ea8402c34a54d25f7df996b6741ff7dabbd4227886392d8952203f31687bc03591dedb2de72d679ece54cc
  | 1 => 0x9e9bd3a50e5636ad16dc2b9c4aa32f498e72c0950701073b95bc74864e1cb527699e7f5a9abef2c76be706173102f78a240246390b5d7f64d8f175551faa4e5425122d1fc049de6ab3367372260225adb7fe342349707603c647cc666a2129b23564342ef87879bffac25875be0d6d33116ec53
  | 2 => 0x5583a1d1e2d3f6a17c304de44b0df006a6e017ec15f1d54d6ac94fc14ae0a756e46c1418047a0e1d0f082f6b2f4f3853ec88864a10149a298a357dd5184e98a7dad9bfcee4381808f0f643a06c404ee78e1d31834ff0954d0f36699c1c4af53361e3b8e6efece0070505806dd41b56e748ff8e
  | 3 => 0xe083ada9a997e023e34f17b24e00055f23bec45a3fd329acd10e0659a89148e66ae2a5b0096155057ef3a3664ba3acb9673e35a1bb408fb7f7196390de6ab15c120021e037b70bd670f6bd1bbf5b17211df46b7baa60448f4203852b5fa9ff512f962ec31e3a0b0e1db6e75eece152b85da3a14
  | 4 => 0xbbc1f6e9ac94b136d7108dfbd09e16d9ae3bb347037ec07da4844dd1fd60b816f9845c87ecba8efe80f3496538e250db19ae4fec82997cf90127ff808e571d25398eab12cdb96f849d5adf5acf94b8729542f5527cf8074c2ae7858b42496cb03f5fe116be4ea9e5ed36aefe04bb5f06c9a4711
  | 5 => 0x24e6951d9f5d3b7d1c0d3f8788943bf430f962c476e4d926545cdefe074ee8a2519b5f54c94ffe67b7e21284b012cafa8b51ae2b0a3dafbe6771afbc7921ed5914ea2107600faa66ad35801500f17bff023d1d84f07af81f57d5acb0c1e1f29d88bcc0e8cb4394bb18a8d0de5b7e8af70358035
  | 6 => 0xaaf5e09191e2c3dc9f0ed49bd091823cb35fbacab05286f22b01cd70a37c6785936dfdd245a71df295d05ee21089284d3a481cc41a8cf93deddcf52bbfc9c147c5f859ac5a66b6b2f3c260e63b7ff73f7bf7658badb8071faf52ae89b13cf0c07489ca530547be96f0479c27fdaafcbeb66020
  | 7 => 0x8c0d3168d30f39baea9189411bc3cba53358a78e53a4fd865c21a187a368924fdc002df3251a137ab81cd907cbb317c566371ba9c33d6b5ca469d11b31fe9d3e90ec6769500e46d6946cd3acfa6a12b8d6e92cd68b5133f6545668f07e1126f2896ca384048c356696c0a667d559853cbb41e8
  | 8 => 0xe3da74a8ca20fbeda5fafccac84332d718ca066b557bf04286c5dc9a3355685f0d817a3491d8b38594700fcd022c5774cdd2632ebc355f21c1c716ab82b59868583bcb4e023129545f7272379b7c3694a76eee0fba99a74caa8d0ef649e0224ba788b0aa0bf666f9a768b1e60070b3a7a2eaa23
  | 9 => 0x31fb40a1c4f816350b9fdd32f3b900382c3d6712b35f676c65d543135e94977185392600cc6ad3c2b66ac2823791f1639de2113bfa49820b220ec7c81c6da652c5e7411672140315bca8fa7d6ccaf7dc0e4b091bdf8fa4b4d9bd546425bd550f19003787048e299f6d12fbdfcd367930f4514b4
  | 10 => 0x2e5029de00868a6d37962045c59e294ade265a9db38903ed5a8e6dc059ba6d22d1560848231387044b14262e54029a75f41081aa662122d01376eed112790661dfe82ce045948812cbc165cdfdc8318cdeb8729d5ba5f379ab8516a65b751dec5e350ec0d2aa77545ea59177d16c5a337b3046
  | 11 => 0x2f95c71bfae511461a7c2ec8c1422687149880bdf14d4abbf2e0a987a8190cd34b6c8199f20a754cc5651c33a941c4b6d5874d31144921549c20f5d9b2ad5f04aa1fb6580f137b33d3ad9fcdc4a63a3cff67e182d17c3c5c5815d9d10c497632988bd967f5443943644bf557c89a7d88871f028
  | 12 => 0xc75176356a3f0c9396735d494bd9aa80673fa7e8f8ea52693cb1b345c45e674d933d92e8794470fab0cf7890a1106a3a79554fb6d6cf4cab21b798f888217a923373aebcfe6b0bc2061e32a7b6c9684b1120a571826c04bd1ff3d21501c3a2a96fba0728957aae9e040682c8363081e8914b1f9
  | 13 => 0x7b6248eb965090b95ef8dd3106d473da174aca67da2f9245c8b48fb97c0d2f191b4b54e25d6c0e106b8dc457df82c6ff68103147a3d20ad17dc44462142d2a42a9264e84a28877038505bd88ebd9e61bdab4b896f04ba31c379fc595a8f47fc427fcb803880873cde730ce2631ce27ae39c5676
  | 14 => 0x6990d33e0535fe74dc8ab2a1c6dc2c50b08e0646a16ed3332160804fcb0ecb26fb0edbec49af64543dbb0ad9e79155a709adb653ac99e0e8fb475e5b5fb77c41d73bcac47845ff6eb1419226a2248cfba59b4413130d4dcd825e609e14fb88cc2ed9645861a4ca5795136a69821f3d089ce02a
  | 15 => 0x47f80d86360bb54ed090f6da43a04e2ddaaabd388b8f25afcc9f27bd3e77a1c8f610612986b6f646808ef21711d36c689c266b1bf97abe41ec2052d1b94288faf4f011c34efe2bf7004a9c653d186a3f00f0cb5ca9af571903e204d30e6b75d35e0857d2a4097a835e095ef21494cce19dc6dfb
  | _ => 0

private def denseT0B24 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x23d7bb77749a9eaa9539d2193a0c68e4358443ab95605133ff26a1a101aff5a808a2641f32a76e9fc675bf9d83fa5d8d9499e49067d97aa09a7e975ba2f17b7ebd25c6123d520c8c76033fb4941e4fb5a0b9890c29deefa62abbf3a026a6446e11f0559bc4e85e3edc79684a573eebf46534b98
  | 1 => 0xa54b21b36ad5d251b04af7e56df2a25c5f34dadf4cecd6a2fc74a7225f0e21ca11674d15862f5428330950171910bf1b476b22e0f62bb90c66ddaaeb25da348a1ed83837dc88b6291abba4d52f958f0330cf4480d5365f6f009ed9aa08fb0cc416e8dbf63d91d750cc26ca66c575afb0ba634f4
  | 2 => 0xd7974ea21320ca64bb5bd90285f4486ed767533bf6def2b5e3a22ceb3383d62ae7a45a7f296f93ded2fd4fe26cabe4e1344313aaa3744441e9d0b5cef264a6ce20c4545dc325efbcadeec5d3f790b7191ca786e6faba842700eb51f140ed281d84ee34bbac84c5618ca899626c91e1a35b85425
  | 3 => 0x1fe09df34a096746de23fe3fa59ccc78ee6107b8946af6afa5db46ad17b136ba39f793637b688fff88d1994aa20cfe27b39cb1c827a332d1cd257a55e132a361c351cbb9d59fba9794fd035ccd733015d4fb0535559aad830c2b8e7718f1c364eea170945a6fc052a01c17c6dd3e1c13129090d
  | 4 => 0x4f02a52a4cfa86ca9845a8d0729dcd51d4c742fb045ac455017b273d58172d80ef48c8711ee6037f5c257e3bf220a5b7b7777457bced3e7517794be9c6b63d51f347ded7110a4512064ab5bab8b12af9b075ea6f7de07726d7be4a8dc7e0610f4c99e48245b8d83bfd1117273966ca25636f307
  | 5 => 0x55e5cfbd348b72e3dd59b6e1cecda23f7bb1092e7bbacd17341f2531bb103598a0c3f3cbfc3542658f0bfc0f33e2d01e802490d2a16013c197ad353fc4db071388e42c8f0a8e8f58a5a340cd630f9c12febdf5e460a3dad58bc3db81580414073ee97f64ff8da099d73a53467e6b29ff690ea3c
  | 6 => 0xcf7341b547c9a2ac0e451580ee2c47f19f9af451a1fe848665963254813edba3ff5bbc385081d2002690286acfd7f305f204dbdf36f1a0b844be916733c1ef05f5692426f0414e3d920cddeedf34a8147606a8c940b0807bcd495a639db68e2429c4a1e1851bc2aed274a2c7b89243ae1bd7b3a
  | 7 => 0x5a2b565f61e1ae2a5de210760b80b06b1c64fba57f6bf13b3e77a1637d679363ec74582da35a815d7575e9a2f9feaf7a1bd3be7f4c2abf28243e2aa5d87a8f9ca729e1a6a174588c889ecc047e50304838ff759ae09d61de5a8386a8daa090d73ffcf615f928a83f1573518d5bcf3ffaf09d242
  | 8 => 0x1bcdcfdbae812c3b4d48d17380ad7264c30018ea0539d15f98bddf3903d29e25f23e9e11b1d34624547c693e432013e07eea361976739bb4a14247457819f9762c247c82a2ece043401d06055eb3a6e8a1731ca5200636ce6f000ed8108d2eb29dfd00418a0666497a919fccea5c9dede476cbd
  | 9 => 0x78852de94402b8a83848102df37dbfed07c5227dde389b0bb259787d472c30dcfc17747301c564d2fa7033e9f5dbddc2f77bf6647ef0cd45c7b2f48ac4f875689b7b71c14e5086f2e6ba5d60faa824b7cfcdf65743433b8d3fafd8299bc43efd5dc28b15c622aa9c73d1ea431b862aa1d0c47c7
  | 10 => 0xa7fa045bbc4302ccb02a048c06474c75c18222fa72c4feba0ef294f68a4f7c2b1eb86dc41d6b349e783bf4c9db15ffb06ec9fe766c9499c0aec6720a01daaf5baa67b69d4fc149c077723366f138dbefc73eb09d494c52114a9c379af1bbb9bd27a0e76292bf09573f85f32244a8dc14dfd87a3
  | 11 => 0x4c6e8822c9e32341d99885c3475406d1fa691daa9ded19dd525d2dd4114fc920d35f88d1bc00df9f9bbbb4c7d41750a5a4ad56f3a259c98acca796dcb79cbe0846a8366e0faa15e4d10e446baa4a7ea9fb93e927f807eacd42706a7767eb45c716f43544dc53b5a7fd6f563c0b8d02bdbf399ea
  | 12 => 0xf8c121316a87798460dd7978094893701538019132c725366f107ab5d9bf75dde1a5bfd3dc15be973e8698601bd999ee5aa0ad361fa90d24b5ef1cd2bb4da3c3db6ddbd1bc3721dfc673b746255b44b9c9279b486a78b5adfaa7306d5c1aa870895ae6ef61f47f7a82e9ef39938828f81cf8f92
  | 13 => 0x26018f4713928efda0d9515f3feebc88794c434bb36c40cefa843651626227aaf84fe7d570e3feae774b480fe66240ad622eb182944966f74eebd6e2a2b193efb0011acba0a3e772794412b8c3732d8b108ad86714d2b9114ebea87229c0e2437b3faa033c0c640f08b76af48714dc011335ddf
  | 14 => 0x98c08a0e09d6551d6d3540663803ffb00adf9ae59f01bf3ff3124474e0b0f6155e3574027cdd938c870f04629bafc8a641c5d3bd19300cd1df0522315c01d3f89a4494bb5f743edc3df3cad42d0334f20fce6dc34c531834f3352ab48a8f7ab9dbdf40846ebf57365ca11e8eda4c450abebbcdf
  | 15 => 0x9178b7051c9d3c58cd7907830c585d26ce263bfa23f752ea3f1a7766b78a0af7f7ce4b4bad4d1130e825a7ddc4ddb0143d6063057f362dddd9f782c710a0a8723b3fe55623df464a883af9606f4f0d4a81de168e337d5a567a8ea6dd37c70d02c0cc92f85f3f92b22065e986491dc998263a190
  | _ => 0

private def denseT0B25 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x333ea9b40b79a5c7f81d8aa8cd8ca82bf18e393a2d1ab16c4283b0bfa4d81ad4a0b02599573c566932e3a58251656a0eb54bf2702dda46532833be38d412c88c1555e329132cd62ff96a3cb6446c134b7bdd05e98bf735b5a53f4b67d311bc177bc6eb15c9d1164469d747782e4ad2e627c3a2c
  | 1 => 0xd4ba7359cf3c279ce58f4f3386f41f9d2a4fb6232fab4206f6b0a5f7bf285ed2211067b00c8ef91cd9c923fbea5faa56e6822d42b3833ab1870e6bb555706e6e2dfe89463451065029c18a7857d7f2545b584d09cec9fb066c6833c49e5deb0339ec3ef16701b049402ed3594f73cd8c83b118a
  | 2 => 0x57de6d8f5aab6aaed439dd6861c0cf177ab22a9ede03cbdb43ad601c86eb4db7c00a4948acfd27abff023b299a99ccee4b7d8e191289a55bd0b0febc9f9c26b6d5277d14e51b6015bf5055093a2200a3625f2eae227692f4327e254fc09e0f470041b548efc1c3f464943bd6c503b47a43ffa35
  | 3 => 0xd29dade4db267bb21964ce775a46bcd228532e77aaea1e6820348d0995876d88812ef5e6ed95cdc46480537b1bbb3125597287813d645454713177630eddd967378f28b2dd2c0a26f9cc0dd15a5352822a5b89882d27ec397884d24412b03ba67038c71f7e58329f238f02d755b7186109c8da
  | 4 => 0x22eefd839c4e78e6d6713ab19cdfaa8b72e39af8c4a7f7d1c9fb60e324b69afe5cd72b60adf0e2e746dc75aada3b3873d44454b1644ec6c20a39bde4720e76790cc65abf941654b7e4c957bdc3e799d8416d9188fcd44360b44a960169dacb503281bf9d8296a5203ded39bc44577c95a3cca22
  | 5 => 0xa0b134db4a21b389d79b903e3b519a34fb17057acf9c5eb92f061f65eda90383b33adfbbd78cdb69608f46a3db6fce259d0f69442e008c5c21559e752dd4c25a44cf0ff8492b48983e3d732a8645cad3e06da98ccc72f7ae9ac46ed7166198a261d925105bbec62147a4b3c0f0fddf61552dbda
  | 6 => 0x262b9d123ac3a1b00062cb83f7afe6ba425a5dac2ccda8d72fb2bca352cea13a686b57b6b023aab50adfdaeea010acbd76300855abc7d0bbb9495845d75ef9febb87705430a0d599837839c25e320c0bf8e75534de0f86a8999d8c65ce772d31276838532f2d400bd422b6bdd5d8946e4d1c500
  | 7 => 0x7db232e05fc24c6535e733a96e363c8aa5fe1a2aa50f09d1f9f3a768a8be5e8655b48d4ee1cb40d7337c11217c9e7eaf0a3cb6fef731c831c0a2dc275cf01025da04a2525117f16ca86c2b57376722d937bf5823da986d9b4f9a42fc81f9c15dfd2a7e20013474ad28aa80dd4ff2b365a4ee1d4
  | 8 => 0xf5e9ca92ad37ae2bbaf944fc2f4bc9d7e2de9c91318caf2ed34d6ff960bacbae5933838b65f673d3518246ddcbdc4c19a9f0bc8d75e749b22bcd1632b88c26cca45377d2288d92b6809892a1fd843e87c169f78ef790dd9f67c0f096947337ef4752937d10c838e8d24468ad293066908267e9f
  | 9 => 0x6479c43fe6211cb6e7910e28d724240791f23f45e626e61a7eebc1f433d2f39d7d976b4cd2d2bf890e6606b0deeae36ed60f628d2a7dc08191bf209b2863b7bcd12e93975aefeacbe3120cc1e21e8273f2fcf04e35c4cf89ce5c3c107ceedaf158e5963c6fbe1c38dacbf50a3820b7774f1930d
  | 10 => 0x22c03df843e7d6059404ee57b7b938ab76d658ef191533847460f65759a46147c1a73a3b7472d9b65bc02bb3ab8ff7e10bafe25b08fad75108b3613a2c2e9a7f9f57edc42cf141b2d5f910813daf08990fc3113d1c33ff06b26ac850d449daed610e893a8cfecbbc3a4817c91eaf114426e70b1
  | 11 => 0x433e6dd7821284f9e7c41ef96928772748abe66a7c3fa91235c933b59680a12f827d8f9251f63127083ff05cd7150f3e1f45f195b5ca1bfb61e7ed66518a1a8edec7d63f14c72724c6b375036ab91554a0da3ab0629e71005b7b8154610c3cd8ea0827be2a827c78a2623d2f21a86e40ae77d7e
  | 12 => 0x49d1e022eb0a8d6d273ae86af4cc7bd0f858122baed0303be8c61c7be28b1f51aed5e8c1b45edb638f9c5fef5ca274923703520d3792ef0f9fc631a9bf716f8998bc922dd2e78edd0ef389866ebb9e0d208bafd6b2e6f8f8a68d0c2ee09d6a6868e1568c6fe7d54fd762f794bef8c2c7dd683d7
  | 13 => 0x6dc4803c2eeb9c15bbb159bf698ced20133f35c6602767d0778b4f9b3e2c90a2d385175ff506f9f0736a6f94645f5a1cd7cb8e3c84fe1716ba30a408ab8abb7e26a422cdaae9f23ebc9aefc61f209271df68314f2c3dec8e02ad19d23671e4074764fd9522c2ea690ab0cf83ec41a580272c478
  | 14 => 0xeaaa0cd19bcbf772b7886d3bb93ab5fcbe823e29e8bc8ece8800bd3eec1d3d25688973158dadbc7e7ffa1e2565f51c1f9e468d90826b67bd89e919c93035302e38e8fbbda4736a8f7a320a82cd01559da16e61ec0d8168a6939e68db19c21186e2b3006f7af08c2c8e762a93d6d6cf8bec56338
  | 15 => 0x8638641383c2ccd4b9221964b90f6838554cbbb7e7901bc43cfc7cc2e5bceb2231ea630c7ebcb5270a4e04c52ee7f23a405f13c6a742bae79b45ba55481ebf7f5360008e3b1d7968b25a8d57bff21e2164f5801714f42f8014a774b1214aea6e238e95b27a66aa21dfc7322a13dfc070f922df7
  | _ => 0

private def denseT0B26 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xa85d1dcbd5387a2b0795bb040c5e79c025cf1b1f7385ef343776bc5d3dad07674f50e1b18369a873d781dd6e6715a83812981d0b8829aa4cb461bc9c51e55c6995827593a12eb38c3e765bf748dfccc07356f367bbc674aed64db5828edcc011cdd44fcae72c81ed5c22f7b855bce9e349b49ae
  | 1 => 0x324ff7806ed1e2472386424c00cf7bc313be73e2b6ec99b9851808fa73f736a2c0fe088d6a9074b46f91e837c8c2d9ea56283998227e3b6733d14d5b55c332c7c52247cbafcd115f5d8e994795e3dc14445397f7a614f0f84dde59c1d66620edd682527879962c0e1a084b3da0325dafcd2b054
  | 2 => 0x42caa44292a22efa31b791640495f626bfbfcbc4fa12b5215cbe5f740f25c0526ad414e34fb2ea36045f9037b0f49c7b5867ffa481821424c40d701deaafc7d95aa85c84e7ecf5aec7832860f2313dbcc1588973b90678b0e55139ff2e6141bf58ca56a1d97d6f47ae70a186fb5d293b69ae120
  | 3 => 0x1b2644b3db094aebfbecce52774e16f9773ef8116fe4cb2c05f85a8de644497ec21e5def4e86d3de6908fda64330e18589f880c41f1db8f1488bad8187b9ae353abe5d4fbbe0c259833ad6babebb789dcac6a4e57e0e0adfada49a783b92253989ec67d49e97c9f3a96903ccf3046198c376165
  | 4 => 0xf6fa78619b303e1705a3c31dd0c61b6f68d32723fde60596cb15fc15c70bffa65ca426901325e9d2d4678b72375c43bb78c5e22db86c35f5ae1fe0bd89887f10c6c5e5fa027ecdfd0c1141d0fc2e8b2ced24dbe723b29a66e089c694f0ccbfe458e9834cbd5dd5ce5989a7d71f1d25912671825
  | 5 => 0x49824808104a0586e1bdff0b3c88bc3886e89d04f7000517c046dfb6f3be75a40ff5516c57ae2963792e9d8a9d64c0be7b8c4b75f599140c1d33ee04b2d2f8f716134fc0cb38d7742065ece61bc6509938617486b49b0a5f9f058dfbb2df701b04fcb84638d5b918fe96a9a9c56322acb09cdc6
  | 6 => 0x6cecc11e9b2b2681800c3e2d771c0bffcaba748c91cbe01a7dce9db1a3dfef8f52db2b4b86584b5f0ed787a9aff5a4d522097042accd55ee7601a767e07e0d0f6092e5dc40df8895b9b981320fa8cc797774e8130b9a1daaff06fe1a6fb6341b00d1eef60ff4025ee567a69475c617a6b546e65
  | 7 => 0x7a1744e363cd3347b454dcadca8c9cb165cc0b59b2679a85ac2ee04768709e6eebe002fc7de6d3958ecb34be034a2858888e13de1321e7efd48dd2e145776ecd61506c5eeae0b3909470d9b74eece9b2957a875da2ed258128544d732730bd28205852bc01791e21a0d8991418df6f877641ff6
  | 8 => 0x4d12bd38e171278de66effaab5a838d6f9862365e0a8c66e5de15afea2842b4eda137021ef271f8103cbd4f491806e0c7e9365cefe7a8b701449404262963e7f30641e45bda46ca786dfaebb17f258b111d6a2cf0379329d5377c5a0dc2b632be5e34d80ae606f2086119bb4b4f9dcdf43da235
  | 9 => 0x598e36e2dbaa95bb6771cdf7a1b45a5d791a8fabd1275cb70a9c38e7047803303e8990e95aafb612da847671b185f88ac2de861156a843debbc0678aea241d30d0bd371d16876cefd2c9b1c64ff637947a3a26c96f55bfea2f7aac111f046b364b2ff78a9d698231ba96bd84aae0174847da724
  | 10 => 0xef16195d56d9291ca7d8cc8de78c6d2b50e101d4c940880c55698f17177d76c133dc0eb523d70f0ac2ef48542fdb632af4f812afb4e9a2a59d0a9c1593dcb3d4c44ed97a11a9d092f503654bfa2acacf50918f0b037eded6ffa01331fdd86dba975016f1ef65eaf3b3de30cf0bdcc0ced525536
  | 11 => 0xbbb8dfc6456bd5f9433c293547504b101dccc9489c6b58474295be5e0a9f8d4f89977fa641f3ef4371fe6b3bbafca4e83f0c592db1c11b04de08ad7a40fd96ef4fe306fbf887c64ad27e402348a881f41333c21ca82e31a5aa7472df8443c57a2549b2a8bb8746a94b91ab71d4bf05d6ff8d621
  | 12 => 0x385b206ad3c5593138fd4c915fd4d4c8a6b02830d40df45ed0e23353a3e9a9af6cc9ef06d1259e3d7689d630a2045dfb7f8933bb5edb24d26440a85a83fcdbf55695734694d6022aafe87ff9add492a0bb6fe1df17b90c3524c3910472fc9ec2d10d092424c0d6c34e891b63fe1b046030d6e63
  | 13 => 0x9670ad624b53403de9ec2afedbfc10bcaf36a18921f7e2cf22fed4d0420b6b75eaaca7453fe3cfd4e04b621589c2f6d04b79748011c414db1c6a84692d862c5180b0e0d87a59d869073be9add28965d156bf5bf3150a901f865e57c3dfe3f4a3e44cd30327e9d5c8daf5d93b72a0c70931884c9
  | 14 => 0xce7526be01c10cf21d150413050b6066e18ce5ef9aea94cbc645d65ddf6dd15c907880a67e3b31561ec8808bb946c5694cd3ebe968eb7a23776f58a8c5a490cbc285e0bc6cfe5e2e6c2ff1a998a697327b95438b12bbb5b365b98f4952bdb56e50571f50fcb41072d253d0a5318ffe625e33e4d
  | 15 => 0x31de95cd5f4d0fbff2ad7251c0921d17b20654bda8d704fd85afe8ef9123e21262b5fb95f729fff0f55d5af9c25809486926c05cb5a63c5749559f3f93f2cfec17c987c410c38103b5e421cfe02f738b850f7b513ba8c05f6f86fc3c8b8aa5ee277da3c9207e6389ae25130e71986c21ef3d0d
  | _ => 0

private def denseT0B27 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xd2f0ad435371e219a581e58db1a9c9b1debebbaa9f62a5e78d345372f51501926790246a10eb2919e50d178c4536ff02275f4479437ba6eab2c175ff127fb2b9ae41d44e8d2d31f8a6b9c79ebb46cdc6a99b1d02d5545b77fa556cc601fd2e1a73d416a12c0876579273c6f4e982a32e7577c46
  | 1 => 0x18f64e255e21bb6bd44c4272ec7f15a0112817a1ce3db02befc65af9f15decd9eadc9733832dff803c5612d7c8bb717a3a207748329b750b2b0e1d603f410492706794dc439eacb27f243ec572e94b6e45cefa5d0d8cd84fab559fafc92718cfbdd0f295c9e9a93b79899780cf99f0c998bf07a
  | 2 => 0x8de925d7022318e6348a75b1d32f93ca5bfba75d887e488bd0f55f94f3c80cbae508c1c70cadd1b5f49b4a2c1261023dd50b907a9f00a100ccfcd794685211ab087fc4a5231fb183f602f2064f61c4dceea97812d2c30fbffaafd6a541b8f5930588da4ab68dbb53e5cf6fc6602eb7a9d65b467
  | 3 => 0xb2a8ea04203f4322df8d2f99feef742e434bf83a01fb0faede19db3c1310bdc13c359ee880617e313afb70c202cf65ac1c7d20b433fc784f1ae87c7df829f5e02661bcd963ac6ef393833c255d700c8eb6d112152de9c32c3e51cbc35ea4d9db720145a48c52408e1306774b5a66e3d12906af
  | 4 => 0x89ef576d19bdb8d803bdc6247fa966c7a534c3b6989db8eea9aeec28f8b8a2a9e9a206053c382a97cca380a0a501b082746e422be338762a24918b24710fa0f380322725a3f3bfaac9d0bb2eeaa0aa7bcf4f2b2e1b362931081a4adb92f11a75464142d436a6a8d29bbf059172a01f6de5d8e4b
  | 5 => 0x32e8bd1728012dad3116114f8de8966cbd9de4c21ed932fad79d8b5799d66755921143fcf82ef2882eb8087c8b0726317139dda6905938a9b4968ff3c7778cb176db103190b3f19f12bcb88380b8d483a9802090125f764466bda7be3cfa2ba6b5a4677898ddd9839138db4a1a85d904a672fdd
  | 6 => 0x75eb635e3ec8a2673e261059303bf0a2545d7c87a20a32404691e4efa967a49b3c85d595e9297716c015ed5961eb277f1e55e7970ec990ddd7e9481ec667bf38109f2028be0dbdf55bf46c0e56f4c92f13d5a5d94f5e9ab301e675c0b2f0e4db9d5a745c720bf52a29cd56ca58a97fa68e9b3e0
  | 7 => 0x585f82cd422102cd7084e9ea2607b24bcee3eec4c4ef499c576c984bb088402712acc0a4ca1c96f96026180760d4477cd0a95552b59747bd300bda7fecf0d854a3efe595699c4ec16b1c3170fb2a728067d6dbe5dba51de7d47a711c3f1af587770b3f753b779e2a790371b6f869ebd04ed2c55
  | 8 => 0x126bfc4cfa988a7b143a3bbd1dcfc7da45439def38a2ba1a91480edf45e51961058f0250f0108af749bc886199a715d6698deb0dcbd08bb6bb0ad15eedf67829ba583db15d9d42253cd6cdc5b15746d5f339c5bbafd0e2b12557b07c43f724d1e5ab58e55872cf41a6068638437049a8de8eee
  | 9 => 0x94656604e4bff150c11b39ba92cfd48ff6982bd4979d57d1699b9557c4231b5c34759c4956023e280f39362dc79680a9be00edc031d7e962227c0bd1f3201f8cc9df5415005d918dc36868beef44c0d3f431d7ca10657d3755660863435081241ac71cb6910ae9db0dd085e0c7aa6cadef4c6f8
  | 10 => 0x66313bb5058353ed1cf4e145f4af3f138f771f978dc8879606539776b2e6d9ff7bdeb6e833a18eb7ec8fb8e37212588354d2c3d47510ef71b0c492845ae9db301c3e21ab6d6b9bd8914f49f11a919a9c7d3b159d4262715d73112c84afde7469128474176bddaabba5033ee538f9f9a1f8be9d5
  | 11 => 0x5c9f4b3e17c8d2af8f40d5079e2b9512c0ff7ffb9223e1a3940b1fe7de444f785f8c6d4bab9573de224e2640f0f2516f76fe75c875d5133a651deb8fe73d81bc0c5cca1e5a9d8430355053e8750522dd754c26e3c76d1bc1a04c91ee9fa2fbdf470076ded79c7dd916e101a0312d25d0c7b7419
  | 12 => 0x471d8d69cf23df2852266da256b6cda24a4c8f48c1e63e751f021e333e277462a97f2db8769ae9d81ca5a4455e6ad9aeee35494e1f9caeda303bf8221f003b2fe23036090e088859703ffcc5d785d1fbfc11338d098b0e47b338821838160b3199eb800d03767500e257e2460a89cb92101c149
  | 13 => 0xb545f66d428fbc29c9077e221818a6ee28ed27ec9fdcd6e9fb63d12f63382c01109071a5624abf52332e4fd21be4b7bb64be1b35ee3b6cfb0b8d2bb0a3a7dc74d41cc5f28b2ccbe1172e3d3fa259789bb23cd8a83eaf396bd0e4416228b6c908da0593b119f3693ae035200dbfeeb0148fef2e1
  | 14 => 0x1ec2b40d28d1833f262beffc206dd03d612807bca4f6fd956dd9247443542333e13d0ff9bbaf7823f298fe83bf061a81ec59655c2485181cb8d02f747c5012ec34bff344fb15f64148dacf63e9d757094aa63f0032421db201e378e0fba9a9514992ec2398a497bcad9b90abc3be2789c67b174
  | 15 => 0x1c5c609220f62402ecbee36ecf2d8f8c2919b24e0136cc0e072e2163b96282d9ca492a445b361eab649ae872b51459178c742e91dc5ca87bab23dd39022fd919be22c98016c5e1b211e7d2d499f519bf68e59684ac610d2711e920d5f81fc8f930f91d092115d8d9bd59ce393b6a575f7bbe016
  | _ => 0

private def denseT0B28 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xcf97c631a6e4a67525b46d0e350d1dd86cd7b2ae0a968fd1cf65412d211a12aeab538339a6d7f7188ac7e3011bb0f6b409d9bceb920c67fff4d17a59156bd89c3cd7c90be936df77df7520ebd719a971919f020d5ac0018a7c168c52d4f46e7a0fafc881faee8de60f5beed551c9aed09b55e83
  | 1 => 0xe2a01160c46d79619836909d7dbfc56e28a8e6e3c8e1e92da4693230848137407290aa32de7e62f84f0b71c1dfbd0f7c029fbe8a4cea548ebd52ac64ae78ae0f03c8d297b37d89de156f3a3b87f53640aab8e2921936371982ad9c4d39179c1c84aab0ca177a6e925a62e7592f0d1d3cb8893a5
  | 2 => 0xa039b168f3c49e29acdd9f3563d7d8a0e7d44a33df9beb9417229cdc11ce26244b1244b93d69ddaf936b92f073cf8de25227b33a896711cedbbe57dd2120b8b481de50d93ad3e08613ab9a0fc4f57a0763b8c1a14cadcb94b9aee818ffec929f0001788e37b2d922c830eea917d34a1d07e0254
  | 3 => 0x8cba8132c55962689ff59e0b3509840a66917a1510b56aad037f788b0363a01e5ac957776757b9752f10f2da0f3a9abf1b38c89ba52ad2a3de842b1d5e86f08f688c37a636fa08481c801efdfe89b6fd1e23ba6f52bd6771f86d69e3a6bfec8f1443c7244d487f65f2bb795372763ca07e9596f
  | 4 => 0x4ff97da09bcc98fc77031cd99f7d49784ac590f19027ced44c84539575143cf39177e0b311c4c47a61bf1c62c516365f509210bdb00e08a751c29fc2ff4c50de4c5dd05bca23f687e2ddd50ef1ce5979bdf6ec1063686a5c04d4263782e582347fc30e8a33741a91b8434eafe5dd2acdafcf5b6
  | 5 => 0xe6396e07eac647b97cf12855799cac2a0c92d859aa0622743eb424267bbef85964b2781bd4de4afe34a2434673ffc58a60bcc302258e2f9e0f4ba31444a83a2775925bc18dc76c9c1d7d120f87fc7d050b8a92dc3437da648c8ae1dfd4400739ec03307b9efbc012f76c879b083c805eef89f
  | 6 => 0xec5620e673e1996408c37541ab83010868b1e36a0e58c44cba6f60e9df42ceeea4911fa4b2dc74af0d472771a2404e2b1bf3382b20dc2a4646a21181a85a4aa7c1ae841dc8bd33b269f387b765c035c26ed61a94dc9cef40ee25b289b4d69b8ff8128aa9135020a93ea113c5a55c04a311857e2
  | 7 => 0xec3103a00c4509de18bdb392c5370773d1bb30f638e50045c2c0befff60955f0ca16b57b1abc9279717aaf254d6c5a40c0e676323dd270849fc10f19273c369fa196c57fe1ce7c9a1df7b0dbe4649823071183ecccf1d06bb4e0099913bb3f15ab0006393a1ba31e5db3e066cd16cc15c0d70e6
  | 8 => 0xfbc44c7d3ca1d0e28508102b288880e9b27c66b3078946d69536f5fa70ff6b3835b3acfc4a2db0a24a7595af776115897182cc1fcd5ab2d73d6fac6b41c91090449e2a2771fcbb5b55f40970ecfc19823578cdca335ae014595b1c77ff5f60eb61a6bc67199e4d44750634a7ba4bb5cbdfd0712
  | 9 => 0xa98195d8d53abac1ce13aa355a636b4c4d14cd4e59df664aa091061b55afb19c4f7ad24e9c7271a6f4bb69b27992da1ee568ddc4eb67f6f0915fee554c19e99a123a6e78236ff7a454b20cb485cf4f852368f07a3f5ed034474832547341c2398a45fdbe8108cc62b2c3c435e2bdbfd9033f320
  | 10 => 0x98ad57aaa072a1e5ee572175bc022d05367c7afefaeccfb1646760d3ac924757def2673c53749ccd12db6bb2c438a0bbc3622980162fb0e7df3e711c58dd6c3766f6f9d3600419f2ecc8bd4aabda5db46d3e472acba4f5ebbc45a83abe166fe8c00d07343dc354f574055a665bd2b566d16ff8
  | 11 => 0x7cc841ed2f2f2ae79197f9237dfcb72c6fd0ec29ed59374b70ca0231dfd79f6f3e4177e2f3b64d496d0a38ce036eb9179eaec38628323dd4f3a61c204f6e9877836de02a568e863142af53edaa67b99240fcb627a03430e17c740180defcab233277c37ba95202851c67b0bb06c4bf60233acbb
  | 12 => 0x86d24292641be1e2357ab81c5f6ab3cf2d0e9ad7e1b0ead91f20ec2c632e893d14ce31adfbea30d0f570cdabc4180379858637a29f9245cc9b64ff9d33d45ad721a49f4db768d930eaef427709fee80591a7a5983f08695cbd3e7058cfa403b87e0264e4ed084c7ac9991be16fa0f65841004ab
  | 13 => 0x702d5236c825a89af5d9800b3fef13c63fe19e39f6ba1d718d16ccfd221800e9687ab6193086fb60f1dde2b683ab53d37f85592c7ed21dca8e75a8f1a157f1c099de5759ccc2994a6a700eb68b5c8bdf22974d39bec8c4beb1170d2298e0fa9b2d2d4e3d4bb36e37ae87cff8443d5e148862bad
  | 14 => 0x928283399faad870c631269b002691ff57e9998e0c85412311fced1d02b200e0023da44d18162dd637bf0e3159dfed4ffd97c8e48de58c759970fe01c98176f638cef766c8ce993749f94bc27d49fa10625efcc1cb4f1b57ea279df365fbf986166eb3f214292798ac812c379e582d290cfe22c
  | 15 => 0xc9aaeb82e90743d87f0524156e7f3181e92e7dc7af9208ec10e52984ad5cfa39898d30ff19d434ea771e4403f112d0c85353ddeba808e1c44d647f0671e25e20fc8005744207adee6fe3c2e0ad1b548cabe28355b3e8227270b1a8db777efda48b7abc14eac0726cbf15ba74ba68f06fbd25de8
  | _ => 0

private def denseT0B29 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xcf89fb7bdc1b5dd3ae84f1863a5a6b5af53134b775e623493096e167bd1a69ab64013b19fc2108ad2056ee7cdd57081dce21613117476047f01242697285173e361056ff4bb75197f3fe2b276431fc5053a690a05ec9fcc84b2873bccdaac2fd8373fef2d378c68ed6ed4162ed11bd8c3c7c0b1
  | 1 => 0xf4af08519d88ba6c933c0f2f39e3a2f2e60bb6e18fec319ff4d890c1ecef5532758ffb59febeeb3b901d23c667ba65e27ec9c8fd2b7e4e9c49b4455ead76afd59851fa1d3b68b474991d87a6cb41f567092c7caf6897ab1df2963bb50b04decfe135a64017fa9060a93828c13d6a1ab4e88e85
  | 2 => 0x6c2a5dc3b77ca44f341195f3813db738279d80d42914bb7e172afa26d3b96c49de6e7dddd7bbd34408d1244649d132028d185466b9fa011527112619b12383c0d84a350d2b1b5466374d74707a6f513542caa165171faee47c4cc80cbc747f1e4090d2be3401f0ae4127735f62e4a2dbf0e1dde
  | 3 => 0xe893abc5136ad88eb2ce2a846e59b02474daf779819668069828d63e999f9555d34e972de03062f8e068e8034b85202ae418bdade8f63c405d486baac2d5796cae29cc0d21dcd961ac7f6c7eb14ba2f328530241b8802e2158cb58ab2e9cd8da344d1df26e19c779f7eed608a9079a799320e46
  | 4 => 0xf340603678ca35bc39bf92068140d96ad84a2fb5b65d0bd845ddfa95926a46bac5df3449b5b2b9ebbd04058dd0c1aeab611f78f6c3ff83caddb18bb011b5cccf583d0f304942bea4edcf9bb3ff0b0d44125875fedc3dd696d632aaf041503ae51784381b8226c261f276bc44c1bce71d12cc4a6
  | 5 => 0x196e6e1cfa3c3b759a523b877863eaeb74ab1c058594a8dc8bba426424023699a77686f30ec0012dfbb358fef7c61730250f8c39d14fe179f05bc1616f46a3b7b75f86adc6f3e53ac34b5b7f490e8ee2a36f77d6daa8c0f0d20677bda94eed91ce566220c2fdaeb4b619803ef20e5e0dbad46bf
  | 6 => 0x8fb051a89347b90b987f36ec38fa42e2a98f1a33b72b897b96022e3a719f14fbe6a2459fc13c0efddb6d1028a54190081e01a02ccbf6cba47b34f713a501607dce5fbf0aa537452da59abe252db6b0f7c238e9dd3cdd76c07e856b3b60b683a2d4f44b6b613249ad0dc2a6703e4e70897eba946
  | 7 => 0x7667c466377b5a9a074566f19412fa4c2d236c4767b40a52a0562f01f03d74ccbf7748d30b4318fbb5271aec31c6a7f271effaf7a7c388831f14f3f5698d1ce32620028e6d33463fea92855bd2af3d6fc7a816e010b0303583e37c69a0e953da563eba581736e61158a6a64cf182f63b551ecdb
  | 8 => 0x71dc73ea5dabc4118da3f49cc75d0a6e9ccaf93b48147e09fbf5e1a0d07e29ea4578da429d955541ae8977b316e1f91eafad18cad8da1185d17a5172abc6fd6bd5e3d3ce2f9162e255ae306eeda6f538803a2dde70e47830e73f58636c1e3d44395e30daaf9887cf0733ab278e064f12833aacc
  | 9 => 0x3c24a17071a595e20e3724cf72753cb050dfed90546e8dfbfdf2ff758012e03458d6a79b346f733f0b87de3c9bac3d07c7f6448c3bea74490e89662581c5c65d4003e00618d729e2c18cd4e935e0a4adb851eb0be16277a09209a884742f7b883d07f4204344fe05c357f9f588620c99190368f
  | 10 => 0x890e799d1b55dc92d9afae17109748826ef4c3238e5a08546270a70be60a58680b27fd4b1f1aa3da7dcc1a330ae2a1ebb83abaf6d9d7cc3de7e546f52106ef2f3408bdde2bf4d3148b54de5ef7c8b99864921394314e8c060c88d3dda557e2dc51fe8f93ea1b5c074161eba47cd3d7e82d5286a
  | 11 => 0x89d577596c2bd9f05e02be42160b9f61ce7fc099e19703cebc5a6a0b1ed715d5542c1f0f46865e017ce450771c18ba1f140a8ca7d9e5b2917576f19ef0774cb508fbdd4bae41e4714e5f301404eaf12d402fb15d77e0af04458fddc8c88dad8a406f2b056192a0bd101f55961c44d0d358a76e4
  | 12 => 0x4dae6f5a84d8743a9845a74c6cee5bb603f939bc365027b350eee4b845587f3fff66e5df65cd829cb8c26358d1d417476df6a4b6c90eddb3222dbdcee5347016647bcf919a37956a448d4a300d4d0909db1116ce9f23a4f805c89ef7c55be75aa4773fe092c781981532f724a267d2663d9382e
  | 13 => 0x50bc1f72395aeab2177ef8ec65d8f29c2bbaf304c3d596f221e16f3871f00eeb7849d5a26686f5620240eb53f8c9dfc1f380c3cf7f38b8a7dfdd8f2183318b3ea02a7f704d169da7f944263fb392a776c03063aa4c74c16dce36893ccdbfa6ddd3d51bcd1edc07be850c21c7a31d7e597774db0
  | 14 => 0xa242aedc45dc3ebaeaf1e8b9edf2c81202b406c093e7407365ccb362f42d3262554b051b70987e54fe49a13bb01241e441a485d232b6b8e7029e8a1775e886aa9b9fe61f1a6c5d5c66547dacbb886a429444874c5be8e359c4774c69b1f00bab067e59c5a9594d8a56a1bbdba126c7ecebc1b28
  | 15 => 0x5d79022ae0cda6ab2046099413b0d378e162bb2744b503b4c751e6d231f5a180922c1c02886fc894c803a048183bb5bb39984c06645d3227c0fdcf3b0d8ef75d95cbb3205a491154cad95005eddfd3599e1b586f60c0590923829c50310e0fd649cdc16f73b801f75bfb3b02829bbc01f8ede58
  | _ => 0

private def denseT0B30 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x26180cf46f3bb80bba3ffafc15392a525b838c4888d00db1fc7d82216c5dcacb4542c97bcb860bfe1c9e07baaf091ccad6c66d8e17b4d4d5f852dae8c46d8e73b9829855dd405b4a641dfd0c383f51a2c15bccbe338d224bfd9dc8f76fcb0485ed88c95390d321e11c9934340029ad918b31864
  | 1 => 0x55f9082914f10044bfbcdefbf5c39bfee178d33739682ede5c498235c793f83491b736ecfb690a60763f826cc5cd1a97d868cd3752836122747b9c1f2a0080f0ddd57c66b61b553876ef0f973ed9222bb287511c3092e17952caf1eeb70f1cd507f09d0584112ff779c855929f632aa419686ff
  | 2 => 0xe4e1b8b9a49bd2258a4054a0e56a6a8fc1e5a7de26be3892bcf99fe3fbac591b1d42a0630a7b2a03e6c3927a22707a6ca48e9d645ce8bee756dd036498c202d875737c848396ea046d54005cc208466b0e526bf5251310fb8971a9d6c68d204bf023a417181bccbf853c7016d6c2ef19c32e8b7
  | 3 => 0xcbf2206441051aa459c7a20d2d67ac854cb23543fa91aea290e2601fb47108fb10df3796466bb039eeddb53cc7277e52af9a9e3e1fec6156a55c3e818524faee47044ae03a6d75ea925f3752c43acc6e692cc70dba27a64aa702e4b9aaf325e165c68e975fcb24ea9d59acb019fb6d486d5145e
  | 4 => 0x5c2d459eb30c6657305e1006f3b48b3b32d4e267fc9572a931eeb80f4acf1ab5e1619d2e64b544f57c1a15f86018223ae7aebf1ec5868c31683bc120faccc0dfbb447c799cc67b4485ed8013539a15c899c7b414d9e3778ea41291f589ec8073b9515e9cfb310af413875fd86175e93388b6261
  | 5 => 0x7b587e6d47c711088b139d12eac514c703929ecef0e53bd07ef9bd8c08ebe98169445b90c9b7b6d35b972a032f919fd0739fb156e7264172babfd5bcaa5035aa00f9ff53cf81ed214c43ce546a8306055e88bcd92dafd4e373f8dbf3efdaa8f48ac041db5643d7e32e7c2f54efbd3db93f25efd
  | 6 => 0x4d0ac45ad2c53ffcb3b62758ebca819dd6a688601da5a72146a426044ba3fae9392a0aef6af197cfb2dfa2ee0237434d67ca1947906f8486c5f1c7460239517ae6c5b6df19cbff554ba90c1b6873c8116de2a4facb3107e674550cb000b79d13c9156424e669316ac0f898d984929901ef79447
  | 7 => 0x3bad01a0bc0e08e008c93f59a4a0f618259b9b95776a297fb530e3fb3b07bf6cd0b25fde496adbfd9b6a448e3cf34ecb67c6dd6ef84277735e260cb3e9334b39c87674f6563aa712f3a5b491fdbc6e2ae6aa6d634834a5d91c9c9ff29999b863a8ca87ceefd771f84d3ed77cfacb6e61b2c9223
  | 8 => 0xd103f376093ab941fd199a0cf36b73af5f308cd4f4f73a79108fc59aeb6a0dea2e7115cb274e3cc136446c8f4ea4cb07c08aebcafe159ff748a7d6a126e356466c23b5eb083aba13c3a299b4c43ff39cc6768813bc61a1f62edcc9ddfb3b48d21b2084667eea821c9f040d958512f1595413d6
  | 9 => 0xb3613451fec79faaf1d762fb5fc2af89848e4050333752f688a23c9295d45ff4f018c6d5d946661faa3aab19132d26e2ff3b9f822bd0dc54e922f8aeb0b1ea933ff72507a216ccb70c3182e1173f9476def8a7bcc6461bddd604e37c4956b90a140e4ac2cd2126a815e9555ed8287e8855791a8
  | 10 => 0x3413d7ef6660011cc6bcd939db634409abfb0ad3cb61823ff6661208854a0b0df2b92cab93c33c62b6c9e5b48309d40ad91af99391eadb23c3be6be72ef679b0c30a84f58ac345c4f5ebd61a3de380c00c141ea22d84f94c86c442b236baf3d3632cd1b147790e788120baaf7f19fe66d3f53d9
  | 11 => 0xd8d482f0e2a0dcc25800d78e72ec0d52f783bb24e07b277a020cb8b08308c952aad08ae164da3014532789572d678d3daba0db9385b4ba0bd88ea07749a5cb0ea2be96317811d1171c7e635897b1ccd646f56d558fad14bb06a71efeecfded0ca7e002e9cf557dbe02396c718ee468c56def8f1
  | 12 => 0xa702083cba5cc3713035867205eaca1f9f31a87a1b10143730b0564ca276b6dc4021ccb65081d0b29fc9d96b8c12db18f28e7267f123724b02276b577c5ff7cae5b0d7da2dfe7f505883b705e7790945376cd58ad3f4974663a5fecb5015faf78c39b08de0f463c60c19d61137cc8ba7a4f0150
  | 13 => 0x1ad3f492886a611bcc742e049d9f9caf96910693975cdfad591d14e2399d12104ad1e9f9fa04556000d16533b71d5cc4be6d11862654406496e5e31c27685fb10f1e8a1d2c5b9b0bde40c0ee7cc2cbee4588c1b109d5eeec5ba7ee76d52ae86d283f229f31239e43414ae686bedb00847dcf7f3
  | 14 => 0x3cfc3833dc8131f1c8520667ec7fe207c1f20bfd54bec8dde90765acb2c55ea67b57074b396613df375f01a1970734230237074d15e6adf037166cf5a0c5070f285b28da34e9fc77d1cc999f9e29df318bc0a87cc538185ad7bf38776a1dd7c50f408df05565732f169ff27f8ba5d735a94026e
  | 15 => 0x853aed0e20093fe33297c24b1d25b0b2a380a3234e56eaee5236b4f85f95046ebf825985f11b4a6b2a9c94a44660a27cd683c42b27571f9f6cd840faaae252bd0f2fd4c27dbaaf77de4edc4a1f24cc7056bc4f3016d57330eca9109563a103128156eff09fb0069ff8522cd2d0f8f8392079668
  | _ => 0

private def denseT0B31 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x78feba6895ce2258c89a4713821c8e1ec135ae114ba210e9c4238402839f04e226ff6bf9e6fcd7f8da504ba3cd833904c68a589729ffff33b1ee6bbcc72507c34886510af8bb5115e7462ef00b84e7394683b06c695204d0197e88de2ed5ff4f21f0171f818e14a9aa28e4f6a8c516d4948714c
  | 1 => 0x5c7301416d7699a8c329637203a14ff1bfd350e7c06c500344e4beb2209e11155e7d2f9cd2fd949d395484d02201058492fd333d361389e19ea2f92961f5be50aa9f77080c68d11eabf316325bbaeebef4af54666727c0f712cc48caa2ac89b32b36a098949b6c615fcd738de72be0ddf80112d
  | 2 => 0xc28a316de29f31cb7401e3226bad6fdc33f894fb3c3ce9afad9320e082e017f976dc972a123cfa6833865e84b00e82984d0b257dad25ec848007bed77e42d1e46f98ad5c2a6b93a89ecc1684afcd32970c99962d481b11a9d5244f34b3760a273b4239a288f0a068d12ea58c8b41aca60dfdab
  | 3 => 0xe81b006919926746a938251288469a6eea0fa8fcb018d2d4866f272da1a3380d89431001c8063b7308b84dd5fc2227b0ec030ff7a86fcca62370f702f020c59dc637b1bf30ad30a3f92d381896505da20c35e2e5485bb1746712f1295b22fe5f42743da87482ba6e4c207bfe950639b8f185a1e
  | 4 => 0xe9daf1a627a1ecf97e128b318bd824ab8816105df277f1cb86a9960b89cd9f7dc6ad0ac9864a19c4d7877ec6851cce7b9d2aa1275d693bb2f90105aaed0ea39e5fac1fece6ef38813099e3adbd3ba41971a4db44876b4f66c3bb3e2326652e37ec5dd6e9957b85e5834befa1f5912095645e81b
  | 5 => 0x13e19698397a3dddc0e8bfa362d0a6cde44e1deb4c919d38d3972befb6d3377e9dfaeca001245363512c6d78391e98669a3f85d60216d9ecc5d721b18a80d100e0f0c666b97b8f20d95bd777cc3c757a2ea6aec2cd8e8f6547db8d0f3e756f7707a8b34584b29f932422306330adb80d8cfb942
  | 6 => 0x4f7ffd98539744375b51b03f98056f1c295940136b059eb9e4f5a75ef3f0720476d04f782113eb114ae5032f06fafad3687abd9c407dbcbffe3d6a990dc5366523b15a63dc745483ae49b636d690900b034acc30b96c561fcd33ceb5afefa9e1ddd137cf34075c83e8c65e469edc809e95d45a0
  | 7 => 0xc9ea742fb5b975e17ed870c9299c26c44cdb7040670a511fe43688a21f57577ea7bb13565e5d12f455fcc0ab7563442dfe6acf4d9631f2ee4afbb50fd25b7b0c3219713cede36037a5162404e0e086f67d9f684d8930136533e4d6f23b18570e8a66bbb85d616a85444a5befbb074d835a06432
  | 8 => 0xbb3ed406c3f2662f49ac3494d827b67c0b87a7e8fd8865e0fa3c13656fec5fca033e79236e9937afa4520968bb4ed3e082828ecbe62657d5851b2b976ced57f1bb576dd7ced0f2afa20cfa5ddd5a2cc7e147270598f11d6cc4ae60285828f0abf0f1061846d96e4f4f69841a71446348e5abf79
  | 9 => 0x7d5bd2b50714695716f3edb8506b43cbab49dc836a08066b03b1eb66e82ce84a92a36fe8240b603d61ce78c09ef3cabfba398f14719285c76ce285644f81851cf5e6ec60a13ba751cc0d503d6a0f0cd99fde7e5448c229c9ef92e6a29f9ec01a015725554ac577e8a0376d9c22474b8fa024f50
  | 10 => 0xeb05a4ce2eb90eda76cd4b207fc3395f223e6057ff8424c39b090b82600dd2435471e7ef1a14d1e38455b641b455828464a773fec4b6d7ba16e5dca47c2cbc1221146b6e09b5bf69f015fb36f049d36eb6820ee0fe330a9096f24b80f5bf6d43e76cd78959fe2e4a03fe95ee697f0b87b4fe581
  | 11 => 0xaa7b012a0aa01144668f55eb62fa448d4e7cd6713ee28102f34037de8c8585bd62179bf583ebde7e6025cbf1f4176ff8048c7a5534fa8461a19ff02209589832522d6138aae425c1e5bf1b958f2cdd7be3833df14bc873be94e4bdce89755c9b42668fd29ed2ad4d8ebab72d1b858537b8c8cea
  | 12 => 0x8c891a2e200b5e1c154a53146b08a39445190b68251c7f0412338971d22fd3de63f1d231ce39312f78c5f10de3b3180d10b5d8f7f8b5c70590f36cb87df0ec71f8ce6554071a733d93a6e3101802bebc6fed8711393fbeed59def4d3afe7ef415849bb3ae34bdf8b4b8d3568ed4eb3255ae8519
  | 13 => 0x9b54fdf6c9327cdf415d706fae3068a08bc33133ce236192fd9db073329d1a436ddb3a72e5eec0a04487381bdca6706a0f30e8f5125aada6c2b8ddaf5f6fe60283be3643a9ecd56977a94ec11bb4f93d18700954a593f4a95fb7d46961a20b33eaed8703e556346737cd2d1468059632240d066
  | 14 => 0x9224f3ed08927d46a258bbb9c8f81c43badc3830a1a4288deac3d84a1050e1d3f719f694d87038417c1ab701cd64accd2862b5f9b4d4b26d34cfc5504eefe175b39b991fcdc33ede557349f25fae98722a558250a97cd6b375201027599dc906e01f6dcc6fc3477513d68f51844913ccd751c45
  | 15 => 0x66c30509701af9d663b9f9647d95a8932a1e530be11993d3d14209e91181304668e8ade60e40ff57823372f0fa5b929cf0ebe30397e9fee311ac484c84584045479ad31b5ea794074cdcffa1dcbc0c32c109dba1721f4babdbc145c4f10f8f967c1958e3f6dcfb5661990ca311d8bad4dbb85cd
  | _ => 0

private def denseT0B32 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x97f08c3ce2875790efc3303f11f11cf84d37c87b6a631da563416a83e5593971c23b828a2fbb61d725609a2e3d506986ec0b4f07977570e74d433ddb6f29c6c29d19ae1345fb933b490e16230ee173889a1a0e3ead217e141706a842bd44225614fc5446522e8a88c28b591ad67b8a88718f7a1
  | 1 => 0x742a6f009ae407f9fc2e493993560938804b72a1022562be9e559117df19b018c133bfc4d613fe5d6c540b4e04db7c455bf605d9b83c9d88119e165b38e0f25c4a2b7b2940ac928532376d8343f127c73b32ec3655ae22e4f3b22b6b52e240c11d81022f4d458cbb10aea6e0addb1a8e8627a2c
  | 2 => 0xb8a693719516dff4e526916e638ae1ef6252c56da338efd17ec876bc6ba0d5f2d6b0e63da089816f8deccbde931485c36f395ec43ca0af3ba75544d4e89453caee840ef6742b3a2f463c35fa23fd1e70f51f95530a623c2e5a6991a84d0434227de00ecb79a8759295536e51bc68a76c4350d19
  | 3 => 0x278570ae7e34e90137cefa9c9cc485340f4fd8363c9b3cd6d8edd5ef9ca2b91d8d5d9ec79bf37cb2f7c4d40e45f579bbb9d316febd7d70008c08724871b93ab26f213824b233078bf4f7e5e5e1d07615b075d522c36c953a8e2eb86f47581e1a4b9b4a767adb5680babd6e1b1dc2515283462fb
  | 4 => 0xa243626667fb1ba0c70f349fb89a4c93c5ed4184877057c0ca514ee439f43cc2d622febd6de6c9eb3e6f7508709ddec83986ea3ea7396baa75dc6c8ad6aca1097ac3befa4d5807bcda6afb277871346cdc2e072817708c4571ea29d8e25e973cffc58fc3f0b3149e2997e9f5f3d81ced39996be
  | 5 => 0x4a134f08f5ccc25806a19320d7238a66402b2e2fd68023b3956475a33fcca2a357a304829adc7ce6d4a7a7aa5227f02340473f09cab7d45ad4d0e33d79194a5d47991802959f1a819d99843627ead5033e94c2dfbcad2ea27cf3790526ef409e6030383e1648fee30a93640890e16282240259a
  | 6 => 0x478207016d6bf4f4bd55275982f92517712c8b21033eaea5fb9cb3f2c4d185cbaf8dbfc35ef3f111067ce4dbcb069e24ab0f3c64e68a896fea594624abe7137cfcfd547820b2ca734ffddbd17ec5615fc194b62e96f0e717618f3f081bccf1f5deaa9be8395a42dafed95ff7f369a1e64669d6c
  | 7 => 0x6d5d60f44e85ae357f41c28d48dba728f84976924c0699a3f74bb4a46bacf85c07ce6308de51d712e163793cfe9d3398f6e2ec10de2cc619664c5f1cdd1884583922565708f336f6f9e05fee02aa032093776cc26d56b69d6f38f1540838492c4c53fa7aac848c76c9279d5ae424b8a786986df
  | 8 => 0xb5336c15624be81505b2a19b400b76dd601c0c0ee3cc16218458f586e422a0098cee08939dc345b737fc6c7af92eb3eaa8b09fe36ea2a6384a652b8c05b938bb7bd812993bbbc8ebb73c769a6863770d657356833e707ece4d97d102a9e5ecf207c57cf4f76eb71dd81b4f575f833a3c18f744b
  | 9 => 0xc6bfff246e2ee344629d97858671d27c668a7c03b7103cc4c655081ce8eab4e5f978650c95d36be7f8c589fd04f06f01de15f1e7a468f53ecd04666416e0c4677c5d989744d2376ea05d0a080a7ea916e24c1c443f1d07045b77b0afcd475557a28b41903008fe90039631b2ba3499409aff42d
  | 10 => 0x82083774daa4b2ea702fa04a7c86932c2fc41e11b427268d88fc0945c07150140fccf5a0a43c9e20dfc9017e0aef073e495bddd8dfe1cdd1f1a2f3abe3d9bdc42e78ebf25588ab967a4b3edb487785fdba92cafe757d2b3d014a197ed648117fdc940231be54f4de88b1b312939b90f40a5834a
  | 11 => 0x41cea0c74ad6e1966a0bb7a9eba1a6b15dd9652729f7fb8319474b46e4fa0c1854720d247c06a00aaea197d06cc9b5cee4d73142d01a198b4cd9774811b0d5b4740f9a2893344bc67df0b9c9a054f3d775bf8905fe064757934d06ca382cea48de4b3493ec366c0b6bd86212441488c6b0fbd06
  | 12 => 0x74d6ddb9d920dfaa158cf71c4dee3ea4c701a245dde304e6a85b048295f35098921a5a464776252b48787bf330a112ad36386b4479386fc5505cb2147317ddf2cfb4042a0ed6a42783bd5021aa152d827152414d68ade2cd2c610fa8ad74b31be091c39417bc930ab9f987cea3dfb66b5d6dffe
  | 13 => 0x1b4a916034410aaa74a8d7d339b77a4d23b8a152d255e1010deb1a0c4e65ea80eed6a649be9494928ca126cde93c68ce0b001cd639f5081236ceed4b028bfc74540d92156184fe5f2a812fc2a4b5d26c4f6ca85fbf8a47899e8a162ff868ed9325d91a7a4aaec8d8fcd322c30321a23fa635bf6
  | 14 => 0x7c968864d9a6def078aebac533a7d233d31fdbaa1f3e20bd459b225e16b7910958508c16e423f8a82963c75cee7e9d92ed85e310c99f18c110047edf35d7b060fe422e26eaa77846eda85c1033e1f144b22470b6cf03dbd21fec268b21264e59007aec0ae1d04c8b4581bc65bd14c64b35ceac9
  | 15 => 0x3e8a89e2282e355d7f327da1b1fec902d292622a5746a45ec06637daac567e2bc47be953b4aa1470a7bce29cf76bcf1e4ccfad6a71b52354730778461aa58f54135f8fcec382691d61753ed942dba3f31a20dfb8b361f63ec0048a9783f5ad80aa811d53d17b36541b19c3e2e6b86e9231a27ef
  | _ => 0

private def denseT0B33 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x36a66e465531309f37706e4197785835ac43a2c47bbac719423eece91dcb4b8f7ce3e31eac69e7b542968753ebdaed2c0b62826b125d122f8c918f25cc071b8b957eaa439bceb60f8c478f94acbebd6280b743b9e8cd8dff7bec83bfa6c9369fb31a74004c2f7ae217106751e876fcfa7f1f8db
  | 1 => 0x674fa8b2de27203bbfd42511cece230d4788b1f43adddb38d07a7e0c0a031b670215e137040f50f44aa502870f57b7b8146f335b07873dcd94153495d101d5dac2308f171ec3328e087d71c87480bfe37a3725d1af2af5615e2808489f03a1fb962fee6d8a71bb1e7ee62fec7c1a5930420a86e
  | 2 => 0x29e8c173aeb50dc5d0c05e64daec8b9f410788b7328c6455b8227a4eb1e9b6348cc379674ad6d632a25cce077f359324d9b42fc1f125e880b7fcf54cfd66f33358d9f131d73737dedc939771ba0957f04a4bd52234f22dccf33ba498bf4979373e4459dcfcf76d54c6a26653fbd2f531f832fee
  | 3 => 0x38900e7a8dd9fabc5c2d5e9f96636dbf83f30c04fddd318d1b0bb75537e005845aab1d2036269db47e8b81eb5c0a9c7d5578dc000405c8df372dd19617ddfed421c8aa37bec330a7398cee369a2011d185f2e09267762990cca773538a5c1ad1accc2b16d851c6a0a6044bb8bf2685d29674c04
  | 4 => 0xdb002ba0ea07d7489289c250446335cc04789f8eac1828c668d2d4c5b1f298fa38e597c1d3bdbae58416dee29e39ec39697d9aa4e58af6ba27106e6ed967bc77d9d76aab4d7a5c0398db9c6b6960187488e0a202e7f0e60e37c934494324bcf6d62c45ce61c697f8c7a6bc3c8256650dbc67c66
  | 5 => 0x3e2856c4cae425e03176c9d12cf0204ff51b1cb07f61f3cf34391545b29254c9a0f0ae01b36cbc451dfdfc7accd0c84b6e68e8e9b4a71fa3a39a2830149615733a2cc5b771beb98fef0993cae45368918ca44205f0d74ff5603c2e0eeb68d47033016140e86114d311e7625cecfb4e16f8bcf74
  | 6 => 0x439c65aa4f3f732a55521a90728cdf8e49c6ae65d53b608acbcd133595b5a42b0b55a5cc052e626c1d01866a42ea7ba200513330781096cc8e9c41045fa46a6fc760c9fc430c84574782a733342ebd1fd79e198d50787c86c311909f17565a84a0b8f3a108534d239a16d982313f415808ca012
  | 7 => 0x46a82f13b460b57ad866fd5ca311e976ec5f18e81229c00da70215b225a512678a6877b95d487ca52a966c098265958e13fec03a4eee908d0d70d594dc7bca53e95a829ee1e8eef612c23be96f0b2f1df9d6741fce0d347368cf0662e89064cf17f1a30171bc6894c78cda103eec093e8927059
  | 8 => 0x886221479eaed6bf4f52616516a932c14bb89b9dec83d2c90cedcc3830f6da70f31d6a6facf0a9159f1c2d46bd32e1c8a6cbbb5aa9ce703d1a4d79f3cbb4c4fdd0f1f9892fd8143d1e8e822f2fdbd9878f22820171209e947dc60caded8205bbb79c261c5945bca34b5ca6fea02999988046961
  | 9 => 0x39839b07751b0a576c7ffc4440b626c0609a900c42598d11666274de81c7a7dd018964fd074f9d7ef4628501c3f5cbfcca4c188f51e79eb5b034aaf51eafbabe5b6995d6bbe6686babad5dffea1c7b26fb591bc4d76934b3e086f2431cc396fa33115ab6cf642b3bcbfe19ce2a338eb6766e672
  | 10 => 0xeb0e47ee623bff6c12927a5d24b8fbf69191a35c34874e6cea0d69bf64f796ccaf2382e1d4815510a5424fe84da78141710b06012ccfc02544f00365a2e8b7de4d866532759023f1c5d8cf318dad61f94dd014d9ecb6b9c06d1b660a6d37c67eb75c616dd695795ab6d84c06ecc5ea1b1adb1fd
  | 11 => 0x5ae413b7c663b02b558df9e6d1bf7c954237a87f09eca7e524d636d0bcfac15737caf8c87c8e67e16090584a554a4bc4dd3c80a4ecc9c7ff05a7e5b65c0953521e093a4af5368db11c6a6c049c4ecff10b7b7addbf178a4b3af8f3cef9aedd3d7b2da7fd914832d4efec33a141cf3cb9b595f7f
  | 12 => 0x12bd7737844b0d5fb5bdb4ca4aef937e34e5b99208e658bd4c2203c615ac8e4a6af95a82e742084e6cf76b9b489c3deecbf155f78fd55cd7d289060e18c1319ee441388f7ff5f95c9b02954e1daa6192ec2f112e8c8bd3abf7b4af0d429e04dfd3bc0ee128d8ebb631e60a4b2c874c93bffeadf
  | 13 => 0x6d669a70511f997a7417cdb196db40cc009445a0256e29154fb7b60b3861ffaa7d6a61067567222f4d8cc8ae9f4a654c12b901cc1a65789c764163e1ec3715b7b462b368888b8ed04c5f862939242e4e2176bdeab0c82a023e9e988d1b06417ca745547f136edd3101d28d46821ee68cd3a1016
  | 14 => 0x684cf57a687336b952e56c6c33dcefc88139a47aab7021bdf4f18e8dceaab5b8288067f60dc0be48b52c31e97a53e574eef0d47f830d3b8a16489c227ec61627f0731231d51dfccb145c002a5e49110ea51c19c877d9697cfcca346a87fa32301ee93751905e4c1a8929ff0d92246001f55ac5d
  | 15 => 0x7e261a2d4062a6bdbb6060d7d9804ac09720c1dad05d9b8f65c52d254972fa94c59b356b052a086d64f9e2255d7c2e447a056aaf3b5dd033bbc9c53104d6613dbcb2c0d410cea2d330f07b142e54fde49fabf8dcb79db1ef379dfd79570e37eae53473f1433e1f3e637f062413966aff3da784e
  | _ => 0

private def denseT0B34 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb021ef7188a935f33e8b8ea3f2aff8e57f5af6ca954729fd78e4ad667616ec2a18cb4ff6d189653dc86aad1c32b84d7119b8fea0764a1f3ba63a7922b446fab242dd51deeb11e2dc92f388cb9ecb905e9ca9c9859625a591c12de6ebc31eaec837d838b7e3a1a7e84681f9af1a982ba8d30c9d3
  | 1 => 0x2a4de2c36f9a4043b13312400082987eaaee4dad42ebbbe9a4f5e552348aeb1b80184364a2d6156300bfbf7ba50a2056b92c48a69230db7c200a76322a5540c22047dfddec3255dfa97be9791789f1a1d12c4d995aa04ac0c3224beb11a73c1deed6ae1ace76b175c337519ed992c71e3eb4cab
  | 2 => 0x912148b6a19918c97f1883b98c7cb1b1d2a2704b4a891e6dc6c9e19d7cde1bb23b461eaf80978ef567fc9eb45cfbeba37d72260812a6b00b71bc6e2a0af314079949de07ce8919abb54309defbc5b469d4d1ed361185de74b6582f507783feef08271adab905dd714012d6bb04fd27ffe9f37b
  | 3 => 0x358d634ddfba30997b60d8de2a43a448b739de011b96060b9ea6443b6c9bd0d59ea7c99cf47f5efbaa408428c5793310556859daed40422b31d244331fa80870344f43d2a29a200b650d3d98390b9fd66161650fbb0dc7ad87e5cfc0af52ac3f62edec3f0510edd37e7d82118c43b8fba619867
  | 4 => 0x7541c5bab631f7921234c25d7d760b792200525ddf816aebe6432c74509232102b481121de3ed395c8ecfb7f4b4682c111b854abb743f4364032258c4b0e234ea073b50e85a1fa2e516a987aee8662c04d741bc5c2696dee9132fe1ecabbdf20da94daab9f4986adabf17abf235b824012eedd5
  | 5 => 0xba8270c5a46ffbbf762ce23270bd974ed91fab258558e6aae1ee456f4ad831e7ca63b36400b30ba829960e92d9d9750fca027cd8d1766f8ee43de5ce661b7d144fe375716f73866f111c38a919387cddafb2f5b5dc969c0e205e614732bb2421d6149f3403a71f8fd014a551146874a01a5774f
  | 6 => 0x3e0a1eb49e6b66f258d715fb55433ff94b267f6c298dcd9e688e245047ea12aff48177663beb241ce1397d1e97356ebe015e7319d419ede0e6bf1f86e1078a0810fa2b544389514a4022580ccc197e1c7398f73e52ed9f62719d832c6f02f260467ce99cfad3d3d19d9104c541f68586bd54d44
  | 7 => 0x96b6e5b3df00c6326468f35776a1e8e3df7388e88f9b68d28f359e8921f4bd12c612b7e0b11a1a31b155b6caa95a6b2db4349a931a87bfc1b844aa3deeec24ff45a5e86853ab07b2435f2d4ec3bb3ac937290896397a1e84ec29f29a7b0abddbac4d7088d87fcfea1d4d2e7cac7dbf2b004405
  | 8 => 0x25b34086105450303045104a50064c96f17dd366060ec3483076ab99f15604f7b2f4af80219f9ebbfc92e6c0242639f00e5e1b5107f86f404c947469eb42eeedae107b32caa36da6d7b127cd14f19dfc0304538e5671b0a6337252160ea6bcc5ddd24f441ce0f58fa3d3502a300b4a633adf16b
  | 9 => 0x7d29ea0b24bef145add77a528223a7be1a86f969c6d3bc544a3fea91ddfa92e03102108032281392636e8336d05f89b112b176102937cc3d6d3356d0e39cd59d59ad6933fc3381317da47e4eb743da425b61b909f58d70a9681c9b2f2cbf19eafe8d925a9c90e3160f9b4289b10db98dfaa7c27
  | 10 => 0x2a3ac8b6cfdfcef563ec1f9e4e15720e2be72a9adcab1adb3b80f9294e172127b90b23264c3d8a12849ef661c553d47c7625c648eeef1ac716cfef06dc6ea82f97464c7f7281f32c5abcbc433235b600d2f74d9aeca324173f7d53de865fa200f6c6c22c4afe71f823520244ba684ef79314a20
  | 11 => 0x4c36da74438f63ffc1eef7a57dac18a8e0e6944dcb6aa162211a96fdb4d63c20f5ae560f22611970e287dfeb122d5c96b583cfbb7655e74af2aadc36fb727f6154280ef4d66f336c86836a3a7a7c41336c4baba6a43382abc0ead966110edfe864310e22c36af0608bba9dd0138dd8f1b2b5569
  | 12 => 0xf587ba5e9a5b9ddabfc8b7913c4ff356335d39a4aea032e7fd096b1dfb76d2fffa6e156d1715e205fb17c01f3f24f93af090013d822a4989c3ca88ea048dffd511e5b4fbb079de1d69c00688ee28284886559ac8fbe8b2384ffeed32b6cc7aae81665b2235d527510733442479d9f36bfb069ec
  | 13 => 0x669a779e5c2b1877f7094263a3e1f178af0a72c27a044d85077bef0ff797db19546f29da27d611ce7e691c499b93953d8d7a315f11c6295a954ca81af3d7ed99b2dec234837d20f961cc760fb65e4eff78039924b9f8b63aec5d475488f0bf1f41a864d58544d8cc725c680e895f0b6009d5df0
  | 14 => 0x4ea0df3266c252c519e744cbdd2335913c41bf4dcb67ac8903e846a156ddb96618a3088e10a07a8df0cf5f87a0d81013a59651637736aeca01e77249ba23c97dea5cddc0b8f24f51013a1f34a5668fc54ad08493938d64a53d88c6cb733054df667e5cefb18d551f432c70e934709cd56f0905b
  | 15 => 0xfe9b2abcc359dc0cac362d1905a07831428e2309053d0388b2b883262184dd60ed625ea1593c4061df30017d16bd4665398eb77c876ce20e118abd81209b892997cad8841677388e04e9f6e3275e7fab6a07e4b5f907035779794683db460cc6d39b71dd253757adc98e4f068cfa6e18d5bc696
  | _ => 0

private def denseT0B35 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x79a099872bf2ac69b19d9e9759e7b9f812f289f47e7874d683126536ff0e0793a2c9afd7775ff309498f40ab5c027e2cb415881596d9a78c44eeaca7e3a265df170396843ed18aa2029002b634a296b1c1f9d64dc0f66ee3d362543caa6226240b9894a591de8f5991e373aca8b687f5667b530
  | 1 => 0x1e1b43ee1a5fa547a1306183f728e64af596ee6ddc165d8591841c3b9be650d7d1c95d10c2a3fd582aefa01aced64bb8e1b181cfe4dda86958c73d77f2c5750ef0659a8a681d27e01ed2bb7aafb95da034256fa188dbb6f8da2150c8b00c958a81c0d0fd8936270d32cb3cf0e5b8a51bf4bc1d5
  | 2 => 0x12ac90e0f5c8bf495e31d08e19b4f8c90c7d683a096b2d48fc768805f1424f14cb21a7961adce2f2bc1ea686221cba1ecc31d46990d3244589bfe4be46964ef38f6d6ab09bfb0cadbec013329fd10a0efeaec3d698e3eaf414b89a65e4e5566897124067992a777fb5b3f627f1afc08553e5046
  | 3 => 0xaec1d42b3b1c2792925f41e0b9d1bcf9ef6643d2f22a3c9a09748d907be837416520ac3db3c556c04b88e85fbaf207ead060cd86f0d5c3ca0812a3b27751864b2dc1bc9fae1e2694f5c3d4c52b35c8a858ce00fb0180f17be31192673590f47a4bea47b69ad0c509c1028d4c5dcb00a2254cb82
  | 4 => 0xb54ed4abc160089aab75b98594e6636f50f0160b82fee592c207b1019270011a18e631064b827df81eea70dab0d730ad769f3a859f458445ae9c28f2664ce1e6e28026e7eb26fcf2c336878eab0467855fc81921b7b8ed67ebbd38f546d20c713299ce14c659bf2f3235ac1087d888b747a215e
  | 5 => 0x2c5adc643b5f721509b2bb88eab4f5d6dc97430d25060d87436ceb9d8c2b88f99b519e2df8ac9d690a4186e659aa7eefcc596d2391de8bbc3f672d240f963e4446f23ffb8d452422b8a74e90bfcaf53ee9a7c0781a826abee671324223488941fc1810b8eacecd4d88d07699588b76a701175d6
  | 6 => 0xc60bb8561c68bba540af3637e372b275ed846636553ecbe00e2e7d78bc6ab17d97687b11bdf161af3ea52f6057c20337a029a9024d39eff032f930111986feafbc4ea4de28595f1db0e644a875b5305de3d643c2d32b7aafa6da366758c419d499504d079e40dadbb57a9cae06130c877cf574d
  | 7 => 0x5fdda42125fcb4b1fdd79352c84dd74a13c2f1e781e9431500639f639ecba7babbf5a883bc006a4d9286f00208cb4705a5623d59668f449d7fba2f1d29595b94a65399c34c720298263b2db51a1a895df547ebef597787394d8dbbc4cce11dd2bc616dbe050d7416c9ca54dc323a73d32b89440
  | 8 => 0x52d7ed2d2066696e96e79f6678bc34778ce1f49e7028228c33096f60b8125df64e7734ee3ae11cc95afc998de7b803f0f53e707f5c9aae0bccb6cd9f425e8c2705fd8798f045507a93f173373a04dd069d925b6cbaece4d64696e5c43aac0b605b4f00e0af3e815910d777ccf79459bfa35abfe
  | 9 => 0x742ae1e14cd2c719e88eee1919e620df6e2481d796559d0db664ace3b9af39a5ee8e2c6c3a7c740c4a0f967fce3dc9c321f12c2ace4383e79cbb7d4ae5ba65d2fc574a8ab3d2b666eb8f090b8abe490fcfd4cc5880eb5bfff5050ed41d22f699d79b77a3629bd9486fa473707dd1df665e5f63b
  | 10 => 0xfeeef1c952d00889d61e5985c669018c19a636d0f4211d2763df43a1884f49e80f3b348511362452f6994a9c846b870a5a5efe8ef667375b4e8496c51adae46a25ff6c9ada5b3eb155b4b91712c76586457d2c31868cc8ce51dd86d25ed50155dea2aded7085d1f6d5b3ed1e8e2d2bed251d4ee
  | 11 => 0xef020791eb88489137efa260b5764826d03615ef75113a327965cdb6b7e766ce4ae77f50fa76682a2085a9c55253e58816c430b0985284124678f1accb15a69369b9572beb618350a80b19b429eb9d5a4bfb0742a27df218796c4efcbd50b6c0cd124ecac96a6f661e9a029f04fea8641a55330
  | 12 => 0xf294504c143a7575342524d7d334176376aa30a61d3d2ba23104b99f6262e5644588c69b352aaf53cababa24ae0d103f8dcf4df7ecd937ec564c17badcb3068eb47704bb91e8307a6d8922c561d12bc047fb624bd02a9caa595920a9bd9acbdabbadc713db2a4986a8bb8c75ba7e9c577215c4b
  | 13 => 0x9ea2b9fea6fb9791c4958720e7bad92acf5a3cd87292aa9de7e14cb51b4b299a8ffac683b987d872394fd487652f0629a27cc02324c90460c69bdaaafa525a19e2836f3261ae22329045070e2ef007bff9f3dae5d9657f55acc2901ff7f584c936c579fe662b524a0a9b9dfc62657acfc22b590
  | 14 => 0xfa30a9b271b2b0574f5276298d12f9350ca210e46659f90ad2edc5a66e7261a82e1e18a2785e769e48fa91a472e1ab1afe7ddc6fba3998d92590714ed5dc61e890282320dd539dfdddd36fe8b18fe0f2423293fd4dcfa280fbf5a5eb2e143b70e1e5a16d2f41f3e05ea153343bcac1984add3a9
  | 15 => 0xc7f282d9df1de9009b4b10495744ea3176647cdc094b66772037305b1ffc24993c70cabcb1dc8e9134d005d3502ad5084443926a251e4ddb83701beb77a2871a09d4807d9f3b4498e85561cde1df2e5e4158fb984f058e3d4fa6289d8973435b5fd5872249b5b28116a70bc7af5947f499434b3
  | _ => 0

private def denseT0B36 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xf7457b1bf530aa8d075af79c1dbebb7601c2173732186be9441dd609edc3ea1c1e863d2929ad084603597b787ff9f47c3fd7e11caefac2e6a2e871db174c4970d3f91424ec2401e22cb16cce46aa276cf29106fd8fe7b523175c7d2fe892c7b9eb5d78e7b0ac26bf60d200ac64f602377ff67d7
  | 1 => 0x86472103603958f6860b661615781675a7ebc82bbe5c7d7c6b682a475a23456ed8cb0236642803e56a0d7fe4cf5f0454f14367dcaffe5445b50de530ef06301a765d2dfe8a16460730e371da700a9d6b5f55f86ce9ca3bae823ce35e138ecfa0cfe24ccb1d86ead3cb7e3ffdf9e6dcfc10b1dfd
  | 2 => 0x61d44936701e277c9b1f5440a5308aeecca4dde626b84d934b23feb0e47aa7074eed75597fae83d117b6fa0649770cf141ab7de795d4b298a3e3ff38f10959790df4a8aec8866c802c0c8acf414c281873279e54abde711315e1449deba7ee3b3438f7cccf963dcc3987cfda4d9b5d188cc29c0
  | 3 => 0x69e25c3ff17885b58050b50009f2588a4fece026057dc95c74fd93e7879cc4137cdd6f99eccad465d9cdd26ec671728b136b985b9fecb2a681429c6e3a32581500a5c5fbef2c868bbdd6ba75f3371410814514fd019f7c354837591baac4426ff46e4048ccb70a0abc7bc41d87787d6e3edf5c0
  | 4 => 0x45d1f9f9a6aeb311492f3d986dba740deb0d62527c7c7fde66c85fc0351ed5eaabed77aca613dabb9cfc5306d30c231df364542ba9b775073ae0e63ce567ccc1318f95e8cf2a547cb0cd9c5e73104e4027f74a4f6b6c05b8845e40385469d701552e555f05ef6109454523287049df8c76bd82e
  | 5 => 0x37e7ef8247678121d8615fc89c1d5284e656fbb1448db50598525da16c264eae62b48f5a54df717deacc810583685893cbcd14ea652da7a79dd3b5d495e0f86e81130adde720c8bb3bb93edb3d2f0c323a07b6a5337382110fa92d35b052e6cd62fb01055a9c194c5ec21fff56188109a1ad945
  | 6 => 0x24985fcb8bce0446da5a392c9c941b031a23dae790273888d51fa92d22aa097d00452092d9d93770b6a05ca66f85cfcd126a0ae4ccadd8871d23d6144e5f387292753c30577b3e3cb644ad3ed4e93ff89e49545a0edbb42a3afa67fb210baebf10a2afa295883ab719db69745aa93ca3f47606
  | 7 => 0x22213bc913da552950b7a2763aa40d30ffb42cfce9c64edb59e426a25b35abffb6c58ecb6b613518179fc11bc976792377f9b4ba4d94cfb2e8d6cee644fcc2ac9b7931dd81ab711b530b91740d2af49280dec688b43c9dc691bf7c6b52ada22f5c3aaba08da7eb4c9a7c047a49a19cfc50d44c6
  | 8 => 0x59032ae1419c92b4e301d8ecc15add31973486565de7257177965a8b9728279addf6aea926a7ac2fa7a4107800fc503090fbf1ae795031497fd46a49d21fab557a2fafa4c0ee05d1df781752e518eee5831b66bdb5649be86ab3251881086e677965c233d28f6c13dcb21feee56a412b7d41f7a
  | 9 => 0x460836678b6c7006d39b441109576d805e937fe0488118c804d35ed468324d0e25ee12f529e15022dddda70a3b603268f16ed8f79429feffe155bafb289676e1b07d7e866c00ff265a26f215631d12ea39c81e98d7007ff073f77a78afb2c189b79fad6800a9c798877b9f0f0a98182c30611a1
  | 10 => 0xd32b03fd99c1174300873ae7cc5c4881a30b44e93681087d5dfb1a758605a6ab21bbd3f22d5e1ee981091cf4a8698b38c60cdf5f249b473c907f8943e2b0df76cabe254acfba093c603b5a4ddb6a64f040c7ad0a10a3bf1e21e11f15dfba4d37dd5eb1117a95776f35920714d7ddd685eaa612b
  | 11 => 0x6ab46fd9f9d6d86d6aa8cd0cf430c095770e6d8f6b6258a322e70d2f9c895c86cb5692fea8eb6abe6d34bf03a00612f9a19c826de5c6f6c2157f89fa09f0ffd5ba0f5d83a4f98936c3dd7075db8c0bef9e1bf8a3bbab894492131bce3bdd47cb27cb836fb44ee350a2c558603d171c2f8d3ba80
  | 12 => 0x266b00472353fd4d633e46e541f8c8fb757b03e4f8fd77d44fe4d0433d2bf0afb05ef2d00db3a5122c39fa36156323ed96bdfa5e80fe2cb71af0b431c2b9b8298d44ab785bc3d2766bf727409363073806c5b7d45fcafefa0f4676fbb5c86dd616a64deb7584c9bf894d05684efb8f735a1c79b
  | 13 => 0x8282a868903d46307ac709b35fe673b7c75218a801735e1864295c55fc184d21b37f593bdb27bc8745f499b08943bd6ba42875e5f68fa5ca46c80bb9e3e3e3a064a05b873fab9d7b1d2107cd4696ca75ca0c4101e688b22887443cafc95b3474db15eb12ce4087c3a56ce7b839aee1216a6f169
  | 14 => 0xdaaef97ee8af1e6d858051977d709292903d30b631e79d4aacb2709f4219a8d14ce091d54f75f4f75b755fe4dc266e13371ffb3868a65f5eafcedf3d38a6f677d32bbcd31a28b424753d7f9ef960ce3f141e3a40a62818db0d6c6b7616aa3f1546576eabc8f9d4009d1d26f8d77008d3251066e
  | 15 => 0x45f5a47975420c0b7c558264aaf31784792b6d6381c2b5e1330df8e87e877b5f9b3fcf55fb75972196b9a637e2b20bcb901bcdccea0a1042151136dbb6889e7c7f3e841320e90fcf5f422994c5bb7cb3202869c1730cf03449cecbde293a4997357808a8b38911db83466d8c23fcb54bbca9072
  | _ => 0

private def denseT0B37 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xfa1b037dd82fd182d84292b8e62da36cb6541ee905d348c2eb3da23a581a978a5ca44c7c56428f82b7061b8ef6e1785077baa96b20232e4644199e3d911b1deac084824bcb22f14ec472fd964ad95a898d0c9065174fe9cbfec28a1e14f7a687f8cfd34a9664189b4be8c3666ca3631e6a1a0a3
  | 1 => 0x8daabf8edcf56f1ad75b8ae8e43d6beee35c8b1ef6106f400bc6683e41547931c2b36421e7e0458a8456423c8c585a1371ef27953e09a578c7c24db085cd4a2b0c775c4feaed206b59ddc93c6b884743512399bfda005dbe5e88c56b15c09cf78647edda922c0f26bdf0f89e32e9cefec5320b8
  | 2 => 0x59795bf2ab126bb1cbc9c28857f37497e78f25c210dc27eb31f61a16889a1e9542fc6d2d5014b074bd556b95b2628f8272ef30209e5d7f11e48f6d011034d93f3e6432433aa73442cfa29c80c626afffe96b07a70047ddc3fe3f0c050f6212563e294ae32fa77c3a688be365914b6024f4fe934
  | 3 => 0xeaec28e0a2ebd1ac8470e439b8b0cebff2db830ebd932e22473ea4ebd196f49d8bfd7db62036a1bab4c23be6ed4bbd33ca80a67e4d4dba8524167a1f9130a1786e37b94f7ad00edcff34b8e4ebacb4af42d51322ad1a635711851f725c49153ff1bc8c8ccf65f819df856171bb03ce594a0f473
  | 4 => 0xbc22f4e56eeae329f62330009809e01d4dac57e6d88bf032997c0ae78d5cca7d021140e10e3bddf5a298e63715d0b295041b2130f0e894c8f05bc5f930d201c0fa042292edbdaa0c89ee803ef51ea039287ed1b083a59deb929a199ddde76d73f77a6286f1064b68e99238629c0cfd08cb8c842
  | 5 => 0x8bb1a5f689537f5a0a6beffafe3c3887c61edef4da027c8a024a8afc9226cbe039a79b6e37a1f49518596277f5bb87f00611883e4dd0fab4e7f5e611fd2babb19541fdefd21578c36d02135db4860f039d811fd2b2e1d4e077337d05b2afb360cdff7c2d358524667cb3dfdcb4bda01af32c594
  | 6 => 0xa7ce670098413f4095911b800e77605de1088171e6e643ea5663c129200d72d0de18e739b6d1b4de9869703bc54d9fcf682428514ccab369b01c3e01e064c7863ddb7b33a2f224f6b6645321df2c8e9834875445949e5698fcdbbcc439bd9aa0a88c6282303478a0e3bb8ca10ac0836cb8e6a95
  | 7 => 0x44b869dc3332e3e508606bbc79218ec74f1db20dd82d0b511793b75222ad89fa16181e416d0af22ca10e13d22e77f2596c9f07cbdf9259b69a153f52d2d9ea70397edded8c12837beac1bcf21f1d67bed45e4e2ff724a09c65807a07a921c0abf6045353301c5a23bff041f092b9481293035a2
  | 8 => 0xf73b048b0c52b8b88060fd3ecdea41b9f8d0d92554407e9bb126b6cac852b16440b7229b51ccf1c74d8a1d37ed072aadc2a7b85217049c3d639dfdf1c0a6dfc14f459ce7afead7b1a20f45324dec08e45b1105a9e3f9bf36ed68da93eaced348c4bcb25e0336819546f3cd8d30dc591c3d65915
  | 9 => 0xede905b67070f4e19e525229ba8b37b9a3c51cdbcad9d87cb10d9ad292f3f91232f68e8a58c86e0a789c0d5f8b880050e0258accabda5b2052496ef30869b7c3850a4c6903dab338204aa3091ed338a91b9b0e1aa3c468cda6413f0bae89da1ae3fa095078ec35ad9e062a1ebf719f3dae3b385
  | 10 => 0xdb1b338f8597fc26e16bd935cac303f1fd891d754e5bc083c6c67306f1f3c793469950c80ee865afe3e18cc9c87375fa1cf1b45c9cb087cd3c30af194aa1766d9fc4d6b740e7c3727006210617428d1765d9ac1077f80e554c0926eee57e8117c1b88c168d28b44b69f7df3cae45fd6af7ec76e
  | 11 => 0x468fbe6f45bc909a00f2f67ba1fc29b0346eebc1e10888c7f41b0591cf3819b833f70358e73f466d146553b7cdf5c64fe7c8cf81a5f7ab2b831bfc2a4818f16bd97b5d71cc2d416bb9836a3e00a9670787560b7705f79d970ad69defae497b166c961fd0c672a445eceb5eaa7b465ed6f83df50
  | 12 => 0x55fd64f565f68a56ac7dfe60293ae88d632c83fcd42cb807302042c5e35acaa59a3a2720298bbf15c64aaa5e39d7e69958af5fa794d6b50fb68470c1c5fca0c703bf6e7e2122e50fd840b7096268053d2455ae9d63ff4d8b733b745d40bbb810fed69ad12538a23a432915273ba2b2be0eb0403
  | 13 => 0xaa2a393e61a382d70e74f49c3ef368ae8407daf5f34a6110f5feda0ec6839e1ab823a10fb177431958d8e92bbc6dc1d86beb6ce993ca5ac104adcbbdb62e27731c0286558fad4c99efceba0d775755ba45a72c1c5dfbaf657dbcbce06284901520b2db66ef7c0fddf88003052e7ac0d08d1fa88
  | 14 => 0xf67a735236ba041c8a04d5a0aec70c66ff12ba06267a93dea62d527a15f8bb1fe573d9c634d472043d499fec582e7d78f9a729425e2e43fed063006447549cf2379f7578328641e76709a87695126fd5b2a4adc17d24583408804d39f1b14544b4e3c53cd56aa7a8a32cb3ce804163f0a8ce9f9
  | 15 => 0xea7c1e7687d65383cd54614fd61dcce84b920a3b6ef0889e879e4bd5a04dd320c9853a43c3953797f8531181793570f0a7ca74758c89404ca85da3bb9cc21c4c8d55a9a694cebc878f1121553dabbc06ec19e22f7890440270ca7b4742ba0ed987f81319ba4048d56ddaffe21930825a46a06f7
  | _ => 0

private def denseT0B38 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xa111dc5a81efa314304776f114135169394ced1ca289426658dbf74e75d7607aa15f5c2ba8147173b5ea42d8539b4aaceeced819b207089a0f205d9cb205224a78da34b316282614e3b0ba4184c67ca48d14a323cd83fa25972b2d08b2d0a081e5af4074efd6e6aeab649f4ac9926968c6a058a
  | 1 => 0x2afdc70cee4306adbbd894a86f19e5e942da8544661fa7c23b11b5874cbaf13844e7f39ed1200ee4c94c1e586ca044dd5cf7bd619a44febc4b6d92f262ffad61b9495ac5bcfcf6c3bfa11d4380d92560dd8a4922a99c269ce47bca91e4830a0f9b1285c7824cfb68f017369d0df398cc35ed2ed
  | 2 => 0xfd3d08f78ac971e718c8bcf75091a25a80048026c5a28e00f76b4a2bd1b9bb4f26bc307902efc5e4cecd9465239d9d23dc577b7ea2e1b20c5a8bbafc996706ac521e07d0822838a104685953bf71a0493e936d19850a5adb470a67a657fb595b187ecde725d87af81a0fdf0a328acf57534b1e5
  | 3 => 0x8c7043a70255d6f2146e6194e4967d20b2d11b48250a05d032d0cc6d4c910ea2bd59e6ecf9e917d40d73b1210d192e3aeba4f320a2623833bb6fffee850f013d1790f58180bef8871c2ad8def7e4c12cb6eb41e8c99acd71cea455ccda3aaf209068fddab1272ccb133916fc0525b7f231f3cce
  | 4 => 0xebed43e13e5c901c74258497cf4f9e57226d845b347be0af3d2a17df3b61d4d6b5390dddc81d16d6da3a5dee32688fb932fee99e03872b4272522013a0a78790bcc02d3f255671b8ce73d7cb711e1a4f5d484774d39d4a2f90b4ad7f4d7eb37cd78f9fc2477691319c767fea53e49a6b18f6f0c
  | 5 => 0x58f1c6bddace56914e4b1cbf3805de2071ea4e77218578d498a6e4ffb7f5e7cdcf31bab1e92c7541d913507bae4a47142a70175b3a67f16e1c63721b9da93b4e385a444ef72f6ee3aa143efddb72e7903a54e6ebbd63412ea6c87e9bc697ec095b054b3149a09af63e53ee491e035fa7376aeb9
  | 6 => 0x2069b57e874c1d9e3b7ad1d8a7183958bedadcda79e6ea9238884fe21d51c425b8d99e3fb8d551c879cb733fd578035253e4a6ab1399b8dbf524908e9a5a8dd8952b3bc69bf849006b153bdbb6c5e3fc92c016c28c6e4902737b0929435c42323d4f3ed332ba7925258be776efa92bd93fef556
  | 7 => 0xcdb43750e2af0609c617d42ae8c7c25e1c12b3186db4ac9ff1583335f615881554a92103062d74dea8169bede87d4be2e65bdd3bc7a48a55555d092057b71fe97887e180083caeb1d148db1c40a611e48202d781f12ce1ab4a7180345ec5f9d2a00a74a939a55ae2c0370487e24194ca1fc0c30
  | 8 => 0x7d586c7a1f307b57b9cbadc1e78a4c569e7f489523140a46eb0227ed81e3933ddf2159d007c5f2ba7976d814055501db70891c28f27d3844654e20941ce839b4eae5b61ee35691381cde6e33184d0b959d6bea97bca506ae82fbf965b6943e10790befaa86426fe50fbd5d5a916c7c7da2fbf65
  | 9 => 0x23e2609b5dcc91ec70c47d04a5f24de45888a390ab92fda710d6eccde9cb8abc131a6880099f0998d535e23ff6069931a8654a7843dbd3665d5886edaf915ef3caec084d5ecb0bb9317aad26c3d66c532769a53cdbccb8e67c61e8282c6e9f55ea8fcd2ef705fbd92a2c92178f63d4d0d96b022
  | 10 => 0x428770292608aca39f900ccfb09d42b102debaa8b24732da6c42aa7111221f520a7d9376e4a64584a6ed2e5a32fddd829b9f9a60eb7c634cd2fcfc1d946bfb651aecc1ba04a66d5f8553ca1260aa85b50365505ee230fcbf47ec6076bb497152c11886f5e50e88ef4089fbc085d400c80a4cafa
  | 11 => 0x8b098a4b2b3636448ded91648b038d38746bdc238cee8fee68660664b7df8495b21d8670f0c04f5577365bbb44ca5a71f00a25357bf2169363ed5d73f465963608046846f3c3d5e6df2adf4f2c7dff60b00110439ccf88ee758fe448c7f63c05c384c6e72f2a49636855fd837ecf1b39f74abd9
  | 12 => 0xecdc93c8ad92ae2b1aea2cd726c983b938bba74676c7e6851dfc8ac740a340da64005fdc06106ca34c2daaf1e73274efba56bb702aaf1c7e0e1720e4fa65b44489bb13917950a5c0a44f6aafd48b017c36527d7b30a3db825b39d0dfee8d7a54778d7e5fd3ea39ff3a2786a5d99fadde1ff3a8f
  | 13 => 0x5ac322ee268fceb28d371fb236b694f1558252bb93b74932bedf9b917602ec5660573c61509e6d4e61076fe472cb25ca74dd914258baf2c4f0a513819b4b17a9398fd7cdf0bb1f2f28ee009b0f50822970e01e4798f23e8959d24f6471f94f3fb5935d847a23c641ee44b690c803bc80bf26b3e
  | 14 => 0xac9e15de22c202dc75c55b2354358fd14e43f1c44316f07c8d646297e815ef0ef88c0724951c250869f8e947ac631fc4d4704fbe83422ce2f57d8bece589d47e3bb707235e71dde095d0449197fe79ba145d3c325ceea277b11764058c1638f1a75902269d6ba9c3ecaa7729825cad5e2d4a55f
  | 15 => 0xb1fd519567d3745652edd5b2a03a8c83ca19fdc2991a31b607a28c271d2c47109cef4976938667680f606f9529fd7ae28c4a3f2f7637932933d54393512757dd8360c2ce98ef42c64e63260482fad4b3899aede626b180d2284af2efc2bcce0fc140665d6c0f8695b34cd5b73b6e49a735537d1
  | _ => 0

private def denseT0B39 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1b5620edde238e162126a1e0b6eecd1c56ab4c5cbacf2efa2dab2eccee67825f6f2c92072377f5831632a94288ddfe72eeecdb181fc2a0cb8c8a96860fd20ce23d1c42f94044b2928234568922fd44667e4d62826a98857b233add838cac40bcbfe020438e47180723c500a2f06a013fa244650
  | 1 => 0x99e0174beaa2eb18c886f6992d2624b69710d1f8cfe80aa71fea172f5800fd820147652b287dfbab16b6e0bab69a47a9580c0af6606598777c50c96b1f04927c9f802c4227846cdd2a0b725b5bacb6283ee69e90e09d2243aecc6cc6f1e24bda2cb29452535ae0b432043096412f7cb5521a9b9
  | 2 => 0xb6e9cbb99b1f07f9131620cb789d62b069e498f7032140f8bbf13ca4fd32e283e8887a71fe5731438a462319c30f9c4080de07fc69ae7abcafe1610ac46798ce638ee73cee4086a6b56c5033fff30044306b9e118edc710ae7a769f8302e1d0218013cc1ae9e99189f2c90b9fd3e498ddf74efa
  | 3 => 0x1bcb6b956ce8a4bf7a2346e87b4942a8692edcf1e4196cfe71b408b3bf2107aaef9beb27f7b3974200dbce55da5326cac0e40228f9b99b06400bceabc7a60e7a6e743f38216110639aca7aec96590bb691ecd779235bc36dd8442cdd88d6f81b6bc2bda225da0af2ff4fa1f0a2dacb38151e234
  | 4 => 0x63dcfc82a835c7648c1d6723d1ba8ac0793de16c1a699a4984982f0688e270036aebfdb49c81dd00029df9e6fbaf017e585b68ec76ba3c2b4f9df1d2222a86d152d7758f1e913bdaadd7246a52f566bacd6d5146922f0ac6db8370e7977ed8efc1eeaaae2c94308ef2b29f57957427ea4f4a8b1
  | 5 => 0x9ce9f43decf182b72495fa9354c797152d9f9c7ba64d00fabde34ce32f861217d76b45876f1aec67a90734494c8c55b701975411620b917d867621ca48804da03b89483423e341ad0d64ad6f55cb0b5c0b8d78bb6945d40ea0d5b60b939b88bce31b3586312214f18de238c72342f11684ec1b1
  | 6 => 0x41fae83f880d1a3504225f5ad12e723355771578c70f5a745b1fcc6f0640c90921f668b554756a3bf774697592a941de883ef608d6f6997c108b4eeddb411d046acb806d76dc01882ce8ce3df8fd69683b6d80a74bab3cfac4ce67f870ac19e18f458c880075008e8f83ec00396d984639994d2
  | 7 => 0x7fe9a17ae340fd797e649f7c281e06609c1f6204e7c998724600b8f82cd071e0f2b1132c4761193573dbf2b9e108e30932ea59c9aeb6774181a3d6fdc4429c1966e52b22dcabca096ade5ddd712b16c58fe202b9b6474a6aaf0e317d46128699a90f2686649cf9e75bcf012838cb29ad16d37f2
  | 8 => 0xed72147e01293d508fd6978c09a21fc0b9f10efeaba237451252752acf793100d7c861adc39d3aaa0dbb232e15a475c78ff70b3a02bb9f5285d86e86f65430b66358df800ebdf7f7b714bfd43e22b72b9eddd98087eaa72354f8a2e2176dd0b5d7b889bf206ac13b594620048bcc02ee92f3d5b
  | 9 => 0x20524cf2e082205f3629420881efc0c77aa613354b385c01fe2afb79d5f8d8c6aff505f7f913f9bdc7c29333fe60fee40f7b3844a4a858d32fbe5ee5c8fb8866bb2715490f1e4a0434b5e4675ad1f93056e45abc319de6d07a0eb4477e06f30654ccbdc860800cef9223e04f68b200d3a1df14c
  | 10 => 0x359a794b09bec051e9a48dd67c96fd290c18dc21e744827d105b14e6938bfc9fc92fd42d7c7c32f81b3378ff845c7e30bae9c3acfd4a4bfef383551f3b22ad4949c54bd3308c65e19db83d4deadc86c8604bbdb1b1f8e3e768f0adbc0955f328b08710b2141c1102fccdfc9d3764477f9fdcf4
  | 11 => 0xdf3c16df93bcb043b79198d5e1fde31e1fb861b91c5c31cbbd544616845c93a61624aecfda62b5ac27e43f9a92b67abbf8690d3d3519f553dd7c7dd7c629a88823a6181c5eaef3b445037cd0af8bbb24048efb468bfafdff1b8853c8d8de517316afc518c3c2bf4f50b865d4c502f5ae61e7be2
  | 12 => 0x7fb8806a66b5aa5045a0cd51a176b97349731a013d6214031b57859aca4de126a84f679b575a45583e3368b574ec23384b39094d8ed545da6a79361669c896c4cbb011547f0b9eb854aa33e0da16541c33c83e1b288388cae60f2cd442bdb15332eb8e139fbc197c225d879ecaa00d23e27c5d3
  | 13 => 0xbe77810d7c81693a13839f0428fe691a93a3879fbc4de326996e9c954277519a5ab0b951ce7c14b9eec3ff94545c20c562fe39d9aab35b06eb88cb00b3118f89b09ff7dabbff17e898ec0c51434df04bfb415487daa1d8f97430194a733e6db531888e872b4ca095a09605af678172d9a598195
  | 14 => 0x838608cfd9c3c4217c4800947fc8dfa9e095b7dbca965f0b723d62b62dd0d63f05e1b842c2f6acef0a173e5aafd39e62c95d509ab29c98047844746979b00bf354bf60f0bf8b48b3005b7c195e4578b6bbd557ea010a4e744904d05ce903c6343bfd927d01e80b68f2f6c5c41e5d5ee1de0bc50
  | 15 => 0xf2ec1bb4a921242b5585f70a71c42c6dcd4d8fa88eef217bc083736fcac5fa789afc0e939913973fafc770613aaac4caf69d9536752918a14f7742ce1026889373a0e48e6abf84b9d0f59bf06a64d8446780b802d7d809e530e69505f362707d8cdcafe9198676f8ebc9bf0cbf86db895298f78
  | _ => 0

private def denseT0B40 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xbb38679cfb3256078a903ff5cd160ac1c86d68da4018fdb0d795a3f14aed2cf19f9d0d0b509a478ef052457abd50d45145ef2f8ee140b8caa64a0477e0bfcfc00f70c54ae7a9504ff714b2243ba07e8d44707ae9987adbdc84889651e4c6c9bf72c978fe5e48c7e66f830fb1f34fc18311297f7
  | 1 => 0x97124653eccc5a387e1a927c4d3f0aeb3bb54f7494ae03f02de8a4cd83741a47ac9d9192e1832ae08acaf3805baa25803a89a75494f4482dff768587b05f929203bf3d2ad49dbfc14867433ed7652a4424b171e9a936c887e08b9b65ecaf8dd3e444d457dfd0b0ce95c343934f692a795b5dc71
  | 2 => 0x5ba072cec8e9c2134e4d603909c98ab97a1609c1961062441939e82754ca4b5c5b8960efdcc418ae74b2d4a132052f704f418de54fc081fa755b90e2f372d1e304aeb106a0171d527e6f75e504615a3cc818753c0c9ed1b9b61ac35d7a70f090667ce97321c4d683169f595674abdb541113d1c
  | 3 => 0x90ac9de95aa85c1cd8e0274ceeb94c0523eb80c046a175d30c8b3f7ea92ef45acbb11e8f00a9d06501949b8a03a8054e1b6d161948fb92bd714c80be5a1513db12114366750e45973135bf1ede3913d7ed96400e38013ded488cb05a51780115ee8ad47c014a6d4067d9b9d38d32fc442bb03dc
  | 4 => 0xf2daa9717b8b455043c277763b220f10431198bc0120102a24f01b8f5fb994dba27fc2bc935e9541fd043eb968425a80c55806a3c84862dea05a8a58aca660121057dfaf40e7c54aad4898f289a63b99d495e254019360bc4781db8808ac4f9e49a7945fa03dad7aea5f51d659a303cdafa0ea6
  | 5 => 0xffa164dc66a60eb0676558c27d819dba1e9c7623667ae9488c4d5fa93e53cd4178eb8565cafb3747a522e0898d4467e5e08675dae43f57f2ca2c9c3ca7bf0310c060ad3a41204136c6bac94d351983004170e4bbf38a74f56d62b1e4475c67061e9e433e310599749e208a627cffc21144f92c0
  | 6 => 0xeeb5b3c23df0bf9189c2211f9c31c887831f719ae0b2fa38738f9ca952b6f3957966b595b35c0963546a13ae3109facaf2ea14e85c1afa24ec36cb9362c49efc3e998bb6fcd46b014c5424df20aa584ae050d832b92a258174e199b88eda1b3dec06b13c7e0c74679007a33e99b3c8503f4392c
  | 7 => 0x3b63731fc64fd3a04da7d0e27c8eae52592af87f70a05166f0df2986bb34f3b395dba18552518fb0660cc8171e126abf23e9086d4c77e49fb5b6ee46a44874817705d7e4bfdce128a50bc7115be1138419a07b950eb55a1d222021f93a909207c0d6f3740b6b1c0f8ccc7ba9a03bb862bccd096
  | 8 => 0xad9609b7ae08d9e4192b48543c87395680170fa19a0be9cc138d1ca0365b6896c2669b19fb28e011e50a3744a340222b0b54e81b02d0c5e6c0db6a925658e38d1bc1b5e4fef7fcf3c16af57cc951beb3f759ee1f0f3b6caee5cfbaa58e45f971a644bd220e7a0aaaef0885b98189c9a703421ea
  | 9 => 0xeed0bd3d0d6fe49cf586a99ea39400fa30e39336ea1d5520170ace117e38d1e58502e8e00b0f5753bc293425393c7bd95c70d3376ebca6eef18a214151923877139f155480772b1c1e4995c22b5ccdfb4071a5845b61783783354652747fc0190f603c7890b1859c77e0e46a52f38caca5cd1d7
  | 10 => 0x5a9881ac2edf1e97eeb60bd6b1e55ee9793583bb0ac735614dae32f94b84bde8ccb3ec2ae91666261c7223040af6de5d9afe5247d8b3cd4a6868046f9572850950875ac06b8a922eb26769b70ee286f87536b984aeace55280ce03e0f6c7cd99c4588f0f10044f438e3f36c4e5f26761249862c
  | 11 => 0x4725aeb571bde679ac69cd3ea49a08710f993a806277311da13465a0ea1bdf16f5d30bb34a57353cb60de99d3449b0c62f4d420bab796e02e726c78a97585340dc083bd51c35391bf9fcf7d6eb0334f0d038e509f992398185ae32e4e1fc6f0cc58eb9e0cc1920da1266451b50232ff2580caf1
  | 12 => 0x84d9165d56aeed4d8e62bc925737cae9f3058d29910ab253c30eaed2e6001a949a1ead934c21643e6f7560baa0d9bc5eb5b464b9ab4766cfca8886ec442cf4a58b0eb5bf6eae0dfc36e82e6a184289a2b4fc1fc179abd479914e997e6c2a01ecd0209572359cf1375a64ce952dc315c3257897b
  | 13 => 0x97240a14cac619f973837b038823c84f7eacf0ac7fe12e96ef90ee9908f5d591054163c43b89fffb09db6dfe1da4842887f47f432fafa78571d57984efa228732f31f2e9fae90423db7e589e1c4763816277d1675e948a06939aaaa803efb02d147d0afffff0f23aa25407c8e7e65e0aa8a9a83
  | 14 => 0xdfc1bfda74bdaf7c523d6100f0fd561a9b142eb5a87bfd3185b4ea9b97f1739cc76892611b5218ed2191ab3dee77cd79e544834fc4dd8799705d799eb7859ba95b192ecf64e20e86639a80058f34534750635be5db50e2b672b1f413d07059f459f0e307a507296242681ca8ded4adceb212163
  | 15 => 0x795e7e0e0cfa3596abd519a632f924d45217f35183b240b8baf1a937eaedf5c785e32f2104e79f1f61cda83a9d8998977924938ea9fcc16acf532cf88a80eb67fecf8e6b8acb84a0fd84426440d7a47709ecbe1ee112496c767723245eb629c04b3be4e2fd688b72b26c67697732be027d71f9a
  | _ => 0

private def denseT0B41 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xf28d9051775f7bf0c14cedce506010c42e10c9fdb19b8a6382d08152b844a37c2c038cdc3d9f4adc559919991a2d31f9e003d78ce83347ff0ca014af616c9c6dff129b19668d5470e1029565e9c39c411e2c9e222ae61231344ef40c72a1adb77eb0f489d19ac80dc6cb64e9b54c98ce7484d3b
  | 1 => 0xcba7885005ddf835c9f4e1ce56cf1981b993030846fb0adc3bfc626ed5c1d1593230e36cbd4a86e0367b4c42c3d19eb784013e911ed480fbade4d565cf2a1684c51ed35c641b63b7997bb707081ab71e006ec765a8281a0bb6475ad6d69c6687bf43c054e75b8975384be2ebc75d3cf295e9f3b
  | 2 => 0xc7dfec59c5605995e6633bfaf570f78449acf69f8ad7b6119f54e5dde89d4651df3f3fb5e9785352bf2b75cb48c05178a141f392cc8764b3cbec1fdfe3f19f9bff9bb430778513be88bdf9bd5dd0a0f533e3b2c65a942e8704d7b664bfeea3694c34df97bfafa3689e61a52ccb66f3b21e550
  | 3 => 0x566a9f9b925442777b97739457baf0b317819670fdd8b59fbad3afffa1306ea0841f6bc2653f6cebf59626cf8c622980d269a1bf68e82ab5695a3189415736a0ffa78c1e49bbb86770f85991a1898bd514d97bfe2dc08fd5d2bafae9f20ca349dd8737c366f2dfee7f2bbe5b38bc501fe774c6
  | 4 => 0xe277d6060b16ff4e578cf062614a748663f0696f0056dbfdc9f4df5aa87600312891b9b2a8f509b86d6e2893159ea18b91de1abe32fe8d507a6c2f4740636009af5ecdcd8288c9447cb37b51497c5996cfa27131b93e58bcb6128d76baae31787a1d5f6dd8cb5a08699fa7940f699412ca3f3fd
  | 5 => 0x4e18cd23ea62a04d059fd8fd3920715f05b7a0eb6cfadac2ca1e0b7663e2e9894557493341c14fec2606aba85d2eca113715be8a64a40e5bda361e7dbe3f1bc5b46562016a0f5b4024c13b2d52bcca353664d257fa0d921883e62d26d913dc55aedc0086af916439e42df156733c76973228d1e
  | 6 => 0x935bb6e3b371f74318d3517a299c01de4c48336de808db9591b2f95076ac450ebe34c92241db08b0d18a7a988dbdc8fcf1042be06582bc1a2fb203064ceeb7302e4945dd5a9b50bd431b23901e1c48971ccd50f3260904809c46abd62909bbfec4d179e59454e71aab4117a493df0948064793
  | 7 => 0x441b569257966176ddebc81e6d93e79f18c75ac776a06daf647ffa981cec373c6a6293d4f6963a6061691b04c5aa1551aa2ec09906be2429783b13b89b838953b3189abb2f9d8d3140bd601ca24efe22222fa5868aa0c03953059759e27ea2b1694aa606dc86cd75acf60ca3df0b3d9bd226697
  | 8 => 0x7ac189a75e604aa4a1ccfbbc8112961ad60fc6136a5cda03d12d9edbedc3e5e5ed302e41013a2032ff132f5e261e292ea1503e361c60cbf4cfd936d74dcf08f54433c3a5d1226065f323ef6b7cc64878ff67fc32faf853a0adce9bbfc0e31e2c025e3468e987bcdf20280971626e6a66b4b86d1
  | 9 => 0x27235806cba2a884a41f14667ab4828c04e478dabbb31e88d8f10139d48dba8cbaf0fd2db5f50426796519473fa3348ab9814cb9784a29d122f833b913e1d30a21905d434a4bdd3af9bdc3e05633e3dc35cffacd4e4c004c8aafe477a2c4bef67ecab73b2dc61be250c5dad457381119c4dfc0
  | 10 => 0xe0e974e56277514358ea0d2e8381792667a040faa7d24c75e8d9209678060db7b956f298e1cc378e9f6f2ba71ec59d97ed690259554b271a402613a2deb6903cb81d13f5bd836c8925808deaee874e11f3f613eea94b0f8fa43b17d93be817f45bf9219c6e212ae191b8cf51f4db56350065b5a
  | 11 => 0xe5a1dfd9e02b2786752a4411a9a26d183d3cb8be1a3bb343e487ae37fe3a04503899a656868a165b41c5b7c4ba55bbb4c7910e99689d214c6d365f9c5b5611736469937b0b206e723b0547b8cc5c0e9f7686fba3d591a23539f335c69bd5455272517904791e9c2faebe25fb0765ac82f4012cb
  | 12 => 0x22671f77cdef36205e18ac1319c59eae4523454a1d292aea73d810bbc6deb08b08138b4fba73a89195a46a2c42e6f20b9629c56802ed49c27102cbe020f1d5903c2efc840f8a3733617c0c20a19c68316d225a95d51b5e189a82253aaa40278ab8974fd0b1a674c69a3b0cf1c6361627d0bde73
  | 13 => 0xb127e0df66cb5e00c4e7b073f9439d4b78e008a51d38da49cd110b58cdd385fd8b43d40b6c58f0a43efd653de1e6786ec764262c14d8319cb4f84713ac44d8f9bbfa5df39ead55ccb4c0039eaeb9cf8f8bb8f62062632d25d8ebac51e7c96abc9c35859cf3d2297a3f8722f642feb9f814bdd52
  | 14 => 0x217d8c0b900eee1277de4ba0e334dc25a7203773552d9792e5ffbf3eff2bca6d28a72c0d1eaca8649d2c045d33847014a91ccb372288c50343ec6e32a4bd1ce0f648a8561bac53185341b7e8dd2ae6566b72126cb89fd1e551bb75d257d506a7d8990be84d22deb7afc2d4c5c763d8a6a4070a3
  | 15 => 0x28b6ac5f989bfcd64bf78bc20bc28797b248ac364b5f51e79e639c83f387dfb371e92982a76915d98fe69d621e0a3f8010fdeeccca5ca0a5062c720aae346631098555ba4dd637112c08cdef8a0da0cc9b5218f2dee0a73132b0b84d6363e0c1ec9cba7348faaf1a130f1076521be9043ee0304
  | _ => 0

private def denseT0B42 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x585f94d9df308d5564ffa030966e816c38fa319b6b404628ef835f057e42836915213672df8d479fed93661bbe41eb7298080698992f54193869c5fe34569ad5e1a02fb696baec404a595a6ed66f3e6dd29177f4a07abe50e8468fd4340e9088355fc31305283c735bcad5bd06ba8a3224d1153
  | 1 => 0xc701d1d7765732c413aed0f4cba8cc25e28d266cf1c0694dddad4be1f38c39eee2ae7af24b49e3b5746fb34323c72ec03fda79dbd664c6c923866885c57689d0edd03c7274911f6e4f935e8376354435b4a1311e7862b645be98f562d550093e0c41950c561caca49dc6ffd08882dd0419de40e
  | 2 => 0xb3aac70bd7ce09c0d3647857534b62079505469474a050091e55bdc9e310fbadb06475cdc385bee7773e5e8583a20cb3cb72f483954c99ba9f7f6d356dea2422420a8b65480de9654c209c22c90745bba42dedb0e60e42307dbcfadff02055de989d4ae3637cfb994080f16c841e6b1eece5827
  | 3 => 0x9c9d7790f46d54e9de6c975d321746389b78df80f0dd3a3b88c159dc9de23bc8d79734f478adea7ecb6b62d5d45be1a009bcb03e39b7bb0b438db32edb0266d011db3553800c034f5f99adf6b8b1cc14c10269002fdd90e20f094e1d042a57058688b542edfc7dba4b1ef6092d29d60017c21f8
  | 4 => 0xcdf8bf5603afc3f3246085a04a3f97389fed4ab82e53a6b3b13bd97bd0eda14c1755d64e789b6925f3b92e648bba256f06086af534ec38fa6d477213f214a5395421ecaa8cac59f88bf3b1bee989d454de0b5031e9304995279ec304736add5ae44fe47203855d296ecfd7ed38e1d233767396f
  | 5 => 0x615baf8b7299ddbe511572f8a14c9f7408d86345bfada4d5aeaa7065c060fa7b5f5b708f71ccb3cced8523393ba9440ca5dc0d1c75904cfa5fae35685e445c6c1a64ed01dce523dce6a594eeae520b3f9f710b628f7c1b1b4ab4240dc63922a41dc52da713b8389460cdd33c072d57b60a259ae
  | 6 => 0x39bc5ec3eb39a8f2a58f0d9702ebdd7f4cc20104dfc522aeccba089d6102ad1df5741dd457213cf0136d03e59215751eeba304923f413b59262e3bf0462ce21882c5fa2cb9b6b08cc9841bffa0c8b73e3bf3862ed60c31bd54c115e91dd5f82707959740caa4ec066d29a7160b770d1d07f6d40
  | 7 => 0x7b1c8b7d7a839b458fd92a8846d61465f7861117791bccd9a1d3d7d6163722141b94e0921ee339cec3e85bbfa6ce79cd0edc6bc25a1357798b54a2e515c1cd2d95ed25235c184c5269a52c94a1f511032d7727bc04d946cfd9d10edc28cf554daa92f96963ff2828bdd9991adb33c075336ba0e
  | 8 => 0x617e24eb0a0e5d5531a81e98a50cd1d331316431e7a9d4ec7f785231ee8ca04580479898a3a466399184e1cb53fbc2d9586634cd168e0c83e4e815d7ba20bd88daf8e0ee9fd8d493092aea3ca2d420a1fa8f1f62c9bb3d218196b8a751de17b3e931a3a6e1d8914ec8cc0881c313be67303d4fd
  | 9 => 0x3bdeca05fdd9d44e68266563d14c113e9b363a7c72501dafe45f4f41c00562ab16133a5e922239414d8313faab6e067f3b8875895cf54cdf52189854a858accce8db727efa5576bc6758c042b2d3cd4febb7d056bae92bdacdcde3490010a261860a15026d8413d9255944eaea3946860676c15
  | 10 => 0x8f8c85fb123880fa4b115bed0fe07c0b67f81d0a0ae4f184be35e1338995b41afcbc12201f4289234f35987489ce11ad4c23fc759ec47312f452f1998423069f663453fb7ee8ea1de7e0f49ca28fa814568436a6ab7620fe236969e17afff22e77b3ea6bd8e990769764372d9c2238a4031350c
  | 11 => 0x9e2a3e6f8280c34898b5fcee56086ed52a506150c43d650711d921364dee6aee1fcb85d4c021a833765237d8c8a72f0f5454e4d32c3591e8370d5d0ea391c85cde9093daf8c2a66cc121f9eda47ae8da71c122c2ed23dfd0d9543d48d789699d275f8ba76f313e785467ea402adcafe7da0bee3
  | 12 => 0x38d0ecef2b97a4174513923422767f6327320cc293408598cf89ba8c33f23d853ce139abdc568a83d829b2f31dbe88e16d7b7c21101496f186fd306f1d2807b34156c9304cd787ea6eed328e90acd5e861301b6f4bb651bb9b60877a2e7861044e18eca5c506a8c0bfd2cc2fe1db76585a56633
  | 13 => 0x6c5b5d1aa12fdbc944fe375e1cad585fc4a87b8b401047ff953050b1207f0db0e0a8315b2ac4cf9ca5e7e872f92f7fda370ee9bc8f2268298fca2109f4cfcf396feea10d39dddef86d18b87d4c6d02a7a169553f222c4e76b88f66bc432dd001b0ffde9b4931bd7e50611b6b3380a8e711fa4b5
  | 14 => 0xd392681f36d12b915525ddf2d63ea00ba61c89735ea73dddf8212e67683696d83418af6facd876feab0521d2e6a936997953bd576f5be50eea9f1e8a7834c61b70d190dd83dd1229768f027b42b5b641a407637543af5306c48f1f4cfb5fcbccb44dae78f1da5d70afb744c32d85034791e041c
  | 15 => 0xf3f9cb340483fa9ab801f3f137bb81aa2fdfb22043b8e4bb95a091bac0ab847300e12779c3b52029fb9cac1ff67fa31937247654b9fe2b21888c3196de201eb625f4ef763611395f9e7142c644f5a11e387e538770c42a4bacaf08d583760ddde26095d3ea7c277f146ab296e7ad0467870e9b7
  | _ => 0

private def denseT0B43 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x7d198c171cd949b34fe389e5e287ff20d6576a9e60e3986efc9e008679619a887b2c385a0be3862d0e2bcffe145bbe54985361ec0b61cdd7fb94766ed56113e4524775ff7637fbd4d86c5d934f0c9f2594932f48acd248b96c88e81c3276dd7c89e69ba1620648852e395291105efae11016eb9
  | 1 => 0x9d79b3c038a78c8c9fa8dd47df6ef6bdf7581287eed0f531d6aa81e835921fa049f77fea1d36e67e830a2e0581b702fbdc1ba3cc302c4c0ec9732f34e2e905be500649a2ec26c3a4de99e719b761e18583f82a6ff7eabe64bc8c78e0c803f9a4543742802e80fc820542828a54398db00f68c4f
  | 2 => 0xfe8493042495ad8f6895270aca2d0779a267872848cbd52fb6095d947257bab241b73b0c0d409808151484679e13d52fba3d169b93efb682af9674a93b68bae54874cc04213b102605a6e478fa67f221c4d253fa27857263105dcdf453e2ed504a331c27c054dca5e4ec36fd4a66873995731c4
  | 3 => 0x184dcc0715f8b570f4ab1925eeb2481cbed9752b17d84db9f684b15a9d00cf0297ac06451e16f80cd9be093213c432e62518673d84977c233f36b37ef2105bad455ec189c4ce23dc48d22fa01bde7f9ef5fd594ce94448211ccf7f65973de8d104d060bed432f0862faffce6653fed3344d3b29
  | 4 => 0x9cfe0eaeec9f004629566f5711749c3ba650130e350f7ec72df890db0f645c6081e6cc09b4bba6cf29a9379716bcddf6f78abe754f9ea505bbaa413fdb22b4b5b9be4e7b2cd8c196bb72cdc9af118e6409bd8f18e5e470c05d461490301d0ff695ce6fe8bce4a00ae48a86b57c430e0b9213d84
  | 5 => 0xb3e0df36e0f7ecf15b2113233f011e002a1d73b2aec78d8a9d2b1f9f299f6ecb90494ff678e02bcb1125527d85f9e6bcb6a9bbdefd4ef5393c4c6e3733be26b8171c263117546e2b3c738906394dd31a27211b91df3992b81b13a4943364703a83a2eec97265d11200cc0691c5d04444ba16a37
  | 6 => 0x86325a275ae3106fe21939a6f6bc0beef92d5b85fa3aa14cf5f396cbcf3c0b8658b9b878a35cd8d5ed88e0ab30b34adaefc0608496db9237d752d8ca2a96ce6f4dbcbaadddb280cf7f5b1ef214f123a3627e03ec7c55f9cdbb7ee8fd8d09dda46e3347bed46b3fb658d5fed5972776ffda7b651
  | 7 => 0x1c750a1143b0b76cd8793bbc3a7ebd9312aa6e78da64d97c2691fd47422093f0f30e2459f1a0a3b0042ffb9b6ed6286c840b79ae91ab64ef617795f8b6fba3680441106238c15d6045ad885002f2019234a26efcb5cee47b4969ca20e262b678964619f9d096b196e32db366d9a074ace24fb60
  | 8 => 0xb0bff68e2384564a036bad978913434cdef9a6fa2819946ad0d84d60f2605ed7ad7dce8708690cf08defc042eba791ebf6e47c3e9355f4027bad04a87529f61ef224367911b7acd63429032d233266f66ab3165ec3d14c41ab3ca7529308f98b772f3e8ce990f35a30f12f188d34e67d008e21e
  | 9 => 0x3e33371777a961a3b792860450bde2ea1cf4197615cfe102985551d040ac86f6a31d01e0398854ded0dfaa466f57ce730e67485eb7a05d60a162382ba5ea5582a987de0528357c40c920ca24b1e7e058be4ed3f4bc2a784011f60ea998775cbacdfcb9fbdd4619218fc5b8a40f7eea78d6fb0e8
  | 10 => 0xc6963889ec12f7b35adef989df9c4429a17a5dc2b0585e6b2d84f15960e6750af5715b449feaa26f516c99101937e606b3a0b391a6f1bd8ae34047f80001eb9acb85a4001c7e7b416ba85d951984e70569199f6ccf991f51f6fecdc1b9c515f9a630b96bde69b5f08e3fcb592c873a59163d4e0
  | 11 => 0x432d7ba1eebecdb65cf10e54b91c33126e5ab28bb81d7dc98954dc75ef0b01f7fcd0bcc7ba81f6d26cd6859bc7f3ddd97b3317b8763c4d5667f27ea81d6d14b813fe4a20fab2213fe502511ef1c21cfd3708994a6c8e59a82d17b80954e16f13924ee43bbe8669d2dd5591cbd775fc8c342765d
  | 12 => 0xb77520e9d773707716ea3d34cbfd3b73411373cb3f298f7f7d31bcc9ad09aa89d50e9cc9e7f23d7ce8e34828da62aa1f2156dabaec12698c8833bf2c0e673acca03147a7cb3cb92fe9b3c2258d764d48a6d7b9be7f2e932661a2956c80528405b39e87a8961fb9984ccffa748061ca533159aeb
  | 13 => 0xc8346da45791f16af5d16c64d389ab7e4b42945c6dd506d89cf098881b57ea3a4d0fc0b35e6d2f07dda4a7a130a040ed78e7a5ec896ea8ed7c7e64a87c50006d09b8b527b5c8735d33fe1408e6acd1673223d317fd93344d673a072a1821ae945343563d8336519405d4463a68053c4d8b27a27
  | 14 => 0x4290f0dbd993d3db51c327c7cddf3a9802a5a72f210215445467d3b41df119d7c1ccbe4de61f74ee4176ac17bb83c9319f7547232350d5721e9f9fa63ed56984de65214b4c6c2ef7f8566711136f7fa84b575959aa3d14c614e69b1a4c5e52818e8f40b5cacfba08e2396a918ce5dfa0238c03d
  | 15 => 0x41ce68266c7caa4dce09b0b2db6d1c7d3ff69f968c490eb821bea8c1a2c38272fd7ea9f72ac0e6e190483653021b3195730be468bd626131946cd807faf6e580f51d95f4a1409a2075e52d05ecbfe7bba61ad1a6197767b449c99a30fbfb193503420eb59690fb088078bd29122642cb6f4f7a3
  | _ => 0

private def denseT0B44 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x35b7f2129b683c06af43cc6e7349e4ba98d887546d1db4c776ffd5555123a0789ff6edafcc306ab6ffba478a8db552d69763dcaab5c090a1f2232c472bd874e68962161d1a9a5bdf704dd7aba3bb20deae0ff75206054622c71ef9c1dfada1910fc7fd7daf8a7151da0e99e1a1c619757c5a4a5
  | 1 => 0x4dcb2e6075d23f4e1e2d76549a8565a3f6aebc16925d661b2fae4501753f5ecb6a7b1370c862be0213e7a9ad81aac97b8943e07d71828c1e96ae72b826c25aa27f0e718db7235bacc81c0613996cc063127ce86e67fac1c28231c8527501c2ab577d7217e43a8fdb1a185bb1c5f4d5b495da185
  | 2 => 0x4536f231a731b782076d22d9bbdff191b19499b5d66f7267455c4f7d41bb95574f0be12ee043626b3ae0b1bf34d0d264e79d225d4aba2be880b96a7af37ffad5c01a47873b12e0197eee238f19e71776b44d929582debe3c4e1666c527c330cc578b37f6de2036eec93affb0b02a408b9a25238
  | 3 => 0x76156ffb0a7d7094b96a4bd8c6e04185a8000bb0b4adb98d7af3ebeb476fa7f72d5033c5b7b94cc6728ba5dfc89663ab43872da9806c7824cd1f235dbc4e0868a17c5d5ff5de362027e089456dae47537cb621f7bf62a1f92a3897452bee0a465d40e78e6a89a46cbda784c640020fc0016d62d
  | 4 => 0x324aee7a2ad1e9d1fe8fc021741bf24837929edcda25f4345b7dc8e9e9907cc58171f24982cf858053c97009434cf707b9b8844adf656b73eb564c407b6cb833026b18bc8aac0bac138cdff55fdc55d12a64907eaa1c70e8c3ea84e8e0e4dbba2b9377342ad02153d74c36547ef35527b9a7d9
  | 5 => 0x16bfb5e2f93b73819c319cbee5741bfda8a53f3fcb15e3936dbe96391f2746b5e2e519ea9c77aeefa903c011ea1e0f4ded5f7ade3f64d5c02d4ec497675f60c4821b2377e75964489babe80e2a6f72d6ccc8644d8ae067664fb1698d3f4cde9433f646a34f202aa10e62bb37a1e10bb269a1e7d
  | 6 => 0x1c17d6d22523131f1a107bd5d419c7d34f8d182e9bbb92c59ac94c97eaf5e05f8c05ca213799fed99da413b9fa32b0c95bbddea6d6898503494a5493d7687c4966361b3f04a97a0895511fc36dd60f1edae0bcc95722c52a0deb5f760724fd7030a7b61e530bb8ba778b62f5dd53bf7701ff623
  | 7 => 0x1810240c9dfb15474f070c2231081e2e3ce830c379cf1e6ffaa4791fd1ac5aa19eca9b0b7a97ec1c12e20024563e59967f11f7bea7a8c4ebf32a2465069425fba8774c9d3a4ab0b78f66241a0499e38819d3e5af1f79d8628009858e566308be42cafe1ea273566118c9594af47a7ea671d9b94
  | 8 => 0xe53e34a00d17f077dd73ea4ceba94b06fcbed81adf3fcb2672f5a3aaf4a7a21b962e0d160db0084d53b5180c5fe24a78b40f19f13abce6476367d1772aa5450b3114b916115b5f824f1f6b691b1ab6fdf42c4ecf983da672b67d4eeb8380d4aa80e96946bbe94363d08d2995c7028b08aef40d
  | 9 => 0x58ab5f2301b797269c45489907e3d3190afad4365e3353d6c16515f493f54f3793a3172abd3153f5ca163163fed6083d8998f687bfbf76cd0990db7a37ed9decf444b71b930585fa86bcf9c78594a6759a63285eb00320383bf60188d3c57a3051a5aa2dc311dbc6dbbe00b1ced3bf1ae65281e
  | 10 => 0xbfe6b853a37cfa4719ca6dfc3cc2cc6e9552e60dd5f1fa1ec11501af805fb1f4218383709d4230bf20efb2af1eebdcfd617e02cb5cb8130bf32c38b8efe8b739282d92fd72804af1341a1db56bfda49dbd0476118666a08f11a801dd38730ac3e03cb2318d038973dfd0cbace8a37957c96b39b
  | 11 => 0x37868766550e097caa328d2ea8e9b3b330f6e63ce4cc525555c36f2802139edfe944612fbfde9fc0290e2a7bf7f6f5cba0376f826135cf858f1de6d9d1dbc382e00969cc41bef713633148360fe1c9c088349e20fd7392d43168cbbd0f4db0a2355ead1078fa79523ba0633dcbec5c7a1fcd759
  | 12 => 0xd73167450f056adf2d69ea441461645c2a606ee43e95458c8fde39683b20ee0ad2b8ad9ef44dbb5fc2f47794db644d9e1fe4b0764c5f97e22934952c289553eeb7d6c12f034a6125966e1fdc53759333ad1d2742e486a8809e20e9e42a658827d8aaf6b7432c04782eb26f4556e7a2e298a3e6c
  | 13 => 0x8a136d567c49639ea72e1158ef46944e299d7c8946ebab23d79475ac042b54fc04fed7fde6bd1a0b5a059dd678f7fb14a795cd63e710583ff81a075e54a621d5c1309f7d413015c8be42b17a13708c6c9ed5cd2ec0babb1f2d20d761dbfadaf37d58b3042b2dd2b17dbd29f9dca42414f32cb0
  | 14 => 0x1649d6040b63a1279b8e3662e9f7260c787a03ba5d7f62abdf38dfa49f8f53881d80c61935a8811704f18d196e13a2cc0c5f832eb8903e7081813dc146e35eb140b1fe091aabb76fbe900c4aefa68d22850a7446a067bd0d19ad92f5e9d8dd2cf3d016c0b05142c7381c7169ef62e3b41a7c4ec
  | 15 => 0xcc59df6be86f7118c958c243741c30611d1e2220e534464139a593ef62d3178652cce9fc2615161b103c726835b113e07df789f816efc5b750e1f96f5fa02425256e90066eb572234ff8544e22f7b73eafa2267a03359c620f111230479f8650047b92f0d4ff1872dd248b82020f1890af31728
  | _ => 0

private def denseT0B45 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x749240a2d4ea2b3aa94763282061066947dfc2615b95008ff26ea58255d3795995cbe3d4bd0dd794d931129d28b87ead65941ddcc9d0fc0b99a923d92f2f18384f07be73cd6370f29ca1e9cb2014b7a6c50fd05b6d740dcdeb29c85922eb6e13c671f55a4dd98f2f55ff74ff3371dec06f1b2af
  | 1 => 0xd695d613daf1a77602ffc9b367fc9eb8630a9641074f85124bc0e8aad66e457b49add9ede26ab16bb0d8b629d90d8c1c1935f1a948162335bb7d1e568e0514e51b2c61e64f436897d793ce219aedafe8b80ac4583f91c9bc17549280bd6bf1146c022e0bea8d5c2f6b68c405567b4fe47d782ab
  | 2 => 0x2e369243eb80cd5d79f1889806541d81db3c444a6edb03878c6fd9c40a3dcab59f4718640bb96a841c87579eee63c652447eef5378b25a94e6bf0625b5ae27c2dd55ab4333a7ac6f36a3c1a9a906e298eb05e194c6d74bd7c6cd5062b4aabd7e6a01bfa6c6574ababb478161ca3aefc7ac7780b
  | 3 => 0xa682bd7e5dac5e244dd5cff4459733b65dfce24f8a36bdb3e58f9253e24d59e1a61c268b0b358e8bfaa71cbc50b9a6d235fe1e0a81ea8afccc9718cbb9eefede0b25cc8a0fe93e97c9924cfbec830ed9e1d26452842ae07f6c80af384f7e8576a5b940c3c9229f3c4b2ab6f664436c67c7d90ac
  | 4 => 0x8780a1cfcdbd8ac2737cb69c183ea1298ac13c04a5a2b4b3f4eadfab8ecdc1409fa7bbf418098e336145a299b211d94ce50bf9da679efd16b957186caa89b5fea5fbc13e5fb717fb51f1376cf578250b1becda463998eba67fe80d564a445d7471ccdd67e671493e6ef3a144ce4fdda794868fa
  | 5 => 0xb4a7fcdde6fe86e9d8bbedc7bb9b1fce04843ce402efaff65c5a87b4460953fe26128a1ac9efda2ab1caf407ab9a0459442232f49854770f70f47daa83a5de82624f1a019012b6c7e87815050aea8f703143be03c120089dac0078bd3da29ce88d5de0f34c84c9a37ef93a333ab2034b1fca9d6
  | 6 => 0xf383d91a2b540eb80225876a95ed241befa51e50c147b6fe3a040f57278e5221aff0380c0190e5478bde8d19e5f6064fa0f429c5ca934c221da4eb76b761013e30941b21de44293b993793cdada82b1a7078af81ec6614021fc0dbef69e00ec1984c815b3aefb96dbfc81712153a4eac828716a
  | 7 => 0x50d4c3a0ddaea525b7d1fc530404051fa21450ed4a017435f4e629b39f333d98cf00b45cbbb4840677d7019eb78f52a1ec88242f59cc14d01d1fcbda54b1b0f4c1425428c5e25feb512788cc5b2142da820a579a7ecb64ba6b3d036d7b20974c4680f49d58f63817874e1972bdc5c9bd52353ec
  | 8 => 0x8a9fe4accdba89c8942e0102155308914136323275d637cc184bd36ab46317a8f3f3a8bd5028f8d28d8e1a7257c90a7c170a019e99f9046542ac3860c3331bb7e4816f5170ca3dfbb935ef5dc87d453d1d70da26316850892fa887a402b7f7daa7316776d6052e65f367113e99975cdcc26a3eb
  | 9 => 0xbc29734c5782cdf11ceac7c153e6f339f3cd83ded23810c9b7c08041eaab57b90dfc52f22a67eb0af7a14d37bc3b99107d6a0c7f08247cc2c9b1138ea5d2f2563965621ca1e9909c7183522aa28520ecb69859083178e19850d5182b3a0b6f5d5e0d0bb9d3ecfc4da7eaeeef3ef3e5898e65124
  | 10 => 0x8a86f316e5a57b93ddc7e78c24b2477f6eecd61845f40c0b0fd3b335df9b4ac0c37210b437e5b7c405aa69e74533639931efd9fdd1d12dfa29b4f28159040809a0db3aca77005a914c77cba82334f79e06990bea6f013e47d924a2f0273a7199c4cb023683b08dd8a083c2ef4c72c009ffd7d86
  | 11 => 0xdd426327d7f8be526ecccf40d4feb7319c020d9dc12b046aa40642139a118e9d684593b055bbadb1b6c497d7cf6bccec5698a5c5a9e1fb151e577c06af9d47b4a0b48712493e7ffb9051890f4eda206549474aba7eb614cf03d1016d655f9a43f2095e3dae94b90cf372fa747a434052954883d
  | 12 => 0xb7f6e27a14227c14bd274c48526340734fb3e2d1745f1209881f18acbee94e975c5958d836da6fcc909954b84c6856b1049f8f829cdb995559bf613bb27d712aa08b0c5b1b249ab60432c638257e209f580baf47fdc6487c7097ce5b2115157f753c9d84035b0a4f62f5785aa2507d60dfcf11c
  | 13 => 0x6352c74b8ae84266735bef53237b503fa2dfa0f4e8d33ddc94ac81ae4923448f796b3d396d81fe0d1ee73cc822febcdc5f70a4e39b267de31a1ac84a751e2a1819d4adbb94e322499c2075c7c21b1bb4a133de2fbb85d09d1f3296b895308d1d09381a499b1be39a7ff82972d859936a4402809
  | 14 => 0x33fb5b211893bd6cd17935296f12ec0d52bc6aee75e81d1536cd5a185630089a06abd89739032f9c6af2c54e8274a9831bfa4f266f9bb679d503f72236b1b85b3eb68cbb2105cc4bbbf165a783bc3e29d9140a758efac67aa4fccf16120df4728bf5bf8e207c1e49339b50b6be5175a59e5a16e
  | 15 => 0x2ace995ad2c60c814258d06b4f3a17b65d936dfdd699a972a8436678d010c4e331b62d7eb729457dd099c4fdba697ad0fe11f4e22d39b8184bb21e41ba9d6f277d206911dfd26ec46a0b5ce4d0fe70a3581f0dfc658ead4d078235d137122297c3795de738b9a312d2545ce01b9dc069d87da8a
  | _ => 0

private def denseT0B46 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x793a39b3f615cb1f6883c5110c9e5ee77dc67bbf5d37d7558c149703d0072616aca7cdedadc91e8c68e8a9c0d2835590e64f6dee8103d33cd88b3b092d2f99c61c73dce7e64241ffd3b9b4425e1a7b2d9fd5c78cbdd68254ec9b45056efd4890b5843d1249f617cb7b28be94be9db28bd417a84
  | 1 => 0xa6267965d335dc871a4ea457540878b1438fc7807e42bdf05ddf90dafa8c2f54d06d5dbd57fbaae71a96183969597d4066af8d31c91df6c8ffc49563d0206395a9e3421d2f9542cb0c0a07726f2569df9e57922a1ca91d551f7db3c8d8aad08b8e1439f71fd4d98a8e7595fd5c3d70286cf7d3e
  | 2 => 0xc20fd1c73726e1b16bedaf8094be6da393ecaa76ef829e226c8532512ee6ee60915e7b7625ac30a7d8b27d16a325dd130bdea0dc55fbc0921e9007bf8021cf9b0248868bc0d1cd94c79db86e0971bf1db4a2a8ebd073dde10168fee11e46aa6bd9d1b55429b209c31231ff15eef3a371d07cd38
  | 3 => 0x8f7c30b49d9e6d45fa8d20dd87c0d0d637dc14833f48f4fd543773e54aeb90471ac80ecae67a972d8f6d1b525a2309b8a8a59734a209d6c96ba22e72b620fa2a0113510e9c66d5d14cf3f60b1acae469b26805b7b461c0e298713095abd1eb75f7be3ec82bce49db427ac601de9cf1705cfaf5
  | 4 => 0xde64a6a8275e6488d54aecd6530ad963d34d088f873fc419a638badbc840556a8f1f1e9d644b55ef5542f021a3853e52ffcbc2a20e9977c6bec03136e5545ad9169a697f4655ffcbdf1819efbe07ce3cef5b2a2a7a7595f453aab0910da4ee315aa1fc9c8c785138648c049bc448abb991fd41c
  | 5 => 0xbc43e0df7f56094bd08c77db3511bdd739c751123fec2975e7574243e12973a8c9976293e0b2e1cd07d6c7b11f895a05cb34bd9a2676657694c11f112c46da28905e3db5a1c59734974598715fc4c864f1d960cbb2afb7d89f40c8fcd38eb2aa9949b5e97e04e97f7766d1e4437258fb5b7f380
  | 6 => 0xd4e8ea6d8bc5b47dc8d95af1a441accf1807a6943e5d16aa18a1dfe29addb9c54e5d4621d86cb5391e4e1f3bd022d99d36df1ace7f75574ce681adb0db03cc1ec62f57a6a1f1db900159ef7e59c26cdb27a504d9ef3d95503271752a396c88a6ab8cda704fc488e16fb77dcbf71cbb714f1a1e
  | 7 => 0xd62e83581d13b9a78c0b8dee17b45d6aecd6d771f1f46dfefca7c8077e31caced4caaf287f9b3912efa62e242f5349dfb86cff172cb1ce527b4a757e0c83720bfc6f841dcfb3279c2bac6c8703908e496be56466cca77f046ce7ba980400d3594e82b6c0514aca078279ddeeafe652865cc9eec
  | 8 => 0x592deed24f987c200d5f003057c4c4d2d9a7a0557483eb4a3ccba9516c5dfb88346591f9a5a1bb1c54f501e2081b5ed592dd91d3b7dbf8f9d7c96ee5956817b27f4c61bf3d77c1046fd6b0a8683d6a108bffbfa3053bbfc9a87198fc46180eca565900a585326d69921a7cff94003d49d865d79
  | 9 => 0xc359aabe907de50aaf3acc0c72a524a46d4317be9cce1eca2ca576b723c82f42e6b620f012b3c40ba24bb051105bb4df84f44b8e1f52077a4b02a29f0e3354f9ac911dcaae9c76ceaee8b1cb5d7d73fb77a3e160c4f19b64dad3a17d0df0dd450d1b552455e03efeadaa624313b76b3aeedef25
  | 10 => 0x962c23e38d06e0f898ca0dd44dc16c1a832f93df3d0b0ab0d1d5591bcba7dd5bcd5bdad6ac05ae20ad2716683b8d740c9d1738012e9ac2c7481919b3155b605c1eac753440d91586584f12d8d2539a13ddc81dd1a780e625791527fc5af71e31e816944ecd4da47e13d41236188b20fdc113f7b
  | 11 => 0x515927bac2ad079c876e5b3a8f800b9069f0eaf9c3052b3c18def44a5a4d201735b1eece0bf25638785d6e77671725c06fb9e90e2f18df3f1ea0adeea8ec899b3749949bd0dc56624e0337a86f6bfb0f088190b5d577a4a935e02e9932627165d9e1c487782cd6ad5f98c1a76a5676bc9b87f3e
  | 12 => 0xad307734e61780399af340b078fe560194b64cf6bc15ca4172a37328d8ca50cdaa052e8223496fb027dcae48be6840aaba2fdb9ca1a29b5d454f5896a273d0655b371b6accf8ab604eead6244259ae072377aa363ea9846749a6d58bff31148fb58b873fb85f0fbc608153c82a43b9371290007
  | 13 => 0x76025f2907ab6e799933288668df21b34004aacc9b0d3821f67dd04b6c61890b7691052f57b802bf245a1a59a3904577cdc90945769c96db9f0e54df891ccacf7e397ab804c7013e1a6edbb89998c306cb755b7ca6e49ff056118c5f01a3b2413e1422b8073f4c530e39ab70efeb5a449a0db8e
  | 14 => 0xa595e3dc41ba17f924f8c2c26464075f3dbc5bb0c954284ccb25ba61a268dbe6d032dc50b23f1d005770580cd6b9935e1db6fad763d3dc53e22cd077044327141ad5a7ae7976c97acbdcb7ea3215a9d1e256265c9b70a6118713acde98f087d531f8b114c3be98f02332c981cdb053a2d1b90af
  | 15 => 0x476544acaf1a20f6062d0e1caaeb9b0c965a9bb679da171f95e48175e379e437f6e74ef4a1741fd070ddb44bdb3ca545c2d353daef256792ad897dc7ac67113e888fa929c55482eed689886ac493aea1df12441bec555896fcc9b6469bf3ad140c41af078f60d1e33b1374a41c350c2a30c0d5
  | _ => 0

private def denseT0B47 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x4ea7fc8ff64d2a3ad0473aa7cd307fbd53256f418bc26098357fac64d2f9c6c1e46a1c9f68c0a25645e76fb0ea32242c3c9aadf3a64c133fbf734a7ec1e7e63ac6183427b54106592cb97a11eb079c73d490cd436f614132a6c5b1979e45b65385583e952f67985d876522bf6e13c5697683ac
  | 1 => 0x746eb4bd0f9c5a0e2f10114b3ec097abe9318c47c8e0e7f36d8aa6f54196dad8d7dbaaa3fff1fc7740361bd4d29a294f49535fcd7020cbd8c8391cdc17f31536416f891574ef2e944550e333152ccb2f239593fdc72f4c61ff3a3ccb8c7c3c4713b3fc360948666d9ec33d46b7bb99f3819dd4c
  | 2 => 0x8096118b06a85c6bffe72bf98c2cb7dda987de57460ee84ac73052228c8dfbd006d03ba9b307ade8ec0fc035edd823a2f471df882f030f1c03dd8c7ead5f00915519ef2bddac0e9eaea373051a1f19328e571e2d736c86c8e7f692aa2368cd14a7e5b22ae5315ca4327077054f71b19a84ab890
  | 3 => 0x6473e7d246af90d99d03101db57d86ae6e56eb1a18a8250a55ca55668235b354146fc5f6018be5f612d45e82cdc25ab51e33b2a749aefabec76dfeb523e570e714ed26e17cc5e8b63503912fd05e74cf258c575d4fd5f26f4492d92ace1f20e0f0c99f67012fdd81cb91e4e9d69460a9215d39c
  | 4 => 0x57d8e851c213e8c0e09a3189c5446b91bdb9cb78dc420fabb43a17519bb7d45029b7608fea99022937c2c559bd7b658cf7f8789c74266447608474db6f73ce9a4feb828cf54dbf2ac3b43ec6f5d03a9695ab02d11fa7ac119f42184e792299a2835cd9dc88b1a1991a442ea7f9a8aa367b0a7a9
  | 5 => 0x4a5031d18468b7307219686e6f957f1ff388adfeb5ab0c91d1476cb8eebef8459043d963d9187da6448962807502dd538e23a7846245b42c23cfacdf226beb6d55ce42c302e0b0bbb00bdc847dd988259a945f064e4475951f9dea9de99e79f14680838ad24c5c814b77217bb943963313b1b1b
  | 6 => 0xee24fa168f3af4b887183b1dfd7b920da9dccd9c7779288237ce98cc3999708be3c91901c595d1a2dbfe9edc069effd8500f4df7ae5e2a410ab1ed7d0029781723ac3878e96662fdfdf0a6a9e7e4df23baa14e41fec257f48196d46bd3055fbef4116af14755b4ae42695b0b026eb595b0399e1
  | 7 => 0xfc7d1e0a00cb833beffb0820725da0c488a555b801eabb3e316ef844e63100449e6488ce783b75de103aa4fd05e045af848a2fdb48f4b7ef27591675d8356e59bf22da5ab3c79f1a32448b177dc7a3ed154f5bd87235f03cd54c2de78ca260248c2bab2f503624764a3762c7e1c61e70c4e4839
  | 8 => 0x39c4774861b9da858ecd823fdd596c6adade75a8a45e887522ab4476bddaa23cf5664ef6f6c88117c532eb289aae57564fb5d5bc3b602c770dc5b34ad9f1561f089f1faa8933c6429af06f1ee47a3c45b9a48082e59fbee61b79f67bac70c2de1cecca0e8d09083ec442a3829d5337ac5127c33
  | 9 => 0x8bf4055d9f00b347bb91e21e3a84302ac05a71e7009be6639e283ad759ebac25635368431aba52880ca5774089bb526154de07f12fc0b4f729a0feaf278bd0e449148f8fb4ecb37ec6caf619042831a2d2306d8e70b2428e842a21e7aa58fb81b2af358c36a91131c48c13d6ed6e4d29dd397be
  | 10 => 0x68b3d5778c1bdd43cbb4525fc98bfaba758d788765fc4313c0c51ff418dd5b91b7a678e0b3f10a17971e70adef0562f2e2dedf8f981ee5c4d0082044a1867449b239758d980ae74ef572201dcbc35db51183414f126ac6e1e3a24ff81e2d53acbce3c76bccfe9368c83b3f1924d8b8f6fa7adea
  | 11 => 0x7b7314689f4d5c089d05dd99fef9aad1b33c83b2666e140066b93d8d4567548303d67e92396c58a211e719f569ce7281fa54b51c90fe89d366143aa386506d80d7645c41cb47e4615bfe270aeb1882772fa8456f8d1539f13c8a343dd45ed91b59ed6b4c0cce9f98701b34ef42c17e33a4ca2fa
  | 12 => 0xdb3e81258cd4cee95d8910fd1c2be6ff6adec1a07bab147e401c7499cd151e867b76658df2a8bddef055b3d6e9d8867edd3a77bb92e34b6e17c34f7998606293634472d48e2891d2de84d010f65b0fe4dbad048f7d02d2adb302edaeb1fd0caa20e8c8638a9e9040e9d3f17fb6052f72d110ece
  | 13 => 0x855d049aa603f904a1c93c57c65f0b42635fc282d2a1a097d1e25b9a9d2757200ddbe0a8d6d6a99ee8f7cce13bb1ec3863263223534daaa853ab6b0ad29579aeedda041841a5b80e97f21bf7968b116524198fcc8307b4ad9791812a6de58f88bb560583b6cfcfc4791da95f930605456ce7aba
  | 14 => 0xbb9cb83f67b1c164e4a84626168216e3bbfd64f8f3b89505ff713f3eb0885c11621dc2fccfac191ec3a83a990fc8a68725821e9718a47ee4c32c94f214d762224fa2a641f550e0447aebc869f540979e24e6a62a989402a05b1e068614fbf8fca166a0acb46664602e251b95c476f4baa8497a9
  | 15 => 0x3045b0a31e6fdadaf285721ee2fb7091a9e073ea857209d98f37eef880653bec239d5130e1aef50ae71bbf572df7bb60eaa72375fb879a9deafe598846572722cebf5a39ad5c521abed358b987cc73842bf9b0c9377c0ab96be5e2650777ebe145406697233163e8db33aa9c5b3461d173243ea
  | _ => 0

private def denseT0B48 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x27628b4d5dc1e0a1fdcab58b45c84c6705362176bd4774d14ef631b7a85619cbc6d4e44ccbffd0e35019d3df0120167230aa33b46924a3840f932083edc5d75cb602072ffbc53d90d9d8020e28291bff3546985db37e81ed34f0a4e6f61540706e851586f092928a30ab108dcb99fcf7399064f
  | 1 => 0x648083e0c1e13ae75cf71594aba3b298cca2295a74e3bf83c530e7a224f7eb6e7ee3f6301ea0ea9b628371b3e12dbfce1c1daa744f1b232950f768758e37ab7d105d105b2f9293337be7b08d1cb4b390cfeb3a7ed777f2bf135c4c8a474e18a52756f97a7543f3eb9e398d69968008a36db5678
  | 2 => 0xc0e4e337f500f7f5bef8b10e62bdb828475c98892c847c428d65676bda74a1ad0194da61cec790c23e6d64437153a0e5afa12e35dc5d892e69393a594719960b500371f37b1766977a534c01ef439e242be7728ec39a5f9eb2b13e35f0c5f3c1a1e9d650dc85d04358ce9045efad06390cbd9c2
  | 3 => 0xd6a4b2f3f38756f44308074e89a62b127166fa10af5c77b0b4179b646b998178efe0bfc3369fb7d2d6c04a0cdfcc26aa9b2464ff8da8f74c54f86f11c565d7da41521e645b9d624dda6448c101233785a69caee1bc265226cfe8b44c416ad9a914908a2410e040430d9e8f71e6d6c48e455a07b
  | 4 => 0x39669acb1c73e1e0c52a7ebe9da70b71abb81207036edc14c8f3466118de45c984449445a1ef7bdf56819edad88ee993674dc425c96213dea5ae34549cb110839c29635654369d4c6bac5369537cd9744fe058be4176ce7fe7d4d9a800cb9ace2032479c86d733891bbe6f4b439a8de29cbc4b8
  | 5 => 0xb1021c4cf35b55d2ffe5cea9cc7f6606ca576042a55fea16b786897a0e9ce5ad0f0f704fc44e4a7c835b80532b2c5f5914dd97c95d89b7bc0a1a5cca7c31f968891b0a1626907eaea8035e88e38f6159c80015f6194f2f1b3e2012e4b7ffeb4cdd71bfa292251e61bf480a2b49fae2b351b69cb
  | 6 => 0x7b6b125416cf54b80123558c71b34e206ce1b462eb9894fc9fa3f7b80806940f6c9342fd80bb93a83767c33f0f8dc60435aafcbdfe274be7eb5641adc9f2bf006514995ea0fb4e469883466836215d9e467cee96310298a7f7e514cdba7ae7bc073597912f904b6b5c4f27ba1d919ee1668d736
  | 7 => 0xe05ad31e170c0583ba207638d255590d11b1e6e7d65557286a1d621b2f13dbc29ec6b7e46f02ccfa341bc724296bbcb4e719975873e3f997358f667bbb948a6eb8909fed4b8656ed4eeb170726c3aa07ef23001680b8cf91895117284f01112d116be013154e2809aabe2fba180e06d99b2f11b
  | 8 => 0x9793df08bee8ac75aa12f19cd038928d035033d88d26e07f054b804362e2f82d9eeb246d0ad9316a70bc0c7807ad4f822a09d9680bab04c700a21b5d2bf0dfcc8e47f8b6936386f9f58d15373c0cc6b417066150a6eecebcb95645f59200cadf9a6b55c8205d74e6eb3f224fa8b54da1335b1b1
  | 9 => 0x2689b8c9c9bb037160e3b10b69c0aa2a0159372c05f4a906271455bb7da137d60500ccceec87700ed2ffcc33543a98d1ccf6611ae4a41793d5f436b611b69179d9d09b4c36583c992057ec2e7a65993c0fd09e876fc1bf3f152383860acfa454a01dffe42abeac84f96724cab52bf535ecccf16
  | 10 => 0x43f2995b856b6b1aec6890f8848bd104293b90319bb9b516791ebc8f1634a185c96376232bebab28234cf0fdd61673619b0b6946f78710e42577e109f141d030b61296dc65c3630508e8ab1f2f459d08e85c97b95ca9967c43ef17bf7945a876fcb79e99c436bff5cc00e92e5e630b544b27539
  | 11 => 0x15b67097dfb4ff8b65be6f4a2f1023e35904c79c2b4c71bdc7d100652b7c699739cb997901c356d19c4b83343e7a0ca7cb565c70181a02bff5020d99d100f1cb179ce3bcd6f82ab837a22039640b1415c56c69ca77372e1fb2233ffec7de93bea1b4f6df21d6a5476ccb7e0feae9b53c4f322be
  | 12 => 0x6f119f00238f9dd6c648c50050379422300f81ab41edf722ba057d4b67be2ab38f3805d3e54abb10713ab63ceb5d7d8e7528c52e7fea7bdd556815d3a125c37d7e573728fb279e1c4d6f5df9f50bb1f3b8f71148e42a721878e0f1091bdb28a03bd79e6e2315c8881b84a3daddcf2c3fc720425
  | 13 => 0x94016e3b81498116a4ffdd25f1dc50627e79e97b9152984775fb44c39bbc97612822e760ac6eca342425bb15e89598cc42eba7a52af0e96efd9a4e6a92f0680c85c4edaaccaf992f53b41384a405ff5c4d426c6bd9591a74a28d58403384b5d3233a0dc4bcffe608687a51ecea7126dd6e6b017
  | 14 => 0x31cda1e0c65a36e65c01e4e946d8f4a67c0c17c586b25b21ee29936d286c677b049e558df97e8361e0cf85802884e0a2b79f7ada3b40bdc2411d6481b37bb46f853e5ef62880bf2c17789c517db5cc0b8fd758c68e8c476a25e2db5ae048377229677276d837404bcf4e0468fc079bf020ecb3f
  | 15 => 0x16fdec64a1a760a41c3a1b5c5605089b7388ffcb254a850fa6ae39658b4f025db080cccc186b312e4721979dbdd60e130ff5f2c89d6b72089722e2acd9ba78f274496acd7e6e2c76ad35ead41ec5db9877dd350052ac7f2e57f71a6207f934fb2ed3c04d86f39e555b270d73e1d924b38871475
  | _ => 0

private def denseT0B49 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xf636e40ab07da18e30bffa5e9395114e42f5e6a1231417cc23a562522fe541c63e4ccb2d8bdfb4a6c9b0065f8d2aed4ddc3958bf0a06be4b60722c270bb97c8cc1d5705f5f90dac7dcf831ab45c2921c707619e4494d3b435013dc1fbbb15ce5b9bc8e661b217aef85296ccc3530fd297ddad9b
  | 1 => 0x67f81ef948f3dfe5b14d9cfcd9b47cb33da8574bf16108ae6ef79ab9f0ee539ab3c4b40eabf45bb31d0448a74104ded139f12e1bd4c09429827b3d6f8876a3555991a04fb81708312ea2dd2052d9703d2d747240c5af0da3551be70f7be15eb35cf3bb74d6115489071404e9d801b2a9afba1b8
  | 2 => 0xe1d4e678ff035e7b72339f6a628fbf600c77a414e4326969efb7261d6ff78f3c6ff93cddf1cf17a65c0d6b2e2bb6a948a449a40509bb82e8a14bac3e798f3d7520116b168e93ca8aa55d6993b232cfcae545c9667779dfa03456130d4399b46e468e180f747671138580af122c88b7a3f556e0a
  | 3 => 0x7388f8ee50c0e94cd8935817b644619a1346c0c11260656db48572e3443eb25f93a237451d3d877fc3eef10f0c3aaa2678923ef690607bbe8a4c4416b84ada9f36daeacc396292529adc4a03b28fd69a015d2b12515b61db004226464fd649d497dead4c6832170993889dee3f6d3b39569e211
  | 4 => 0x51202c400153d2fc34b4ad517ec21995e3acabe4e7519faba18f4ed9f4086eb0b94283351321244a06c371b0f8736faf5f7af2f93fc1f8cf3bca0a1575edc9f5963baacf477a9820dfceb040f0f706b6716691a05353d5a704a2429d18a0d13afb7b7049f675f03da9eba9c1a906ac4730bb430
  | 5 => 0x99163ea7428c3371195a1bf4c9401bee8f291d342d795a2ba6a67203eed8fb473f6dfcbc8ad6d6bdce08f81bff5e68aab279e12feb6012e0184f7a07cf098cd39e34aa73acdb08d244ce4bd481476f639d46e8f6c25b42b75958d40680e0089298efbd7a5ece628a71e2f53528040d009275059
  | 6 => 0xb70b01e6b072f748076850bd15bf3cf16a7de458666362ea2df2e1ce41b5d6c80a80794a06a1eeeac05ab629b76823fe12479e7cdc1d9a7105b18a0ca6e7510f351afebab745688050e2ddd1c53a76230c6154d2b1c56652686a670ed21a636ca1c880df1ea8375307ad3ab0c3fb74fc8e6f05d
  | 7 => 0x34aef83df60e692e299f0ea05f4752fb1bb7a6dc72778f3056a23b691db9597c0ab87c0e25555680bf0a55d2b38b1c65b57d6fb3c653e318d14a9af2c0dc12b506cb7ac59b94014d9c5638a99823ffe17b6b099c1b3bdd90382c9757ce476c0866307a226a25a2bc69b7cfbaf1063a520cac5e9
  | 8 => 0xf8423b3e8af156c9fdadb1ced24de02504e9dad35981173866596b5fcf8bcbe530e17db88c613e5698208147f5080496dbceed404c16fe923671b2916379077c8efc7853a39ede2739370a575ca9aec223c28ead15b22cd1d0abbcd3b633fa0bd17032456a93c26506c77d60b0a4e8efe07087e
  | 9 => 0xda8d91146ce3b64afff697b9ad7a86cbfdb933cd5b2ce6f360421c8430fbfee2488a5433868a9d673cd959e57f26f8338ef5a230d73e33afbbdbe0bc66f8383d43a9a389678eae72b2dc2d190e8b9e16d6c428bbb2cb72ed619b3f8ee61bcd1dab2dca93621efa5cbac4c9b026343119250501e
  | 10 => 0x413d15ca26f3603b71a35fcc64a6267915233b1459f6372248be34aeed68f269e57248e041a259a816373dde9150648fa0c4d3d1e3bef8d3a90187d60e31184b434933fb947e95b48a19998a8fa0b8cc673add8071ec4e88b035f18545c09efe0199f81f7e7dcb1c8464388986d6ad279dff80a
  | 11 => 0x841d2bf7ead12fe9169e40db38153fa25f32214e28a2d50da89b8eee28adfd896db5ed726b3a32e6962ff703ea4d3807e6ea9d62cea08cf37dca3c51c01e902d98c0bfa040d735926f0a5f66d44df6d0e500933f21310dc43a5970ad7e13d1260e0ef817c1d66dd8f7ad1f466aa30fa7289a79f
  | 12 => 0xf62010f00df7d5dca2a26e12679494403a5e208be009237fa81f51a84aa41b25ba710e0100dec41f9390a54d1f85853f424ca79ebe121eb51d53bf85ca207a3d2c4a5e83e633200d78ff19978ff2019caa93eaf0e573e2e2c733fba5d7a72e445b7184eefee7f12a547ace222265ddde435e63e
  | 13 => 0x4bfe3a9a0a73183e50b817059145135e2371784e9e1762c3d2fae7bc60a5c54cdd3d763f297d6dd138d2addc31bbfacedf1b08b9396542574ad2fccff0677a0bf245e9e6765a646deecd94e4bbda16533c4f6091b5898aa62eec442e6c5fe9eebfa7de9a24419cfe7b8370521259f177e319d70
  | 14 => 0x1d78db324696ed0f71759181accf1604533c496724457da1e0dcf7a88c2b6a6fe4240bcc7121ea81065118b7bd9fe1817a52e55e408c823454bfa43ad64985cb907de5ca4f0b3b0f6c32243f1836479ad52366eef0c65c7acb02cfe8ffbe66b2e72a33dc45d6522326bc7045fe844afeb8efe3a
  | 15 => 0xe3fe5f6b9277d1f9f46278049b0b3d8415084d31ddaf72450bfd3860de0069e7d7267cb735d2d68d4eae7b201e33eefee7eba99ea956a43c025779793417b420bde42a6338d4e5c1d58dda2f971a3a053a436451a2769772579955b2d1b4a2edf0a3e4aee034b79275fe657c3fea5b92df2949c
  | _ => 0

private def denseT0B50 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x13bd1f238bab4368b5d16320e6daf62c683f249b1718fcf85ef01e9fd646a7f97edf2f58fb3ed5f7893f877a777934f038fd890d7d8211d06ab4daf0d2806dd82e3426682b4dbe5fec62ffed484a206ca9f9c534de6e162d04983a2779e29057ad4f11e50da9983044921f6ad6f700e0810dc7a
  | 1 => 0x7a680f34ae76e1de9de5fae35db62f6b2f25baf998b09658671eaa0f917351403b08ff60b3249dea0d73d1d31cce6701157d6849c483b12b6a1d1b9b39cb99bb88b9c122d28186d974ae3b3bd99556ef07931854e854d71dbc472ee73581b20588613a2ea08be93dbace86eba9b7229ac91784f
  | 2 => 0x5d7334ffcd9533eb588fc03496bc33f0ae4c1eb7387c6da04041a8008ef3666e1f36f44371b7840ef6da5d5e987b7a3b096a2bd59f3c565612dcda1b2aea76f116ae0fd315c10ebb19495bc94c65ee79632de398e51e86ac02208a0650140f511f052dc0fe6d5e4db1f7b7b029d9e8a09cbfb1e
  | 3 => 0x1c9d873f0a2313c80dd4c12ff6b86d9c81bea36c22e613b5d2bce40e0623b9377a8725a90fb4c41e821faba64c373c280b27f6b83f1aa0d2f276084bfdc400701acd051058b3ecebc4f68593dadd56589903d283b040909c1729b64919a505e5bab0acf7ceccd1582fa9c9d002356f69068bf56
  | 4 => 0x89e14648181d6869309920d2c1834514fdf6e326feb397ed05347ab1abe7d03cc6a31bd5f65756783bbcfecb72532c70a9feaae39183a668b9aaa6bc341f4e38d26069d7a8c7400dad3b08895915d3891ce365573c1957e3ecaa954a30a5ce653e8c71c108ff6a26860ad64c8e79565fffe4f30
  | 5 => 0x675e1affbe40a67ce20806a29fbbc2a33e0cc8f779c83f562cdbc57c0380e88fd80e22e8ca14cf9ec190b755cb435e37fd8800c06dc04eda36c4d5bed150cc0dabf5fbcb7fbd204fe7dfe1bff98633eb1625765a47e56f6b11cb184252df0ffb46fe5dbef15c218eaf9bcb6b7c84e9c967af707
  | 6 => 0xacd23c829640d430f24cc4365fc4e6d847654f67ccf5164b895877c710dd4cbb84b72f6cbc6adfd6c9514bd0825ef892f701c8202921f80f3ee1f4ae8ecbdeeed5994c3863840c401c37bfca35200b29fa7c2f9d5205954c1190ab0950e646acae54577fc32e9738a62b91609cebbbfc9232dc1
  | 7 => 0x6b489d1f9948cfb8eb9742e31bfdd784d07c98e80821cd64efa3176615962d8708445ef7d099bb4de3ef4584406578066350f9e3f5685735510409a2ff58fd9d3fe8931a36036f263e7cbd56fe9aab198b01434a97daf845dc90be6eb1b17e8f5ba31a88abfe5c083442b9d5aab5f14a2ff6f7c
  | 8 => 0xed52f9552e39a8ed6812f6e4bb3230c879e07a28737c117020fc7d2ce28fc33f03b434edc83f6cf6603ed0bfae23acd326506ee85bdca53a729202283e6220dbb766b7c46a4fbb0e6e71c1b630e7b62c1429d6eddbc05b5686ccd854024946f6eef4e0b3db2d1d5dedd6a31701f68749a590583
  | 9 => 0x72936214a8f9d010c55dc81337bb0182045b8f33e352a8164bb8dd5002274098cc46ffd86c00051a879a7282dbd268421fa4f899327d59532950cdf92f0161b846a5c176ea0d1ed326be111163dfbed047bda63a1a4598b027770b66e2f89fc952d68ba6953bfc8f3d82c60022c004303443cfd
  | 10 => 0xd4c3cf342f89ad649c39ffc2f4c47ef1e870aa3694f2a5a03459ae42a82afc63c03e1541f3ab3e19d75016a89905142557369ccb204a8158f598f423188ae0b598adb2d46f7d46289fa41c600ea1adc07a5acb1531b88e6040fa2f7ca4e0664747b68f702ad4322ae5b59febb59e88ac942770c
  | 11 => 0x3e3b11e5454f989be465d41597a5100f7792418f65d0b73926de7c4c53e580f760673e21d1b51c2a61c83f3a18e0cf634f1ba823acd2a1b3801f5ba0e1f61dd3798d617801b611f29aa1ad68dd1f3aa195dab118e782f8d1b5947a979528e53c8567ee13ecebd6fa45759052e5d96adea120ca7
  | 12 => 0xc429e1ee7f735fd7bd16b3589ead072c22c5db74490ece0aa9940ad1f508d9d6593f995a8e93e2fc55f088af540f7c507f3d8d8ae0bde6c1a5a8de808c66bca84b363d997fbd568df15ea2f1b8c71a4bbe42fb112acc735585fc573ab44a14f8775d9f16cca0a984c85783d70d66a5256df6067
  | 13 => 0x7c7e212403c153c5ed5dbe12769242b8c93ec36b0f9a499f1ab59d6269054fe18f76e8cd65824d6114f24d0f172e1b562eb41b3908f1f82200ad6df12c8360c0d073470ca644044c90e1df2b1366612ce5624c9b9ed98f9a2b58ed69ee18be9f70b8899ed87fc1c8f22893989979bad72464025
  | 14 => 0xb40aa3dbfedd164f9eaa026e22bce3da78ce5deaadf21f5cebb5d3c167fe5aeb0242d604cfef875e9cb87c7aae6f81348ea3dabe31c89f1915c76b0e96b107b037709253716725b01c08119ad47391cc0eb72fd15f55da4a2046414406d3999e1606381d035873302459e2c5b674d55ff1fc924
  | 15 => 0xe0b25963df1ddf8623740448eb6b2d456755b0a9d81c4837de8c3bbdb9cb6c38565f040f548268bf6d0057b9ffd9f3536f38599b8ab29146e4e8f39c6077b60b856bf13f768a471dcba351c40ada93e7cb2884d3e090bcf39e739ee555fadcb85db4145c51b08a3aaace44e3e74f7f42866ee28
  | _ => 0

private def denseT0B51 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x5a9922c0ed137e56a0b7b2c4dd9b2009e10f0246c2c32efd5a7abf9615b6ca6bf8c36eb28ffff39a8fa533c314ff76f1881cc178069166c7fae91e3e720291a262a8cb4a27c7bb13eb167067637bee8221abd5631b7e1eaee1c94ad7d49840c8dd7f79ac76039d6dc30403188451bd0988382d9
  | 1 => 0x66fa8b76720e85d336ecd3a8bdfe2899fd7c9d9639df55efeadb902268441c50794c5a201f3f56e84620ecbf35ee034e5427c5043a8e75589e5a1faa86f4489eb8a5f76c49f17dc20704f585a5b8f3daf074d3094279c3eba587e1870477f998c34e069840f4fe0065a977c17acbd8070e9a348
  | 2 => 0x127fa456b5028f76e3b19b240bb58071cc6979a8d5d0c40b4790d34ff1eaa588e8f6488419ef529e2a2fd00eb14ee47e805ab5ad418f9bc5087cc64d5787fce0c5dd741022ea6d871af74099459c52a922e0e5bc01cd5ba8f02407226ac2d719573d24d2cfda14f1305f9db7620f9e130645fb7
  | 3 => 0x5fb1e4bb5b622c4d2277937b4173a46ace7104b1b511c6ac34b5a24e0a45f73a27ba371677655e122fa718aed13c7e316c933ce43e4eec8a5defb2eec6262af397146a4de620d8d920c6940e7738ed45a1c8060d722c9bf93d125b2ea59ffdb2e4b544e3da514601c10e91be5ab82f0ba9af834
  | 4 => 0xb1050378ce4a2087ce942b4019fc07cf7123a2eaf99393cfe8f670ff051b3c9483a26da37889c1ffb95949097e25df61106ef1ed68658cd43225cab0e6829e12a042462620c6a04819d0e62fc1d81c7b32e8eaa72f939b951f755325e33a23f1e8c98657751a81572104d68931add4ec6f528cf
  | 5 => 0x54d6aa1dfd39a2b9667335183609c180699d887c8b886135a1f9c4692538bf6fe16d0536f0cc321d5392e2d605696449b1a5007dfe2457249f40cf0b8148fbed6fc1b3b268f8bfc3ad4b71bc23f86db143629539f1bf87593836b0b247a2591c7cb582a1bcbf2258fc48498224a56a5ba769b33
  | 6 => 0x9990896f47a80f80d37fff525d632d0c49f79cb8d0c778d3cbe0522ccf3762ff85e334a207188c765b471ea5aeefe4b71b422f10b60e982dde0af3ab1782581db97c959fb761a0e8ce0c282274de369f5677969c20dd3d7a98273f0c5b797e5e57d12fe4ce9ab2d3044a513da0790b7ba74e54a
  | 7 => 0x8b27a70c0e484d96c502f5c54176d57c2d97c70b34480b2cf2e6f4997024345511edc1f9592734f2f43db7f3929bcdb53778907b1467c6cb36f45c48d5f73fe5560b512c6b4c256d0649419678468e07aac874d7397926e1744d062820e0b497d08164f627a1f3f20dceb15bf76af429a4d2c9e
  | 8 => 0xe8a767cc298e3e63ae1ee240bb5cc0094988c84b600a36d7f105ad8214d7da079a15d9bacd80417a2f1a934f09a44bb742b38dddcae18aed1fab8696bf4369021e87452bc75b5854acb34130ada333bc7f71af1f9dcac0901723cc494a305cb52fd3c066abe7fd0c1f1610cb47baabebab67c49
  | 9 => 0x8400450bdbb191780f3706ed5145dbe4605c5ef374c515c9fac783672a509866de41e459cd60aaa47819b208c021f5ed760f048631e05d51a58a0ed091c2fca214775478b1e8d5d2b0f7847db789f2f2c6e3a6032a2cc06aefb3d56ceb3ce6ca25fedf25335f0817f73e15b2f78e62debfcacc0
  | 10 => 0xc483e7b7a7cdead865fac2716ddc075304855f27375763f4f9b379202128558948e805407b61d62ec314e7495bed2e99a56247bc9a3e532d9b8ccea5beda4b83134eaf4978a5f689b4b54a32a848d742c3479bda26a1f287315ef3a85b7668f72cfe37dcc6d7075a6ba871d48b0816014766be0
  | 11 => 0x44e67de79d40b2271250bcea22e7709b01e4e1f606c07855645c28508835409691f3bceb4bb2590ce93c7b780428b0a4726db7e34d0e03fc5ca9034a8e8f3f8c619279222b93d6e59b776fb6d97c529b1302f1e32a399e763bfe384fb72c77b12f644cb6b46ccb45ac5df246c66f02e5032669c
  | 12 => 0xc59cd85f03eabbb55b0a18b813c8f4b9ebf515baf9b28ed8fed6dde6b5c359789d102ea70007394624f97301d87e2c841da88f5f87786124fdcde341c7f0975d550512f89c1252b8fedb3611d4457c9e552669ffc4214b0b910f4f19c4f7a4696e0a590b27c59f2cd586fae3d65798abb9b8d92
  | 13 => 0x1239cca1b632d27d729825e9b8093a6bb7ad5a2e03cc5eef54f8a64c7417226c9bef63e8e800e628c30add07694748f95220a4f1ea87005d5db587373a3bf1d01bcd0caa861f267f58ea97623c5fdfa985c786ba93fa4cddad955bd1b02e84583f6057c9214785655630fd8e83d3228359a8015
  | 14 => 0x5d9f5b4ed5284c9959c4886160daf35b95cec1886ff7fc0cb49c700486fdbb0215f7b039c738a9e83ed8549ab1648d3a0129f0951cebdf36538485f86bf68b0b772c7f1a5c23f58b2b76f9efaf51cb09e195146a7fb0f311e000ffa697539365273f0f4d592cb80438bc56f1df655147fe9e000
  | 15 => 0x60a107c2959653a27778ef787f71cf0099758a9f0515d48dc710d1633f3ab8ef1a5bed687f490e227600c015791318068cb0fc6e1bda1b1771b8bfdf99a6451d3b57dfc43267a448134837012b795ec251c38f3397ef4e8dfb07c3407795ca575f5f63f9e99400468a353ff98c64ca299dc0d4d
  | _ => 0

private def denseT0B52 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x44d5c32ce0362b3489ac85789ac4aac0b071baedb2233ae84cdbfe861b5d4c9be50691e55d493a60ffc715b1c1dbebaca066b71dd2f8f6f59a106b3fbbbca6c1e096410d7bf431cd25b976c5dfa86d05c4ad1b698f29ae2b92f85017053f336a15834fc913c988d25d1c78831ba733b2eda3764
  | 1 => 0x34949cfd65aa0802f7508d2165461bf84087dc1886b3269e4559837d0babe84fc50ff0f1eea4677dcbb2362f840c3f5926e5fc4ca85991c0d3b362f2eccff6f6bfba0023b94229be85e99cebe9f7e637a34fcf90803593f52a2491760aa48d517a61243b2d1b7662b346b9d6ecce3a46c0e481b
  | 2 => 0x5048ccc0eab672e325ad1155551f957c87b146273c9856c46f4476698dda6822d1d7b2c9385fa55e103039336dd5dd6a2905a366b6dcd6a9f19d55290dcc37eb2b1b54746a602cfe5cff281b500823e37e76111292c11aa6c95e461c712e8cf2a5b413d3877f5e278551f51aef207cd017becdc
  | 3 => 0x3e6889e12209011b0aed0fe8394e83baf52d70f67ee7a3206a68aa1f402df74b521cc4014756a375671cde78b39281d4777bc0d57ea2560e5c06efcc822fde1238d33459c5dc2af68be715fba90accc04ce756ce4e93d0bdf59eeb31c9c7e1f9647f70b34b3c66909881596b904d38568754312
  | 4 => 0x9f66d15b4343415e63b7e25103f230309c7cf13c5dc4fe33c64082ea78430764585cb5794f974ce3a30cbbfebd09c12a8e8596dfc11057c54e39a6c0a51bb7025ae17a952674c39c61dc2ec47f48665c0849677c68e50e9f76649cabad54454ebc2d5202f01e75c8fd2116684e2758c3f751881
  | 5 => 0x4746dcd4962b250052a82ac6373d920fa3eac56c4c7261ede8f203f24493f73a9baeb95fe129c892edfb5f38112a7141212fa1207441dc8354f598661f30805b4fa5d87316217ac49ca92be68bb8a765edd52046c2d66397b9d85af8cf707dec903e7daaa89d658dd0fe3e85a030b70a0da7740
  | 6 => 0xe2e3c34d0aca0ceb61491381fdab316b8deea5177dfc254ce4e42afb769e40d3856a0003f26a6b1e4db222264b6c24cfc994ed15b9726130c495f6640531084a81dc93c396ab87c6edc1028303feeb07d6ef71f9c170f342dec03fb3f0605be6950767eb10fc1170e1ca128fb16a1d3dd164004
  | 7 => 0x93fd821571980692b6de371eeed5fed4e214a575eef85676909e61f68c22e8fe2fb17929a40e10e7cc19939794a7a268913eafb55fd2e9f589fd0e9812b64f21f3ce90e513b7b5c16afe010440b8ce70e96ed90f1b99f5befbe25c95a34412c9893b1f09484f3881c4780e6af8a54a3a93c5861
  | 8 => 0x7c836a730f6328644604e67360a6df07d9f975aee1c83979634fba8b5f6295087a9f3a0ff8e4d77fc191573aeed14e5c431db72f044192ee6e39f26fcb272f7190d2d6991921e4ecdb77cfadd190edb9431af7e0874358916104644df97908b6e444e2b515f6003b2c3e91b7252782152cd1fc8
  | 9 => 0x1befc6272c7bb3c784c5c4fb0715c8e0558884be356bfa4061e8079ad61f5700700a255fd043c785a3351623f7e54ec03e843d420aa7fe3eeccd29c59d523b2247ac06f689bbd8775e8c885475aed38bbbf4e59fabeaf8c6143937315fa506a0c73c1e4a84612f79cfe11942c23c00b6087155a
  | 10 => 0xfb06055a878e84472ce0180e360c294688e7d27ee7a761404a6bd15788055ffdf858ff5c65b6c00587a7834b073b0f652dd00a986bf43a40b7dad4d54cca4c04d2fc6f15ec5ab74524b0f5b7a56035ac1183bff6ac40334449188a7f5d79164e775686eaddb5653322a775cfdd0e2ceb8584293
  | 11 => 0x6ea77972288c40250761ea86acd4025d9712189e72c57f9d4908cda3b558df687fb309c3ea1b1aa4d05db5f22239b1b35494b7978a4d2c2998d8bcf167f1da651dd71fe51ce6433410aa2bc02379b0d2b0fc18a599db7783814340dc80f79cb78a938d00a9cb31e6045acf3e8d9953b9a5f3ff4
  | 12 => 0x559b7dd07cdf5e736b8b9edfc076f56268abf8453dcf2992a40efec8af115f6f6dff83b16605bb1ab3eb5997ee98c6deaf5f8a99492e30de0a5d7c4be524803cc305033e6019a0b52eb739f0479421beac2dc3cc30f2f19cd1eea0383a9190b33024c5fd778845d147b5110c1423ef72d358780
  | 13 => 0x53194bd0efcd6353163d171500366e25f59dc6dc33c2acffd7b98b1a7bf2e8dedd0a839eec54d44d7d78ee69255f3b3366730d6c873d0854d86e4d047b2294cf07898deff429f07cb8c841f3aca6118e9b3279f5e0bd31a8154d7ac3f4e8bc2673a840e3510d2ba87b28035cfaff0196a1dc846
  | 14 => 0x8a82fc5514d03eeedeed691e812a91515dda539277d131a713a408fe017a75cef895b2541e9c876867a686962ca2b0d99611d3dcd815e910d18b381f47cc89d9ca0b1edc0487b909fafce0ce6b0119d450a5c924b184cdf823e49a5ff8cc9f2c726b422be24286bc00ef9b1353454c03d664501
  | 15 => 0x7ccd299a6082cd0f8975fe405723ca94ccf8174c7ec1ad97f99c586b70242bbfef497109338498b9070b614cb4d3669ffd15d4ad876358f220f8cdf0dc8ec63368571401b46617cde1584fb29203ba8fd803971b27004f71cc84ed41b4c274a701bdf45505291bdefa65ffbd8f787caf6f4cc4e
  | _ => 0

private def denseT0B53 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xf95351107ec5ca06f956c6b4e52edea5cbe5e15bf7b9545d36b0697a5ac7e857e6fdf3568cf4579b1b6f92a1895f977ec22e95f05d6b60ed327012e4fcef68982977fed6c85c3e254875cce7338f5c76029a71489a6866b61f568820ef36cdabb6491cab916a334f3cbaab2c71972e31e3c3f4a
  | 1 => 0x6694a0170728a4bed5af54ed1dcf1ceb876000c714d1bb9edc5b13ce473c9ab8e15e97fb9b4ea9a9ec3d3d92e54947d15a660e0f3381045918341c483f2310dca9b7e48ed9d989c8d283629e098a015114f79359e2ef8b38e2aab039f92c01f1f172d3205ef49a83525b13f58bce689ede5a976
  | 2 => 0xbd8d65b2f8304fe7f7187cfda50beda3fe6673fc8bc36453eb430cdf1d1b9ddcccd475938de581471284d9b3ef540cacdc78c8a0d79e1089d839b2a4f1f0bf6a018d41cd9dd8992f23d397829ee6249bed34da87a6d0ffd6609a82f7c3997c0f3e360ebec6d768d8e358ae9193d98767a37a7c9
  | 3 => 0x7e783f64feb0afecb91f1d1df31eb95e479113ac58a1b504ede34ffe7e5bf402b4ffa629a8ebe6964a068ec5f363380cad1184b8a0cbea6e4967405947af9f863aaff18d53fbd412765c595555773188de067627aec947bd2a3d75b10045d3fe8b447f9ee6bd2d71dbc87b08516db6c06a79be2
  | 4 => 0xc830ca5605fac00a5825f3fad700d3711545c75b2f93eea053a058871c63982626f5b485ebecf7743e4f866f5815ac4402878746a74042887723d82c0caff3a7cf101397c2a1f5ba5ab20db5b421cb58c5792c3aa68d15c26a631b36be453d957aecb8b76a321bee4bcbd67451482dfbfb9d60b
  | 5 => 0x1f22db90315acf598e1058638947c9746d12b62516eddc424aaa7879fa17954e09f8e8bdf81f39e2cd019109e3152349e3689b8e3925b819625488d345f7908e9e900b43925393270de8e150acac636bf034d2bcb70ba58eb576a8e2125f1906f1de667e8fc32113d0ab8e8ea7159a4c5863a58
  | 6 => 0xe4ec896b3a2243e51eca4d7b1e969e6be52fc3be4fea361898db6a7a9371329aa47c80a64fe55aff633fa81f2053284fbfda1ddec4c2944a70d8e17435c7624e05a78ebc162156524906fc72d407a11ae33620e92617f08f0072549af0bebc16132ca406b6dbda786cd142f417388988effb517
  | 7 => 0x4cf64d5df7e373070a4d5801549939c5272d6b8ba706015593b6c48f24b3fc350f6130ac12ec3e2e03518505c2e5efede6205a5f12854399108f640087dd6584bf924d146bc3c566273e405a0e0acf68d38e9b4fd2ec078a703040fae0f9cb8e03a7ef102c5be6d0a12cb92451a74e4ad22d76d
  | 8 => 0x80c9f838e797ba20ebb6d3f1f05735f2de31da04c124cea9b9dd14b34200d4d8318a0493a9af27b702dad8c8112f2a3edb828cb5041e6368321c7e9a3ff8d3c808b2d6cc85ca721397088d4f32c5fc847c334a8ae5f1b61c13319ddabc34bdc6ebd310f8aa359cfa898b85bfba61502306e2f8f
  | 9 => 0x6e13ca238a04d3238f9b544d38199ab66f2925706582dbc46c7ef9a6a2128d90beb9fac2cdfb73b0a98023ccd03d06d2b6e9f7ff800decdb0ce382530a640b54431eb649f36e70e093ce07d551d50d1730f1e1082d4ce4314be9048389e452b52f021d346839e24b6c25c6570c00671a4b4b4fa
  | 10 => 0xa6006cc031b2a4a7c40c4288965083d2de68885d9e980a17588d85c359992e9f4a5ac828a2688445438caf6cf54497a08cf3c61b02abe3edcc69d168fd215c461dc5480353bf778ba4a8d13666bfba21e5649ae06df259ab787c74ad684a581bbeb0bdcc3f3a1ba89dc8145e722401e6bc0890d
  | 11 => 0x1bf437cb5083c18815059398371faa1a9aad0473071c5e73a1b3086b0ee03b58e6650033c704dfcb1d28f6f6b7e2a848dcdcb2abed36160fe294206697fcfb26648ea9299d8d7f537ee442b48cd2b66841ecbb8d5734560fd0ae295a94eaacc66c952a5bc8f259892ad3c5602143c36e917455e
  | 12 => 0x490f5fce9d826bd1b438bcbc4217372246681a143e49872be033c6e7a5d1f4894a5083a7ba5617b2fb9231d29836ed068a61817d4f7ce5ba9a07a1b1518e1a496309879f3f06113b617aba95c10dcfe71ea30b4cf14026e95d164ca72e40c2cef52b93d462d5ef9f26b549c3518a1c594c3aafd
  | 13 => 0x95056fd0fd99cd07593804939e34796534fec29fca6043fc562fc84145782890dd5e36aef562117eeb107971150cb4262c7e501a6de4ff0be266c55e70df82f10964c826a40e22b78296bc23cf8eff387c536a89b7a2e4189c7701b61daea128ca9e013aa0534329f0d89448b603e9175d58912
  | 14 => 0xe0356bbc705cf94cb3a215f7d95d2b322501bd10e4e23877677d603696d6053cee54aca4ec5af4aa4de4c6f7770a344d3bbde2d2d86de0facb50be88e81d5db25b306fd292cb358429e81c96db1314808253f65999bb50206dbb1d179dddda5f2be8d7e720966d717970d3436bf967b9909fe15
  | 15 => 0x1d79f2cd32f131202bca8de7071990b9b9833a1a5333863feeb46c73ed8cc299ddc075de3cd76311b8b814953ddd6ce804187b21e52f3b2398911bd0d5941b94af84949cde61188654bbee181ac19342980cf5602b15650b273c325e3a779ade7d551292c6dc1af3fe0d27b02353532568306f7
  | _ => 0

private def denseT0B54 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x50551824e6ea06acdb0d37ab109395b01d7d3501222287d982bb5fd8456e1cd2bf48a364cf853bb6dec6a1d958b9fcc4c5d352a7cca490f56dd731384ddf9b45223159f6a36047fbc5d0d3234f74a608ce6b3a37de4c73655591be5e89db5e7de5ed1767b5c4bfb4e608233d7cd0f9385d7ab84
  | 1 => 0x465de10897ad1ca91dc863478b5e551e3e2ab4f2c6fdffecb1234d973545daf7f7163c7e7a9312bf6cbb699f7a5e41e82fd098a13482a9c0645848ff9a4192820f07fbe6a605a3761dd8997929adf285a5bff3f772f985d4d6d87102708d35d5980c1a85e59eb9dd851971f5440d7a1e92ec957
  | 2 => 0x8b4603c511ab49246b474cfc0ec658b637c9d9a37f813f358dab5076b357e842ca513c91292db5129b5e246aa6cdd8f1fe672cd2afd252828b1c4f1fc1ccacd67fd784c6392cf82f6572d245a316344cf6e30e800d759ac2d790f994736bd92abe1c6f392445b0f38488b43f3779100f52a5b02
  | 3 => 0x1f298fe724953172759aef5e437a1d849e4e1bd14f4b20c18c6abe5285a3d4dde26c3deaca5c0418736d82af5fd4f7be2d860dfc83a65463a9db0d0e414c404a722496e764d2084b45b4b83858eaef702d771c220000574a150cc28729a250e0dd4430384feeaa71a89931cf4a187326dadcfd3
  | 4 => 0x14b902f6e91fbdf8fdc8d9c47e65312eca9205ce8814d03ce508ede4e731c5be66a58c62d851dc2af9c8b3d003c10c0101aec1e7dde242bef47cacec1c134b51390c9e9deabb688075adb89b1ea0defc16d42c81cbe2df8daa35bf4dc11eefcd6e7f481e339323e4f33946d0b155be9060c19f3
  | 5 => 0xb7ea990815f33bad15994f47cfc6a6e354b8c9aafda5f7cb101e50068414be3b949b770face32c90e8d478d163873864708f858b36ad8b89e7f660a6ff6911ac6985408aa44f21c25e0d66bf92391e50441c07db8d45a9e7ecda5401deb4260737d0d334ea008830c2a12829ed8c9e3ede9662
  | 6 => 0x18d6d240af92a74cb92e3de99b36cba62257d8819a2e0a729fc47deff4344887f5e840f88599e3780ba3e1f4177d1fdb8b27d2f1c3576539b490a13cc7f79268616c66a120fe9fe3e8b2d9f18419e643ceecd095b07c3b5f449901d849233a9474a0aaa7cd7a913e099cff3dc3dfd93b6dad8c1
  | 7 => 0x4b783130d846507fd5a5faadad51576f7b5ca439ebaac2578e93c4dfac8dadf890329d71e1d61a5c3c9b5b6f40f02a2b119ed36cb5f0d05edb1522db0e8d86bf431bc439acd62382ca43b8eb09e4d016ee6bf58ebc3f63aa78a2fd0f74921de672011e360e82f452b46856108aca7ec23b5be6b
  | 8 => 0xba71b27791c5afe0b3ec3f4cf76c520f18e707b59e056d6880e5b4bba76b5ce35914d2fcba46a81b81efb4c4cbc219a36606de400fd41d32a4f61e7fe1ed585ef3fc6c6e445520e9869fb3d68fcdb0220bbfb00542e532446590d92cb1528ce478c3cb64e7855268f1b88eaba4d4d655e7d03a9
  | 9 => 0xe055db45acbc716a3cd4465c48763779092f230c9462b3aca1e499000dd6760793ceb4585bb1011589ccc381336ba2df6e20a2e580bb224221a2edc0148a0d30399b3cfec8269ce2908df46c4309613cf487b8bdd5d86002a82abc1c29e5de3f096b6d959351b2a53f7f28cd9bb469fd851eaf
  | 10 => 0xebd66d93f7f97b2cd129039899c5b9a164c9214bf436c3cb60a04c31e53127bd0bf53b9436c5a8a25c01c451d7404a006a8c284c6a7badbf96923100cbb0eea3e88ae6e4a3b25bde9f58df18bf3dd8335ced566179c54c00cbce5ddc70937fd3e008fdf2b16ddbafb913acf91c4a31234b92a5f
  | 11 => 0x338c4fa080d3daf8263273d23847ab70da62af4cd58b6e2693eb4baafdd3e7b131959eaa76b8731b2b1c7b637bf34e1ed276b00a3a45b183ba28aa9e93eeb6f4df6476382736d01f5b75305fdcfffd2a5cb8b683d9d6b1aec9c4dba5ed056ffd3438887f07eece3fdb802d32b09cee20115e73a
  | 12 => 0xde306af978ec331379ce7ff94a45d0024b56695f3dbda70746254ab49eedff49b746f650f19695fa80eb7ffa1f42789ad70067e3922272b3a44b2b2a7aa81005ec0a706248f0fbb6a68dcd93d871cb2328b0977ca67b76a600a0fc401a2cb56dad067c77c50ce45cfc5523bc2719b4ee79da839
  | 13 => 0x354239d9d7eff58cbb3b963294c574af184952b5790e2f588b9d94af06434c845d47072eaa0585e6aa6c82d27cd63fc959938fd8f4d2c1263f1ed2b91dcbd8b5bc14183cda6ee4709af120ec9b759c82a9f1bc8f0be906327d210f4661f1afeb5fe6f6fa3b0166bc792338c344ab1c78fc2b1ca
  | 14 => 0x1c4329d2b09cc2357feca44ac74f4fc65a2d94376a12b5c93013f0aa07af92eb64532b505ce281934e8743c87ec96cd36c8110ebcf86d832ad2562801f4eb9374b722455730802b99f672d10e1ccb79bdd69adb4a687231aafe2e4a59e954949e602206a852d4e4460bb34dfe9c2858e49a10c0
  | 15 => 0xc545e91c464d5cd9d15095603f2e4295826405962f6aa18a8e76a4a84a55f105f9f196b367e1dee8f6719b78d39861d8ead1151005c1f2f9d65d2bff47debdd8f7403e37891ea26b282371a7f80531e59b5c756f6da8e069f904bd9ac27914b28a2996ec1825a595660fb6a90c97f7fa922f153
  | _ => 0

private def denseT0B55 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x5ecfc736b9532cc9d1681b4fe1e3520b2a438e80bb465652ec30912c09f38541a9e4a1fd98b2facc981541801bd5185f517bd24d77569db029373c98d019b9515f22eaed320f142ffabc1ee37d943c78167983f66af28608ed969f664dee3d9fc2d5084854817412e55ca6def9399d4940a25bd
  | 1 => 0xd86baef0afb4b3a40e20e6877f1f36ceca50837dff1677ed0d468ac8d6ae7ca9e446c0b45b854f3984830370eddada28030578868779ede273a172bfa7dbb23a1d5fa70c9c7fd0928eb7c9fdc3fcbdd240470ac1d9665e1b4cee012c5d2a833eb51d3d0854b3e14d0bb9b8aa5edcd18481abe40
  | 2 => 0x7765d093babd2069e9d2a7d8f0dc5bf3a04f9c4185fafc1a90388146872db7c456f69ddcb630fde02fd9a3a76f12f5a947a24ebcf983ffdebf2ed3becc01cb7a79e49df3babafc0f2177d4a991f5243c751bdd03f0c391974ff07c9c82e4880ac2facd6bd05cfdb89e6c83cba3d021fd9e7bf84
  | 3 => 0xb56ad5f547c0a0534cdbe1d3efd52f4cbe81aa5fcf7b536a0dc2dbc2ba54003dfea29af11c9513a94ac3e58ab99ec9e894fac7093ed130a512e2cbd97f40b5f2272fd7609574e443469fd1ec6b7324e63cc5a2c665f9bb9597c4590093a09186272620a3dd346cb28fdf48e144060719ae4ba2a
  | 4 => 0xb72f08caab66b93ca8c73aae8409874491b655f48061dfb05ef18f382beac542b5569ea692e1d02e0363f4adced7e40fdd13c337883c1a024e5133ed30bd26ca2f45ac50ad62704f8083ff32b62692cbe62a7527979365f63cb168e48fe15ba53a20a8c5097933a7c09ffae864928abd665725d
  | 5 => 0xef6a3d5d08e3ea2da49cdbc406bac966d379a0f2270b6cfce8903ab6f3a085ac1c91bf3271455c1750122c22f1eb266a8e1fae3621466a47a747da05794b654fc1338ba3cb8481b7378236eca163bac2fd17aebf8374e88ec9ca52a9b8d10c0db1a93e39544f0b5b698f19816fa79330d1b5d1d
  | 6 => 0x26cec89390597c9282b02d47d113b15b169b0b606e09c4a20a8cef7182462784ed320da3acba28d1b9adb104ad27d925b895f7aa0f799fb30ff1ce0d4601e18e4f165e8159195f955c19d48963a6dc1204738459dde0dc3ac97387287d54497f059d2a1bb33bdf0f291bd5d425c76be77099158
  | 7 => 0xec9d34b3e5f40c354a47185e9b52fe12dc9bc454bdd4105eac67a23c6caa6ff6e24b494140960526547149dbde78c43f2c821f5f8ad7ade4095224602afee3ee9b334e140f227cd0942b4543b490624e3a2884c89afaa46fdd551efb8d5b08466348f7102354697cd8573ca5f81b9645efa003
  | 8 => 0x44cf2e89688f407f9e81e2f6f443d28f277ef28ecbf24beec79392da571b2eeca019e22a08d62dcd6b41d9d0c86f868da8523ccc69533dcd09559fb1a869ab93ae5ff3c6154ae4364ff7ddaf5b44682b7569f8ed8319ac5e73c3e2fa17809ea77e270235aa6fcc7364560f02d7f8d211b5f109a
  | 9 => 0x985faec9deaf5b729e10c2a688549462ec6c779ceb2c86a997a503534b166620c56b1cb69c3ac0f75fb3d3b2f5a7b886c85b6013ac8b98f4c7140585c8900417d646483e0039ad997e665cfbc22d449d3b29c450ebc7f35b33da44f4144c80abf89a7664b994bb7983618a03bb7dc928ecd81d1
  | 10 => 0x1069a23ea89c7c59a911f17ab8e0012c123e394f45001df8931e6b35a581defffdadbf86b2229227e2d60c8e5e5cfe72c96caa80b385ab0e0c1f7a7fc5d1cf8e101c1173a252af93b5c708d991ebd45bba4f9f9b220bfaf9a3c9abc6d6e46a4ad672b2451841b51e48779bd30d16b91399bb83b
  | 11 => 0x18825e4238f649704db2546c5a3dc12d378a57aad329d325a117e15db5ee220acf971df277410325c835f795ddeb1d193949d7a1df5f5804cb623b9799abd09d7104fd22474fb6c28f989930e883f90d223e671b545fcc3aeae204f04a557d0661ea1a2d5c9d8cd71515591cf8db2e93182acc2
  | 12 => 0x7221e5bb55ecce5cfbb5f103ca25be5f26dbb101caf94fc9f16e0b3fce82566b678f0a54cb02794c9ce73e59da518631491eb32dab6674073fe8b0a37b7d933b558c9959849be6ee65cc37d35ae6ee7a68070024342124b5637405f279cbd7ad20938037a37bc65ae022cf8d56aee7e65245e8d
  | 13 => 0x53576f6d6a665fa6c6814f878655c2ba44b0c3be32f219908d952f9167767ec937736030f952ef882548f4f6f7bc9c9bc4aea76bc32c81ec243d66cdd5cb71fd4ce4629e7c359f096146b869276e8a69cad96f0a08d4ebd415387ed2fb6d970d723bd958c5fd0101c4f4382fc9c6cafb3efd840
  | 14 => 0x8588f1677a3fdd266edd120a78c0195b8feed050804447804e52bb569c970507f4f3aafb69591e616950d0165306078680419218668e6f79ecfb7f066cdc1f35f39f91836076dd64045a2fb22e534c8f938322ec14895451de91c4f756daa61026fa1b124112752e308ac50b9096f3f08b1de37
  | 15 => 0x3c477b76b1972edf48ee7a924c35db4873febf740b53cc574d03ddc4fc565d179d1213964b8e24c734e40a8969523421cd3d8c5f170ecda8c493184e58e9fb52cc78ef2477ff08a33c7c0a6f806c8ee8a0da300af03138976f2e79714b9788dd4f600a829d1925b4b062d04129dddf23f3e22d3
  | _ => 0

private def denseT0B56 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xaab90f99039e7b8d4f536b5c0f7d24ca3042b18c3f0324a368e82d9038f6e7094327458ff8fd72288cabc21cb4cec846ce06e2e2f33043536466dcc1f4d345a6a692df0e975db35f824edac130c9a443afb68621d2f5ee1be40718b079b36d0576850b3bd6a3c224dd6caad64c57f32028cf989
  | 1 => 0x7b8eb917da26529dcb99cca1f9a604682ddc14d99f7c4e0c5526011aa0db0bd6e4b270684b283ceba05b9ed52ed5082dbe878408d8aeb3fa03580c58e2361af52064f38eefa670e9975852fd64fb44319ddc4157fd348ece03392b1ad544907120b940a4fae9fa75526c13075624d92d98ad593
  | 2 => 0x8a15270a636866bd992e19171bd618dfd34cffdb9f108c47117f5525f577f25ccd52fbcdc276a2cd7c1c6158c94e05eb431dded31b312d5c74e104610e783c32b755b45a7aa83e7ac1aec89eea92f574ba6e3c9ddb63264e8074e3e2f45c481cff6e2729e49a113792ea66aa40bf046423adb3c
  | 3 => 0x4adf17e4d2caacadb9113af8fb6548b8cf2c4600841c89547e79350cb2be055e2072076ab4cce69fc269ed062481cb30dda2399b6ca54fd41efc039d3fa32b644050d2774595bd502a2e6e495af519c99fd76c0faa452def8ecfb7ec71d83451950194f239e279d6144d5ef3c859683cc67f754
  | 4 => 0x2371bd0165886871ae6321cb97a5d78bc7639241c2e876a6715c3401e3d34d6cdff71a9c9b451d6d31da3aa2058841667cfc17f20a680fef7b63d45510d3ec613b799839d95594bffbb1a79861daf846c565cb3a382b1899e09ae3067aa523afbf070129c1aedfdab221a0a939da0c558c26fcf
  | 5 => 0xa8e796d04afe05838e153f3e05fe573fce1c5bec2450c86700b925d76903015804e82b23ae772a50c8743db442292e5886273798c3829c00f24aea2094297125d66cf2d984ea1d860ddbf14cf9e4b9d32b2a4cc284537ade865ef2d2fd9b24ef64a5393265ef7f0734c0a335dff5f404f8ed3dc
  | 6 => 0xe1ca51cb2accaa4fa4b42647e0bd12400e3871fdba721ddd7dffa21a6e175ba0c4b54c89ed884bc286c311fd2855349a88202ef4467f9ffa5696016cae4b10ea988bca49596b17d3af0d75d640025f25ecf03c013b159d7e670bb297064f8e451de6f63ff800b35f9994d4e3d77200eb6072239
  | 7 => 0xc6b1c7d0478060590221a716a456effa046c01de5a0b4435f5ec6364b3476c261d54c65babd50743ba8f035b19638b887c4714e0cb78b3e9ed555cd4699f7b53ecc59b568e8eb531889b0be2883eade286f16a4b563141b8c9100d2693fd9a23edb3c3ef905ab41a08a1196bcbda38cafb341a3
  | 8 => 0xba97de3678e179c2c689237ca9f4b567c9721b0fbf42446a00fa3f7e72b38073b414cb35a291f9a96ef457dcf1dcff0c706ba51a335e66b684b2773eeb8380971ec20fb6a6d44c2de85123b9c5ae50ca5c3c93b0037f513faa4acd2e9b960b9c77a1187d04121b47fb08371fab71345f9a377b7
  | 9 => 0xa953fe944ddc1b6de9e07ab6315be32665807e22eaf99d72c69329aaa939eb8cb0837277b28030dd44e5380cc6759c77ab6734fb40990382cad71c7f05683235ac64163b7d836c0a0fb2f8ff87d03a3daa9899dfa9c1bf8c5f7b64ee3cff1f7d644dbaa2d8e06674f45a0f44e8befbd78363b8a
  | 10 => 0xd37fc2c72da4a34ddc2dad8d99c377623c0e7e00b6e622201fa76e8d106e224872ec50d087231a09693dba158e784593c93d68e2b8b4a8b2dd8d6c908043f2569573dca549c3e23c6d4ab47d7ed2520bbafe1336380ae2657ac0198b6e7e12b85299cd119214de5e250f97869afa2843ffc6206
  | 11 => 0xc8eae76f470c974c4e8cd7b43dc4e475918e53b92f7bcd64f30af1f9956676327adc70bb0a64b9e16b7d0297f146897e9f9efc6f3d7d0190ba61c1d2387dbe6500beaca10b03d942ef8627c66a1032814a6f16a3131b3646b572db80165a9edbf64318e26e16e33805f6b805dbdc2b8fe1fe2a7
  | 12 => 0x96b9f1e503789bb8625731e694e75190604079194bcd25e5c3aad572d69a7b5ba414c3a18e6d2fef1407354db6090f7f601de80595ee11fb5447ac22ef085ed597ccf5d73344b1161b1ac0b50f61245b4ae7425e3cf52b82208d95a410032ef3dea3d32ecd2bf4123ecefcb42ce045348359b05
  | 13 => 0x6cd5d6538d893dafac219f7931991d2a21d15ad52508905c5894d981102b039e5c7d56dbcd4e9f0f4bb4b2d72a5a7bc8268c15e93c7a4b6c40d55bb9c5875d70e28efd62be354f3300f12466ce844155316e19331e0024f9043c8a56de98a232baa241d27c2a74a79231ab7aa61150849914254
  | 14 => 0x8cddd0ded8161cf5397e5d534e1d3a8299da1aec786aeeedb492c24db19d22ec57c9213e9fd657fa12d0d0425525b3013761eb10db0e4283585635e259dfb12facad01c59603b659c57bc907b983eebd944927a25cfaa3b62d190978d257b8c91f712878f2c7f7c8589e73b9c7ebc18a066ab80
  | 15 => 0x11c1045a52468bb6ad68d93303c048cc750b1757e067425b21b78fa6c1b8e6434c3d654b20d5115b52ff1ebb5773c7756e4b7e0a6fc0ff146cd247b1359174fae722d72532aa8a747bbbc93a508658291046a8bc6f894ea0d47d0637b6844196d56604dc4dd4767c11343ba25b422c31b019894
  | _ => 0

private def denseT0B57 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xe135db32e39a5e5486de5ebdeaa290b09e4f684d13cc80759763a78fcd02d00c237a036061c763602e16c204c199c5f10cfe230ff51b2041d858fd74601b93dba890920027aa89b29443b14732659cd87ae712092cb93ad39e4e9b34001300faf8f2462b8e6532f15f827b884b21e9b5818a981
  | 1 => 0x470a2863df01afb71013b3b2b1f24b1ed3f111e269d75402976314a97ba63aaabd1b44f0732f341cb41793c35ab49c32b4574ac9822ef36f832b9ff27eaf9397ffbbb4b608e683d65d17d9d3d4c61f811d6f68a66b3bddaf9127226d857cfd62df6e7692a99341d39e9db89dda492c45dc80f29
  | 2 => 0xfeadfa264dd3bebc5e6f49b2a60fb9745bcd7d7d59f5e75d4e054863f0bc069d91a0c2e2e98c6674ca214cd87320234cd80480776b7109f14f0a9c35f167be4689066d22037df86aca0d9a3ddb556435f0098b30ddfb19f7b8df1baffe933944c64be20a6840d0276b36db8ab9721ad2cf40122
  | 3 => 0x9dfbf4770947b0ef951406bb722b8c466c2d4fc1ccc593ff4aa6a16b77c423c36958e35085f5d538f7b22925bb202536b46f12dd11bc7b5248588557974705c52c6fee5dcf5dabdf8e729532b1f9ad793557dd17c92b3502542dad0290aa4d822e47ae7ead4e8721cb4eb9b12e843238674c3dc
  | 4 => 0xd549288c363e970edfa563afdcddaa724bdb4216e0be683840d709602f878542d3d7ae17d3144382b3f8d93fc25a9ea5e8800940b183de85762ce30cc7ab6c1d54cd1a7701591d41fc3e116e2b013cafed55aaefef3e43e62ee84bbe28036854c563adee438e4167ab455cb51da6121a88285c7
  | 5 => 0x5f1d705d2ade67dacbfbb8023bc6303eafffd2c068cc8efb71b64628c00cd9c16be9f9a146bcd9d2f0f9260f564fc39736a6ab38e8d41b9941d256c1400fd51f1d8ee23b02a4089cf502029fdc13a02c14156217080e98e5fbf7a693ed4c139f5f416cff1e6188abcb61bb64e6629918d831708
  | 6 => 0xab1b8adfd19447312f679b94db7c7d43cda60a9e16acce47831321c869c478edabad1e26ac170bc3fda4167ddf593f8721adb16be3217fa4ebe6421fce82ddbd55f79e41d5205f33663e8c73001943ecf470feea2320157e4b528744c96f04571339728fbe97ab82fadec0a38f3f73af225774e
  | 7 => 0x5c9bed41e0cf4958478250758e7ed1b1327c6bc42d7f26802d570ca7e906d45c14b36fae77728e30ae3327fb72482f99199546d41681947934248f1cc3f985b45c9329a28d447b92f2fc7ca848b986be9164bff50b3628351587cae3f42d2f7d905f69f36490c16e64af162cd3e6fdd259e0b6a
  | 8 => 0x4652fd1d04589d80d4b73c345a9bb763647bdee31c01bff600c75cca2c840c9371e87ba8c8b78b3b1ea6db965b6fa248a404f04b2bd2dfff040536751819c972cd7ddc9bd2034736cd19d6ac9ab40d428b3dced3588c7389fb33a45e316460bd29155523a3f94a3dbd37383be65b3babda844ad
  | 9 => 0x108eb41051e517234267e84d5403af8b449ab9e96b3967d6ca8aca33f93b5b850121dc5467c36900685db703c75fc119ede4080e2ff518904fcbbdd1f70da6a80ee7762d36fa71a8df53dc840cb913e2d78c6f30fa5e3043f018439590b6bc330ee57045f0da31d871d542201b013f8f918d7b
  | 10 => 0x6779e90838458db0496c73609568c126f5779d5426e37b7fd15c2ba9234ff8f40ee2caab065f968c9d5df6d79331468e5346340a98f32b3dd2740736828e7616b10a0800b50808e9dc4465556dfb6403022d00687380c125fd82579b7e29a0d149566ebd4a2f52320c9d8390a585563865467e5
  | 11 => 0x50f28c30954388b71189e644ca45d9afbd382ca8821788150b4934b968aa2ce3f0c64f30478906cf3205498135532feb15cc1edef1ecb35af4ea16d424731e15d8caa59d28246a8fcaf38f7bc6957c188590ac2963dd0fc39f0300bdb7664176d435e00a7e33662cfcd87feacddf9c82ac67d35
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
  | 5 => denseT0B53 i
  | 6 => denseT0B54 i
  | 7 => denseT0B55 i
  | 8 => denseT0B56 i
  | 9 => denseT0B57 i
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
  | 1 => 0x84210840000000000000000000000
  | 2 => 0x84210842108421084210842108421
  | 3 => 0x108421084210842084210842108421
  | 4 => 0x108421084210842108421084210842
  | 5 => 0x18c6318c6318c6318c6318c4210842
  | 6 => 0x18c6318c6318c6318c6318c6318c63
  | 7 => 0x210842108421084210842108421084
  | 8 => 0x294a52948421084210842108421084
  | 9 => 0x294a5294a5294a5294a5294a5294a5
  | 10 => 0x318c6318c6318c6294a5294a5294a5
  | 11 => 0x318c6318c6318c6318c6318c6318c6
  | 12 => 0x39ce739ce739ce739ce739cc6318c6
  | 13 => 0x39ce739ce739ce739ce739ce739ce7
  | 14 => 0x421084210842108421084210842108
  | 15 => 0x4a5294a50842108421084210842108
  | _ => 0

private def layerChunkT0B1 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x4a5294a5294a5294a5294a5294a529
  | 1 => 0x5294a5294a5294a4a5294a5294a529
  | 2 => 0x5294a5294a5294a5294a5294a5294a
  | 3 => 0x5ad6b5ad6b5ad6b5ad6b5ad4a5294a
  | 4 => 0x5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b
  | 5 => 0x6318c6318c6318c6318c6318c6318c
  | 6 => 0x6b5ad6b58c6318c6318c6318c6318c
  | 7 => 0x6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad
  | 8 => 0x739ce739ce739ce6b5ad6b5ad6b5ad
  | 9 => 0x739ce739ce739ce739ce739ce739ce
  | 10 => 0x7bdef7bdef7bdef7bdef7bdce739ce
  | 11 => 0x7bdef7bdef7bdef7bdef7bdef7bdef
  | 12 => 0x842108421084210842108421084210
  | 13 => 0x8c6318c61084210842108421084210
  | 14 => 0x8c6318c6318c6318c6318c6318c631
  | 15 => 0x94a5294a5294a528c6318c6318c631
  | _ => 0

private def layerChunkT0B2 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x94a5294a5294a5294a5294a5294a52
  | 1 => 0x9ce739ce739ce739ce739ce5294a52
  | 2 => 0x9ce739ce739ce739ce739ce739ce73
  | 3 => 0xa5294a5294a5294a5294a5294a5294
  | 4 => 0xad6b5ad694a5294a5294a5294a5294
  | 5 => 0xad6b5ad6b5ad6b5ad6b5ad6b5ad6b5
  | 6 => 0xad6b5ad6b5ad6b5
  | 7 => 0x0
  | 8 => 0x0
  | 9 => 0x0
  | 10 => 0x84210842108421084210842108421
  | 11 => 0x84210842108421084210842108421
  | 12 => 0x84210842108421084210842108421
  | 13 => 0x108421084210842084210842108421
  | 14 => 0x108421084210842108421084210842
  | 15 => 0x108421084210842108421084210842
  | _ => 0

private def layerChunkT0B3 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x108421084210842108421084210842
  | 1 => 0x18c6318c6318c6318c6318c6318c63
  | 2 => 0x18c6318c6318c6318c6318c6318c63
  | 3 => 0x18c6318c6318c6318c6318c6318c63
  | 4 => 0x21084210842108418c6318c6318c63
  | 5 => 0x210842108421084210842108421084
  | 6 => 0x210842108421084210842108421084
  | 7 => 0x210842108421084210842108421084
  | 8 => 0x294a5294a5294a5294a5294a5294a5
  | 9 => 0x294a5294a5294a5294a5294a5294a5
  | 10 => 0x294a5294a5294a5294a5294a5294a5
  | 11 => 0x318c6318c6318c6294a5294a5294a5
  | 12 => 0x318c6318c6318c6318c6318c6318c6
  | 13 => 0x318c6318c6318c6318c6318c6318c6
  | 14 => 0x318c6318c6318c6318c6318c6318c6
  | 15 => 0x39ce739ce739ce739ce739ce739ce7
  | _ => 0

private def layerChunkT0B4 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x39ce739ce739ce739ce739ce739ce7
  | 1 => 0x39ce739ce739ce739ce739ce739ce7
  | 2 => 0x42108421084210839ce739ce739ce7
  | 3 => 0x421084210842108421084210842108
  | 4 => 0x421084210842108421084210842108
  | 5 => 0x421084210842108421084210842108
  | 6 => 0x4a5294a5294a5294a5294a5294a529
  | 7 => 0x4a5294a5294a5294a5294a5294a529
  | 8 => 0x4a5294a5294a5294a5294a5294a529
  | 9 => 0x5294a5294a5294a4a5294a5294a529
  | 10 => 0x5294a5294a5294a5294a5294a5294a
  | 11 => 0x5294a5294a5294a5294a5294a5294a
  | 12 => 0x5294a5294a5294a5294a5294a5294a
  | 13 => 0x5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b
  | 14 => 0x5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b
  | 15 => 0x5ad6b5ad6b5ad6b5ad6b5ad6b5ad6b
  | _ => 0

private def layerChunkT0B5 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x6318c6318c6318c5ad6b5ad6b5ad6b
  | 1 => 0x6318c6318c6318c6318c6318c6318c
  | 2 => 0x6318c6318c6318c6318c6318c6318c
  | 3 => 0x6318c6318c6318c6318c6318c6318c
  | 4 => 0x6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad
  | 5 => 0x6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad
  | 6 => 0x6b5ad6b5ad6b5ad6b5ad6b5ad6b5ad
  | 7 => 0x739ce739ce739ce6b5ad6b5ad6b5ad
  | 8 => 0x739ce739ce739ce739ce739ce739ce
  | 9 => 0x739ce739ce739ce739ce739ce739ce
  | 10 => 0x739ce739ce739ce739ce739ce739ce
  | 11 => 0x7bdef7bdef7bdef7bdef7bdef7bdef
  | 12 => 0x7bdef7bdef7bdef7bdef7bdef7bdef
  | 13 => 0x7bdef7bdef7bdef7bdef7bdef7bdef
  | 14 => 0x8421084210842107bdef7bdef7bdef
  | 15 => 0x842108421084210842108421084210
  | _ => 0

private def layerChunkT0B6 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x842108421084210842108421084210
  | 1 => 0x842108421084210842108421084210
  | 2 => 0x8c6318c6318c6318c6318c6318c631
  | 3 => 0x8c6318c6318c6318c6318c6318c631
  | 4 => 0x8c6318c6318c6318c6318c6318c631
  | 5 => 0x94a5294a5294a528c6318c6318c631
  | 6 => 0x94a5294a5294a5294a5294a5294a52
  | 7 => 0x94a5294a5294a5294a5294a5294a52
  | 8 => 0x94a5294a5294a5294a5294a5294a52
  | 9 => 0x9ce739ce739ce739ce739ce739ce73
  | 10 => 0x9ce739ce739ce739ce739ce739ce73
  | 11 => 0x9ce739ce739ce739ce739ce739ce73
  | 12 => 0xa5294a5294a52949ce739ce739ce73
  | 13 => 0xa5294a5294a5294a5294a5294a5294
  | 14 => 0xa5294a5294a5294a5294a5294a5294
  | 15 => 0xa5294a5294a5294a5294a5294a5294
  | _ => 0

private def layerChunkT0B7 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xad6b5ad6b5ad6b5ad6b5ad6b5ad6b5
  | 1 => 0xad6b5ad6b5ad6b5ad6b5ad6b5ad6b5
  | 2 => 0xad6b5ad6b5ad6b5ad6b5ad6b5ad6b5
  | 3 => 0xad6b5ad6b5ad6b5
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
  | 7 => layerChunkT0B7 i
  | _ => 0

def layer (i : ℕ) : ℕ := (layerChunk (i/24) >>> (5*(i%24)))%32

private def maskT0B0 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x39c83b874a826c100000040000000001
  | 1 => 0x2b571d0862e515804800082200120002
  | 2 => 0x1e8a8324eaa5841028001120000a0004
  | 3 => 0xbb1d27a905c64900000210200000008
  | 4 => 0x14c1501af8211c006000412000180010
  | 5 => 0x64af113a2ac01004800810200120020
  | 6 => 0x1ed85f412eb199906001010200180040
  | 7 => 0x2bd9a4f56811fc004002012000100080
  | 8 => 0x163604a2618ec9804004012000100100
  | 9 => 0x11fd29af763f11106008010200180200
  | 10 => 0x322224998bac15004810000000120400
  | 11 => 0x27f235341edce4906020002200180800
  | 12 => 0x12f7184282e2d9100040002200001000
  | 13 => 0x3c61f147f11f80806080000000182000
  | 14 => 0xc32fd0c544a61006100010200184000
  | 15 => 0x732331babc18d904a00002200128000
  | _ => 0

private def maskT0B1 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x380c3ba3febcd4000400000000010000
  | 1 => 0x17ab1c848f1f14801000000000040000
  | 2 => 0x17d7274981370100000006200200000
  | 3 => 0x2ebe244ff3a7ac900000024200400000
  | 4 => 0x3827dbe3e491ed900000000200800000
  | 5 => 0x2a50660ecd022d100000010201000000
  | 6 => 0x179e041ee19bd100000024202000000
  | 7 => 0x6abc8900ad07c900000034204000000
  | 8 => 0x24d057998e4965100000024008000000
  | 9 => 0x113c00a377a545100000034210000000
  | 10 => 0xaf97c146d971c000000032020000000
  | 11 => 0xdda241a6699c1800000024040000000
  | 12 => 0x242f4b9b3fe7ac900000026080000000
  | 13 => 0x15dfc0e4e0c52d800000030300000000
  | 14 => 0x15a2e9a2de5155900000030400000000
  | 15 => 0x5badef64aeea9800000024800000000
  | _ => 0

private def maskT0B2 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2a7658db0a80d0900000021000000000
  | 1 => 0x240eba02f56fe0800000008000000000
  | 2 => 0x36a2b5a84292bc808000000000000000
  | 3 => 0xe7e17e7021f34810000000000000000
  | 4 => 0x201087051967ec120000000000000000
  | 5 => 0x71c124b4a38ac140000000000000000
  | 6 => 0x32f14b0d84e031080000000000000000
  | 7 => 0x12b4306a676aa9200000000000000000
  | 8 => 0x94ddd6d90bd3d400000000000000000
  | 9 => 0x2eac576f68bde2000000000000000000
  | 10 => 0x16fadf9f90019a90cb30820000080001
  | 11 => 0x4b625b7763735b0e4700000000c0002
  | 12 => 0x3c63d6c48d5e56789390824000140004
  | 13 => 0x2603cc5ecf50aeeeb2c4804000080008
  | 14 => 0x1989bf465df75837ab56824000100010
  | 15 => 0x452c9ea5e6b1c733274824000040020
  | _ => 0

private def maskT0B3 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x18916493f8c345266ed6004000140040
  | 1 => 0x1b4d44fcae6d597335e2000000180080
  | 2 => 0x2fcae92b15220ee91ab6004000100100
  | 3 => 0x1d9aff8c339536cc8ab2820000100200
  | 4 => 0xa565134d59da8fcb062800000040400
  | 5 => 0x3c14519daa15e7c0b8748040001c0800
  | 6 => 0x3efc0beba355299ae3e40000000c1000
  | 7 => 0x29f969e3fcc29b260ca6024000182000
  | 8 => 0x351539fb421f0650f7e20000001c4000
  | 9 => 0x1cfe1290f9131dc8bed0020000008000
  | 10 => 0x3dd21fabeb335359f460000000010000
  | 11 => 0xf342c474afe6097aad6024000120000
  | 12 => 0x2abdc31604605c23c7602c000200000
  | 13 => 0x38241c44f2f82fd7d042018000400000
  | 14 => 0x3aebbc2c1fa432ed2a90810000800000
  | 15 => 0x1769189cb9c0c7ce2110008001000000
  | _ => 0

private def maskT0B4 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1d5f157e747c35e3be32018002000000
  | 1 => 0x3048a1d2f58a872c208402c004000000
  | 2 => 0x3305367bec87c5f420d482c008000000
  | 3 => 0x1d1d955ff8e177875c4202c010000000
  | 4 => 0xd2dad6b39a654ce686824020000000
  | 5 => 0x3e76fe4d8ee6b47726c0000040000000
  | 6 => 0x3a76289c63199588ebb4814080000000
  | 7 => 0x217b3436ae9641b4bfa6020100000000
  | 8 => 0x1b9e76811f06726813d4818200000000
  | 9 => 0x69758e43edd23a6d012814400000000
  | 10 => 0x27f9570957d00aeec202824800000000
  | 11 => 0x21f12a957b99711ceed6021000000000
  | 12 => 0xcadcd1fc81a04d097d481e000000000
  | 13 => 0xa4c29f9270595a8d2e4840000000000
  | 14 => 0x16f1bdd746939a75e902080000000000
  | 15 => 0x37c05b040c7d2221a812100000000000
  | _ => 0

private def maskT0B5 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x32c32c97877bc2affbf4a00000000000
  | 1 => 0x2dff7a6daa646ddb3804400000000000
  | 2 => 0xc86feea31a1e36d3597000000000000
  | 3 => 0xdb4c29c5c5681e29318000000000000
  | 4 => 0x1e348681bd2c8a0028000008001
  | 5 => 0x157a00f4e2ee7b0013000018002
  | 6 => 0xe3553e8f428bc0013000100004
  | 7 => 0x1f5aceed089bf5003b000018008
  | 8 => 0x34ac68510eeb85013000100010
  | 9 => 0x1c240c56d02b4003b000018020
  | 10 => 0x448e1f32ffc36003b000110040
  | 11 => 0x38446e4c66a571028000110080
  | 12 => 0x40bd280ce674013000108100
  | 13 => 0x5e6e4377a4bbe003b000100200
  | 14 => 0x61e3b40d141a4403b000008400
  | 15 => 0x2bf50b1a376034013000100800
  | _ => 0

private def maskT0B6 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x8d4660668f4b5028000001000
  | 1 => 0x8c71aaca12d15501300011a000
  | 2 => 0xd1cdebe901bc0101300010c000
  | 3 => 0xe6e6f0e8521a21013000120000
  | 4 => 0x1e1de78394e2c4013000040000
  | 5 => 0x9c6af29731da6103b000080000
  | 6 => 0x1d5678759e70d34029000200000
  | 7 => 0x8c09d6e6e7e1c100b000400000
  | 8 => 0xc1b5ad9db1da75003000800000
  | 9 => 0x8bd2d41ef22d65008001000000
  | 10 => 0xa0ec77e0a79d80018002000000
  | 11 => 0x1e3d126eaeeed54013004000000
  | 12 => 0xfb9422f0b2dc10029008000000
  | 13 => 0x6941820127b3b403a010000000
  | 14 => 0x15ce8f4f802e921032020000000
  | 15 => 0xf2de7be9b5a56501b040000000
  | _ => 0

private def maskT0B7 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x124c4d63405800000a080000000
  | 1 => 0xe76a16d612b3b4033100000000
  | 2 => 0xa0cb0f46da3f75018200000000
  | 3 => 0x74c4e670eac924030400000000
  | 4 => 0x1b0dc9307a4d2c1032800000000
  | 5 => 0x1c32c2f15c9727002c000000000
  | 6 => 0xa6517aa4437f4040000000000
  | 7 => 0x9a267a24648184080000000000
  | 8 => 0x3a97aa38e0f95100000000000
  | 9 => 0xdedaa8274fd755200000000000
  | 10 => 0x15811df741058f1400000000000
  | 11 => 0x1d63dd836c16674800000000000
  | 12 => 0x118bf995fd74122000000000000
  | 13 => 0x121a04cce60e5c8000000000000
  | 14 => 0x992e140000ecc4fc158028000080001
  | 15 => 0x299b47d00006c2fdde0403a000080002
  | _ => 0

private def maskT0B8 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x14738e00000de84d568c000000100004
  | 1 => 0x172d5540000c397648b0028000080008
  | 2 => 0x33757e9000061be67048012000180010
  | 3 => 0x21658a90000533d372d2012000080020
  | 4 => 0x3c937290000f5d6ea292012000100040
  | 5 => 0x219f374000022dc15e7c028000100080
  | 6 => 0x37c22940000e9280c4ca028000100100
  | 7 => 0x1ef8e1d0000980bf5fbc03a000180200
  | 8 => 0x1e857340000648b1f9d8028000080400
  | 9 => 0x2e2269d0000f1839b2ee03a000100800
  | 10 => 0x361c4940000226ed7744028000001000
  | 11 => 0x226e329000073fae55aa012000102000
  | 12 => 0x29ce9000048ac85970012000104000
  | 13 => 0x11f4bf4000061e4dabde028000008000
  | 14 => 0x4c71a90000bec9449ac012000090000
  | 15 => 0x311530900009edbe293c0120001a0000
  | _ => 0

private def maskT0B9 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1a99ae00000cac697744000000040000
  | 1 => 0x25142ab00016ab945976016000200000
  | 2 => 0x2361f950002a8761232802a000400000
  | 3 => 0x2e4d1230004c510c1a10006000800000
  | 4 => 0xb69e6b00083d7cc16ca016001000000
  | 5 => 0x32720110010ab08e96ca022002000000
  | 6 => 0x368d79200207aeb0dfc6024004000000
  | 7 => 0x24fd5bd0040635cb177003a008000000
  | 8 => 0x2f9114400804491145d0008010000000
  | 9 => 0x1b11f440100f6927d044008020000000
  | 10 => 0x205d87602009655d153402c040000000
  | 11 => 0x235133c0400987d2ff16038080000000
  | 12 => 0x3e0874d0800c0861259801a100000000
  | 13 => 0x3cbfb63100062b17773e006200000000
  | 14 => 0x17648ee20004ae7058cc01c400000000
  | 15 => 0x1b6c6fd40000716d49aa03a800000000
  | _ => 0

private def maskT0B10 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1f2147480009f0676866029000000000
  | 1 => 0x64adc00000076a311ee040000000000
  | 2 => 0x31e08a000001da2d44e6080000000000
  | 3 => 0x18ea420000022ddb6786100000000000
  | 4 => 0x3d84ea0000096b191cf4200000000000
  | 5 => 0x8b5da00000d632d93b0400000000000
  | 6 => 0x19357c0000002582ae1e800000000000
  | 7 => 0x12802c00000c63d8cfa7000000000000
  | 8 => 0xee1d161ef3daff470bc025000080001
  | 9 => 0x24cdbc101b316aef42cc00c000040002
  | 10 => 0xd849bf6cdb90a26d358029000100004
  | 11 => 0x3aace132274759b84f940250000c0008
  | 12 => 0x29eb72bb8351f8dcdc10029000100010
  | 13 => 0x230fb4ea4d72eaed5148029000040020
  | 14 => 0x1d60a4358b24a8a91f84025000140040
  | 15 => 0x2f5590fecb6890e41a2c025000140080
  | _ => 0

private def maskT0B11 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x34aa6279f0325a99fb8025000100100
  | 1 => 0x34b55cfcdb00c2576f780290001c0200
  | 2 => 0x1adde6d5eabc99f9d174000000000400
  | 3 => 0x26bd64a2224fc2593368029000140800
  | 4 => 0x39779146c4be5de400000290000c1000
  | 5 => 0x255ac8dc797166324184025000102000
  | 6 => 0x7362f11c4e6628bbd780290001c4000
  | 7 => 0x125d76aa1ec2935db0200290000c8000
  | 8 => 0x239f5d6ca5b21ad757e8000000050000
  | 9 => 0x2d42dac53e04ebb6fdd800c0001e0000
  | 10 => 0xfb05feeed6d4117f568005000200000
  | 11 => 0x3572ee11511eb2bb9f70010000400000
  | 12 => 0x1170772b4ad40f1d8298039000800000
  | 13 => 0x8017f58d338a9dfd54c00d001000000
  | 14 => 0x31ac52174bf44514c17001d002000000
  | 15 => 0x33053f27445f9a4f9ad8021004000000
  | _ => 0

private def maskT0B12 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x37b7b18a002a4d6c3d04029008000000
  | 1 => 0x1f541c9b0c17cb8700f400d010000000
  | 2 => 0x2438a5e19e67f02977f0021020000000
  | 3 => 0x2b1ec7387e8f1831aefc005040000000
  | 4 => 0xfaf9aa7c9ab3ae6c688030080000000
  | 5 => 0x25a52ff5d773384bd288001100000000
  | 6 => 0x38155efb7c40b157f5a0031200000000
  | 7 => 0x5ee74ce3c85661d20ec011400000000
  | 8 => 0x17f80908e3b489020bb8005800000000
  | 9 => 0x1cc224244d98b9897c4801e000000000
  | 10 => 0x2b5e9bafc60373264d24040000000000
  | 11 => 0x223aa1fd589d0d292c1c080000000000
  | 12 => 0x214427a60989460b88b8100000000000
  | 13 => 0x18335dad282ac8536624200000000000
  | 14 => 0x3b5872bd5ba9a614bb80400000000000
  | 15 => 0x2d6a4a8ccc02cc02ccb4800000000000
  | _ => 0

private def maskT0B13 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb8501580a33e7e00835000000000000
  | 1 => 0xae3c6b94791abb1989a000000000000
  | 2 => 0x37f094fdf6d25c800400040000010001
  | 3 => 0x37bc41d3919abd0069000b6800010002
  | 4 => 0x161186b7ee8281800900124800100004
  | 5 => 0x324b487ada3908a00000212000090008
  | 6 => 0xb49abe61d91f5000900424800100010
  | 7 => 0x107c1bad77e8dc800000812000090020
  | 8 => 0xd497bfa7d0801a06001012000110040
  | 9 => 0x33b022fa294020202902024800180080
  | 10 => 0xe8c37dfa0d59c802d04024800190100
  | 11 => 0x2807b3af3c5a7d206008012000110200
  | 12 => 0x3e5c381515e055000410000000010400
  | 13 => 0x395fda19cfbf3c800920036800190800
  | 14 => 0x263149d44a5df5006940036800011000
  | 15 => 0x160a4ffce8c374806080000000182000
  | _ => 0

private def maskT0B14 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x29974d6e451f1da06100012000114000
  | 1 => 0x673851a76f00a06b00036800018000
  | 2 => 0x33935adcc411a1204800000000120000
  | 3 => 0x51f2ceee875bda01000000000040000
  | 4 => 0x110fa33d05015c006500072800200000
  | 5 => 0x2565aee6712300802100090800400000
  | 6 => 0x3a765041c9617d202000110000800000
  | 7 => 0x22929d0b51829c800000200001000000
  | 8 => 0x2091f23d20ed08006800434002000000
  | 9 => 0xb63a2bfad2fdc804800824004000000
  | 10 => 0x1ff8dedd8ec1bd200101000808000000
  | 11 => 0x3c071065b6d4e0804802024010000000
  | 12 => 0x3e569b0f5844b4a02d04016820000000
  | 13 => 0x28afa98eb50c0000108000840000000
  | 14 => 0x1a2b45ebb62849804c10026080000000
  | 15 => 0x2179370d1ae97ca00920004900000000
  | _ => 0

private def maskT0B15 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1994f7af9e2da1206940034a00000000
  | 1 => 0x1b554ac7ab8609006080030400000000
  | 2 => 0x1a4cdefd5ef180204200021000000000
  | 3 => 0x3d71d76ee3bce1001000008000000000
  | 4 => 0x23f7f831811920808000000000000000
  | 5 => 0x36a199367ca969a10000000000000000
  | 6 => 0x3c4fad674257fc820000000000000000
  | 7 => 0x36c9fb61ac357da40000000000000000
  | 8 => 0x20457b67e38a98280000000000000000
  | 9 => 0x90a67fb98bb8c900000000000000000
  | 10 => 0x1c1890f45336a1400000000000000000
  | 11 => 0x1192a44db2ea8a000000000000000000
  | 12 => 0x1de15741271abd6d3e60000000010001
  | 13 => 0x25f3dd1290b0e872880000000080002
  | 14 => 0x1ee277e8cc0e9e7db304004000190004
  | 15 => 0x286b6b5c29621f119724000000000008
  | _ => 0

private def maskT0B16 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x234b53c2ee043fa497d0032000110010
  | 1 => 0x23e6968fdc8499c1c0f4036000080020
  | 2 => 0x8bd638624c07c7ef310036000110040
  | 3 => 0x3a6cb3be8bd0df721d80036000110080
  | 4 => 0x86be0a0abae7ea54b08004000100100
  | 5 => 0x25c15e1f39ec5498aee8036000110200
  | 6 => 0x33443870b687bd3a474c036000090400
  | 7 => 0x25f0f7c67440811fbe74036000190800
  | 8 => 0x2e50b999bbf3d071a44c000000081000
  | 9 => 0x1defb1e0a8a884a907d0036000112000
  | 10 => 0x340e5cf18050b895d1b8000000194000
  | 11 => 0xdbba47d4837b228b9b4004000018000
  | 12 => 0x301203a9a460e7a38d70032000120000
  | 13 => 0xd738d272db1da8eddf8000000040000
  | 14 => 0x20a8291da0b2210f9730013000200000
  | 15 => 0x137b32723f675e378088010000400000
  | _ => 0

private def maskT0B17 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x15d3e2aab89cbbbc64d4031000800000
  | 1 => 0x273e1029ebb10ad9cc50016001000000
  | 2 => 0x39ec5f9b649b12334d90010002000000
  | 3 => 0x3b31a4b8cca3c58c467c037004000000
  | 4 => 0x649cd6339a7563e6eec005008000000
  | 5 => 0x2ce0421f197586db7230013010000000
  | 6 => 0x3f7c2bb846a1983f9c28024020000000
  | 7 => 0x148cf521ab5d0667894013040000000
  | 8 => 0x260a6aa8d987b456db80035080000000
  | 9 => 0x2b0c5ea606c481a1db94012100000000
  | 10 => 0x688f19957ed79830088010200000000
  | 11 => 0x1bbbcb34a718884a3e1c014400000000
  | 12 => 0x38f026bdb3674612e4bc024800000000
  | 13 => 0x44750ef8ba948897928008000000000
  | 14 => 0xcfbbbcf731290f6feac040000000000
  | 15 => 0x18b140faab0e64897cec080000000000
  | _ => 0

private def maskT0B18 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2c7b47981df4b63c1b40100000000000
  | 1 => 0x17b121e8b9963300e4d4200000000000
  | 2 => 0x2baf59987e5f24acc864400000000000
  | 3 => 0xcbf0ca72b11c18bbeb8800000000000
  | 4 => 0xf933779649574c96ad9000000000000
  | 5 => 0x84714f1017c3d8ecd22000000000000
  | 6 => 0x1e140ef0a07c50b01af0000000000001
  | 7 => 0x3f26a5f93529b0c5b4c6000000080002
  | 8 => 0x2ef89177c484c7be2d8e000000140004
  | 9 => 0x330b3b9859df1185b2c60280000c0008
  | 10 => 0x610d83086c16799b0aa028000180010
  | 11 => 0x87160438b2331dfb520280000c0020
  | 12 => 0x34fb49a7da416db10000000000180040
  | 13 => 0x3d15f7e8afbe0bb6f0c60000001c0080
  | 14 => 0x31ecf98f67ce0eed7112000000180100
  | 15 => 0x23a7ad1d3d6544feb686028000100200
  | _ => 0

private def maskT0B19 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x211c8f08e47ade61d046028000080400
  | 1 => 0xbe7125f3899d807be1c0280001c0800
  | 2 => 0x3738a1b9c565efc49b8000000081000
  | 3 => 0x143f22a1f91e6e8497fe0000001c2000
  | 4 => 0x3a1611d0b08947b3eaac028000104000
  | 5 => 0x2e21d7710ebcc97b5c06028000048000
  | 6 => 0x138f749c7ba97b541508028000090000
  | 7 => 0x1ce1cae70e562b9cf1a4000000160000
  | 8 => 0xfd8ae7ec574c6c88b5e02c000200000
  | 9 => 0x3551e3aa8f14900f930c03c000400000
  | 10 => 0x1289a6944d35bdc0c2b2034000800000
  | 11 => 0x3a24f9d127c81b85e28402c001000000
  | 12 => 0x3648f7b247b72116fde0034002000000
  | 13 => 0x2680cf3406774560ea1e000004000000
  | 14 => 0x22379911bcc81e1df0ba02c008000000
  | 15 => 0x30b80185c009dfe9f074008010000000
  | _ => 0

private def maskT0B20 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2ce8ab67455073057c34000020000000
  | 1 => 0x2f6b017b58a0ccb4ae6024040000000
  | 2 => 0x3a723dd391e937631d5c014080000000
  | 3 => 0x30dbd786debb277b39b0020100000000
  | 4 => 0x1b8322dc191a2d5301fc03c200000000
  | 5 => 0x20fc2d07e16c4d32dc2a014400000000
  | 6 => 0x2b42175a10b224c093c2008800000000
  | 7 => 0x17a150bd0a82c4bee37800d000000000
  | 8 => 0x1ecc84f664241ec89c6e03a000000000
  | 9 => 0x19ef16cf78b9015942e6040000000000
  | 10 => 0x1c8bc6e45e3947ad70aa080000000000
  | 11 => 0x2e6cdf7366f4ba55274c100000000000
  | 12 => 0xf1de078ef7ac3ed268200000000000
  | 13 => 0x31365189b281b1f5813c400000000000
  | 14 => 0x195d02cae81bfd48a4ae800000000000
  | 15 => 0x175a58bad2c18df5e95d000000000000
  | _ => 0

private def maskT0B21 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x4df4c12ae15f9020bc8112000080001
  | 1 => 0x13275438e28fd8025ac0112000000002
  | 2 => 0x34614f99776a2100490800c000180004
  | 3 => 0x164ea972460168002f40012000080008
  | 4 => 0x1c1c762d072fb1025988112000002010
  | 5 => 0x465adb6030bc100620801e000182020
  | 6 => 0xdfa3b88a14f1021b8811e000180040
  | 7 => 0x33a3f9482e9149002e48012000100080
  | 8 => 0x21fbe0a0094434421da211e000180100
  | 9 => 0x331345cab5849d4200ea112000100200
  | 10 => 0x32f194650befd80242c011e000000400
  | 11 => 0x25776344c19e51027288100000082800
  | 12 => 0x16f81eab5d512540352a01e000081000
  | 13 => 0x434700435eaed40736a012000104000
  | 14 => 0x1c5f4e86268eb0027580100000088000
  | 15 => 0x1b64b769097b1d007ce8012000090000
  | _ => 0

private def maskT0B22 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1df0da675c6be000630001e000120000
  | 1 => 0xb352bccf72e980250c01120000c0000
  | 2 => 0x38c22480f70f15429caa132000200000
  | 3 => 0x2916cbccf4248143140a118000400000
  | 4 => 0x3fb903b502a868023b4003c000800000
  | 5 => 0x3f1fd53db6b941465a0a108001000000
  | 6 => 0x246df61266f5e14a330a10e002000000
  | 7 => 0x213b6185ad3e6550632a008004000000
  | 8 => 0x387536ab98bbcd60166a024008000000
  | 9 => 0xdadeef80f62d84206c0108010000000
  | 10 => 0x252d1af5331fe180430801e020000000
  | 11 => 0x3ff510e33f3b74004ba8008040000000
  | 12 => 0x47bb1dd589ede422ae212e080000000
  | 13 => 0xd56435acd81d022cc8136100000000
  | 14 => 0x2899b477eb90b50019e800e200000000
  | 15 => 0x2bd893f6f5ed9d40546a01c400000000
  | _ => 0

private def maskT0B23 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x35d1f5fa10ca60004200008800000000
  | 1 => 0x13a22d117a4e0942464a11b000000000
  | 2 => 0x2ad67381fc5c7c40e3e2040000000000
  | 3 => 0x1d29e460dbee6943734a180000000000
  | 4 => 0x27fd6a48f56af80457c0200000000000
  | 5 => 0x39a5d1b95db72948394a400000000000
  | 6 => 0x12a98e99d7b49d1024e8800000000000
  | 7 => 0x27d0dcd86f0d192068c9000000000000
  | 8 => 0xf2018d5026420802104000000000000
  | 9 => 0x8d7366a3b0a8a005450000000000000
  | 10 => 0x300796ca20c791257c8602d000080001
  | 11 => 0x22712325737c845aa0c025000040002
  | 12 => 0x1a89869ce13d7e45dee008000100004
  | 13 => 0x3e82f5e2307738b974c002d0000c0008
  | 14 => 0x397f640c63e387112ec6000000100010
  | 15 => 0x241acfb36eda22e38922000000040020
  | _ => 0

private def maskT0B24 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2d029e8d826becc7d56202d000140040
  | 1 => 0x3d8e821940b4baa08eca025000140080
  | 2 => 0x3841b908f2d5ad2e1dee02d000100100
  | 3 => 0x113bce5095d35eb3c88a0000001c0200
  | 4 => 0x1d3d2ec74a59a84bf728008000000400
  | 5 => 0x10d16c17bbe831db300c000000140800
  | 6 => 0xd7de8ea23f06b3a29e20000000c1000
  | 7 => 0x1b527682e49a45dda40a025000102000
  | 8 => 0x15eccdcfede3a6f347ee0000001c4000
  | 9 => 0x191ccb5131ba5672d28a0080000c8000
  | 10 => 0x2ed8134c94dcee04aec0000000050000
  | 11 => 0x397f9357d1d862e4c9e802d0001e0000
  | 12 => 0xcfe8893982066e21aca029000200000
  | 13 => 0x1006e94f01aa41bd72003c000400000
  | 14 => 0x264c20d39e9d3e48256a039000800000
  | 15 => 0x20bfa2e3e19e37a8b0c2021001000000
  | _ => 0

private def maskT0B25 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x5ded292eaf053b48920031002000000
  | 1 => 0x777bfa2e55b8cefd28800d004000000
  | 2 => 0x30c7b19433ae31ec1000005008000000
  | 3 => 0x39841a59fb543502d2a00d010000000
  | 4 => 0x25b6980ad999e9a484200d020000000
  | 5 => 0x943dc3a0bb82df753e8029040000000
  | 6 => 0x232f907fbdc4ffe461a001c080000000
  | 7 => 0x26ebf888a23e1fbe3d2a02d100000000
  | 8 => 0x3b5b8986090d96a21a0201d200000000
  | 9 => 0x2e1e7e087b6edf9faac0011400000000
  | 10 => 0x238a898d42b09fa243e8029800000000
  | 11 => 0x330cf9814cba5b7e34c201e000000000
  | 12 => 0xae916981e8caa4c708040000000000
  | 13 => 0x3296d8258e71f1a3eaa080000000000
  | 14 => 0x2ba7e11f4e18edba1022100000000000
  | 15 => 0x21d21b8ffd3b09c29bea200000000000
  | _ => 0

private def maskT0B26 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3b5872bd5ba9a614bb80400000000000
  | 1 => 0x23b75b56cd5a3cc69688800000000000
  | 2 => 0x17495c6699916f3725eb000000000000
  | 3 => 0x252d1b1c46b34946d010000000000000
  | 4 => 0x37184b3a724e2f1568ac024800120001
  | 5 => 0x3e87048b28019f1617c4020000120002
  | 6 => 0x15bfed90df22833cd748000000060004
  | 7 => 0x1a87380f3940e61fa6c0000000040008
  | 8 => 0x11f8882ad56af42da144080000020010
  | 9 => 0x1a88b92577ca6012ec4c000000040020
  | 10 => 0x2da1ac399945af848524084800140040
  | 11 => 0x284a9b154cd99adb0dc4020000060080
  | 12 => 0x39f67fcf13f1ac01882c020000020100
  | 13 => 0x14385a6672fb2305a9e4084800060200
  | 14 => 0x3b5dd24b9e951ab72c4c024800120400
  | 15 => 0xadfb5477da29bc4dc40024800060800
  | _ => 0

private def maskT0B27 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1cf6f237879b0db4fc4c020000121000
  | 1 => 0x1af93cc8e9e90fa44748020000102000
  | 2 => 0x23d2ae1f055ad11a4964084800024000
  | 3 => 0x1e9ec7b1d61f4a679b480a0000128000
  | 4 => 0x3ceb97827cbe58899d48000000010000
  | 5 => 0x11a6d58b16a765e3e188020000080000
  | 6 => 0xdfc128d40b8040eb8a80b2800200000
  | 7 => 0x354c0d9b6063d2700c40006000400000
  | 8 => 0x1671c76aae1614bd76480b4000800000
  | 9 => 0x3c1b4297ca10d691ddc4032001000000
  | 10 => 0x351265780320ca993424034002000000
  | 11 => 0x292d9533ec87c1379ea00b2004000000
  | 12 => 0x17cb259dc92d88a3c8e4016808000000
  | 13 => 0x155b4dc1fa63fa81dac8024010000000
  | 14 => 0x3433aa639d5d5d497080016020000000
  | 15 => 0x7b523d6a9f377d0fac032840000000
  | _ => 0

private def maskT0B28 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2c8e03b7d037adf134e80b0880000000
  | 1 => 0x160042ab223cc37e06c80a0900000000
  | 2 => 0x38423bef21df87508b4c034200000000
  | 3 => 0x20fc6082e309c59f6140002400000000
  | 4 => 0x34152f388972fb30a608037000000000
  | 5 => 0x6e4873ab417107fc364088000000000
  | 6 => 0xaaff40ccfb737d1166c040000000000
  | 7 => 0x197c6070734ea68caee4100000000000
  | 8 => 0x188fabecddd937974a28200000000000
  | 9 => 0x168abefb64f0011e93cc400000000000
  | 10 => 0x175e346743aa2dce376c800000000000
  | 11 => 0xcc8e7e9f336147e63ed000000000000
  | 12 => 0x207aee6bcf79019eda06000000000000
  | 13 => 0x660725a4390106c1a50000000000000
  | 14 => 0x1d469b5b8011ae4842e0000000050001
  | 15 => 0x16d88d96242068905589012000050002
  | _ => 0

private def maskT0B29 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1b4e754904423626e241032000150004
  | 1 => 0x32769ba4a48ee4bf8929032000010008
  | 2 => 0x277911ef21056143abc8000000140010
  | 3 => 0x53d2714020f2130a500032000010020
  | 4 => 0x3f1392d8800944da5621012000110040
  | 5 => 0x2e0a77eb6800aaee1ad8012000110080
  | 6 => 0x2cc3567290036ced18a0020000110100
  | 7 => 0x1ddafe00040d15829409020000150200
  | 8 => 0x34248e112407b61e9459000000040400
  | 9 => 0x127adc9fe000f26967d8000000100800
  | 10 => 0x1c6dfbb0c402055cdc71012000051000
  | 11 => 0x23cdade964017a76fad9020000102000
  | 12 => 0x3fc75afe24051454ba89020000114000
  | 13 => 0x360f9f54200ab0178308020000058000
  | 14 => 0xf9121bdc400b001b771000000160000
  | 15 => 0x16fb2696e003d57d45b8020000080000
  | _ => 0

private def maskT0B30 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2f7c738f40114356f2d0008800200000
  | 1 => 0x15a74152842afbaae4a1018000400000
  | 2 => 0xa38e7484441fe65871102a800800000
  | 3 => 0x7c68ebfa48fcbe02fe9000001000000
  | 4 => 0x1eca8ea7250c34c699c9018002000000
  | 5 => 0xa2c1192860494b701a1032804000000
  | 6 => 0x2de9a61ac408827863b0032808000000
  | 7 => 0x1d4f70fc2c0aaa5ebf09000010000000
  | 8 => 0x36ccd5a79402605c8de1032020000000
  | 9 => 0x783f54ba40fb4c5a6e103a040000000
  | 10 => 0x26d54ad1840a34f14471038080000000
  | 11 => 0x21f5fda5e40aed5a2959020100000000
  | 12 => 0x3c1a15b7640aa28bdd99018200000000
  | 13 => 0x2752a55a80093e7c3620030400000000
  | 14 => 0x22cc6e22a00669dcbea801b000000000
  | 15 => 0x2017e7b8800a9864362002c000000000
  | _ => 0

private def maskT0B31 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2104b9bf6017c51fefd8040000000000
  | 1 => 0x25fbc174202702a65d08080000000000
  | 2 => 0x139fa63b844e64b28ee1100000000000
  | 3 => 0x287c6257008f4bf715c0200000000000
  | 4 => 0x2d336292450d55e62491400000000000
  | 5 => 0x30327ad02204cb55b408800000000000
  | 6 => 0x1e4279470800ad0051c2000000000000
  | 7 => 0x38f1299d10079699e744000000000000
  | 8 => 0xeb65e692560000057fa01a0000c0001
  | 9 => 0x204cc0b6e3b000000f48028000000002
  | 10 => 0x1c232da48370000064b801a0001c0004
  | 11 => 0x10dd9d7fbcc000003fb20280000c0008
  | 12 => 0x169e0412379000005d30032000140010
  | 13 => 0x2ea7404335a000005a2a028000080020
  | 14 => 0x369e51fdf99000005010000000180040
  | 15 => 0xcf5c7fe7d9000000108000000180080
  | _ => 0

private def maskT0B32 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x27708fa0505000005ea0028000100100
  | 1 => 0x1551bae562600000510a01a000140200
  | 2 => 0x19513e6a97000006f52000000000400
  | 3 => 0x386fc90ddb6000003bc8028000180800
  | 4 => 0x4cec0c4360000062b80320000c1000
  | 5 => 0x24f1f32755b000003280000000182000
  | 6 => 0x2fe8fa2643000005002032000184000
  | 7 => 0x21ad8be78960000038ba0000000c8000
  | 8 => 0x1750558368000005fba01a0000d0000
  | 9 => 0x220cabecc2a000005e50000000160000
  | 10 => 0x3bb27c0ed8e0000005fa032000200000
  | 11 => 0x330068ec1310000057fa034000400000
  | 12 => 0x37ebab54184000003942022000800000
  | 13 => 0x3c8fef033be000003550000001000000
  | 14 => 0x204c622b3df00000529a02a002000000
  | 15 => 0x2576116c35e000006662008004000000
  | _ => 0

private def maskT0B33 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x6e5f89800e0000063a2000008000000
  | 1 => 0x2fb7e118d51000003c18000010000000
  | 2 => 0x349bc777c7e000005e12024020000000
  | 3 => 0x91713ddd9b0000061a0032040000000
  | 4 => 0x18320a3a0c100000045201c080000000
  | 5 => 0x1ac70c318800000058d8028100000000
  | 6 => 0x29a968e0875000005be802a200000000
  | 7 => 0x3cb59e3ba7e000000e2a030400000000
  | 8 => 0x270c8834a670000035f0032800000000
  | 9 => 0x5d8edbe1f3000005450005000000000
  | 10 => 0xd5336dae650000054f0040000000000
  | 11 => 0x15ab323d24b000003e4a080000000000
  | 12 => 0x26abfc29ec2000004d00100000000000
  | 13 => 0x7ecea6ffd90000038b8200000000000
  | 14 => 0x253b6815864000003d30400000000000
  | 15 => 0x3ed5a9780d8000007062800000000000
  | _ => 0

private def maskT0B34 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x20f35a1b082000000219000000000000
  | 1 => 0x294b09f3df7000002c0c000000000000
  | 2 => 0x3babeb81263ae0000000000000200001
  | 3 => 0x9ec1eccb65f09802900010000480002
  | 4 => 0xdf4de29236163004800022000910004
  | 5 => 0xcd2eae0a70021006100000001000008
  | 6 => 0x23d9c8032b1e81800000022002110010
  | 7 => 0x157f05724faa28002900000004000020
  | 8 => 0x15a769d6df140006100032008190040
  | 9 => 0x32e3192f169cca400000032010190080
  | 10 => 0xcc2cbd5f74663000000032020190100
  | 11 => 0x37ca3a137d6e49c06100032040190200
  | 12 => 0x353a6a28cf9ea2804800002080010400
  | 13 => 0x325efccab307a0406100020100100800
  | 14 => 0x3fb6111eabfd40406100010200081000
  | 15 => 0x3b2c2b7409af28c00000030400182000
  | _ => 0

private def maskT0B35 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x25429a075d9163406100032800194000
  | 1 => 0x3bab411682910b402900013000098000
  | 2 => 0xb936796641bc8004800024000120000
  | 3 => 0xd3b41e894a32ac00000008000040000
  | 4 => 0x28e6d30e9375ebc00400040000000000
  | 5 => 0x1069eb380582a2804000080000000000
  | 6 => 0x2486ba149eae6a804100100000000000
  | 7 => 0x3ca1fad948b4e2806100200000000000
  | 8 => 0x3fe0ad1b031c12000900400000000000
  | 9 => 0x1a8d0825faaa3a402900800000000000
  | 10 => 0x1ed51ad51e812a000101000000000000
  | 11 => 0x3333afa10c9902802902000000000000
  | 12 => 0x876a51913661402d04000000000000
  | 13 => 0x16f29080941109400108000000000000
  | 14 => 0x3a845d32f0a842c04c10000000000000
  | 15 => 0x34aac1e982fb7a006820000000000000
  | _ => 0

private def maskT0B36 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x26a6328d3cade2000840000000000000
  | 1 => 0x1be5546abe5a71406080000000000000
  | 2 => 0x107dcb4100960b004200000000000000
  | 3 => 0x567fd9845e5a0c01000000000000000
  | 4 => 0x23f7f831811920808000000000000000
  | 5 => 0x380d39a848f561c10000000000000000
  | 6 => 0x291ae0fe81dc60820000000000000000
  | 7 => 0x2d3016665be2e9c40000000000000000
  | 8 => 0x2ee9dbf9d7d690480000000000000000
  | 9 => 0xdcd8e2fe9da9a900000000000000000
  | 10 => 0x3c1867050fd74b200000000000000000
  | 11 => 0x15554d99c38b9c000000000000000000
  | 12 => 0xbe2019c9f796eff85c40090001a0001
  | 13 => 0x21600376bd49c51162c009000120002
  | 14 => 0x3f6001a00cd6e3163cc0021000100004
  | 15 => 0x2ae901067529835197d2021000120008
  | _ => 0

private def maskT0B37 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1080191b102dcf20210000000100010
  | 1 => 0x2fe10143572923be0fc20280001a0020
  | 2 => 0x230000e7187f4f8c5400009000020040
  | 3 => 0x387e00391b04d05132fc021000180080
  | 4 => 0x1a89007c06880bc477120210000a0100
  | 5 => 0x23e200b3b519b33d97c4028000100200
  | 6 => 0x10801c67e0e7bb35210028000080400
  | 7 => 0x113801d7fb05d77db070009000180800
  | 8 => 0x50800e336ab27179810009000121000
  | 9 => 0x2aba00bdf36a7acf55740000000a2000
  | 10 => 0x23b1000bb829cb2b9762028000104000
  | 11 => 0x26ea01e3419188904dd4000000088000
  | 12 => 0x515018b78c443b7c82a021000010000
  | 13 => 0x20b001ccce5c87816160090000c0000
  | 14 => 0x3cd90299e5aca260f9b2000000200000
  | 15 => 0x284a040993daae447094010000400000
  | _ => 0

private def maskT0B38 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x22bd09ef6fccfed0e57a010000800000
  | 1 => 0x37e510096d9fbc35bdca029001000000
  | 2 => 0x103420c7ddce9d844268031002000000
  | 3 => 0x19f041cc90a824e171e0021004000000
  | 4 => 0x12cf811d894589f6679e021008000000
  | 5 => 0x1ee4006b931e4d84bdca000010000000
  | 6 => 0x3f5e019dbfc707946eb8008020000000
  | 7 => 0x541000db44f7c511a8a008040000000
  | 8 => 0x3c860009784eb45d091c038080000000
  | 9 => 0x10470185b877806cf0ae028100000000
  | 10 => 0x1afe00a284c08f4815bc010200000000
  | 11 => 0x262b0038c26935bebcd6038400000000
  | 12 => 0x236a01e8a1069f3357d4008800000000
  | 13 => 0x1c9800e8d246b668dd30032000000000
  | 14 => 0x13cc00123a363632ff9802c000000000
  | 15 => 0x1c06022f500a2f13b80c040000000000
  | _ => 0

private def maskT0B39 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x27df04b765ecc91ecfbe080000000000
  | 1 => 0x2ef0099f2a439a6a5de0100000000000
  | 2 => 0x10ab119f2a412a442156200000000000
  | 3 => 0x3c0a219428ce8270f814400000000000
  | 4 => 0x38e6409811c43d7df1cc800000000000
  | 5 => 0x3a4780d3baaa0765748f000000000000
  | 6 => 0x2ef91038e553796e6919032000120001
  | 7 => 0x3cbff4eaee88789e31b020000040002
  | 8 => 0x1229b94d5f86e090702b032000100004
  | 9 => 0x1623587c16c6682762b032000000008
  | 10 => 0x38d40723fd3f2ae01980032000100010
  | 11 => 0x2057e7fae90ec2a1c58b000000120020
  | 12 => 0x27dd3fda8e5f231d651b020000100040
  | 13 => 0x72ee371369b424c1530012000020080
  | 14 => 0x6f11a0194dbb0600b22020000140100
  | 15 => 0x3ead93898e70e61743b1020000060200
  | _ => 0

private def maskT0B40 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x12a0eebfbf4357c1d9a1000000040400
  | 1 => 0x3c8f82b6ce5291926d88000000100800
  | 2 => 0x1479346ca74d73770701020000161000
  | 3 => 0x39be24411d6f7762359a012000062000
  | 4 => 0x16db26238ddc8aa721b0012000104000
  | 5 => 0x2cdb58993f2fbf2f1d82020000008000
  | 6 => 0x35fba95b8ae722bd7c08032000010000
  | 7 => 0x3c49df99f847ddb5dc2a020000080000
  | 8 => 0x3fe388fd08d810a4a022013000200000
  | 9 => 0x39b43c140adecd59aa92039000400000
  | 10 => 0x379d222b065cbf7a65b2003000800000
  | 11 => 0x1a2e5f6cb0bdee124518032001000000
  | 12 => 0x25a5f8ac116c09f57c13003002000000
  | 13 => 0xda0595c93498c8c749b021004000000
  | 14 => 0x3481fbe969c26b308322021008000000
  | 15 => 0x3657cd159cc5391502b0032010000000
  | _ => 0

private def maskT0B41 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2c326f593c91c57f382b029020000000
  | 1 => 0x275dbe2cf9f8b0a03099029040000000
  | 2 => 0x3ff03e0a54ffaea85f13019080000000
  | 3 => 0xe16cefd50d46f357783001100000000
  | 4 => 0x31abbd4c35f60b4083aa039200000000
  | 5 => 0xa05782fd2d3ffc8ab0002b400000000
  | 6 => 0xdab13222a1a7b9408b2013800000000
  | 7 => 0xf1978578be17a013381024000000000
  | 8 => 0x185877d5f738b9a46988040000000000
  | 9 => 0x9e65fdd3c1c90773603080000000000
  | 10 => 0x1de0cef491d0dcbd3cbb100000000000
  | 11 => 0x1ec11b87c16b8e4d9913200000000000
  | 12 => 0x2f30a2901b7f4cf3463b400000000000
  | 13 => 0x2b9f51323133765df082800000000000
  | 14 => 0x25bc46e41e1e4fe15394000000000000
  | 15 => 0x7d34298de453222aac0000000000000
  | _ => 0

private def maskT0B42 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1c6d0063e9da5296302000000184001
  | 1 => 0x6a23ecd79da83f97e1a020000000002
  | 2 => 0x2526ae819d36855f5a2a028000180004
  | 3 => 0xeab1aa3b85a5baec5b8028000080008
  | 4 => 0x395348ec0a610ae049a020000180010
  | 5 => 0x1176a67e973cfd08cd48028000080020
  | 6 => 0x722e0f1330e49a4c308028000084040
  | 7 => 0x2f83f1e337886ad6b7c8028000100080
  | 8 => 0x2c9f2592092173ae5db8000000180100
  | 9 => 0x232ab68855b0cdd19548028000084200
  | 10 => 0x322b9aeb7cd3b1bebf98000000184400
  | 11 => 0x37ff3120d1878ce2f6ea028000004800
  | 12 => 0x305709ac704ee342abf2000000081000
  | 13 => 0x1fdb289e5940985e98a0020000102000
  | 14 => 0x16ef32e9b19d9bcab5b2000000088000
  | 15 => 0x3c07f7dfdfb5daf68bf8000000010000
  | _ => 0

private def maskT0B43 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x24b561bdc30ebbd2ee1a000000120000
  | 1 => 0xa8e37127144fa85d18008000040000
  | 2 => 0xd56bfbd1de9667159ea016000200000
  | 3 => 0x20ce80f2d42f44187128006000400000
  | 4 => 0x264ae9b25f07f7e3d80203c000800000
  | 5 => 0x23fcd7a4663ceceadae003a001000000
  | 6 => 0x1898fe868ef03a287892034002000000
  | 7 => 0x1a8ecf31bc79941c8d7203a004000000
  | 8 => 0x5f36c3d3f6fab02f0a803a008000000
  | 9 => 0x33ddf0d58782e8f68ad802c010000000
  | 10 => 0x242216bf48bcb4164b92016020000000
  | 11 => 0x263b70667b8b1e60e9e001e040000000
  | 12 => 0x23868a5cbc57e2097832014080000000
  | 13 => 0x69fd589d6ac82bcf76a00c100000000
  | 14 => 0x2eff8981bc42d796d5d0034200000000
  | 15 => 0x25c85ec102f0372dff50002400000000
  | _ => 0

private def maskT0B44 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x257ce6c5e73f1c313280024800000000
  | 1 => 0x348886606c3b24d49f0a037000000000
  | 2 => 0x157dc9fbae5b177a5410040000000000
  | 3 => 0x3b023334f1bb1ff03b38080000000000
  | 4 => 0x3f66fc41ffa7b77e6eb2100000000000
  | 5 => 0x27277870734c16a2d252200000000000
  | 6 => 0x307c42974b129293452a400000000000
  | 7 => 0xeec7bca61d61d096f40800000000000
  | 8 => 0x157aa844d14a24b93bc1000000000000
  | 9 => 0x195e2ff08177b2b84e9c000000000000
  | 10 => 0x100029051d564858d84028000008001
  | 11 => 0x30005c1200918b635e4008800018002
  | 12 => 0x2000082fe9e1c295ab78000000100004
  | 13 => 0x300103f8abd9b8a7944028000018008
  | 14 => 0x2000206fb79c52dcbde4008800100010
  | 15 => 0x30040d3c6ef5106b354020800018020
  | _ => 0

private def maskT0B45 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x22008054a737a9b98fb8028000110040
  | 1 => 0x220100845f32a8316b78028000110080
  | 2 => 0x2102002342f701e70cf0000000108100
  | 3 => 0x20040096253362960174028000100200
  | 4 => 0x108002ef1d6b6b00a6c028000008400
  | 5 => 0x20100101b5d796dddc8c000000100800
  | 6 => 0x2000d2f49788a22ff4028000001000
  | 7 => 0x234001fe62341b477cec00000011a000
  | 8 => 0x2180008ae3b92346acbc00000010c000
  | 9 => 0x24000115d2b7c512e04c008800120000
  | 10 => 0x800018e44aff58d4924008800040000
  | 11 => 0x100000043530ab9587c4020800080000
  | 12 => 0x13e76a911c0423c008000200000
  | 13 => 0xe7c2e66b5f1a1002a000400000
  | 14 => 0x6c137952a0fb2c010800800000
  | 15 => 0xcd652e99c4433403a801000000
  | _ => 0

private def maskT0B46 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x156871e60352110018002000000
  | 1 => 0x2960446ca94794032004000000
  | 2 => 0x4a56978969b86403a808000000
  | 3 => 0xf5fffd7272424003a010000000
  | 4 => 0xa7413dc201934c000820000000
  | 5 => 0x1e2669c9b919000008840000000
  | 6 => 0x17e174d05f9ab7c038880000000
  | 7 => 0x816386e13b8e98020900000000
  | 8 => 0x6b644bbee22300018200000000
  | 9 => 0x2e177d4116e258002c00000000
  | 10 => 0x181c438bbe0026c021000000000
  | 11 => 0xe28c63dba997b802c000000000
  | 12 => 0x12bc55b6424d23c040000000000
  | 13 => 0x4ded5f6a96d8dc080000000000
  | 14 => 0x175180de68307dc100000000000
  | 15 => 0x17fa0fa2cb08644200000000000
  | _ => 0

private def maskT0B47 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x193be9b8c284484400000000000
  | 1 => 0x101f6fd78333f2c800000000000
  | 2 => 0xcbaf44f8381c75000000000000
  | 3 => 0x18401e62c82b0d6000000000000
  | 4 => 0x1b365e542602a1303c300040000c0001
  | 5 => 0x23cbffc3d2ee1e9773c8004000040002
  | 6 => 0x1ac2e80254e012a73b780040001c0004
  | 7 => 0x2493b8875d043ae82b120040000c0008
  | 8 => 0x3b18889585d4ac2ed982004000180010
  | 9 => 0x20fab812c740963a6cd0000000000020
  | 10 => 0x1dafa537f379bf9bb902020000100040
  | 11 => 0x1f41178e0d3c7069d5b80000001c0080
  | 12 => 0xc66b5d1b92e8dc921e2004000140100
  | 13 => 0xced0b3010b98085ef42004000100200
  | 14 => 0x13610668db5346daeac0004000080400
  | 15 => 0x2980081a7a90d3d4c69a000000140800
  | _ => 0

private def maskT0B48 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x10e8189af6c4d7b63830000000081000
  | 1 => 0x3644f1b08a5d8452c5620240001c2000
  | 2 => 0x3ebc1ab64ce5b2672830020000104000
  | 3 => 0x1b3f2bf28e1f94708c8a0240000c8000
  | 4 => 0x32cd8ed6e2f6b717a138000000010000
  | 5 => 0x3b4d61032a8819546ff2024000120000
  | 6 => 0x14a66c8e375471ba883a021000200000
  | 7 => 0x279faf32b359959afab8031000400000
  | 8 => 0x247226292db1496ddf80034000800000
  | 9 => 0x28efcbf72bafb95d4e7a016001000000
  | 10 => 0x1292760ed1c0768e2ee8034002000000
  | 11 => 0x31ad7c0e8ed07476f940000004000000
  | 12 => 0x2271613feb99ff5ca7f2000008000000
  | 13 => 0x25badef8fc77c7e3c098005010000000
  | 14 => 0x1c3f9d47706a3b835688024020000000
  | 15 => 0x2e2b9a8000f400079210024040000000
  | _ => 0

private def maskT0B49 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x17ecea3dbaa1edd55450023080000000
  | 1 => 0xbb3a5a74d2d3a693dd8017100000000
  | 2 => 0x1da2a4d356069ab0321a027200000000
  | 3 => 0x12db9d5cac0ae5600000014400000000
  | 4 => 0x124fa2de4426f22110da000800000000
  | 5 => 0x2e9759386fc9c37ff98008000000000
  | 6 => 0x2121ee4c53f2629f9d48040000000000
  | 7 => 0x2582d41b7050db82cfc2080000000000
  | 8 => 0x33f525d3393e99c9a7ea100000000000
  | 9 => 0x1ae1270223b8111da98a200000000000
  | 10 => 0x105ab719a3a8cd1d2bba400000000000
  | 11 => 0x2b7cf471375389bac238800000000000
  | 12 => 0x34a66d91011c8808d77b000000000000
  | 13 => 0x1fab5045fca22fe554cc000000000000
  | 14 => 0x2086ff0437f3935dc86c000000040001
  | 15 => 0x192124c109d60616e72008100040002
  | _ => 0

private def maskT0B50 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2ef89177c484c7be2d8e000000140004
  | 1 => 0x71b2f38597eb488f61e020100040008
  | 2 => 0xc923d6411ef017926ee020100140010
  | 3 => 0x673e9331f4a2e41406e020100000020
  | 4 => 0x20186340431f64d38d26008100100040
  | 5 => 0xfd75a3e3adca0ae070a008100100080
  | 6 => 0x32e5459f2aca5f586de008100140100
  | 7 => 0x2575146ba8a64aeb0592028000140200
  | 8 => 0x2b9e6a5c7354b8814602020100040400
  | 9 => 0xd13ed681f61c55b0520020100100800
  | 10 => 0x3dc73daeb9e28e58930c008100041000
  | 11 => 0x3238e3d14719dfb7e53c008100102000
  | 12 => 0x1ab87795c3b283c14308028000104000
  | 13 => 0x248574642ba9bcd2c26a028000008000
  | 14 => 0x33075498baa9ac6fb484020100010000
  | 15 => 0x2e052170290f93cd0e40000000120000
  | _ => 0

private def maskT0B51 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x14e32ae7995e09628d26008100080000
  | 1 => 0x10b333e59987d9f048f002c000200000
  | 2 => 0x3f174418ba0b799537e603c000400000
  | 3 => 0x2a1dddf06eaca898a178014100800000
  | 4 => 0x32e015f780222b79c46a00c101000000
  | 5 => 0x377fa01bfc0741e730c2034002000000
  | 6 => 0x2f20aa798750a75235a4020104000000
  | 7 => 0x2ff5491f2e4570f79c6800c108000000
  | 8 => 0xd0f5528f2ad5fce49fe028110000000
  | 9 => 0x1a9e75d463a01b131a6c020120000000
  | 10 => 0x31318aa9ac50ccafc9fe024040000000
  | 11 => 0xc8fdac43edb36f597d6014080000000
  | 12 => 0x143de740ef34a73071a603c200000000
  | 13 => 0x140bb4025da3806a29e2014400000000
  | 14 => 0x30cd17c268b360ffa65c008800000000
  | 15 => 0x10c248ee124292df627000d000000000
  | _ => 0

private def maskT0B52 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x38869cc434bdbbda23403a000000000
  | 1 => 0x19b24ecd927d694422bc040000000000
  | 2 => 0x813f2409f98359b95fe080000000000
  | 3 => 0x3af4ebd7a755c863c218100000000000
  | 4 => 0x181ff0c0ff80a5b41a44200000000000
  | 5 => 0x2985274c2932d062294a400000000000
  | 6 => 0x157640abb209eee9e98c800000000000
  | 7 => 0x170700b83805e5e88907000000000000
  | 8 => 0xd2851df3a160000f0e10360000c0001
  | 9 => 0x2257d2b8bf000017a4801a000000002
  | 10 => 0x3ab89d56660e00023f1001a0001c0004
  | 11 => 0x3818e51d4b66000437000360000c0008
  | 12 => 0x3685f512092a00085d1802c000140010
  | 13 => 0x357b5cdfb304001065b9036000080020
  | 14 => 0x28588b0299c00201de802c000180040
  | 15 => 0xa59c8fd734c00401ab002c000180080
  | _ => 0

private def maskT0B53 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x14f0f1ca8d8800802df9036000100100
  | 1 => 0x6a07d2bd09a010061a001a000140200
  | 2 => 0x36080c5ba580020043f8000000000400
  | 3 => 0x31ae71bafacc04007b10036000180800
  | 4 => 0x2ba2974ccf56080047410000000c1000
  | 5 => 0xf9d56c82c4c10000758000000182000
  | 6 => 0x2083326c417c20005d1802c000184000
  | 7 => 0x2e9eef8ac8a6400041410000000c8000
  | 8 => 0xa2e3fbdbfe68000794001a0000d0000
  | 9 => 0x3b61a036f86b00000d5102c000160000
  | 10 => 0x134450fa2770000077b9016000200000
  | 11 => 0x13fc21fab89000002df9010000400000
  | 12 => 0x2884462f61f000004050022000800000
  | 13 => 0x32a0e6b03c0000006848024001000000
  | 14 => 0x3906e30117b000007ed000e002000000
  | 15 => 0xd803d98ca700000142102c004000000
  | _ => 0

private def maskT0B54 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2e13d46cff70000011e1024008000000
  | 1 => 0x16bb2b0dad000006319024010000000
  | 2 => 0x30d15f5e26000002d59024020000000
  | 3 => 0x29e449c6d190000063b9032040000000
  | 4 => 0x1788b10265000002818038080000000
  | 5 => 0xdad97a506000000519000c100000000
  | 6 => 0x21a30d02d340000053a802a200000000
  | 7 => 0x329295bd67000007521030400000000
  | 8 => 0x9d0db9ca9b000006af1016800000000
  | 9 => 0x32412c31991000005f01021000000000
  | 10 => 0x3cef9b04338000000af9040000000000
  | 11 => 0x223de0bf013000004d01080000000000
  | 12 => 0x171751f739f000001309100000000000
  | 13 => 0x271fb074f5b000003aa1200000000000
  | 14 => 0x1c8da029078000006b79400000000000
  | 15 => 0x1006e9dda1e000005779800000000000
  | _ => 0

private def maskT0B55 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1f6fed7b79b000007912000000000000
  | 1 => 0x294b09f3df7000002c0c000000000000
  | 2 => 0x692071e5b3b85200d24080000000001
  | 3 => 0x115801c2fbb8c44b82b0080000080002
  | 4 => 0x16280d8e8cd0d2f54c5008c000180004
  | 5 => 0x28f215979d3197ddf1e4084000080008
  | 6 => 0x842a1d4033eb4fa5085000000100010
  | 7 => 0x2b40419410b7658bf68000c000080020
  | 8 => 0x251081ae9e8c686daa20000000180040
  | 9 => 0x7cb00841ca34eff4f9400c000100080
  | 10 => 0x340884c9285c85292815084000100100
  | 11 => 0x13d6002ba4cd9153e7a4004000100200
  | 12 => 0xb60005ea825aebb36d0004000080400
  | 13 => 0x1ed88520a339ebbe7d91088000100800
  | 14 => 0x1c3285eb143009721825080000081000
  | 15 => 0xa5805366e242589f430088000182000
  | _ => 0

private def maskT0B56 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x14da81f2f165ec70e8b5004000104000
  | 1 => 0x4820004609c6cab2b04000000088000
  | 2 => 0x37328578dd1f86e5ca6508c000090000
  | 3 => 0x3b1004ae0f4a6bd03e20088000120000
  | 4 => 0x1a5a84b2d1cbee1224b5088000040000
  | 5 => 0x15b885e2e4d28ee52b710ac000200000
  | 6 => 0x17ba804fd9bbc6fcaf7503c000400000
  | 7 => 0x35d0041dba11a5166ba00bc000800000
  | 8 => 0x14588031045a42c628b1029001000000
  | 9 => 0x21b001aa38f7052d4360031002000000
  | 10 => 0x2da2849379eddc685b450a1004000000
  | 11 => 0x80000859d8f99ec900000d008000000
  | 12 => 0x184a05a1682c63eeb0940ac010000000
  | 13 => 0x3cca815e66073c8a7995008020000000
  | 14 => 0x204280bb65ec67bcc085024040000000
  | 15 => 0x1ea005c77df685523d40094080000000
  | _ => 0

private def maskT0B57 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1d5081138b6d8e5f3aa1028100000000
  | 1 => 0x1d928480d9cd6112bb250bc200000000
  | 2 => 0x7f0849c94d1564c8fe1094400000000
  | 3 => 0x1b9080f05e359571b721024800000000
  | 4 => 0x1ea004e3b920b157bd4009e000000000
  | 5 => 0x150287a062225dbaaa050c0000000000
  | 6 => 0xfba8846cbf80cc41f75100000000000
  | 7 => 0x1100905a0758af152201200000000000
  | 8 => 0x137a21695213bc9626f4400000000000
  | 9 => 0x2240c05767cc29e7c481800000000000
  | 10 => 0xf9100e1b67f2d199f22000000000000
  | 11 => 0x149c01ebed6ebcd2a938000000000000
  | 12 => 0x6552cda5bbe29800800006200120000
  | 13 => 0x36eb27429c50d0900000024000000000
  | 14 => 0x3b2d6c0ea3f531104000006200000000
  | 15 => 0x2361d940816778900000000000000000
  | _ => 0

private def maskT0B58 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x90a67fb98bb8c900000000000000000
  | 1 => 0x363494d942ece4900000000000000000
  | 2 => 0x1f418810af9bec900000046200000000
  | 3 => 0x1da46517ec5838104000080000000000
  | 4 => 0x6b4b6849e4c6c902000114200080000
  | 5 => 0x2ba322451de7c9000000210200000000
  | 6 => 0x3d4a4ba7861354106000412000080000
  | 7 => 0x310faa617922f0804000816000000000
  | 8 => 0x29b25bdcdde8b0106001014200080000
  | 9 => 0x18f6b773871779904002016000000000
  | 10 => 0x9b06404e5dd81004004010200000000
  | 11 => 0x6745b8baf784c106008014200080000
  | 12 => 0x38eea1998a2099904010000000000000
  | 13 => 0x399a3c7f78f611006020002200080000
  | 14 => 0x2198e8354946cc900040006200000000
  | 15 => 0x3bc77769206671006080004000080000
  | _ => 0

private def maskT0B59 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x26f5e544718310106100014200080000
  | 1 => 0x1ef6f0cb27c81004200000000000000
  | 2 => 0x2f78223e1eb9b0100400006200000000
  | 3 => 0x16ac7ef5c701a4900800006200000000
  | 4 => 0x197f6d6c16d301801000000000000000
  | 5 => 0x1f5b6ab74c6dd9900000004000080000
  | 6 => 0x302cad5a48a768000000000000000000
  | 7 => 0x2be0b326041239100000000000000000
  | 8 => 0x887d963cee0d0900000000000000000
  | 9 => 0x21a0f87da8ce4900000000000000000
  | 10 => 0x6c68520c404bc800000006200000000
  | 11 => 0x134d757796f965100000000000000000
  | 12 => 0x15623913ef60d0900000000000000000
  | 13 => 0x1ecab22918218d900000000000000000
  | 14 => 0x918210fa137b8900000000000000000
  | 15 => 0x1fe3760a6229b5800000000000000000
  | _ => 0

private def maskT0B60 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2e369f8f38e581800000000000000000
  | 1 => 0x3636a3a2fd6a1c800000000000000000
  | 2 => 0xfc111ca918d1d000000002200000000
  | 3 => 0x2b30c7fdbdb768000000000000000000
  | 4 => 0x1f3b2ac7387ce4900000000000000000
  | 5 => 0x1920ad1b81ce4900000000000000000
  | 6 => 0x1269984f8beb5c000000000000000000
  | 7 => 0x2da203420be0d0900000000000000000
  | 8 => 0x115456c5c49768000000000000000000
  | 9 => 0x31036a31f77994800000000000000000
  | 10 => 0x3fea7bdce5c0d0900000000000000000
  | 11 => 0x2c831b38d53edd800000000000000000
  | 12 => 0x34ff001e0b5f7c800000000000000000
  | 13 => 0x1c3050804967b8900000000000000000
  | 14 => 0x3ac6acb509a9b5800000000000000000
  | 15 => 0x13952802139c34000000000000000000
  | _ => 0

private def maskT0B61 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x6c25356aab691900000000000000000
  | 1 => 0x834cbf7742239100000000000000000
  | 2 => 0x3d10a534420b5c000000000000000000
  | 3 => 0x33cccb91f6f239100000000000000000
  | 4 => 0x442953422d7b8900000000000000000
  | 5 => 0x1645b73c100768000000000000000000
  | 6 => 0x36ddbe1c2a6551100000000000000000
  | 7 => 0x16e91126678239100000000000000000
  | 8 => 0x18dbe29093b5c000000000000000000
  | 9 => 0x3588c818faac34000000000000000000
  | 10 => 0x2e3e6c94c1dad900000010200000000
  | 11 => 0x5638ca1c139b5800000000000000000
  | 12 => 0x12df7f31ca7581800000000000000000
  | 13 => 0x17bcf27ea6ec34000000000000000000
  | 14 => 0x2e4d76d290a719902000012000080000
  | 15 => 0x386889eb7d7d1d000000004200000000
  | _ => 0

private def maskT0B62 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xe96278b948e05800000000000000000
  | 1 => 0x9b9749bb6a965100000000000000000
  | 2 => 0x397b1aed3b25c800000000000000000
  | 3 => 0x29277f073ff581800000000000000000
  | 4 => 0x18c7d5348ecebd800000000000000000
  | 5 => 0x3bfc21b89bfb5c000000000000000000
  | 6 => 0x12fe78f02fe581800000000000000000
  | 7 => 0x39dcbcbf0fb239100000000000000000
  | 8 => 0x24b02ab33ed650900800002200020000
  | 9 => 0x52ae9caaa2e0d100000000000000000
  | 10 => 0xa814e80e57965100000000000000000
  | 11 => 0x1f3c569e984b5c000000000000000000
  | 12 => 0xbbfe3bea4a0d0900000000000000000
  | 13 => 0x35b39754fa49b5800000000000000000
  | 14 => 0x2f86becfc52edd800000000000000000
  | 15 => 0x261de0a9887000000000000000000000
  | _ => 0

private def maskT0B63 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x36b4fb75bd38bb7998b4800000000000
  | 1 => 0x3bc70e1322989384c054804000080000
  | 2 => 0x2fcc929b01e8549f646482c000000000
  | 3 => 0x1ed3f2ea4e3490718e100200000c0000
  | 4 => 0x35fda751a52a912910e00200000c0000
  | 5 => 0x2b70ea72517d401be6948200000c0000
  | 6 => 0xac1889b668017f42666000000000000
  | 7 => 0x3b3e7cf8d6d828665f76824000000000
  | 8 => 0x30024f31b5895d3d36848040000c0000
  | 9 => 0x3f04e9ee0347103a430000000000000
  | 10 => 0x101d2d4f01c9fe9a3c34800000000000
  | 11 => 0x13cc59cc72c6255e72360040000c0000
  | 12 => 0x27f72fcff69cf7f484428200000c0000
  | 13 => 0x3b84a9840c391ac189d4024000000000
  | 14 => 0x21a9cf6c434724ca72348200000c0000
  | 15 => 0x672e3f9c18f385c37b68200000c0000
  | _ => 0

private def maskT0B64 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x17205ce56b808c4c0d308040000c0000
  | 1 => 0x3d6426cc1000784020d60040000c0000
  | 2 => 0x2e64b1c9f0d03fc6f3a2024000000000
  | 3 => 0x1eef9c69345a7772f9b68040000c0000
  | 4 => 0x1be2342217a82cad59608040000c0000
  | 5 => 0x28ed8d4c7f1117f8daa0024000000000
  | 6 => 0xf97adfc5850f8c2fad0024000000000
  | 7 => 0x24a79dd6c752ae6ae4c2800000000000
  | 8 => 0x3acc463adfa228ed27f08040000c0000
  | 9 => 0x286f6766a0c2230648b00040000c0000
  | 10 => 0x1405321dbace1d9607820200000c0000
  | 11 => 0x17885fe020ccd7c61eb6000000000000
  | 12 => 0x174e58959a4374423ec4800000000000
  | 13 => 0x2a36db9252725c03f674800000000000
  | 14 => 0x36e99ef9307347d3a472800000000000
  | 15 => 0x399581d35a06ce4042a4800000000000
  | _ => 0

private def maskT0B65 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x285e2c091b7e864bf674800000000000
  | 1 => 0x2eae05058ef62077f060000000000000
  | 2 => 0x24bf497b464fd4622072800000000000
  | 3 => 0x243c6ef117cbd27e62d6000000000000
  | 4 => 0x1025d8b11b8c9edc48b0000000000000
  | 5 => 0x20ecd2aec355b48a8614800000000000
  | 6 => 0x9aa71028cfb80379ca2804000000000
  | 7 => 0x36644741c5d4c0bef674800000000000
  | 8 => 0x3aba9705336eb39b34d0000000000000
  | 9 => 0x2e2d23cdb988355c32c4800000000000
  | 10 => 0x28f17c30647f4db3f674800000000000
  | 11 => 0x2d003faa2a9453c4c814800000000000
  | 12 => 0x2d695aae1e1d2460c2a4800000000000
  | 13 => 0x1970ed268c142c30e8c2800000000000
  | 14 => 0x2e8f0386b4346131c2a4800000000000
  | 15 => 0x2651ee3f7d55f5baa072800000000000
  | _ => 0

private def maskT0B66 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x13d686fa0900ca4838d0000000000000
  | 1 => 0x1aa2b4f8ee99cb74f060000000000000
  | 2 => 0x12ce0950dd5c1ceab4d0000000000000
  | 3 => 0x12b26a4cd2d72a56aa66000000000000
  | 4 => 0x28b46fdd7fe9336f3ec4800000000000
  | 5 => 0x171ebf1da6894d338d0000000000000
  | 6 => 0x2d99e72e51e4c20f5d840040000c0000
  | 7 => 0x3a65f28a7e08cba064c2800000000000
  | 8 => 0xe6540aae083d9c43476024000000000
  | 9 => 0x16150001388cb7d465f0800000000000
  | 10 => 0x176f5f7eb88135045606000000000000
  | 11 => 0x1fdda07d6b97279ca666000000000000
  | 12 => 0x3138cbd0a69f05348c00000000000000
  | 13 => 0x3904e0d76acdef565aa0000000000000
  | 14 => 0x3dbd39a9342bd9b13480800000000000
  | 15 => 0x326ab89bbf89073c6ed6000000000000
  | _ => 0

private def maskT0B67 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xa78298bccd71ea6da06000000000000
  | 1 => 0x1296275b3911c708d8f6000000000000
  | 2 => 0x1cd1ba2ca65f4bf2f176000000000000
  | 3 => 0x1051037f056bd47b016281c000000000
  | 4 => 0x10da9d74299eed8caa66000000000000
  | 5 => 0x279255d6a355f5dada06000000000000
  | 6 => 0x2b8c7518cd151ca8eed6000000000000
  | 7 => 0x26e3be217cf791e7b4d0000000000000
  | 8 => 0x24400c71b29bd904c2a4800000000000
  | 9 => 0x390879cd5ba7be4d4ea4800000000000
  | 10 => 0x2f978d4725af75ed2a66000000000000
  | 11 => 0x11e3153649a7be4d7060000000000000
  | 12 => 0x3e15155164d779369f908240001c0000
  | 13 => 0x962103d31506c8e8c2800000000000
  | 14 => 0x2d695bb32e85cde442a4800000000000
  | 15 => 0x2f14ab27b300e9084ea4800000000000
  | _ => 0

private def maskT0B68 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xec1f035aae7375734d0000000000000
  | 1 => 0x1074cf6345b98e7d94a2800000000000
  | 2 => 0x17f97f59240d11b03ec4800000000000
  | 3 => 0xaa894f40b2ab80968c2800000000000
  | 4 => 0x11c83e9a6f1d51000000000000
  | 5 => 0x1e997989867b721000000000000
  | 6 => 0x554566945267d503b000008000
  | 7 => 0x6bcb308db8fbd1021000000000
  | 8 => 0x1a17a520bff5111000000000000
  | 9 => 0x1f66b698092bc90000000000000
  | 10 => 0xcbaf44f8381c75000000000000
  | 11 => 0x200014c698d3f45f1b003b000018000
  | 12 => 0x200030919f0abf11a61033000018000
  | 13 => 0x53797e80822a40103b000018000
  | 14 => 0x84d984ad025da6101b000000000
  | 15 => 0x112c9861ecf068a5020000018000
  | _ => 0

private def maskT0B69 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x20eb27ca22647c15000000000000
  | 1 => 0x4004201baaaba32503b000018000
  | 2 => 0x200813077ef0d4be71001b000000000
  | 3 => 0x201003d3fc979a534d0008000000000
  | 4 => 0x20201f986deaedfaad0028000018000
  | 5 => 0x4009ea4c0c632191501b000000000
  | 6 => 0x20801880c1cd2375b51020000018000
  | 7 => 0x1000c1b15fe2df0b0501b000000000
  | 8 => 0x2000469e8efd9f2ab5000000000000
  | 9 => 0x4000b4f36be0aba8c0028000018000
  | 10 => 0x280003cb4f5f04644d5028000018000
  | 11 => 0x30001db7a1fdf590e54033000018000
  | 12 => 0x4000062a835c29635d1000000000000
  | 13 => 0x800004b4eebfc0582f0008000000000
  | 14 => 0x100000b52308362ac825008000000000
  | 15 => 0x200001f795e2d8fff290008000000000
  | _ => 0

private def maskT0B70 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x126badb2e041724000000000000
  | 1 => 0x144f74309519e85000000000000
  | 2 => 0x54aecf5d462354000000000000
  | 3 => 0x1b90c8c954d17c4000000000000
  | 4 => 0x168b9f1d6bda944000000000000
  | 5 => 0x1796e5b793a9724000000000000
  | 6 => 0xcb67f1ea0000000000000000
  | 7 => 0x4cc7261f169c95000000000000
  | 8 => 0x1debfca820c3c70000000000000
  | 9 => 0x46ccc64322a0e5000000000000
  | 10 => 0x16aed45b210cdb1028000000000
  | 11 => 0xdc45d870e8b9a4000000000000
  | 12 => 0xe4bb1f70cd29a4000000000000
  | 13 => 0x14ac0cdfc5b2b54000000000000
  | 14 => 0xd1453a95b8d0e0028000018000
  | 15 => 0xf073bb99f835d1000000000000
  | _ => 0

private def maskT0B71 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x564d16a0bd0941000000000000
  | 1 => 0xcabb47955a9a4000000000000
  | 2 => 0x69461e29546391000000000000
  | 3 => 0x80d9520b668b51000000000000
  | 4 => 0xdea829e4bbbe60000000000000
  | 5 => 0x45707369a029a4000000000000
  | 6 => 0x1cf0f8250d2a215000000000000
  | 7 => 0x6200c102aebe80000000000000
  | 8 => 0x646249009ea2f5000000000000
  | 9 => 0xe8a3bbb8f99e85000000000000
  | 10 => 0x94da9fee671724000000000000
  | 11 => 0x1dbc726a8eabe60000000000000
  | 12 => 0xd431ca541bc90000000000000
  | 13 => 0x135b504a38c3531000000000000
  | 14 => 0x12ce011d27ab5d1000000000000
  | 15 => 0x9b5a361f169c95000000000000
  | _ => 0

private def maskT0B72 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x15c4affd63c0b51000000000000
  | 1 => 0x1132d16ea042005000000000000
  | 2 => 0x1bfdd1e8fbf4170000000000000
  | 3 => 0x192d4c537df0210000000000000
  | 4 => 0xaf8795912e20e5000000000000
  | 5 => 0xd3fef0a6f122f5000000000000
  | 6 => 0x6f5ce62f002f30000000000000
  | 7 => 0x186ec004eae1115030000000000
  | 8 => 0x1d0381bb87a29a4000000000000
  | 9 => 0xf122f46ec595d4000000000000
  | 10 => 0x1eed6d0bbef2944000000000000
  | 11 => 0x1073b1c79051c75000000000000
  | 12 => 0xc18a70b5aa15d4000000000000
  | 13 => 0x1a53a91d0efe50001b000000000
  | 14 => 0x1e0e21e4eff9c95000000000000
  | 15 => 0x1497f3e89e42215000000000000
  | _ => 0

private def maskT0B73 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xd477de2747d4c103b000100000
  | 1 => 0x1d6843cc40902f0000000000000
  | 2 => 0x76b9a3319329a4000000000000
  | 3 => 0x6352c01d87c7a1000000000000
  | 4 => 0x167181c7152ab54000000000000
  | 5 => 0x1cf190144246b65013000000000
  | 6 => 0xe3ef994ca597c4000000000000
  | 7 => 0x1c24c97e8aa9e85000000000000
  | 8 => 0xbf3f00000065cb882e6000000000000
  | 9 => 0x332400000b3f16d8cc000000000000
  | 10 => 0x3d64ce00000071b8907c000000000000
  | 11 => 0x870a3400001550c58cc028000080000
  | 12 => 0x1401cde00004c2ccc73402c000000000
  | 13 => 0xb147c00000efe845f08000000000000
  | 14 => 0x2378360000065de7cd5e000000000000
  | 15 => 0x1f87b1500000aeb5b1b003a000000000
  | _ => 0

private def maskT0B74 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3359fa000001558f9592000000000000
  | 1 => 0x36ab2350001931df218a03a000000000
  | 2 => 0x3c4cd150002ed41849ec03a000000000
  | 3 => 0x35f39bd000419bf5bba603a000000000
  | 4 => 0x36b843500088baed920203a000000000
  | 5 => 0x3bc06f10010016d00ed8032000000000
  | 6 => 0x76846c002054a035b0e008000000000
  | 7 => 0xfb427d0040c90d9ec9203a000000000
  | 8 => 0x33217a40080c8d20bcd6008000000000
  | 9 => 0x1bd2ca401007774dd86a008000000000
  | 10 => 0x3d20ac8020074b5a1548000000000000
  | 11 => 0x349bdb50400806792e3403a000000000
  | 12 => 0x3f2b2240800d218f4b72008000000000
  | 13 => 0x3e5b75d100028010466803a000000000
  | 14 => 0x29a3a392000e41e94c7e032000000000
  | 15 => 0x48fc7d40002e993082e03a000000000
  | _ => 0

private def maskT0B75 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x7f555d800053a1c5f8603a000000000
  | 1 => 0x1e4aa4900006948af886000000000000
  | 2 => 0x2ffbd7000086715cf5c03a000000000
  | 3 => 0x3e5cb20000012e8b3944008000000000
  | 4 => 0x48a090000326c1d668032000000000
  | 5 => 0x20cec40000049aa9d1f8000000000000
  | 6 => 0x1e249c00000c12e3966c000000000000
  | 7 => 0x246afa000000a38f72d6000000000000
  | 8 => 0x238a80000001c149a32e000000000000
  | 9 => 0x27db400000a2b736e70000000000000
  | 10 => 0x2efed600000215e5b352000000000000
  | 11 => 0x20525600000040aaf738000000000000
  | 12 => 0x10286e000006f1009a6a000000000000
  | 13 => 0x3e8afa000005439851f8000000000000
  | 14 => 0x310be6900007cfdc148e012000000000
  | 15 => 0x1663ec00000c89d1eb9e000000000000
  | _ => 0

private def maskT0B76 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3bafca00000f70935416000000000000
  | 1 => 0x13adb8000006778ec46a000000000000
  | 2 => 0x146a2000000438666b9e000000000000
  | 3 => 0xa9be8000002bdc02a1a000000000000
  | 4 => 0x11cbe800000e13154d5e000000000000
  | 5 => 0x32a7fe00000f4ed6b352000000000000
  | 6 => 0x1d619a0000045462fbe2000000000000
  | 7 => 0x95bb200000809dfd1f8000000000000
  | 8 => 0xcbd7e00000101b5907c000000000000
  | 9 => 0x29f5d400000c6af46e70000000000000
  | 10 => 0xe934c00000ad2f148b0000000000000
  | 11 => 0x3e273e00000788a2bf14000000000000
  | 12 => 0x32f478000003027985ee000000000000
  | 13 => 0x2b2a6000000bc18f0934000000000000
  | 14 => 0x35e97000000f715051f8000000000000
  | 15 => 0x3fa76e0000070eaf36bc000000000000
  | _ => 0

private def maskT0B77 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x20c10000000bc04c3a66000000000000
  | 1 => 0x12105600000a199c6e70000000000000
  | 2 => 0x1862a8000004800e3a66000000000000
  | 3 => 0x634a800000abef5d8cc000000000000
  | 4 => 0x1ba2f2000009a2c9c184000000000000
  | 5 => 0x1cb03e0000037546fe0c000000000000
  | 6 => 0x22f7a200000ddc5e604e000000000000
  | 7 => 0x202816000007db834792000000000000
  | 8 => 0x3cde5d000011fa6631603a000000000
  | 9 => 0x3a7d420000093615c46a000000000000
  | 10 => 0x27823800000ab0c28f9a000000000000
  | 11 => 0x16437770000e3b435e7a02e000000000
  | 12 => 0x3268800000aa4526e70000000000000
  | 13 => 0xc2e28000003aba01ff8000000000000
  | 14 => 0x3b6c36000008dc70107c000000000000
  | 15 => 0x157bf600000336c95d22000000000000
  | _ => 0

private def maskT0B78 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x170986000007de48d8cc000000000000
  | 1 => 0x120990000009f8c4dd22000000000000
  | 2 => 0x154f800000ef66beb9e000000000000
  | 3 => 0xd892400000dc6f99592000000000000
  | 4 => 0x11126d4000005991ffb4028000100000
  | 5 => 0x3c1e5800000c5aa6c184000000000000
  | 6 => 0x14090c000007ac608cda000000000000
  | 7 => 0x19a50600000412932ff4000000000000
  | 8 => 0x3ad05040000403519322008000000000
  | 9 => 0x2dbb120000058f8cb352000000000000
  | 10 => 0x16f1e40000049cf2f2d6000000000000
  | 11 => 0x2e524c0000080f84f2d6000000000000
  | 12 => 0x30932ef2f3f1e0cbee20000000000000
  | 13 => 0xdb6b08d641480ac3f68000000000000
  | 14 => 0x3eb3dcba01a381f76168000000000000
  | 15 => 0x2a80621bde0aa018000000000000000
  | _ => 0

private def maskT0B79 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x12e53ad9fc98214ee4c0000000040000
  | 1 => 0x115f9b99e7b75fe6984002c000000000
  | 2 => 0x5b7cf46987bf67394dc029000000000
  | 3 => 0xb6ade9c992306b7cee0029000000000
  | 4 => 0x3ddf914193d89ae43f68000000000000
  | 5 => 0x2e47c580df904ff11ef0029000000000
  | 6 => 0x256ea48108a503a162c00c0000c0000
  | 7 => 0x37256f8af3afa7dad374024000000000
  | 8 => 0x17905ebfa38c29958e6c00d000000000
  | 9 => 0x1e6d2f63a3a03bcfbd040010000c0000
  | 10 => 0x3187dac8e0c86dfee060029000000000
  | 11 => 0x4cbf6150efbb56d943c024000000000
  | 12 => 0x22e32c6dc3ab66eb1ef0029000000000
  | 13 => 0x342884b7e03c1e6108a000d000000000
  | 14 => 0x2e6a53d5cca88c14d8b0024000000000
  | 15 => 0x2aace5e55b3dc2b97b4400c0000c0000
  | _ => 0

private def maskT0B80 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2b60c2cad48af4b08174024000000000
  | 1 => 0x3f514340f3652550d7a8024000000000
  | 2 => 0x1e0515f9b41321c5254400c0000c0000
  | 3 => 0x1f1b72219d9131dcf738000000000000
  | 4 => 0x202704d6af3300c1194800c0000c0000
  | 5 => 0x153c512bdd21c494265c0280000c0000
  | 6 => 0x39a59494c874b8e5128c00d000000000
  | 7 => 0x168cf87c8e27003e5d180280000c0000
  | 8 => 0x11cfc1a8bfa905703bb400d000000000
  | 9 => 0x140e7058edd6f09c7f980280000c0000
  | 10 => 0x1b809c7cfcd10aa73f54000000000000
  | 11 => 0x37720a71ada1f182e168000000000000
  | 12 => 0xcf16d5b1ee973db527c000000000000
  | 13 => 0x17c94b7efbe47dd28c7c000000000000
  | 14 => 0x34f26059c78e3b18183c00c0000c0000
  | 15 => 0xbb13c5af905014f3f68000000000000
  | _ => 0

private def maskT0B81 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x31e3bba94bfdbaee8e10000000000000
  | 1 => 0x58464d28fdb63195010000000000000
  | 2 => 0x37a68381b69f69a09400025000000000
  | 3 => 0x21e55220f7c9bb548e10000000000000
  | 4 => 0x24474d2ae88911d30000000000000000
  | 5 => 0x3d34acff2043602b6168000000000000
  | 6 => 0x1b65ddb1d56af4776168000000000000
  | 7 => 0x93f4010f9020250026c000000000000
  | 8 => 0xd06f60e958ee33ded14000000000000
  | 9 => 0x3302800b874b60203d04000000000000
  | 10 => 0x3c9a0e9065cdf686168000000000000
  | 11 => 0x112d0676a88229c1b314000000000000
  | 12 => 0x1d1ab958d33746ae0000000000000000
  | 13 => 0x15ff8d152fdca3e34ee0000000000000
  | 14 => 0x267af51367a91ebd04000000000000
  | 15 => 0x255bebf8f0c57bfae168000000000000
  | _ => 0

private def maskT0B82 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1bcdb49fe4a11e6d3f68000000000000
  | 1 => 0x1a517dc683fb7b5f6f78000000000000
  | 2 => 0x319ebadac54b8aaebf68000000000000
  | 3 => 0x267a2a7487a91ebd04000000000000
  | 4 => 0x9643bee3ea39b0e8e10000000000000
  | 5 => 0x110b7c32777580df0e10000000000000
  | 6 => 0x147695fadff2f0a53f68024000000000
  | 7 => 0xbb13c8d6415014f3f68000000000000
  | 8 => 0x2a80690e280aa018000000000000000
  | 9 => 0x31758762eed07061e168000000000000
  | 10 => 0xc2d199a32701dc618b4000000000000
  | 11 => 0x2ca9ed26c1cb2a7b0000000000000000
  | 12 => 0xa46a619697291a98000000000000000
  | 13 => 0x1b30db9096c12136bf68000000000000
  | 14 => 0x22ac9d5904cb2fa71c24000000000000
  | 15 => 0x57de9bd1e9a797a5930014000000000
  | _ => 0

private def maskT0B83 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x344f7bfbd5669e5edc6c000000000000
  | 1 => 0x2526eb5239134bbad010000000000000
  | 2 => 0x3c6424145faf5489026c000000000000
  | 3 => 0x1031a1a5e95e43e8527c000000000000
  | 4 => 0x3b7e093f7caf50020c7c000000000000
  | 5 => 0x10b7c439f0324f713314000000000000
  | 6 => 0x1539b5543be859ed68bc029000000000
  | 7 => 0x35f9d04a7c925674f94000000000000
  | 8 => 0x1de8a018d3b28ea82fa400c000140000
  | 9 => 0xfaae4904ea9523955c4000000000000
  | 10 => 0x74050988fdc72946d14000000000000
  | 11 => 0x395bbe8e1b16aee8c7c000000000000
  | 12 => 0x20cebd2d32bf932f3d04000000000000
  | 13 => 0x3e6eb9e955d4162e5c6c000000000000
  | 14 => 0x39ab0f0255d2bf43e6ac000000000000
  | 15 => 0x29f1fd68ec8d917f3f68000000000000
  | _ => 0

private def maskT0B84 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x7351fdba39455804800024000000000
  | 1 => 0xf125e7892f000000000000000000000
  | 2 => 0xf601795219474a00000000000000000
  | 3 => 0x2c077dd0eb669d200000000000000000
  | 4 => 0xcf1158fe6d65d200000000000000000
  | 5 => 0x34e6598f7835e8800c00024000010000
  | 6 => 0x438468610e1c9206d00016800000000
  | 7 => 0x2160a1643bb4fda00800024000000000
  | 8 => 0x15554d99c38b9c000000000000000000
  | 9 => 0x38df8ed17eb65d200000000000000000
  | 10 => 0x7e17df3a4e135200000000000000000
  | 11 => 0x360cb65c6c7114000800064000000000
  | 12 => 0x2c718c3d0a55e9a04000080000000000
  | 13 => 0x30717334b8167d004100100800000000
  | 14 => 0x1b53dfbecf3929a00000212000090000
  | 15 => 0x2bc8d7a0fb1831800900424800000000
  | _ => 0

private def maskT0B85 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xc32cd654d90a5004800836000090000
  | 1 => 0x1f779e6cfbb2a1800101000800000000
  | 2 => 0x13ff44aef149c8804802036000090000
  | 3 => 0x2c15d466f488fda04004012000090000
  | 4 => 0xf8f6d19537535800108000800000000
  | 5 => 0x1c6e052aafa6d4204010000000000000
  | 6 => 0x3b777e18c1384a00920036800090000
  | 7 => 0x1a61e613edc69d200840024000000000
  | 8 => 0x1972eb91f164cd800180012800090000
  | 9 => 0x5656d6d94529d800000000800000000
  | 10 => 0x2c65ac440f4140204200000000000000
  | 11 => 0x6351c72dd5348800c00024000000000
  | 12 => 0x126b83f1b9d69d200000024000000000
  | 13 => 0x1e9e109fb23234a01000000000000000
  | 14 => 0x196e52fcb8e928a06100012800090000
  | 15 => 0x22989c5d70f4b4a00000000000000000
  | _ => 0

private def maskT0B86 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xedc6e8210b1f5200000000000000000
  | 1 => 0x3dab6b699946f5000000000000000000
  | 2 => 0x2d9885bc84b1f5200000000000000000
  | 3 => 0x3588c8b17bf541800000000000000000
  | 4 => 0x11086cade2b2e9800000000000000000
  | 5 => 0x9085080273d74800000000000000000
  | 6 => 0x18b52c6e585fc0a06d00036800000000
  | 7 => 0x140e34df67e000000000000000000000
  | 8 => 0x11d030cf04265d200000000000000000
  | 9 => 0xf7910d984465d200000000000000000
  | 10 => 0xdda825ec81f5200000000000000000
  | 11 => 0x31fd292050d0c0000000000000000000
  | 12 => 0x2e6aa5e71ec000000000000000000000
  | 13 => 0x23b75a5b90133da00000000000000000
  | 14 => 0x24542c4d1a11f5200000000000000000
  | 15 => 0x3e372b52b25474a00000000000000000
  | _ => 0

private def maskT0B87 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1e94bea5128388800000000000000000
  | 1 => 0x38b0f4336ce1f5200000000000000000
  | 2 => 0x28729cdf6ec31ca00000000000000000
  | 3 => 0x3e1feb4aaea1f5200000000000000000
  | 4 => 0x2242f7e58f30dc200000000000000000
  | 5 => 0x146be1952f1229800000000000000000
  | 6 => 0x2fa4955e2561f5200000000000000000
  | 7 => 0x28729c0009231ca00000000000000000
  | 8 => 0x27234c74a3b0c0000000000000000000
  | 9 => 0x2e9a39ed6eb135200000000000000000
  | 10 => 0x2a82947e715541800000000000000000
  | 11 => 0xd5746b798531ca00000000000000000
  | 12 => 0x14d8f3b0cab0c0000000000000000000
  | 13 => 0x20dd85813927a8000000000000000000
  | 14 => 0x3cf8013aa299f4800000012000090000
  | 15 => 0x1036c13802b229800000000000000000
  | _ => 0

private def maskT0B88 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2de18c131022e9800000000000000000
  | 1 => 0x508c214c1869d200000000000000000
  | 2 => 0x12a4546ef47088004900024800000000
  | 3 => 0x39da51dae9c48206100030800000000
  | 4 => 0x9775a78306f30a00000000000000000
  | 5 => 0x386c9db150a4b4a00000000000000000
  | 6 => 0x476cc5d775369a00000000000000000
  | 7 => 0x11f8f1d64143dca00000000000000000
  | 8 => 0x27f926165499d5800000000000000000
  | 9 => 0x1676e2f026c69d200000000000000000
  | 10 => 0x12fe78f02fe581800000000000000000
  | 11 => 0x258396dd548229800000000000000000
  | 12 => 0x24045c0a9699e8802900036800110000
  | 13 => 0x331e7d13e8c2e9800000000000000000
  | 14 => 0x3b54a7aa0374b4a00000000000000000
  | 15 => 0xd8866f4ff21f5200000000000000000
  | _ => 0

private def maskT0B89 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2f3f470d81269d200000000000000000
  | 1 => 0x2707a73e9d231ca00000000000000000
  | 2 => 0x5ed0074dcf229800000000000000000
  | 3 => 0x261de0a9887000000000000000000000
  | 4 => 0x2080ce3cb80905f3860000000000000
  | 5 => 0x1da55e11f326b0ce8ab0000000000000
  | 6 => 0x33aabeb0d4dff98934ac000000000000
  | 7 => 0x38771d47054f6ded5a40000000000000
  | 8 => 0x2271ce8c7103c6fbf9c8000000000000
  | 9 => 0x26e1940569c68cab78fc000000000000
  | 10 => 0x244b5b63c0873852a9a4004000080000
  | 11 => 0x1b90494f471d6e2a8f8013000000000
  | 12 => 0x3a805d210184fa9b3a94016000000000
  | 13 => 0x2cdc19f1c69931b2cc44016000000000
  | 14 => 0x1122975b9c1a2447258016000000000
  | 15 => 0x13a5291cd817128af8e8016000000000
  | _ => 0

private def maskT0B90 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x654c4ffa15c693b7008012000090000
  | 1 => 0x277d190ac861130424d0000000000000
  | 2 => 0x1cc19ed87af27bb21c40020000090000
  | 3 => 0x29581825b97dca49b58c016000000000
  | 4 => 0x1d69811b35e1b4c751b8004000090000
  | 5 => 0x319ba4abe76db0d0244032000000000
  | 6 => 0xb0a34cc5eebc15a5b08004000090000
  | 7 => 0x2d3d2b0589619741b7a0012000090000
  | 8 => 0x1dc71d80847232e4ca3c024000000000
  | 9 => 0x2b0aea644baeca67995c012000090000
  | 10 => 0x397524a131722442cb94020000090000
  | 11 => 0x548aef93ef9b85c793c012000090000
  | 12 => 0x34ed03d02d4bb1aae01c000000000000
  | 13 => 0x1466f4ad188638f912cc004000090000
  | 14 => 0x21af52ec804de256966c020000090000
  | 15 => 0x3355f56b66cccdcb781c004000090000
  | _ => 0

private def maskT0B91 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x44ed74bbb1c7e6d1d80012000090000
  | 1 => 0x140d408e8d4476ba200c000000000000
  | 2 => 0x1fab28a12e4e6838745c000000000000
  | 3 => 0x35f734ca040fb5ed64c0024000000000
  | 4 => 0xd6cc749fdc842df8ab0000000000000
  | 5 => 0x293615d80926694c1724000000000000
  | 6 => 0x2cea067ec5ddebaf2938000000000000
  | 7 => 0x1b9f5104a9d76e1acd64000000000000
  | 8 => 0x92956ab100712d58000000000000000
  | 9 => 0x3bbc971b1cb637c00000000000000000
  | 10 => 0xabacf73bba0aaeecccc004000000000
  | 11 => 0x2082d69fb2a79520da40000000000000
  | 12 => 0xea55b59753f0fff3368000000000000
  | 13 => 0x1e4343e003d6ffce7378000000000000
  | 14 => 0x10459c635f0b801f645c000000000000
  | 15 => 0x1ef034c4e75ad337da40000000000000
  | _ => 0

private def maskT0B92 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x13578b421dfbe20d2938000000000000
  | 1 => 0x2c2fbda1453d49c6da40000000000000
  | 2 => 0xb0dae0c12ff7e7c6eec000000000000
  | 3 => 0x3e525803739a9f8aa884032000000000
  | 4 => 0x1efef66f4df593d20ab0000000000000
  | 5 => 0x1184b35648a910e9be1c000000000000
  | 6 => 0x1dfe0543058f8cad1758000000000000
  | 7 => 0x3a5d1a41505b5e443e1c000000000000
  | 8 => 0x16cf12cc3eb060b11d94000000000000
  | 9 => 0x23697d71f73e8866eeec000000000000
  | 10 => 0x2d8ba171f73d30d1eeec000000000000
  | 11 => 0x218bf423803fde7cb504004000090000
  | 12 => 0x2c6f6769b09d8bdd6eec000000000000
  | 13 => 0x320480af61b6c32df9c8000000000000
  | 14 => 0x120bb30a07ea4753b4ac000000000000
  | 15 => 0x24dbe2fceda91215be1c000000000000
  | _ => 0

private def maskT0B93 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3b9013881ab2935101bc016000000000
  | 1 => 0x33b3dcaac7ca08491d94000000000000
  | 2 => 0x3bbe816348dfe966d0e4000000000000
  | 3 => 0x2c57b29d29aeaaa18ab0000000000000
  | 4 => 0x290a90f252f47cb3cd64000000000000
  | 5 => 0x26a9f72e69d823b347d4000000000000
  | 6 => 0x1cb066ce9ae668ceb980000000000000
  | 7 => 0x10828ea8e6d9901547bc011000000000
  | 8 => 0x388e23a3118d5404f378000000000000
  | 9 => 0x20e67d377c4641fd3e1c000000000000
  | 10 => 0x1d09f9f53be2f5a150f0000000000000
  | 11 => 0x305a60e5378b5c240318000000000000
  | 12 => 0x1d4d73b90291d3485a40000000000000
  | 13 => 0x13ec35e33a09065d1724000000000000
  | 14 => 0x213b74994a77cc8eda40000000000000
  | 15 => 0x308342e299bcf79d3e1c000000000000
  | _ => 0

private def maskT0B94 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x143c36a97854de4f24d4036000100000
  | 1 => 0x30bfc7eb05b4b45c3e1c000000000000
  | 2 => 0x3e99badb523b987f1724000000000000
  | 3 => 0x259b42ac586fb6939d94000000000000
  | 4 => 0x25ffd5adcf5a7e8ff378000000000000
  | 5 => 0x2fbea97edc1c92cae45c000000000000
  | 6 => 0xf7a4541329f4285b4ac000000000000
  | 7 => 0x2af177e6c08bf6d9f3e4000000000000
  | 8 => 0x1f7724fbb921d6bdfb52000000000000
  | 9 => 0x1b8a6adc53517236e554000000000000
  | 10 => 0x1fcd5cfe6aefe2a9ab8e000000000000
  | 11 => 0x198de6cc6f341174434e000000000000
  | 12 => 0x22a5e1152f22c3c4eda000000000000
  | 13 => 0x18971ac4b8d8086358f0000000000000
  | 14 => 0x31596f8acb72768ce8c0000000000000
  | 15 => 0x2a579d52bcead9c65792000000040000
  | _ => 0

private def maskT0B95 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1bb30add985a43170d94024000000000
  | 1 => 0x18ee2ec77177098ac82c000000000000
  | 2 => 0x14c56ca62b651a2b850e000000000000
  | 3 => 0x3d25e6e92f3d28a6655402c000000000
  | 4 => 0x29bdd24dee9c5a90800002c000000000
  | 5 => 0x3565afab2d62eb6e6e9002c000000000
  | 6 => 0x3030508182a47c2e15920280000c0000
  | 7 => 0x307d7983eb8443e94524000000000000
  | 8 => 0x246379231b47b1eb50b60040000c0000
  | 9 => 0xf77f27bbe91430130aa0280000c0000
  | 10 => 0x17bab4bdd7a8f6e4acaa0280000c0000
  | 11 => 0x39d633ceb5938e6ab2fc0040000c0000
  | 12 => 0x35ebb1afdd4389e03640280000c0000
  | 13 => 0x30df7986ebcc1d57bd3e0280000c0000
  | 14 => 0x21d4180e80c391d72ff402c000000000
  | 15 => 0x34cb58a61ac559da5a7a0280000c0000
  | _ => 0

private def maskT0B96 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3a5932d24995419baff40280000c0000
  | 1 => 0x35c832af41951fd7c1220280000c0000
  | 2 => 0x369c7eb6e3fcfd0945620280000c0000
  | 3 => 0x2fe40a7b205f9a661934000000000000
  | 4 => 0x358304a41826abbde41a02c000000000
  | 5 => 0x395722dab91b7ace0eb60040000c0000
  | 6 => 0x6d64e16b27c4b9829e202c000000000
  | 7 => 0x20ae6645733bc472a9a4000000000000
  | 8 => 0x1078c503c62a61e21c460040000c0000
  | 9 => 0x2e7ad573d6a90b4f32c6000000000000
  | 10 => 0x154cbeaa65fa5b173a5c000000000000
  | 11 => 0x26ef1337789e22816aac000000000000
  | 12 => 0x38736dc39b62ad883a5c000000000000
  | 13 => 0x1a4dc4d26e2e2b5668c0000000000000
  | 14 => 0xc3c1661e0bdc31a9eb0028000000000
  | 15 => 0x3cdcfbe6e7df001111d2000000000000
  | _ => 0

private def maskT0B97 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1c40e6e20738afad605a000000000000
  | 1 => 0x21d3590e9ac88d540bb8000000000000
  | 2 => 0x1e3658f1b2c6ed65889a000000000000
  | 3 => 0x81d2c40e96cd57e7c1c000000000000
  | 4 => 0x374f89ba7c40a9f12b8e02c000000000
  | 5 => 0x3b4f5fda7af73312605a000000000000
  | 6 => 0xa6e5a5372d24f308000000000000000
  | 7 => 0x249b7d24dbe32b54ab8e000000000000
  | 8 => 0xd99306cc98063cb2b8e000000000000
  | 9 => 0x3eaf8df57c6f33bb2b8e000000000000
  | 10 => 0x20772103b90c10c232c6000000000000
  | 11 => 0x8d1144688ab91ee2314000000000000
  | 12 => 0x38db9bc6dcdfffcccbd4000000000000
  | 13 => 0x36af5bb57adf33bb3876000000000000
  | 14 => 0x314f658a7b26ed65889a000000000000
  | 15 => 0x20ef87077c3d6137ab8e000000000000
  | _ => 0

private def maskT0B98 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2e22a37115198596e05a000000000000
  | 1 => 0x3bc1f3de0f9580c51948000000000000
  | 2 => 0x1de386ef1c3654957188000000000000
  | 3 => 0x9c24a4e125fc730b1e40280000c0000
  | 4 => 0x25a0bb2d05db264c2314000000000000
  | 5 => 0x3cb801e5c0630cceda000000000000
  | 6 => 0x4366e21b3790422e93c000000000000
  | 7 => 0xc36b861b5c4a884ba5c000000000000
  | 8 => 0x128300941808c5353a5c000000000000
  | 9 => 0x3e6f5df37ae7a717e05a000000000000
  | 10 => 0x313cff89e7fd159105ca000000000000
  | 11 => 0x137a3c9bd1ebf33e1b9601c000000000
  | 12 => 0x3a7499d3a4cd227fe8c0000000000000
  | 13 => 0x1dbaaeedd579e7a52b8e000000000000
  | 14 => 0x334f899a7c49f44be8c0000000000000
  | 15 => 0x1cf902e7c81c6f57c34e000000000000
  | _ => 0

private def maskT0B99 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xa4e4652723a4e8eda06000000000000
  | 1 => 0x5c3b22e1d98a706f188000000000000
  | 2 => 0x3806b1c0358ea3357486000000000000
  | 3 => 0x394443ca221726a394dc000000000000
  | 4 => 0x203d3101e98f4b356a80028000140000
  | 5 => 0xecd247669222d034bd4000000000000
  | 6 => 0x21ba210dd105c2b235d8000000000000
  | 7 => 0x2103c5081e28a706f188000000000000
  | 8 => 0x740003a055b062b8e000000000000
  | 9 => 0x10975684bab440edb2c6000000000000
  | 10 => 0x3d94a7eca5308a5ac34e000000000000
  | 11 => 0xe558272ac1c886d529c000000000000
  | 12 => 0x25f9b39cad441c4220e2100000000000
  | 13 => 0x17609bd0726ee4027720100000000000
  | 14 => 0x3e36a1697c5e51027288100000000000
  | 15 => 0x249b61a137a4dc4226e2100000000000
  | _ => 0

private def maskT0B100 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2c5c5ef678fee4027720100000000000
  | 1 => 0x2cec24950afe944274a2100000000000
  | 2 => 0x238db8018f4a8d40546a000000000000
  | 3 => 0x19e1c958906ff0027f80100000000000
  | 4 => 0x3ac15f40ec05954208aa112000080000
  | 5 => 0x17c25842691969026f48132000000000
  | 6 => 0x2a34cc0ed86a88001440000000000000
  | 7 => 0x5f85f9877eca0402502000000000000
  | 8 => 0x38ed8d2166d5c8422e42100000000000
  | 9 => 0x209f4889864b2c405962000000000000
  | 10 => 0x304c2fb40103f942dfca100000000000
  | 11 => 0x830c26d91419c010ce0000000000000
  | 12 => 0xcdd587a2e770007380124000000000
  | 13 => 0x2bf52d2e7c1329062d4813a000000000
  | 14 => 0x778f9da0c3b75084ba8028000102000
  | 15 => 0x4fad5e1ef1920106500036000102000
  | _ => 0

private def maskT0B101 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x369233c46a559c6264e2124000000000
  | 1 => 0x277d546d466740000e0203a000000000
  | 2 => 0x1056a183e5236080270001e000000000
  | 3 => 0x24600551d9fc7100578003a000000000
  | 4 => 0x8ce4b346604ab426d4a124000000000
  | 5 => 0x67fa6c8c3e5d5027e88128000102000
  | 6 => 0xa8f3fcad19a38405982024000000000
  | 7 => 0x301ed32137df98426c42128000102000
  | 8 => 0x3985a10f86664940074a03a000000000
  | 9 => 0x2d254029ef5f1d424eea13a000000000
  | 10 => 0x258b5fa82bfec942464a13a000000000
  | 11 => 0x221a12a103c1140008a0024000000000
  | 12 => 0xeb5023a485f18025cc013a000000000
  | 13 => 0xdbe3d55296a0840444203a000000000
  | 14 => 0x3aa52266046ff0027f80100000000000
  | 15 => 0x33f03be82de51027288100000000000
  | _ => 0

private def maskT0B102 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x28c2c62063ba8d40546a000000000000
  | 1 => 0x2cd6c7191363d9401eca000000000000
  | 2 => 0x79b2878305b89007848012000000000
  | 3 => 0xc7cf177877ee4027720100000000000
  | 4 => 0x11e2333f1c45c8422e42100000000000
  | 5 => 0x37a69e08faf000000000000000000000
  | 6 => 0x17e00fff6c5ff0027f80100000000000
  | 7 => 0x19cc7e28123a384051c2000000000000
  | 8 => 0xef5ed6e988b2c405962000000000000
  | 9 => 0x8d736fa2ec180000c00000000000000
  | 10 => 0xb8406b6fc1a384051c2000000000000
  | 11 => 0xf619daeef9e51027288100000000000
  | 12 => 0x2df62756c011394035ca01e000000000
  | 13 => 0x37ff96410ca1140008a0000000000000
  | 14 => 0x68591886f157d422bea100000000000
  | 15 => 0x9bd0419a834dc4226e2100000000000
  | _ => 0

private def maskT0B103 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xfd90a822fcd027e68100000000000
  | 1 => 0x3d7d91318a257d422bea100000000000
  | 2 => 0x38993284a5bff0027f80100000000000
  | 3 => 0x3e681c766e20b50005a8000000000000
  | 4 => 0x37ff965d878ff0027f80100000000000
  | 5 => 0x310981b62acee4027720100000000000
  | 6 => 0x4479ad968e0b50005a8000000000000
  | 7 => 0x3bd28e48791b99405cca000000000000
  | 8 => 0x1c76ec310e11140008a0000000000000
  | 9 => 0x37d221aba19a384051c2000000000000
  | 10 => 0x22dd694319f768003b40000000000000
  | 11 => 0x21527434471b99405cca000000000000
  | 12 => 0x142b269e912a8d40546a000000000000
  | 13 => 0xd94de651d44dc4226e2100000000000
  | 14 => 0x2df590124f331c0218e0100000000000
  | 15 => 0x173cb5d972df78026fc010a000000000
  | _ => 0

private def maskT0B104 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1f4b52778ccafd004fe800c000102000
  | 1 => 0x19e6f1642951a1000d08000000000000
  | 2 => 0x2c205094327a6000270003a000000000
  | 3 => 0x173eab89027f45027a28100000000000
  | 4 => 0x37f7772c3dc981024c08100000000000
  | 5 => 0x6983b291a9a384051c2000000000000
  | 6 => 0x349569d6f2f1a1000d08000000000000
  | 7 => 0x34786b589760b50005a8000000000000
  | 8 => 0x35622b3808488422442100000180000
  | 9 => 0xad4d79e69ca8d40546a000000000000
  | 10 => 0x1adecb7f7a81a1000d08000000000000
  | 11 => 0x22584c0f192a384051c2000000000000
  | 12 => 0x1f4ed65d3b31140008a0000000000000
  | 13 => 0x11826fc17c6b99405cca000000000000
  | 14 => 0x1416fdf11f10b50005a8000000000000
  | 15 => 0x682a8200e3b2c405962000000000000
  | _ => 0

private def maskT0B105 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x34adf991b538bbbe2c86000000000000
  | 1 => 0xdb6b08d641480ac3f68000000000000
  | 2 => 0x117d011f0081630029e2000000000000
  | 3 => 0x2d66db84bcc248f6c88a000000000000
  | 4 => 0x5d3e34aae07f5b8a40a008000040000
  | 5 => 0x28821ce76e5160875a00000000000000
  | 6 => 0x18bcd7d4ac831375a9e2000000000000
  | 7 => 0x2de2a1241e9361e840ca000000000000
  | 8 => 0x36da8701fb9e6fe19eca000000000000
  | 9 => 0x7496e108e874e5c34e020000080000
  | 10 => 0x3e91463ce695bd11d0ca02c000000000
  | 11 => 0x386ab650c94f1bedb80a005000040000
  | 12 => 0x2e452dd71d7c388b0d4e005000040000
  | 13 => 0x3ddf914193d89ae43f68000000000000
  | 14 => 0x18bf0721c5eda7c45c4005000040000
  | 15 => 0x1bcb5cb789497797dc2a008000000000
  | _ => 0

private def maskT0B106 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x216ed80111e0877756e6005000040000
  | 1 => 0x3197bed2a60e44ed8108000000040000
  | 2 => 0x25c9ae9279282a6fbac0008000040000
  | 3 => 0x14ceedd89007277300a6008000040000
  | 4 => 0x1280419eecb495c011ae005000040000
  | 5 => 0x12af7b8b24662b3e9406005000000000
  | 6 => 0xdc9c295352ddff0f56e00d000000000
  | 7 => 0x3821e45e2ee7acb95d22005000040000
  | 8 => 0x370f84798437be6173e4008000000000
  | 9 => 0x22cdd30ee65678f4f64c008000000000
  | 10 => 0x2a300fba521b21c38d4e008000000000
  | 11 => 0xa6f49ad6fb9d2926a0a005000040000
  | 12 => 0xe20c5b44c5a6df15fae00d000040000
  | 13 => 0x39bab22936f0276cd34e008000000000
  | 14 => 0x311a5a99e1467a16e3e400d000040000
  | 15 => 0x1fa274f9cdf6d59d1de8000000040000
  | _ => 0

private def maskT0B107 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1093c4c0f10b88b15562000000000000
  | 1 => 0x12e53ad9fc98214ee4c0000000040000
  | 2 => 0x1bd8712c965af79c300c00d000040000
  | 3 => 0xbb13c5af905014f3f68000000000000
  | 4 => 0x14cea0b50d4ef3a85e00000000000000
  | 5 => 0x1d76ee8f5ab0b0bbbf68000000000000
  | 6 => 0x25b7cf65246511b3e3e2025000000000
  | 7 => 0x3917d87d22a268f66168000000000000
  | 8 => 0x24474d2ae88911d30000000000000000
  | 9 => 0x12fa715a216182dc29e2000000000000
  | 10 => 0x974915547908c64168a000000000000
  | 11 => 0xd019773bfcb5925c0ca000000000000
  | 12 => 0x2c153a7195f4f10effa2000000000000
  | 13 => 0x252d1b8c537843468840000000000000
  | 14 => 0x3e1631a89584458c5e00000000000000
  | 15 => 0xde15b483b20a1169eca000000000000
  | _ => 0

private def maskT0B108 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1d1ab958d33746ae0000000000000000
  | 1 => 0x3e0f87d368371a61c4cc000000000000
  | 2 => 0x1609e172c7548a780840000000000000
  | 3 => 0x374aa71c623f03e9968a000000000000
  | 4 => 0x3403693ae583fc9a77e2000000000000
  | 5 => 0x3f7c66dac5483219bf68000000000000
  | 6 => 0x319ebadac54b8aaebf68000000000000
  | 7 => 0x1609e1ada0b48a780840000000000000
  | 8 => 0x387fd57793230bf168a000000000000
  | 9 => 0x26372bcaa33cb18aa9e2000000000000
  | 10 => 0x38f69f22ab9d35a79840008000000000
  | 11 => 0xbb13c8d6415014f3f68000000000000
  | 12 => 0x10b94a74707ad212f7e2000000000000
  | 13 => 0x1ebb5ac7eff29296a9e2000000000000
  | 14 => 0x3f2f9901a0f077e67de0000000000000
  | 15 => 0x3eb8a1c25331526877e2000000000000
  | _ => 0

private def maskT0B109 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xa46a619697291a98000000000000000
  | 1 => 0x34fe063597e3c3c1f7e2000000000000
  | 2 => 0x95c979f432096259608000000000000
  | 3 => 0x1d8f63e0cbf1aad8b648014000000000
  | 4 => 0xdae3dd900775fcf21a2000000000000
  | 5 => 0x2fc52deb7e82e00b488a000000000000
  | 6 => 0x2a4bbf938b9c77efb728000000000000
  | 7 => 0x2333213e7bde29c83728000000000000
  | 8 => 0x87c89a4ee2f3a226928000000000000
  | 9 => 0x1e6ad5e3f16abfb56928000000000000
  | 10 => 0xabb3f17dd07f6cfaac0005000000000
  | 11 => 0x224c517ba7b337545d22000000000000
  | 12 => 0x3855e135cd1f9d785c4002d000140000
  | 13 => 0xfaae4904ea9523955c4000000000000
  | 14 => 0x1b8c0da61c7efa4340ca000000000000
  | 15 => 0x1f59e6d67213e239a1a2000000000000
  | _ => 0

private def maskT0B110 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x24f06a4e7476c85affa2000000000000
  | 1 => 0x78fffcb80c5d7bfa1a2000000000000
  | 2 => 0x4a492080c37ed21b62000000000000
  | 3 => 0x29f1fd68ec8d917f3f68000000000000
  | 4 => 0x1fb2b076959d806422c000000000000
  | 5 => 0x2d4e42bce23cad4875a4080000000000
  | 6 => 0xa7b94d3ecaf15e0a00c000000000000
  | 7 => 0x21e2569622b932b2e64c000000000000
  | 8 => 0x304a2981513a943a00c000000000000
  | 9 => 0xe61e7842f3e6fe1fdc8000000000000
  | 10 => 0x532585022c392c41e6c000000000000
  | 11 => 0x336754462aa4a534f744000000000000
  | 12 => 0x2b7739fd29c1728b29a4000000000000
  | 13 => 0x62b2138e92b03cec26c080000000000
  | 14 => 0x21d18c692c4eb7fa19e8080000120000
  | 15 => 0x3b4009a3b04ad5691e6c024000000000
  | _ => 0

private def maskT0B111 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1226d211365b0924200000000000000
  | 1 => 0x19b24fad227c30c7582c000000000000
  | 2 => 0x25f263e283328fc93b44080000000000
  | 3 => 0x7ae7f26f3fe22814ee0000000000000
  | 4 => 0x33911c2d18d7a0766464096800000000
  | 5 => 0xf0277f093b2dfc86a20080000000000
  | 6 => 0x3ebaeee2d7139f92ddc00b2000040000
  | 7 => 0x2d1053fc82329c9ab5000b2000040000
  | 8 => 0x252faab26c5d51c66ec4032000000000
  | 9 => 0x1ca05395a0b97fb74c280b2000040000
  | 10 => 0x20cf8f6fd85c85408a68096800040000
  | 11 => 0x3c32179928bb68f1862c000000040000
  | 12 => 0x19a715843a00461dd200b2000000000
  | 13 => 0x1195f0c28fa318068b80096800040000
  | 14 => 0x3feded9f8f6f76e99028016800000000
  | 15 => 0xdc3bb0b0ddd82174164024800040000
  | _ => 0

private def maskT0B112 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x27d022e49115c0e8fec4032000000000
  | 1 => 0x223ae5e9d72736f1be80000000000000
  | 2 => 0x1d3cb3fde5bd8457cc000a4800000000
  | 3 => 0x30081e14f0fd18046f2c032000000000
  | 4 => 0x3e50f45ab7a976fb6e0c000000000000
  | 5 => 0x3bc245788223d234a9a4000000040000
  | 6 => 0x16fff8456fe628e31ca40b2000000000
  | 7 => 0x3ecc473fe2190a75f260080000000000
  | 8 => 0x948ee95677f5819b7c8000000000000
  | 9 => 0x3794bca5a5e3ffd9c640000000000000
  | 10 => 0x12d8ac23d5682042ad44020000000000
  | 11 => 0x3a0dac59ed4eaf81e260080000000000
  | 12 => 0x27f3ed89bf4c5a3f2d88080000000000
  | 13 => 0xb06c502162edb625688032000000000
  | 14 => 0x85c2bedc17fcc786bc8080000000000
  | 15 => 0x2e6220832129848dfc0c080000000000
  | _ => 0

private def maskT0B113 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3d01d3ca8e9136e688a0000000000000
  | 1 => 0x194e1b1ce0fff64775a4080000000000
  | 2 => 0xa6e5a5372d24f308000000000000000
  | 3 => 0xac3e6600f1341928d84080000000000
  | 4 => 0x23c1ab281d70090d0d84080000000000
  | 5 => 0x945591c8ae369ba55a8080000000000
  | 6 => 0x3cc88220641859c17188000000000000
  | 7 => 0xb0daf777d5247bacbc4080000000000
  | 8 => 0x2d300be9b05b6098a00c000000000000
  | 9 => 0x378274cc13832d504c00080000040000
  | 10 => 0x5790a52785361301e6c000000000000
  | 11 => 0x2ceb0087d801a6b9f820000000000000
  | 12 => 0x37cdb4dedda1dd4cd82c000000000000
  | 13 => 0x926cbb90671a3007c0c080000000000
  | 14 => 0x2081da3baed30e97cfe8000000000000
  | 15 => 0x2853ba982dd1ebdcf6ac000000000000
  | _ => 0

private def maskT0B114 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x4201cd880ee5d50be60000000000000
  | 1 => 0x1124488a221e673200c000000000000
  | 2 => 0x3724db36a6d6f75e23e0000000000000
  | 3 => 0x3d0d3b3749d95d1537c8000000000000
  | 4 => 0x23b883c2e41530a4b7c8000000000000
  | 5 => 0x5dc5698c2935285ad88080000000000
  | 6 => 0x2189257ac90afdc21da0080000000000
  | 7 => 0x27ffe7b8df1375f221c8082000000000
  | 8 => 0x17ade1a46f00f6f04640000000000000
  | 9 => 0x2a507a0423f5bda455a8080000000000
  | 10 => 0x724be4095f810031e6c000000000000
  | 11 => 0x6caae79f55de1d913e8080000000000
  | 12 => 0xc6ce6f36534e8d1a40080000000000
  | 13 => 0x1afdf23edfb1504c3a4c080000000000
  | 14 => 0x813ce1f8e72d3db17c4000000000000
  | 15 => 0x32e2377e219fa3dfba4c080000000000
  | _ => 0

private def maskT0B115 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x19d6f0fb97878f68cd48020000100000
  | 1 => 0x294fbf427da82907820000000000000
  | 2 => 0x39f720f4390adfdc4ee0024800000000
  | 3 => 0x1c6199dcaccdfd044fe8000000000000
  | 4 => 0x37ed94e9cc89010755a8080000000000
  | 5 => 0x37c6a6ce35109461dc00080000000000
  | 6 => 0x5fb17b6e8bda99c664c000000000000
  | 7 => 0x12b779539bcca9737188000000000000
  | 8 => 0x18a31acf44039d55b3d1000000000000
  | 9 => 0xfe0e8fa240e7c4b3e89000000000000
  | 10 => 0x12ed89b620001a21ed88000000000000
  | 11 => 0x2958543fc40838c80ff1000000000000
  | 12 => 0x2a6a858a4003c98c6290000000000000
  | 13 => 0x60c7c2420078ad88908000000000000
  | 14 => 0x2ba0bc29400778ef8a50000000000000
  | 15 => 0x3f46c1746001cba3dd18000000000000
  | _ => 0

private def maskT0B116 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3b998559240eb5e45649000000000000
  | 1 => 0x41996152002f6398548000000000000
  | 2 => 0x2aeaeb4800062773d200000000000000
  | 3 => 0x37c3d029400bf933ef50032800040000
  | 4 => 0x32b89d746007d561dd18008000000000
  | 5 => 0x1799842d4403122f7e51032800000000
  | 6 => 0x1ff200fa24024b35be89000000000000
  | 7 => 0x1a677612a405cae5f1a9032800000000
  | 8 => 0x19a246d7600082af35d8000000000000
  | 9 => 0x103e7d56e019f28c24b8032800010000
  | 10 => 0x3e96e0eb20210c5fafc8000800010000
  | 11 => 0x193dc57c044d48c64f01000000000000
  | 12 => 0x1d502ae8a081a8695a28032000010000
  | 13 => 0x2afe691a850c24ee53a1000800010000
  | 14 => 0x1c8e2fc582037eac7460000800010000
  | 15 => 0x13ef11b9c405a7478b70032800000000
  | _ => 0

private def maskT0B117 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x33dac07fe80a2eee9ff8000000000000
  | 1 => 0x3f6369d3140d635690c1032000000000
  | 2 => 0x9c6c5b6200a72d99980032000000000
  | 3 => 0x14db9b9b000295f713d0032800000000
  | 4 => 0x32c3aeb9200ea211ce68032000010000
  | 5 => 0x7c5f76c240cdb694e49000800010000
  | 6 => 0x1d2495ed640155687ed9000800010000
  | 7 => 0x3c9ee811240769d80449000800000000
  | 8 => 0xe8adf7be404d0e9c8f9000000010000
  | 9 => 0x2df0e372e40db6bcb9b9032800010000
  | 10 => 0x1863100d6403bb89fb59032000010000
  | 11 => 0x3fd7e467440715325cd1032800000000
  | 12 => 0x5557da36009385948d8032000010000
  | 13 => 0x2d8cfd5d20029212d748000000000000
  | 14 => 0x2443eae20003e16a7880020000000000
  | 15 => 0x350726c2400be0cab090000000000000
  | _ => 0

private def maskT0B118 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2b8b7011240bd43a8449000000000000
  | 1 => 0x35a2037064023a115c19000000000000
  | 2 => 0x2eacac152003d3d20548000000000000
  | 3 => 0xcd224fe2002ec67bf88000000000000
  | 4 => 0x2d41defa240a05c73e89000000000000
  | 5 => 0x1e10f838640d64900e19000000000000
  | 6 => 0x17dc515924019f7a5649000000000000
  | 7 => 0x1c0df370640d11cfdc19000000000000
  | 8 => 0x3a967f614001e883d850000000000000
  | 9 => 0xfe3e5a3000abf56e8c0000000000000
  | 10 => 0x28998161400d33af5850000000000000
  | 11 => 0xaccc55d24070299b749032000010000
  | 12 => 0x2874839b6400f5f5e6d9000000000000
  | 13 => 0x280dab5d200b186dd748000000000000
  | 14 => 0x20bf3170640a69405c19000000000000
  | 15 => 0x1032d574600651cadd18000000000000
  | _ => 0

private def maskT0B119 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x16f38bb22409b1476c89000000000000
  | 1 => 0x3256218e440e05a46391000000000000
  | 2 => 0x2e5023b22406f1056c89000000000000
  | 3 => 0x9e764fa240ffda83e89000000000000
  | 4 => 0x3e8ff43c600e9a750f18000000000000
  | 5 => 0xadd48ef04078048bbc1000000000000
  | 6 => 0x238ef092e0076591a4b8000000000000
  | 7 => 0x1efe08f5c009af26d970032000000000
  | 8 => 0x1b0584d8800ebe34b620000000000000
  | 9 => 0x1a22bf5d200fb210d748000000000000
  | 10 => 0x12568e17c0067e5b85f0000000000000
  | 11 => 0xd9b7faf40075b1a6ed0002800000000
  | 12 => 0x2360ff8e440eb86a6391000000000000
  | 13 => 0x38c6382d44071d006e51032800000000
  | 14 => 0x14e571b62008b7e96d88000000000000
  | 15 => 0x28c16140058218d850000000000000
  | _ => 0

private def maskT0B120 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x18da4afa24029d153e89000000000000
  | 1 => 0x18a8a79b640d0720e6d9000000000000
  | 2 => 0x246074ef040b56ea3bc1000000000000
  | 3 => 0x3880982d440e5aec8b51000000000000
  | 4 => 0x22c1462fa40d3b576be9012000110000
  | 5 => 0x19335e3c600b621a0f18000000000000
  | 6 => 0xbfe7aeb00064b94bac0000000000000
  | 7 => 0x56c31654407b4b8d951000000000000
  | 8 => 0x26e2dd1aa40106b446a9000000000000
  | 9 => 0x1efe14c24005eeffb090000000000000
  | 10 => 0x193ba229400347920a50000000000000
  | 11 => 0x3e6a0ad3640d9fd1b4d9000000000000
  | 12 => 0x15ba213c0f3000000600000000000000
  | 13 => 0xf125e7892f000000000000000000000
  | 14 => 0x2f71ceb907b0000037f2000000000000
  | 15 => 0x3043f792555000005d18000000000000
  | _ => 0

private def maskT0B121 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x342e9b5e986000000000000000000000
  | 1 => 0x2dc5855c3b3000000fb8000000000000
  | 2 => 0x2e182400c240000062aa000000000000
  | 3 => 0x3ce9e027a92000000108000000000000
  | 4 => 0x1d74803bbb80000064fa000000000000
  | 5 => 0x17a76efb693000000948000000000000
  | 6 => 0x1a72098cad2000003fb2000000000000
  | 7 => 0x3c12c806a750000036fa000000000000
  | 8 => 0x20a4535c60b0000036fa028000080000
  | 9 => 0x6256c5153f000005558024000000000
  | 10 => 0xe201abea44000002502000000000000
  | 11 => 0x33ba9ce0a438000050020360000c0000
  | 12 => 0x1945922789e000005450000000000000
  | 13 => 0x80a65e2541000000840000000000000
  | 14 => 0x3c41ad8f04800000d65201a0000c0000
  | 15 => 0x350c350445e000010452032000000000
  | _ => 0

private def maskT0B122 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3797526e52e800020dfa0360000c0000
  | 1 => 0x39c99afe403000045ee00280000c0000
  | 2 => 0x1137d9d7a07000085cca02c000000000
  | 3 => 0x1b0f8ccca7d80010373a01a0000c0000
  | 4 => 0x35e9b9fd4f00020361a0280000c0000
  | 5 => 0x31e94dd10a200040605a0280000c0000
  | 6 => 0x416ace8f8580080001201e000000000
  | 7 => 0x339218dcf1c001003058032000000000
  | 8 => 0x28f2f2c67540020055b8000000000000
  | 9 => 0x368e9f8771400400337a01a0000c0000
  | 10 => 0x57e2ebc4a30080008a00040000c0000
  | 11 => 0x1a0398618d50100063780040000c0000
  | 12 => 0xa571267580020000fea01a0000c0000
  | 13 => 0x21a3319187c0400054a20360000c0000
  | 14 => 0x1c7da725cea080005dea0360000c0000
  | 15 => 0x11f7eb3125c1000059aa01e000000000
  | _ => 0

private def maskT0B123 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2063df12433a000000f2032000000000
  | 1 => 0x282aafa97d4c000002f00040000c0000
  | 2 => 0xdde69d65da00000600801a000000000
  | 3 => 0x140e34df67e000000000000000000000
  | 4 => 0x290fbe1e7a9000000000000000000000
  | 5 => 0x2ee30c2f731000005450000000000000
  | 6 => 0x32e82680551000000108000000000000
  | 7 => 0x1d6c4851c44000005558000000000000
  | 8 => 0x2660c0054ad000000840000000000000
  | 9 => 0x55d7aeec5a0000008400280000c0000
  | 10 => 0x72e552d7e7000005d18000000000000
  | 11 => 0x76360591d90000063a2000000000000
  | 12 => 0x235a5832d54000005010000000000000
  | 13 => 0x1bca8d53088000005d18000000000000
  | 14 => 0x375db6d192b0000037f2000000000000
  | 15 => 0x1d65922acac000005d18000000000000
  | _ => 0

private def maskT0B124 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3d3bb676f09000006fb0032000000000
  | 1 => 0x1dea41adaa7000006be2000000000000
  | 2 => 0xcdeec3e410000005d18000000000000
  | 3 => 0x375db60ef550000037f2000000000000
  | 4 => 0x1afddac0ead000000948000000000000
  | 5 => 0x297b441eca5000000000000000000000
  | 6 => 0x1437a2867a70000063a2000000000000
  | 7 => 0x3379b7cb9d000006be2000000000000
  | 8 => 0x3043f7230a3000005d18000000000000
  | 9 => 0x3b78723023f000005d18000000000000
  | 10 => 0x1de39a61c3a000003b40000000000000
  | 11 => 0xf2f3270e3000003fb2000000000000
  | 12 => 0x19beba9fdc20000062aa000000000000
  | 13 => 0x9da71f65000000948000000000000
  | 14 => 0x3debb10ba8c000000db0000000000000
  | 15 => 0x2b3806326ca000003c1801c000000000
  | _ => 0

private def maskT0B125 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1e90eea45bc000005562000000000000
  | 1 => 0x34ec25ece210000062aa000000000000
  | 2 => 0x27b8bf7d0d20000004a0000000000000
  | 3 => 0x33094d6cf45000003eba000000000000
  | 4 => 0x1961f84104000006cba02c000000000
  | 5 => 0x1377fa95111000000948000000000000
  | 6 => 0xda2f79b050000036fa000000000000
  | 7 => 0x2408530785f0000063a2000000000000
  | 8 => 0x3e510d0104000000f48028000140000
  | 9 => 0x1e04d9b8ad20000036fa000000000000
  | 10 => 0x269be8326c3000003eba000000000000
  | 11 => 0x37b78db312a000000948000000000000
  | 12 => 0x3b71a8ad6b0000005558000000000000
  | 13 => 0x38288d306150000037f2000000000000
  | 14 => 0x466c5ae0d80000063a2000000000000
  | 15 => 0x261de0a9887000000000000000000000
  | _ => 0

private def maskT0B126 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x7eaac407d2861804800000000000000
  | 1 => 0x1e80fa35201a8a000000000000000000
  | 2 => 0x50b5edf64a96ac00000000000000000
  | 3 => 0x1952c7b8740ceb400000000000000000
  | 4 => 0x25bc3f132a8a8a000000000000000000
  | 5 => 0x1200077e798dc3400400000000000000
  | 6 => 0xbd5b6c1bca863800000000000000000
  | 7 => 0x3b89d4ea8fdb83400000000000000000
  | 8 => 0x1a4ae16b61462a400000000000000000
  | 9 => 0x18cd3fd41bdb83400000000000000000
  | 10 => 0x2990584528c3e0c00000000000000000
  | 11 => 0x2e369f8f38e581800000000000000000
  | 12 => 0x2ee9da82df3dabc00000000000000000
  | 13 => 0x4f58bb90b83c0c06500032000090000
  | 14 => 0x2dab0e40b85203800400020000000000
  | 15 => 0x2c8111521a3388800c00000000000000
  | _ => 0

private def maskT0B127 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x232663d68961c9400000000000000000
  | 1 => 0x2eac576f68bde2000000000000000000
  | 2 => 0x3f3ef322da5768000000000000000000
  | 3 => 0xa90725ee1722000400000000200000
  | 4 => 0x39ca3dd213a2c8800000022000410000
  | 5 => 0x19ff5faa90c2e8c00000022000810000
  | 6 => 0xb662a4bdabde2006100000001000000
  | 7 => 0x38a1aeb366a13b000000022002010000
  | 8 => 0x2385de9ab2b291806100000004000000
  | 9 => 0xae409fb304e02c00000000008000000
  | 10 => 0x6a6d132f44ceb406100000010000000
  | 11 => 0x23892bf6422d88406500000020000000
  | 12 => 0x9c27e55c944e3800000000040000000
  | 13 => 0x9ee34acd46a61400400002080010000
  | 14 => 0x178855e1761d9a006100020100000000
  | 15 => 0x17ec109036bfe1c00000022200010000
  | _ => 0

private def maskT0B128 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x5ed6a17630b2006100002400010000
  | 1 => 0x103020f457d901800000000800000000
  | 2 => 0x2a31e24d028661400000021000000000
  | 3 => 0x2d59763a3d3748000400000000010000
  | 4 => 0x36ac9dd4945661400000024000000000
  | 5 => 0x240eba02f56fe0800000008000000000
  | 6 => 0xeec80c63ecca406100032000010000
  | 7 => 0x140e34df67e000000000000000000000
  | 8 => 0x389d1a53c87a8a000000000000000000
  | 9 => 0x8986d2a20a768000000000000000000
  | 10 => 0x1b2445221b5661400000000000000000
  | 11 => 0x349eebb6b5b83400000000000000000
  | 12 => 0x3ff801aaac2a8a000000000000000000
  | 13 => 0x384eb75c67c4a9c00000000000000000
  | 14 => 0x2e3f65075f2ceb400000000000000000
  | 15 => 0x25cec6554583e0c00000000000000000
  | _ => 0

private def maskT0B129 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3038e9ca7a3e6a800000000000000000
  | 1 => 0x32dbbd7929dceb400000000000000000
  | 2 => 0x1d2726b7f1a96ac00000000000000000
  | 3 => 0x3474a200eb9ceb400000000000000000
  | 4 => 0x39bb1ae278e748400000000000000000
  | 5 => 0x374d8243a673e0c00000000000000000
  | 6 => 0x345d7859d2b661400000000000000000
  | 7 => 0x1d27266896496ac00000000000000000
  | 8 => 0x4052fa22ad109400000000000000000
  | 9 => 0x38e9e05378ba8a000000000000000000
  | 10 => 0x9a4f7a8f83488c00000000000000000
  | 11 => 0x29905892b5d3e0c00000000000000000
  | 12 => 0x1952c7092b6ceb400000000000000000
  | 13 => 0x1269421a02aceb400000000000000000
  | 14 => 0x3fcd3a780894c3c06100000000000000
  | 15 => 0xc2e51cc518488c00000000000000000
  | _ => 0

private def maskT0B130 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2de18c131022e9800000000000000000
  | 1 => 0xf638b5e84bb83400000000000000000
  | 2 => 0x68c2ed50c74ab804900000000000000
  | 3 => 0x2f5b2ae0957ec8c00000002000010000
  | 4 => 0x16495eabb6d9b2c00000000000000000
  | 5 => 0xb313602e12e9800000000000000000
  | 6 => 0x24763bac2bb283c00000000000000000
  | 7 => 0x78b2868574863800000000000000000
  | 8 => 0xd9298ad4d4521800000000000000000
  | 9 => 0xd8f0ff7d11109400000000000000000
  | 10 => 0x36cdcbd9d0f0b800000000000000000
  | 11 => 0x2809a264b55e02c00000000000000000
  | 12 => 0x2b28acdf852b81402900032000190000
  | 13 => 0xc208e31329581800000000000000000
  | 14 => 0x3cb5da59a79581800000000000000000
  | 15 => 0x294f78d1d2a109400000000000000000
  | _ => 0

private def maskT0B131 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x25540e47c41b83400000000000000000
  | 1 => 0x12521d5602496ac00000000000000000
  | 2 => 0x19f590808fc488c00000000000000000
  | 3 => 0x8b1b7c6e0cde2000000000000000000
  | 4 => 0x26ea0006621669364dd4000000000000
  | 5 => 0x3526002f2ba948c56a4c000000000000
  | 6 => 0x38d9003d557e58b771b2000000000000
  | 7 => 0x2b5001fff6bd2febd6a0000000000000
  | 8 => 0x7af019a6a65cb1d0f5e000000000000
  | 9 => 0x234e00f4577e4e63c69c000000000000
  | 10 => 0x21ba00a999fe8197c374000000000000
  | 11 => 0x2cff0052ac9c6db459fe000000000000
  | 12 => 0x1f2d005703f1d7f8be5a000000000000
  | 13 => 0x347d01f7eaab5ec7e8fa000000000000
  | 14 => 0x3e9700b990ba5d367d2e000000000000
  | 15 => 0x2a0b01fdc1150454d416000000000000
  | _ => 0

private def maskT0B132 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x347d008c292794a5e8fa000000000000
  | 1 => 0xce100a852db4783c9c2028000000000
  | 2 => 0x318a01822952ac54f114009000080000
  | 3 => 0x324800e45a4cd517a6900010001a0000
  | 4 => 0x26ea01b07dd482ad9fd40090001a0000
  | 5 => 0x347d01f721ccaf2de8fa000000000000
  | 6 => 0x149c01ebed6ebcd2a938000000000000
  | 7 => 0x3de700ba26c51366a9ce0090001a0000
  | 8 => 0x5df02c8db731c2799be0090001a0000
  | 9 => 0x1fbc05360af76ce6bd78021000000000
  | 10 => 0xa5808fa86af821c16b0021000000000
  | 11 => 0x2bac11f16ed33e02d558021000000000
  | 12 => 0x330d209608966f6d261a000000000000
  | 13 => 0x3b8241a2b368bee027040280001a0000
  | 14 => 0xddc8121b526c9fc59b8021000000000
  | 15 => 0x105700aa9b9519ad32ac0090001a0000
  | _ => 0

private def maskT0B133 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x22210085cc0ef1c996460090001a0000
  | 1 => 0x1571013b0d843c1ceaea000000000000
  | 2 => 0x307d01b814c099b5f0ea0280001a0000
  | 3 => 0x2333003190abe9fdd4460090001a0000
  | 4 => 0x3482001259bb8c37eb44021000000000
  | 5 => 0x2926001d31c8dfd2c2cc0280001a0000
  | 6 => 0x33640183b4a7af87a7c8000000000000
  | 7 => 0x9450193de7a19d9808a0280001a0000
  | 8 => 0x109c01e28e6bf3fc6738021000000000
  | 9 => 0x368901b1266628406512000000000000
  | 10 => 0x14630074191be0ab6ac60090001a0000
  | 11 => 0x1f500183debb52cf0ea00280001a0000
  | 12 => 0x328901fc9a0862236512000000000000
  | 13 => 0x15c7005b1f1ac73eab8e000000000000
  | 14 => 0x2ce20105ade548d359c4000000000000
  | 15 => 0x6f400d4dc24dc038de8000000000000
  | _ => 0

private def maskT0B134 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x261501984542762b4c2a000000000000
  | 1 => 0x328901148aa36bbbe512000000000000
  | 2 => 0x3fcc005af930ea16bd98021000000000
  | 3 => 0x2b5000923a70f2b156a0000000000000
  | 4 => 0x133300d61c4ce28f2666000000000000
  | 5 => 0x3289015d51647b4e6512000000000000
  | 6 => 0x1333010c14a3aede2666000000000000
  | 7 => 0x393801bfa11202507270000000000000
  | 8 => 0x2da4009981b0448adb48000000000000
  | 9 => 0x133301ddd3f3c667a666000000000000
  | 10 => 0x2b50004d96f9ef88d6a0000000000000
  | 11 => 0x133301d37343aede2666000000000000
  | 12 => 0x149c0010c51b9901a938000000000000
  | 13 => 0x3863012fe2435c6f70c6000000000000
  | 14 => 0x126800e3a2e02b53a4d0000000000000
  | 15 => 0x2a0b0185e0c4e1e4d416000000000000
  | _ => 0

private def maskT0B135 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3fcc00a544b393397f98000000000000
  | 1 => 0x2a0b01fbfc8d9464d416000000000000
  | 2 => 0x344901bb78cbcfb86892000000000000
  | 3 => 0x2da40052f3110b61db48000000000000
  | 4 => 0x20e1018e8f1afa7bc1c2000000000000
  | 5 => 0xd450032d1abf11a1a8a000000000000
  | 6 => 0x102a0026c4e660652054000000000000
  | 7 => 0x29ed00ca69895a8571da011000000000
  | 8 => 0x126800d4d5aeb96b24d0000000000000
  | 9 => 0x2cff003d5cf0555ed9fe000000000000
  | 10 => 0xc1e00c80f1f1319983c000000000000
  | 11 => 0x20e101d058fa92c241c2000000000000
  | 12 => 0x2cff000df4748e3159fe000000000000
  | 13 => 0x6990061702b74370d32000000000000
  | 14 => 0x1e76010979201f203cec000000000000
  | 15 => 0x1333018a641f77e8a666000000000000
  | _ => 0

private def maskT0B136 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x31d9004f2756f8ee33b2028000020000
  | 1 => 0x33d200349792515067a4000000000000
  | 2 => 0x6f40099b9788c508de8000000000000
  | 3 => 0x37d20053d43bb36cfda40090001a0000
  | 4 => 0x15b019d2aa5f6e582b6000000000000
  | 5 => 0x1f7e00483011603f3efc000000000000
  | 6 => 0x15b01efb6494b8002b6000000000000
  | 7 => 0x7af011cd1b12ae60f5e000000000000
  | 8 => 0x71c4b8667fdf42d1c83000000000000
  | 9 => 0x12fe1ccbc552e1ada938000000000000
  | 10 => 0x5b1b7752daac500ce3a000000000000
  | 11 => 0x2e5118ec701cf7c6d7a1000000000000
  | 12 => 0x1d97246484b441ecba29000000000000
  | 13 => 0x3f1fe86117fccf45919b000000000000
  | 14 => 0x2406b09d7b4dea767528000000000000
  | 15 => 0x2378593cbbc13bca938000000000000
  | _ => 0

private def maskT0B137 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x36edf35e70b748f923b2000000000000
  | 1 => 0x1effd07cc31459eca3b2000000000000
  | 2 => 0x6ecc9b2154c2b981311000000000000
  | 3 => 0x4b6f83f7fc0d644e3a000000000000
  | 4 => 0x2f32ec80acefc9dc6702000000000000
  | 5 => 0x3a12496535c5ad3c1399012000000000
  | 6 => 0x36a4d334c7f40f0b57a1000000000000
  | 7 => 0x269b528cfeadc121edb2021000040000
  | 8 => 0x27e78053312b60697f8301b000000000
  | 9 => 0x30cd6615941c9ff920a3000000000000
  | 10 => 0x28cd173c9093d7c56bb013000000000
  | 11 => 0xbeee85b2ef222cd9881013000000000
  | 12 => 0x1602aae87950c36031b9013000000000
  | 13 => 0x3ef0a7b4106b1caa2222013000120000
  | 14 => 0x50f24920877d38bde12013000000000
  | 15 => 0x1a5ab05fb9b46b63b40a021000000000
  | _ => 0

private def maskT0B138 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3fb08175766447971ba3032000000000
  | 1 => 0x2c9665d27435b630d883021000000000
  | 2 => 0x15d3ba27bf4d4904ad1b021000120000
  | 3 => 0x35ae92df294b92cef1bb021000000000
  | 4 => 0x1f2d580dcf1ea56ec51a032000120000
  | 5 => 0x2ca9cc46937b1e688992021000000000
  | 6 => 0x113dcc814e5b4401fe29021000120000
  | 7 => 0x14698f770b3ca03a70ba021000000000
  | 8 => 0x17d15d934a396a0685b3013000000000
  | 9 => 0x105167eb918040d5c189013000120000
  | 10 => 0x15777b9cad32a8b7658a013000120000
  | 11 => 0x2cb5ceca47ed5f4c8589013000000000
  | 12 => 0x346537db134381d7e38a013000000000
  | 13 => 0xd41b33d5a3a3abd6a22032000000000
  | 14 => 0x2493e5512efbad8e9ebb032000120000
  | 15 => 0x21d4dad4877ad10d54a2032000000000
  | _ => 0

private def maskT0B139 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1830cb7ae0d5db3455a3032000000000
  | 1 => 0x279cd2fa27ee360bdd2b000000000000
  | 2 => 0x22cf9064b2fb9673999b000000000000
  | 3 => 0x8d6316f9209491c57a1000000000000
  | 4 => 0x3cae1ff34c90b1e30a8a000000000000
  | 5 => 0x3a09b80a306ed3ed57a1000000000000
  | 6 => 0x22529b4a7922c76fd7a1000000000000
  | 7 => 0x3a9bd40badeefb9a7429000000000000
  | 8 => 0x52bcf2ecbd83cad4e3a000000000000
  | 9 => 0x3528bafad00a9caece3a000000000000
  | 10 => 0x7556b59561b1fea579b021000000000
  | 11 => 0xa7f687678a12c1f2938000000000000
  | 12 => 0x1ba3f42326f7f1caa3b2000000000000
  | 13 => 0xa3648379ce3317557a1000000000000
  | 14 => 0x105aefac2cb977de30a3000000000000
  | 15 => 0x1f6cfc6de454b41dd010000000000000
  | _ => 0

private def maskT0B140 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x11be29b46b19ccd2b0a3000000000000
  | 1 => 0xde26a479401443aba29000000000000
  | 2 => 0x2410bacffe9f7bda4e3a000000000000
  | 3 => 0x77eb50750a9e52ce3a000000000000
  | 4 => 0x25531d549ee3f03641a000000000000
  | 5 => 0x2a5141de6fd4672ec4b0000000000000
  | 6 => 0x2b31b85c3df82d81b333000000000000
  | 7 => 0x230cf0471fdafbc2a938000000000000
  | 8 => 0x20f773df5e36c72d7413000000000000
  | 9 => 0x296d6ff1b495d6ff1311000000000000
  | 10 => 0x34bb978669e11daaf498000000000000
  | 11 => 0x13c4e0a52791d804aa92030000000000
  | 12 => 0x15dfc92285ec63dd3a29000000000000
  | 13 => 0xd284db3031ed20b8000000000000000
  | 14 => 0xd1687ac9f3e215830a3000000000000
  | 15 => 0x3950a199961b98988c8a000000120000
  | _ => 0

private def maskT0B141 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xb6b761277c24963d7a1000000000000
  | 1 => 0x555ea4da4633859ed88000000000000
  | 2 => 0x371d71323f2456a557a1000000000000
  | 3 => 0x142f4b4e011f7bda4e3a000000000000
  | 4 => 0x3009b757aa8ebf39d809020000100000
  | 5 => 0x1413ce479d17381b4e3a000000000000
  | 6 => 0x35cc27c69bf347d644b0000000000000
  | 7 => 0x21959d6ba7d33859ed88000000000000
  | 8 => 0x1cc0604bcc056e7f413000000000000
  | 9 => 0x14569c51d6179b17d7a1000000000000
  | 10 => 0x39614c84cbea7e0c4e3a000000000000
  | 11 => 0x1e962faf31dadc050baa032000000000
  | 12 => 0x27e1b736e5b0c9f4827a000000000000
  | 13 => 0xf125e7892f000000000000000000000
  | 14 => 0x1545c9792e48b734f4c0000000000000
  | 15 => 0x714aafa0d5ba13f30aa000000000000
  | _ => 0

private def maskT0B142 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x251e3ea999fab8b1605a000000000000
  | 1 => 0x3125544522a0ccab7302000000000000
  | 2 => 0x2548b63bedba935ac46a000000000000
  | 3 => 0x2ad51beb08d895f3af68000000000000
  | 4 => 0xbe1b7cb45b3f16ae512000000000000
  | 5 => 0x1d53fc67d7e91da02352000000000000
  | 6 => 0x26f23f7931fac2c6dba8024000000000
  | 7 => 0x9a48ec8c474da66a178000000000000
  | 8 => 0x3778dcf806e87da6d0f0000000000000
  | 9 => 0xe48f7d847bd877f2a80020000000000
  | 10 => 0x3ea74cf1b26091444122000000000000
  | 11 => 0x25397f7ba3f27496949a000000000000
  | 12 => 0x12e94198420f9d8983c2020000080000
  | 13 => 0x1682d9623ecca9ee318a032000000000
  | 14 => 0x3f4941deaa0fdcb62938000000000000
  | 15 => 0x3924c19b4e0eb326949a000000000000
  | _ => 0

private def maskT0B143 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xe19242049afd83b142000000000000
  | 1 => 0xdf21fa7917ffca7f2000000000000
  | 2 => 0x1b83b09b1d91199d78c0004000104000
  | 3 => 0x2c78c500ee03935950ca024000000000
  | 4 => 0x29273bbf31979b7fc58202c000000000
  | 5 => 0x1b3da6a305b9fa4f2eba008000000000
  | 6 => 0x16ca925d3d9a25d852da024000000000
  | 7 => 0x1345070cca37283b55b8008000000000
  | 8 => 0x9536e9cf77392da849a028000104000
  | 9 => 0x2f8e91d0f4c65ca1ab002c000000000
  | 10 => 0x10cf352ec1a05f48822a024000000000
  | 11 => 0x19b93133c1836da4068a00c000104000
  | 12 => 0x354f3db059eee035ef98004000104000
  | 13 => 0x131082bf2c1bdf56d0ca00c000104000
  | 14 => 0x14351a0bc0d2b4f6c2da024000000000
  | 15 => 0x223ae5e9d72736f1be80000000000000
  | _ => 0

private def maskT0B144 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x211b75fc93a33bf67512004000104000
  | 1 => 0x3ac9e760ef34df3cc7a8024000000000
  | 2 => 0x1ec67a6cdbdbf51aa2ba000000000000
  | 3 => 0x187881c48c0a536101d2024000000000
  | 4 => 0x223489f924402f24ba20008000000000
  | 5 => 0x3a8ac7ca1e3cb6cf4792000000000000
  | 6 => 0x33b2788493cf51f74640000000000000
  | 7 => 0x337a8f865c7b8a8f0762000000000000
  | 8 => 0x3d01d3ca8e9136e688a0000000000000
  | 9 => 0x236c643de3de829949a000000000000
  | 10 => 0x334a9bc83cdcfc16149a000000000000
  | 11 => 0x17db496572414f9076ea000000000000
  | 12 => 0x3ed9042d6022070ff6ea000000000000
  | 13 => 0xd03d9e976c6d500e05a000000000000
  | 14 => 0x3cc88220641859c17188000000000000
  | 15 => 0x2f31c1e94e0efa9ea430000000000000
  | _ => 0

private def maskT0B145 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x32e2361ed1b74033e270000000000000
  | 1 => 0x350c65128b22ce2ebeba008000000000
  | 2 => 0x1ccb45ff5a2f51f74640000000000000
  | 3 => 0x13afb346d59f05f376ea000000000000
  | 4 => 0x2e7ffb73ffdded8b8000000000000000
  | 5 => 0x14d204e1d8282f7d91d2000000000000
  | 6 => 0x26e1a861ed431efbd5b8000000000000
  | 7 => 0x82954f3e2a8ea422caa000000000000
  | 8 => 0x3b64af198d70fe1a30aa000000000000
  | 9 => 0x1e2c192260c644a774c0000000000000
  | 10 => 0x86068f7ab485414ad2a000000000000
  | 11 => 0x429faac07d7ee33a352000000000000
  | 12 => 0x1a702204091001fd35e2000000000000
  | 13 => 0x7faa4377d26fe53022a000000000000
  | 14 => 0x2343b788d5b4d36ba4b2000000000000
  | 15 => 0x3d7f1d21f8ed3c523680002000000000
  | _ => 0

private def maskT0B146 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2e89203f210e45d6d2da000000000000
  | 1 => 0x2e16faf1dfd0011ee05a000000000000
  | 2 => 0x275e502b5a81119dc46a000000000000
  | 3 => 0x2604ed1aa73df1cb0aa000000000000
  | 4 => 0x3bc4fd5bc7e8517d2178000000000000
  | 5 => 0x3ec19ca0eceded6855b8000000000000
  | 6 => 0x172d93b54c95710f4308000000000000
  | 7 => 0x163239bdb1c89c84c308000000000000
  | 8 => 0x1a78f6aac7b58a811e40020000100000
  | 9 => 0x4f489ae644a92fc6270000000000000
  | 10 => 0x1f62f5c3dfa01db54f32020000104000
  | 11 => 0x1a01eb86ef5ded6855b8000000000000
  | 12 => 0xa8fd5877ea20e9b74c0000000000000
  | 13 => 0xc28f5a767a009eef188000000000000
  | 14 => 0x1a292a41895189372430000000000000
  | 15 => 0x12b779539bcca9737188000000000000
  | _ => 0

private def maskT0B147 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x12c0c13e2c5bdb4000000000000
  | 1 => 0xd453b5e0cd17c4000000000000
  | 2 => 0x100006ff020bb5fb968020800008000
  | 3 => 0x4c6fcdddc35a40000000000000
  | 4 => 0xe58d1102aecf94000000000000
  | 5 => 0x8365ea13b47a0c000000000000
  | 6 => 0x98acc05b2df20c000000000000
  | 7 => 0x9ed298562f15d4000000000000
  | 8 => 0x13bb4d8afdda40000000000000
  | 9 => 0x1f6a00e7178bc90000000000000
  | 10 => 0x1bd61d947b7114000000000000
  | 11 => 0x195ca90bfab94dc000000000000
  | 12 => 0x1acc3ce757a5958000000000000
  | 13 => 0x13dfc7e397d2030028000000000
  | 14 => 0x40fba703bd4850000000000000
  | 15 => 0xafce454d6a8108000000000000
  | _ => 0

private def maskT0B148 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x6b6081323bce9c000000000000
  | 1 => 0xb518f7bdae6798000800010000
  | 2 => 0x17b73d7ff9cceb4032800000000
  | 3 => 0x4b755a3da7a8ac000000000000
  | 4 => 0x121a04cce60e5c8000000000000
  | 5 => 0x1f66b698092bc90000000000000
  | 6 => 0x30000fe0011d54ce870020000008000
  | 7 => 0x1000236e43c99211794028800008000
  | 8 => 0x30005b5741787c7bdc8020800008000
  | 9 => 0x8e03e9e1f34fb38008800000000
  | 10 => 0x30010756c3de909587c028000008000
  | 11 => 0x210128c2143c85a8000000000000
  | 12 => 0x30040cdb6be18e91240020800008000
  | 13 => 0x2008077de33f4023ff4008800000000
  | 14 => 0x20101cb54a0f9378840008000000000
  | 15 => 0x102010108d0a0d9cb18020000008000
  | _ => 0

private def maskT0B149 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x401c5697d89b184dc008800000000
  | 1 => 0x108009a8d1aea69c324028000008000
  | 2 => 0x10019a7ce2ad5c96cc008800000000
  | 3 => 0x20005afaef4b556f98000000000000
  | 4 => 0x34001ba160c6e3f7598020000008000
  | 5 => 0x180012e35f3c818dca0020000008000
  | 6 => 0x1d943fe9523a344028800008000
  | 7 => 0x4000035b90e49fbd850000000000000
  | 8 => 0x80000003bb1c1a22a5c008000000000
  | 9 => 0x10000035f916f3b57cfc008000000000
  | 10 => 0x2000016b2b9dabaa0364008000000000
  | 11 => 0x15109e9920764c0000000000000
  | 12 => 0x1f73744ab425850000000000000
  | 13 => 0x1667ea28a92e4c0000000000000
  | 14 => 0x18349161f0c9a2c000000000000
  | 15 => 0xd7c869800b66d0000000000000
  | _ => 0

private def maskT0B150 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x95dd73d91c16cc000000000000
  | 1 => 0xd9ce0c1af5d850000000000000
  | 2 => 0x1981eb9dbbf4f94000000000000
  | 3 => 0x6200c102aebe80000000000000
  | 4 => 0x159a66478340210000000000000
  | 5 => 0x19e12ccfdf496cc000000000000
  | 6 => 0x1fe0f891da05a40000000000000
  | 7 => 0x1477959dbbf4f94000000000000
  | 8 => 0xda8839ebb3e5c8000000000000
  | 9 => 0x1fe1a405bb42944000000000000
  | 10 => 0x8d9a43d985e4c0000000000000
  | 11 => 0xcc4b0d947b7114000000000000
  | 12 => 0x10b5bc45d51e6d0000000000000
  | 13 => 0x193f7082f9b94dc000000000000
  | 14 => 0x9e7d5241dfa4b8000000000000
  | 15 => 0xb37489f9bfe7d8000000000000
  | _ => 0

private def maskT0B151 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x6428d169163c90000000000000
  | 1 => 0xcf9a91103b67d8000000000000
  | 2 => 0x1d242d592353b0c000000000000
  | 3 => 0xf05d770ba3195c030000000000
  | 4 => 0xbaed0d4bbd64c0000000000000
  | 5 => 0x1d082b8a0a5701c000000000000
  | 6 => 0x1eed6d0bbef2944000000000000
  | 7 => 0x11b5f7dcfcf5958000000000000
  | 8 => 0x164155fb584c8c000000000000
  | 9 => 0xe2934d29a63de4008800000000
  | 10 => 0x1b7f325c5927114000000000000
  | 11 => 0x1c9a5204c7b96cc000000000000
  | 12 => 0x200000e491fec36e4a6c020800100000
  | 13 => 0x19df166f9aeaa5c000000000000
  | 14 => 0xea07dc42c6d850000000000000
  | 15 => 0x3443fb96ea2a20000000000000
  | _ => 0

private def maskT0B152 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x46b850bf324e9c000000000000
  | 1 => 0x1b574f0c5c71364000800000000
  | 2 => 0x3424bc0257ce9c000000000000
  | 3 => 0x14296892d352a5c000000000000
  | 4 => 0x1fac683dcb61ee5b106a000000000000
  | 5 => 0x3bacfa789b43c4da486a000000000000
  | 6 => 0x20e96dcd7b5e6bdafeaa000000000000
  | 7 => 0x292ea439a8a1cd4534d0000000000000
  | 8 => 0x34bb96b1a6258d310000000000000000
  | 9 => 0x3ea45cb403b5a01dccb0000000000000
  | 10 => 0x2ff614d324169920abc8000000000000
  | 11 => 0xf9aedab6a5d5b52a902000000000000
  | 12 => 0x18f818f90247c8120c3a000000000000
  | 13 => 0x2dbe87fa2f3fd179ca7a000000000000
  | 14 => 0x217b9f185df8c2ec8b0000000000000
  | 15 => 0x229af37a2f5bd17adb92000000000000
  | _ => 0

private def maskT0B153 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x232c94b4cca5a6654a7a000000000000
  | 1 => 0x50e8578075bc03a9b18004000000000
  | 2 => 0x11a086e3b4f71da7a902000000000000
  | 3 => 0xb1dc3a73c5d39e282ca000000000000
  | 4 => 0xe18ab314b298a5927f2000000000000
  | 5 => 0x367c311390289c810000000000000000
  | 6 => 0x882d6e966774b33b4d00040000c0000
  | 7 => 0xbdd1381dbac0edd34d0021000000000
  | 8 => 0x21fdc3b584bdac25ad78000000000000
  | 9 => 0x3cfa13bc0b09e0583700037000040000
  | 10 => 0x5b39f3d8e7dec739e02037000040000
  | 11 => 0x12529a44f26227936f42000000000000
  | 12 => 0x235aeb25921d2c906eb8037000040000
  | 13 => 0x3402fd8995cc4caf1fea037000040000
  | 14 => 0x263c8b14b88ca5c60322024000040000
  | 15 => 0x9beeae017e300bb4aa0000000040000
  | _ => 0

private def maskT0B154 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x29e449a12cd9096eef98024000000000
  | 1 => 0x284964442bc2214e29d8000000000000
  | 2 => 0x57b206232f311b7a712000000000000
  | 3 => 0x1b11b80b65f45b6fb818013000040000
  | 4 => 0x64bb6e44cd722e6c850024000040000
  | 5 => 0x5b4fe5fe5f2fe2fb5d8024000000000
  | 6 => 0xd1a239105d88a2eef6a037000000000
  | 7 => 0x281fc1270c097860cf2013000040000
  | 8 => 0x27f7b5bde079e703f36a037000000000
  | 9 => 0x23a5c26fc8a76e4513c2000000040000
  | 10 => 0x3ba896e8cae766574b48000000000000
  | 11 => 0x3e5809168b6cf45b10f2013000040000
  | 12 => 0x14c0ccc5ab6e2d582ca000000000000
  | 13 => 0xd4be2d86897c344f2aa000000000000
  | 14 => 0x12b81ae80f95407cfd52000000040000
  | 15 => 0x38d1c23a96e9d4b75792024000000000
  | _ => 0

private def maskT0B155 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x295855ea926f5493448a000000000000
  | 1 => 0x9d51ea9a6a54d3557a8000000000000
  | 2 => 0x38ec9686ca2436512bc8000000000000
  | 3 => 0x44b367b6333db198c3a000000000000
  | 4 => 0x3c24a608c670463391e8000000000000
  | 5 => 0x15bd2585e75c2f3aa538000000000000
  | 6 => 0x313bc7b6200db1006d88000000000000
  | 7 => 0x2d3d8042030210185562000000000000
  | 8 => 0x16d493714d0b8a6834d0000000000000
  | 9 => 0x3cd15147e77a3f3bfeaa000000000000
  | 10 => 0x238ff63e57b1f2bdc88a000000000000
  | 11 => 0x3495755594faaca7c48a000000000000
  | 12 => 0x1c1774df8256fc12b9d8000000000000
  | 13 => 0x2595ecfafa17d7d0ba32037000000000
  | 14 => 0x12b14698d7c4c6be2538000000000000
  | 15 => 0x3e073e237a011bd04640000000000000
  | _ => 0

private def maskT0B156 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x476a94511ca288e5562000000000000
  | 1 => 0x2a41fb73df3b9ef9cb48024000000000
  | 2 => 0x3790f156304ab1821a38000000000000
  | 3 => 0x1846818f1fbc78fdb4d0000000000000
  | 4 => 0x3ae852f814c7c0a6705a000000000000
  | 5 => 0x2ede71eeb2df7596c86a000000040000
  | 6 => 0xc96d647c2323e11e2c8000000000000
  | 7 => 0x26d61e95fe74aff38400002000000000
  | 8 => 0x161cfbfb7d3fdbe9fc60000000000000
  | 9 => 0x550b4e189270c491f18000000000000
  | 10 => 0x13f2d6489f4244fa5b92000000000000
  | 11 => 0x2e0d6602f6b017b5abc8000000000000
  | 12 => 0x207103353ee9a9f7448a000000000000
  | 13 => 0x313e989de5f4ef2fb8ea000000000000
  | 14 => 0x2951ebc8710e43887c60000000000000
  | 15 => 0x27b508cac51656288c3a000000000000
  | _ => 0

private def maskT0B157 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x20ddd4d3c5a69e2d2b78020000100000
  | 1 => 0x26148c80bc6405e38ea000000000000
  | 2 => 0x295854f7a2f7bd17c48a000000000000
  | 3 => 0x27224a770d53b86ab8ea000000000000
  | 4 => 0x147db252d2c29696448a000000000000
  | 5 => 0x28d2554023fa011fc8b0000000000000
  | 6 => 0x299983f516efa8b734d0000000000000
  | 7 => 0x85ffd3fd3f9fe9fb8ea000000000000
  | 8 => 0x7990a3cc856df37337e000000000000
  | 9 => 0xf125e7892f000000000000000000000
  | 10 => 0x1fcd5cfe6aefe2a9ab8e000000000000
  | 11 => 0x19d0bece85f079692314000000000000
  | 12 => 0x2770613b83644212e80000000000000
  | 13 => 0x14bc58a5e2ca1bc215d2000000000000
  | 14 => 0x259c032ce0176ca76dce000000000000
  | 15 => 0x2040a222051b20294122024000000000
  | _ => 0

private def maskT0B158 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3ae2e1d717087979d792000000000000
  | 1 => 0x189d20c4e9f413cbf52000000000000
  | 2 => 0x322a7f9153fb38aaefa2000000000000
  | 3 => 0x382e35c171a6c5955a06000000000000
  | 4 => 0xed5f076af8f59608d94000000000000
  | 5 => 0x20b93245c99414c97a36028000000000
  | 6 => 0x3cdcfbe6e7df001111d2000000000000
  | 7 => 0x1c40e6e20738afad605a000000000000
  | 8 => 0x2df81b6fc0da9ef5469a000000000000
  | 9 => 0xaf3345799a3f74e0d94000000000000
  | 10 => 0x840744203a8bd631c46000000000000
  | 11 => 0x2a579d52bcead9c65792000000040000
  | 12 => 0x18cad18656805ca26aea008000000000
  | 13 => 0x18b376c59bb36197a876000000000000
  | 14 => 0x149834a4c1a17236e554000000000000
  | 15 => 0x3eb2f9d597c7d348eaac024000000000
  | _ => 0

private def maskT0B159 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3eefa1d77d03bb558af6024000000000
  | 1 => 0x3c98dfc4c6e591d7afb2024000000000
  | 2 => 0x2201c3108e397b592ba0020100000000
  | 3 => 0x289357449af34a638d08000000000000
  | 4 => 0x271cec1867eeadb207d0004100000000
  | 5 => 0x11307b8902da3fca23e0020100000000
  | 6 => 0x9a0654d8127e232dfba020100000000
  | 7 => 0x36dfbc9679ece98fc8e2004100000000
  | 8 => 0x116f288bf1493fe93d56020100000000
  | 9 => 0x3a00c4d0962613aa4b20020100000000
  | 10 => 0x3cec04c74021f1456bd8024000000000
  | 11 => 0x26a79335fc9c36b00412020100000000
  | 12 => 0x2443e3221f1a554ddce4020100000000
  | 13 => 0x2b8fbb5dfdde631cd268020100000000
  | 14 => 0x24aded27ef61fa7e7b50020100000000
  | 15 => 0x239210189089e1da344c000000000000
  | _ => 0

private def maskT0B160 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x30086ea84377aab80840024000000000
  | 1 => 0x229bc1245e010700f1a6004100000000
  | 2 => 0xf2b3e7959fb3121e8c0024000000000
  | 3 => 0x343652e1b29ab6444cf0000000000000
  | 4 => 0x13075038ba837dbb4b20004100000000
  | 5 => 0x2fd76b7ebb564124850e000000000000
  | 6 => 0xa6e5a5372d24f308000000000000000
  | 7 => 0x249b7d24dbe32b54ab8e000000000000
  | 8 => 0xdc4686e23440bd64bd4000000000000
  | 9 => 0x3ef2d5f796ab5ba64bd4000000000000
  | 10 => 0x34b24da592690ae9b7c8000000000000
  | 11 => 0x1c1478e0a3ce8bc5a61a000000000000
  | 12 => 0x2c43af621d7e8dfa2e80000000000000
  | 13 => 0x36af5bb57adf33bb3876000000000000
  | 14 => 0x258a092c5043f74e0d94000000000000
  | 15 => 0x342aeba157587b1c2e80000000000000
  | _ => 0

private def maskT0B161 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3aba97d5d4b8f7a0050e000000000000
  | 1 => 0x3bc1f3de0f9580c51948000000000000
  | 2 => 0x926ea4937534ebef486000000000000
  | 3 => 0xf6bed7bdf63b2716a82020100000000
  | 4 => 0x25fde32fef1f4e51434e000000000000
  | 5 => 0x61e0030f040b11ae80000000000000
  | 6 => 0x840744203af7f9ec444000000000000
  | 7 => 0xc36b861b5c4a884ba5c000000000000
  | 8 => 0x61b3430d9a9b703df08000000000000
  | 9 => 0x3e3205f19023cf0a8000000000000000
  | 10 => 0x25a4cb2d265c67a7e09e000000000000
  | 11 => 0x3b60003b800909e0f48603c100000000
  | 12 => 0x2eb1f5758fa838546dce000000000000
  | 13 => 0x1de7f6ef3fbd8fb84bd4000000000000
  | 14 => 0x3312d198968d9c56889a000000000000
  | 15 => 0x83c6e41e379757c4640000000000000
  | _ => 0

private def maskT0B162 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1e8b2af4595f54a55f08000000000000
  | 1 => 0x59eea2cf75ccf1b91d2000000000000
  | 2 => 0x2c9e8564f42fd10391d2000000000000
  | 3 => 0x394443ca221726a394dc000000000000
  | 4 => 0xcb81525c0a69ce68e06028000140000
  | 5 => 0x1a0848d042473728ceda000000000000
  | 6 => 0x2dcc3b6e61d3b90e18a0000000000000
  | 7 => 0x2103c5081e28a706f188000000000000
  | 8 => 0x14c22ca61160412dae80000000000000
  | 9 => 0x40f62207b1532db5792000000000000
  | 10 => 0x3d94a7eca5308a5ac34e000000000000
  | 11 => 0xe08da7046d8e07032c6000000000000
  | 12 => 0x35497b27071000000419000000000000
  | 13 => 0x2fe104639ad000000219000000000000
  | 14 => 0x301e23c27e0000004ee0000000000000
  | 15 => 0x290665b5dcb000000948000000000000
  | _ => 0

private def maskT0B163 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0xd98536219a000005649000000000000
  | 1 => 0x3c8a7299e6c0000053a8000000000000
  | 2 => 0xcb64a56e20000045b1000000000000
  | 3 => 0x1410dfdef51000000b51000000000000
  | 4 => 0x21b6d40c23000001de8000000000000
  | 5 => 0x375434e0611000000b51000000000000
  | 6 => 0xd178115808000004ee0000000000000
  | 7 => 0xb841a8482d0000045b1000000000000
  | 8 => 0x282a82938040000324101a000080000
  | 9 => 0x3c62c408887000003e0101a000000000
  | 10 => 0x140e34df67e000000000000000000000
  | 11 => 0x290fbe1e7a9000000000000000000000
  | 12 => 0x2ee30c2f731000005450000000000000
  | 13 => 0x3548b5e80c000005f01000000000000
  | 14 => 0x2cd0e58f119000000b51000000000000
  | 15 => 0xe99fffc16e000000219000000000000
  | _ => 0

private def maskT0B164 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1cdf64876fca00006a18032000040000
  | 1 => 0x176a9b948e0000000948024000000000
  | 2 => 0x80a65e2541000000840000000000000
  | 3 => 0xbf9f947280c00001108004000080000
  | 4 => 0x39b6c83c81c000005649000000000000
  | 5 => 0x1945922789e000005450000000000000
  | 6 => 0x3cc534984d6c0000ea18036000080000
  | 7 => 0x3b2c2fbae1a000012150032000000000
  | 8 => 0xea503459ac4000267f901a000080000
  | 9 => 0x179e434ca5bc000445b1004000080000
  | 10 => 0x171da68b50200008718802c000000000
  | 11 => 0x2ce87fc67d400105f20036000080000
  | 12 => 0x1a9f90af14fc00205e00004000080000
  | 13 => 0x202223039e3c00400000004000080000
  | 14 => 0xa36b6565c180080251001e000000000
  | 15 => 0x136142c7f9e001003241032000000000
  | _ => 0

private def maskT0B165 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x11443afaf480020003f1000000000000
  | 1 => 0x360a069038ac04000f30036000080000
  | 2 => 0x3d0c8f7f38c080019a8028000080000
  | 3 => 0x2d11d3f4e13c10002c79028000080000
  | 4 => 0x222ab4894ddc200039f9036000080000
  | 5 => 0x189160ba4fec40003ea101a000080000
  | 6 => 0x1cf93e32874c800061a001a000080000
  | 7 => 0x2e6b5c515451000022a101e000000000
  | 8 => 0x3f0c32693a8a000079e0032000000000
  | 9 => 0x173281de4530000045b1028000080000
  | 10 => 0x1e6bc70af79000000948000000000000
  | 11 => 0x21ba451ee5e000004cf9000000000000
  | 12 => 0x3a90229dd6000005209000000000000
  | 13 => 0x3b39d74800a000005f01000000000000
  | 14 => 0x8c101b1e32000004cf9000000000000
  | 15 => 0x24d35a164b0000000b51000000000000
  | _ => 0

private def maskT0B166 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x3d3bb676f09000006fb0032000000000
  | 1 => 0x33390108061000004cf9000000000000
  | 2 => 0xcdeec3e410000005d18000000000000
  | 3 => 0x8c1016e84c000004cf9000000000000
  | 4 => 0x234b12fc6b1000005f01000000000000
  | 5 => 0x10cd8c224b9000005649000000000000
  | 6 => 0x32ee87c1820000004cf9000000000000
  | 7 => 0xd1781c21d9000004ee0000000000000
  | 8 => 0x10b0ad38021000005f01000000000000
  | 9 => 0x1b8b282b2bd000005f01000000000000
  | 10 => 0x1de39a61c3a000003b40000000000000
  | 11 => 0x2e21b382a250000018a9000000000000
  | 12 => 0x2e28681df9a0000011e1000000000000
  | 13 => 0x39bf124d779000005f01000000000000
  | 14 => 0x45d7937290000005bf9000000000000
  | 15 => 0x1ca1c7bdea8000003749038000000000
  | _ => 0

private def maskT0B167 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x9f5663d766000002430000000000000
  | 1 => 0x2389ad75cfb0000013f8000000000000
  | 2 => 0x36f748b8d0d0000058b0000000000000
  | 3 => 0x2c66a0178de0000047a8000000000000
  | 4 => 0x2f455f21bc2000004ba102c000000000
  | 5 => 0x2ac132a990d000005f01000000000000
  | 6 => 0xefa35c71410000013f8000000000000
  | 7 => 0x22222c5b75a000004ee0000000000000
  | 8 => 0x1c1a78a222ea000074b101a000140000
  | 9 => 0x96151218080000047a8000000000000
  | 10 => 0x19075f521da0000045b1000000000000
  | 11 => 0x2ef21f949b4000005d18000000000000
  | 12 => 0x2a3e5f68b6f000000948000000000000
  | 13 => 0x1ef1a8779920000018a9000000000000
  | 14 => 0x22bfe0e9f5f000004cf9000000000000
  | 15 => 0x6eebab2805000000219000000000000
  | _ => 0

private def maskT0B168 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x28d08122f970c17ed1a1000000000000
  | 1 => 0x1352855d635c048aa6a5080000000000
  | 2 => 0xb9a0561ddfc2d7b1734080000000000
  | 3 => 0x19b885665326df76b371080000000000
  | 4 => 0x1ca2009031745ad63944000000000000
  | 5 => 0x39e8803b21765af9f3d1000000000000
  | 6 => 0x135284303c65710aa6a5080000000000
  | 7 => 0x51a85c152160ce20a35080000000000
  | 8 => 0x1782041d1cc02000af04080000000000
  | 9 => 0xcb67f1ea0000000000000000
  | 10 => 0xaea014eb176f21b95d4000000000000
  | 11 => 0x2ba08038ec0c8105d741000000000000
  | 12 => 0xe3a805f938d93c09c75000000000000
  | 13 => 0x1c728139425e738db8e5004000000000
  | 14 => 0x156805cccbd54070aad0088000000000
  | 15 => 0x20808579f33181414101080000000000
  | _ => 0

private def maskT0B169 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x135285359b4d988e26a5080000000000
  | 1 => 0xda880dc4c5ede7d1b51000000000000
  | 2 => 0x2eba04820fb73804dd74080000000000
  | 3 => 0xff0840bbbc8177d1fe1080000000000
  | 4 => 0x20808591e39a88d9c101080000000000
  | 5 => 0x2aa881bee12bdd61d551004000080000
  | 6 => 0xb20051853b392cc164008d000000000
  | 7 => 0x3b5001f342199e03d6a0008000000000
  | 8 => 0x2f7000fd7add3ee6dee0000000000000
  | 9 => 0x214a81d9e1bb96ae4295000000000000
  | 10 => 0x9b8856ae7826e9eb371088000000000
  | 11 => 0x14180303129af101283002c000000000
  | 12 => 0x2c5281060e410e8bf8a50ac000000000
  | 13 => 0x25a8ddc15aa624524b50ac000000000
  | 14 => 0x2aaa1158cffeacf2f55402c000000000
  | 15 => 0xcd0a145a8388eed19a1024000000000
  | _ => 0

private def maskT0B170 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x2148412177d70aca6290024000000000
  | 1 => 0x3ba80411ab944d745751088000000000
  | 2 => 0x1da304c0a023bfa13b440ac000000000
  | 3 => 0x314204e5b6ad20ebe280088000000000
  | 4 => 0x2aac80e8ad2add9cd551024000000000
  | 5 => 0x1b5001ccebb7645716b0000000000000
  | 6 => 0x91800eccef186ef121002c000000000
  | 7 => 0x2f2280748e9e0a5dfe0502c000000000
  | 8 => 0x2cd08151997b9987f921000000000000
  | 9 => 0x31c0042807ed938362800a4000000000
  | 10 => 0x2c5280c3ba6b4c73faa5000000000000
  | 11 => 0x7a2050b7162e1da2b44088000000000
  | 12 => 0x2aba0410d439636add74080000000000
  | 13 => 0x14a20154279857ba3944008000000000
  | 14 => 0xba0802481624eadd741024000000000
  | 15 => 0x36c884f6e5363ccaed91080000000000
  | _ => 0

private def maskT0B171 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x12988113315567de2531000000000000
  | 1 => 0x208085d8385d982c4101080000000000
  | 2 => 0x1ca201eda2dc83c7b944000000000000
  | 3 => 0x1872806640a994fe30e5000000000000
  | 4 => 0x393801726cdef8587270000000000000
  | 5 => 0x12988018feea4336a531000000000000
  | 6 => 0x38f2050dd2d989bbf1e4080000000000
  | 7 => 0x3de880eb24871569fbd1000000000000
  | 8 => 0x214a8022c9ceb37d4295000000000000
  | 9 => 0x2a6a85aa8b7abf0d54d5080000000000
  | 10 => 0x2eba055e9c1d73865d74080000000000
  | 11 => 0x2ba08040cddd64b5d741000000000000
  | 12 => 0x19b885d70c46df76b371080000000000
  | 13 => 0xaea01e7302f879b95d4000000000000
  | 14 => 0x93085c36b2f123c9261080000000000
  | 15 => 0x393801b91e7fb7b37270000000000000
  | _ => 0

private def maskT0B172 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x214a804ba2037f2ac295000000000000
  | 1 => 0x1872801c11dcc899b0e5000000000000
  | 2 => 0xdb284421ba0ae1e9b65080000000000
  | 3 => 0x3ff800da69481193fff0011000000000
  | 4 => 0xff084b00ae877109fe1080000000000
  | 5 => 0x2a6a8553d8a70aee54d5080000000000
  | 6 => 0x51a85473d3761b08a35080000000000
  | 7 => 0x2f700131ee85bfdbdee0000000000000
  | 8 => 0x2a6a85637023d181d4d5080000000000
  | 9 => 0x73281a45d32f1660e65000000000000
  | 10 => 0xaea00e2944ea3f295d4000000000000
  | 11 => 0x1298804f4906f2b9a531000000000000
  | 12 => 0x30e08160eca0c45aa1c100c000100000
  | 13 => 0x1ca200c9ed4f6fb6b944000000000000
  | 14 => 0xff085168b50fef99fe1080000000000
  | 15 => 0x208084f6998501fac1010ac000000000
  | _ => 0

private def maskT0B173 (i : ℕ) : ℕ :=
  match (i/1)%16 with
  | 0 => 0x1d68043cd8fabdcf3ad0080000000000
  | 1 => 0x2aa8807a3cc44a43d551000000000000
  | 2 => 0x321804b33ecb3e4c6430080000000000
  | 3 => 0x1298813211c61365a531000000000000
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
  | 14 => maskT0B158 i
  | 15 => maskT0B159 i
  | _ => 0

private def maskT1B10 (i : ℕ) : ℕ :=
  match (i/16)%16 with
  | 0 => maskT0B160 i
  | 1 => maskT0B161 i
  | 2 => maskT0B162 i
  | 3 => maskT0B163 i
  | 4 => maskT0B164 i
  | 5 => maskT0B165 i
  | 6 => maskT0B166 i
  | 7 => maskT0B167 i
  | 8 => maskT0B168 i
  | 9 => maskT0B169 i
  | 10 => maskT0B170 i
  | 11 => maskT0B171 i
  | 12 => maskT0B172 i
  | 13 => maskT0B173 i
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
  | 10 => maskT1B10 i
  | _ => 0


def W (col : ℕ) : ℕ :=
  let ix := which col
  if ix=0 then 0 else if ix≤924 then dense (ix-1) else 2^(ix-1)
def cert (p : ℕ) : Bool := (decide (layer p < 22)) &&
  (combined 6 21 22 59 x y z W layer mask p >>> p == 1)
end TensorTwoSided.Seed21

namespace TensorTwoSided.Seed21
open TensorModularMinor
def raw0 (k ij : ℕ) := packedRowFn 6 21 22 59 x y z W (ij/21) (ij%21) k
def evidence (k data p : ℕ) : Bool := (layer p == k) &&
  (mix (field 2772 data) (mask p) 126 >>> p == 1)
def cached (k : ℕ) := packRows (2^2772) (raw0 k) 126 0
def checker (k : ℕ) : Bool :=
  withWord (fun data => decide ((∀ i : Fin 42, evidence k data (k*42+i.val) = true) ∧
    (∀ i : Fin 84, evidence k data (924+k*84+i.val) = true))) (cached k)
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
theorem checked21 : checker 21 = true := by decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem every (k : Fin 22) : checker k = true := by
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
  · exact checked21

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem evidence_all (p : ℕ) (hp : p<2772) : ∃ k : Fin 22, evidence k.val (cached k.val) p = true := by
  have cv (k : Fin 22) := every k
  simp only [checker,withWord_eq,decide_eq_true_eq] at cv
  by_cases small : p<924
  · let k : Fin 22 := ⟨p/42,by omega⟩
    refine ⟨k,?_⟩
    have h := (cv k).1 ⟨p%42,by omega⟩
    change evidence k.val (cached k.val) (p/42*42+p%42)=true at h
    simpa only [show p/42*42+p%42=p by omega] using h
  · let k : Fin 22 := ⟨(p-924)/84,by omega⟩
    refine ⟨k,?_⟩
    have h := (cv k).2 ⟨(p-924)%84,by omega⟩
    change evidence k.val (cached k.val) (924+(p-924)/84*84+(p-924)%84)=true at h
    simpa only [show 924+(p-924)/84*84+(p-924)%84=p by omega] using h

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem mix_agrees (k p : ℕ) : ∀ len, len≤126 →
    mix (field 2772 (cached k)) (mask p) len =
      mix (fun ij => raw0 k ij % 2^2772) (mask p) len := by
  intro len
  induction len with
  | zero => simp [mix]
  | succ len ih =>
    intro h
    have eq := field_pack 2772 (raw0 k) 126 0 len (by omega)
    simp only [Nat.zero_add] at eq
    change field 2772 (cached k) len = raw0 k len % 2^2772 at eq
    simp only [mix,ih (by omega),eq]

set_option maxRecDepth 18000 in
set_option maxHeartbeats 10000000 in
theorem span :
    ∃ X : Fin 59 → Fin 6 → ℂ, ∃ Y : Fin 59 → Fin 21 → ℂ, ∃ Z : Fin 59 → Fin 22 → ℂ,
    ∀ T : Fin 6 → Fin 21 → Fin 22 → ℂ, ∃ u : Fin 59 → Fin 6 → ℂ,
      ∃ v : Fin 59 → Fin 21 → ℂ, ∃ w : Fin 59 → Fin 22 → ℂ, ∀ i j k, T i j k =
        ∑ t, (u t i*(Y t j*Z t k)+X t i*(v t j*Z t k)+X t i*(Y t j*w t k)) := by
  have checks (p : ℕ) (hp : p<2772) : layer p<22 ∧ combined 6 21 22 59 x y z W layer mask p >>> p = 1 := by
    obtain ⟨k,h⟩ := evidence_all p hp
    simp only [evidence,Bool.and_eq_true,beq_iff_eq] at h
    refine ⟨h.1.trans_lt k.isLt,?_⟩
    have eq := congrArg (fun v : ℕ => v >>> p) (mix_agrees k.val p 126 le_rfl)
    have result := eq.symm.trans h.2
    simpa only [combined,h.1,Nat.reduceMul,raw0] using result
  exact TensorTwoSided.spans 6 21 22 59 x y z W layer mask
    (fun p hp => (checks p hp).1) (fun p hp => (checks p hp).2)
end TensorTwoSided.Seed21

theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H3_R1_H1_R1_H2_R1.H2 := by
  exact TensorTwoSided.Seed21.span
