import FormalConjectures.OEIS.«228624»
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Eliminate triples of indices 4k-1, 4k, 4k+1 for 1 ≤ k ≤ ⌊(n-1)/4⌋.
Reversing the three column families gives a triangular pivot with three copies
of the smaller square-sum matrix on its diagonal.
Credit: @Pixelstorm44 -/

namespace OMA.R_OeisA228624_conjecture_1_R1

open Matrix
noncomputable section
open scoped Classical

private theorem det_A (n : ℕ) :
    Matrix.det (fun i j : Fin n =>
      let s := i.val+j.val+2
      if s.sqrt^2 = s then (1 : ℚ) else 0) = (OeisA228624.a n : ℚ) := by
  let Z : Matrix (Fin n) (Fin n) ℤ := fun i j =>
    let s := i.val+j.val+2
    if s.sqrt^2 = s then 1 else 0
  change _ = (Int.castRingHom ℚ) Z.det
  rw [RingHom.map_det]
  congr 1
  ext i j
  change (if _ then (1 : ℚ) else 0) = ((if _ then (1 : ℤ) else 0 : ℤ) : ℚ)
  split <;> simp_all

private theorem squareEntry_zero {s : ℕ} (hs : 2 ≤ s % 4) : (if s.sqrt^2 = s then (1 : ℚ) else 0) = 0 := by
  apply if_neg
  intro he
  have ht := congrArg (· % 4) he
  rw [Nat.pow_mod] at ht
  have hb := Nat.mod_lt s.sqrt (by decide : 0 < 4)
  interval_cases h : s.sqrt % 4 <;> simp_all <;> omega

private theorem squareEntry_four (s : ℕ) : 
    (if (4*s).sqrt^2 = 4*s then (1 : ℚ) else 0) = (if s.sqrt^2 = s then (1 : ℚ) else 0) := by
  have he : (4*s).sqrt ^ 2 = 4*s ↔ s.sqrt ^ 2 = s := by
    constructor
    · intro h
      let t := (4*s).sqrt
      have ht : t ^ 2 = 4*s := h
      have heven : t % 2 = 0 := by
        have hm := congrArg (· % 2) ht
        rw [Nat.pow_mod] at hm
        rcases Nat.mod_two_eq_zero_or_one t with h0 | h1
        · exact h0
        · simp [h1] at hm
          omega
      have hd : t = 2*(t/2) := by omega
      have hs : s = (t/2)^2 := by
        rw [hd] at ht
        nlinarith
      conv_lhs => rw [hs, Nat.sqrt_eq']
      exact hs.symm
    · intro h
      have hs : 4*s = (2*s.sqrt)^2 := by nlinarith
      calc
        (4*s).sqrt ^ 2 = (2*s.sqrt)^2 := by rw [hs, Nat.sqrt_eq']
        _ = 4*s := hs.symm
  simp only [he]

/-- Finite range before the smaller order reaches 22. -/
def H1 : Prop := ∀ n, 21 < n → n < 89 → OeisA228624.a n ≠ 0

/-- After eliminating 4k-1, 4k and 4k+1 (one-based, 1 ≤ k ≤ m), the
Schur complement on the remaining n-3m indices has no null vector. -/
def H2 : Prop := ∀ n : ℕ, 89 ≤ n → OeisA228624.a ((n-1)/4) ≠ 0 →
  let m := (n-1)/4
  let S (i : Fin n) := ∃ k : Fin m,
    i.val = 4*k.val+2 ∨ i.val = 4*k.val+3 ∨ i.val = 4*k.val+4
  let R (i : Fin n) := ¬ S i
  let T : Matrix (Fin n) (Fin n) ℚ := fun i j =>
    let t := i.val+j.val+2
    if t.sqrt^2 = t then 1 else 0
  (T.toBlock R R - T.toBlock R S * (T.toBlock S S)⁻¹ * T.toBlock S R).det ≠ 0

theorem main : H1 → H2 → type_of% @OeisA228624.conjecture_1 := by
  intro base step n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases small : n < 89
    · exact base n hn small
    let m := (n-1)/4
    have hm : OeisA228624.a m ≠ 0 := ih m (by dsimp [m]; omega) (by dsimp [m]; omega)
    let squareEntry (s : ℕ) : ℚ := if s.sqrt ^ 2 = s then 1 else 0
    let A (d : ℕ) : Matrix (Fin d) (Fin d) ℚ := fun i j => squareEntry (i.val+j.val+2)
    let B : Matrix (Fin m) (Fin m) ℚ := fun i j => squareEntry (4*(i.val+j.val+2)+1)
    let S (i : Fin n) := ∃ k : Fin m,
      i.val = 4*k.val+2 ∨ i.val = 4*k.val+3 ∨ i.val = 4*k.val+4
    let R (i : Fin n) := ¬ S i
    let P := (A n).toBlock S S
    -- Reverse the three column families. In this order the pivot is
    -- [A,0,0; B,A,0; 0,B,A], with A of order m.
    let idx : Fin m ⊕ (Fin m ⊕ Fin m) → {i : Fin n // S i}
      | .inl k => ⟨⟨4*k.val+2, by have := k.isLt; dsimp [m] at this; omega⟩, k, Or.inl rfl⟩
      | .inr (.inl k) => ⟨⟨4*k.val+3, by have := k.isLt; dsimp [m] at this; omega⟩, k, Or.inr (Or.inl rfl)⟩
      | .inr (.inr k) => ⟨⟨4*k.val+4, by have := k.isLt; dsimp [m] at this; omega⟩, k, Or.inr (Or.inr rfl)⟩
    have hinj : Function.Injective idx := by
      rintro (i|i|i) (j|j|j) h
      all_goals have hv := congrArg (fun t : {i : Fin n // S i} => t.val.val) h
      all_goals simp [idx] at hv ⊢ <;> omega
    have hsurj : Function.Surjective idx := by
      rintro ⟨i,k,h|h|h⟩
      · exact ⟨.inl k, Subtype.ext (Fin.ext h.symm)⟩
      · exact ⟨.inr (.inl k), Subtype.ext (Fin.ext h.symm)⟩
      · exact ⟨.inr (.inr k), Subtype.ext (Fin.ext h.symm)⟩
    let rows := Equiv.ofBijective idx ⟨hinj,hsurj⟩
    let rev : Equiv.Perm (Fin m ⊕ (Fin m ⊕ Fin m)) :=
      { toFun := fun | .inl i => .inr (.inr i) | .inr (.inl i) => .inr (.inl i) | .inr (.inr i) => .inl i
        invFun := fun | .inl i => .inr (.inr i) | .inr (.inl i) => .inr (.inl i) | .inr (.inr i) => .inl i
        left_inv := by rintro (i|i|i) <;> rfl
        right_inv := by rintro (i|i|i) <;> rfl }
    let cols := rev.trans rows
    have hp : P.submatrix rows cols =
        fromBlocks (A m) 0 (Matrix.fromRows B 0) (fromBlocks (A m) 0 B (A m)) := by
      ext (i|i|i) (j|j|j)
      · change squareEntry (4*i.val+2+(4*j.val+4)+2) = squareEntry (i.val+j.val+2)
        rw [show 4*i.val+2+(4*j.val+4)+2 = 4*(i.val+j.val+2) by omega]
        exact squareEntry_four _
      · change squareEntry (4*i.val+2+(4*j.val+3)+2) = 0
        apply squareEntry_zero
        omega
      · change squareEntry (4*i.val+2+(4*j.val+2)+2) = 0
        apply squareEntry_zero
        omega
      · change squareEntry (4*i.val+3+(4*j.val+4)+2) = squareEntry (4*(i.val+j.val+2)+1)
        congr 1
        omega
      · change squareEntry (4*i.val+3+(4*j.val+3)+2) = squareEntry (i.val+j.val+2)
        rw [show 4*i.val+3+(4*j.val+3)+2 = 4*(i.val+j.val+2) by omega]
        exact squareEntry_four _
      · change squareEntry (4*i.val+3+(4*j.val+2)+2) = 0
        apply squareEntry_zero
        omega
      · change squareEntry (4*i.val+4+(4*j.val+4)+2) = 0
        apply squareEntry_zero
        omega
      · change squareEntry (4*i.val+4+(4*j.val+3)+2) = squareEntry (4*(i.val+j.val+2)+1)
        congr 1
        omega
      · change squareEntry (4*i.val+4+(4*j.val+2)+2) = squareEntry (i.val+j.val+2)
        rw [show 4*i.val+4+(4*j.val+2)+2 = 4*(i.val+j.val+2) by omega]
        exact squareEntry_four _
    have hsmall : (A m).det ≠ 0 := by
      rw [show (A m).det = _ from det_A m]
      exact_mod_cast hm
    have hu : IsUnit P := (isUnit_submatrix_equiv rows cols).mp <| (isUnit_iff_isUnit_det _).mpr <| by
      rw [hp, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂]
      exact isUnit_iff_ne_zero.mpr (mul_ne_zero hsmall (mul_ne_zero hsmall hsmall))
    have hpdet := (isUnit_iff_isUnit_det _).mp hu
    let := invertibleOfIsUnitDet P hpdet
    let e := Equiv.sumCompl S
    have hblock : (A n).submatrix e e =
        fromBlocks P ((A n).toBlock S R) ((A n).toBlock R S) ((A n).toBlock R R) := by
      ext (i|i) (j|j) <;> rfl
    have hd : ((A n).submatrix e e).det ≠ 0 := by
      rw [hblock, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
      exact mul_ne_zero hpdet.ne_zero (step n (by omega) hm)
    rw [det_submatrix_equiv_self, show (A n).det = _ from det_A n] at hd
    exact_mod_cast hd

end
end OMA.R_OeisA228624_conjecture_1_R1
