import FormalConjectures.OEIS.«71524»

/-! Parity block decompositions for both sizes in Sun’s determinant conjecture. -/

-- Credit: @Medrov
namespace OMA.R_OeisA71524_conjecture1_R1

open Matrix

private theorem blocks (m : ℕ) :
    |OeisA71524.a (2*m)| = Matrix.det (fun (i j : Fin m) => if ((2*i.val+1)^2 + (2*j.val+2)^2).Prime then (1:ℤ) else 0) ^ 2 ∧
    |OeisA71524.a (2*m+1)| = Matrix.det (fun (i j : Fin m) => if ((2*i.val+3)^2 + (2*j.val+2)^2).Prime then (1:ℤ) else 0) ^ 2 := by
  let entry (i j : ℕ) : ℤ := if (i^2 + j^2).Prime then 1 else 0
  have entry_comm (i j : ℕ) : entry i j = entry j i := by simp [entry, add_comm]
  have entry_zero_of_even {i j : ℕ} (h : Even (i^2+j^2)) (hlt : 2 < i^2+j^2) :
      entry i j = 0 := by
    apply if_neg
    intro hp
    have := hp.even_iff.mp h
    omega
  have even_even (i j : ℕ) : entry (2*i+2) (2*j+2) = 0 := by
    refine entry_zero_of_even ?_ ?_
    · exact ⟨2*i^2+4*i+2*j^2+4*j+4, by ring⟩
    · have h : 2 ≤ (2*i+2) := by omega
      have hsq := Nat.pow_le_pow_left h 2
      omega
  have odd_odd (i j : ℕ) : entry (2*i+3) (2*j+1) = 0 := by
    refine entry_zero_of_even ?_ ?_
    · exact ⟨2*i^2+6*i+2*j^2+2*j+5, by ring⟩
    · have h : 3 ≤ (2*i+3) := by omega
      have hsq := Nat.pow_le_pow_left h 2
      omega
  let interleave (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2*m) := {
    toFun
      | .inl i => ⟨2*i.val, by omega⟩
      | .inr i => ⟨2*i.val+1, by omega⟩
    invFun i := if i.val % 2 = 0 then .inl ⟨i.val/2, by omega⟩ else .inr ⟨i.val/2, by omega⟩
    left_inv s := by cases s with
      | inl i => simp
      | inr i => simp; apply Fin.ext; dsimp; omega
    right_inv i := by
      by_cases h : i.val % 2 = 0
      · simp only [if_pos h]; apply Fin.ext; dsimp; omega
      · simp only [if_neg h]; apply Fin.ext; dsimp; omega }
  let cross (m shift : ℕ) : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    entry (2*i.val + (2*shift+1)) (2*j.val+2)
  let raw (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => entry (i.val+1) (j.val+1)
  let surround (m : ℕ) : Fin m ⊕ (Fin 1 ⊕ Fin m) ≃ Option (Fin m ⊕ Fin m) := {
    toFun
      | .inl i => some (.inl i)
      | .inr (.inl _) => none
      | .inr (.inr j) => some (.inr j)
    invFun
      | none => .inr (.inl 0)
      | some (.inl i) => .inl i
      | some (.inr j) => .inr (.inr j)
    left_inv := by
      rintro (i | (j | k))
      · rfl
      · rw [Subsingleton.elim j 0]
      · rfl
    right_inv := by rintro (_ | (i | j)) <;> rfl }
  let around {m : ℕ} (e : Fin m ⊕ Fin m ≃ Fin (2*m)) :=
    ((surround m).trans e.optionCongr).trans (finSuccEquiv (2*m)).symm
  constructor
  ·
    let e := interleave m
    let f := (Equiv.sumComm (Fin m) (Fin m)).trans e
    let b := cross m 0
    let d : Matrix (Fin m) (Fin m) ℤ := fun i j => entry (2*i.val+1) (2*j.val+1)
    have hm : (raw (2*m)).submatrix e f = fromBlocks b d 0 b.transpose := by
      ext i j
      cases i with
      | inl i => cases j with
        | inl j => rfl
        | inr j => rfl
      | inr i => cases j with
        | inl j => exact even_even i.val j.val
        | inr j => exact entry_comm _ _
    change |(raw _).det| = b.det ^ 2
    rw [← abs_det_submatrix_equiv_equiv e f, hm, det_fromBlocks_zero₂₁, det_transpose,
      ← sq, abs_of_nonneg (sq_nonneg _)]
  ·
    let e := around ((Equiv.sumComm (Fin m) (Fin m)).trans (interleave m))
    let f := around (interleave m)
    let b := cross m 1
    let v : Matrix (Fin m) (Fin 1) ℤ := fun i _ => entry (2*i.val+2) 1
    let c : Matrix (Fin 1 ⊕ Fin m) (Fin m) ℤ := fun i j =>
      match i with
      | .inl _ => entry 1 (2*j.val+2)
      | .inr _ => 0
    have hm : (raw (2*m+1)).submatrix e f =
        fromBlocks b 0 c (fromBlocks 1 0 v b.transpose) := by
      ext i j
      rcases i with i | (i | i) <;> rcases j with j | (j | j)
      · rfl
      · exact odd_odd i.val 0
      · exact odd_odd i.val (j.val+1)
      · rfl
      · have : i = j := Subsingleton.elim _ _
        subst j
        change entry 1 1 = (1 : Matrix (Fin 1) (Fin 1) ℤ) i i
        simp [entry, Nat.prime_two]
      · exact (entry_comm _ _).trans (odd_odd j.val 0)
      · exact even_even i.val j.val
      · rfl
      · exact entry_comm _ _
    change |(raw _).det| = b.det ^ 2
    rw [← abs_det_submatrix_equiv_equiv e f, hm, det_fromBlocks_zero₁₂,
      det_fromBlocks_zero₁₂, det_one, one_mul, det_transpose, ← sq,
      abs_of_nonneg (sq_nonneg _)]

/-- The even orders use all odd indices up to 2m. -/
def H1 : Prop := ∀ m : ℕ, 201 ≤ m → Matrix.det (fun (i j : Fin m) => if ((2*i.val+1)^2 + (2*j.val+2)^2).Prime then (1:ℤ) else 0) ≠ 0

/-- The odd orders use the odd indices 3 through 2m+1. -/
def H2 : Prop := ∀ m : ℕ, 201 ≤ m → Matrix.det (fun (i j : Fin m) => if ((2*i.val+3)^2 + (2*j.val+2)^2).Prime then (1:ℤ) else 0) ≠ 0

/-- The finite initial range of Sun's original matrices. -/
def H3 : Prop := ∀ n : ℕ, 29 ≤ n → n ≤ 401 → OeisA71524.a n ≠ 0

theorem main : H1 → H2 → H3 → type_of% @OeisA71524.conjecture1 := by
  intro he ho hInterval n hn
  by_cases finite : n ≤ 401
  · exact hInterval n hn finite
  let m := n / 2
  by_cases h : n % 2 = 0
  · have e : n = 2*m := by dsimp [m]; omega
    rw [e]
    intro hz
    have hs := (blocks m).1
    rw [hz, abs_zero] at hs
    exact pow_ne_zero 2 (he m (by dsimp [m]; omega)) hs.symm
  · have e : n = 2*m+1 := by dsimp [m]; omega
    rw [e]
    intro hz
    have hs := (blocks m).2
    rw [hz, abs_zero] at hs
    exact pow_ne_zero 2 (ho m (by dsimp [m]; omega)) hs.symm

end OMA.R_OeisA71524_conjecture1_R1
