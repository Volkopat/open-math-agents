import OMAStatements.S_mo_360945
import Mathlib

open OMA.S_mo_360945 Polynomial

abbrev K32 := Option (ZMod 31)

/-- Zech logarithms of `F_32 = F_2[α]/(α^5 + α^2 + 1)`: `α^k + 1 = α^(zech k)` for `k ≠ 0`. -/
def zech (k : ZMod 31) : ZMod 31 :=
  (![0, 18, 5, 29, 10, 2, 27, 22, 20, 16, 4, 19, 23, 14, 13, 24, 9, 30, 1, 11, 8, 25, 7, 12, 15,
    21, 28, 6, 26, 3, 17] : Fin 31 → ZMod 31) k

/-- Addition in `F_32`, with `none = 0` and `some k = α^k`. -/
def add32 : K32 → K32 → K32
  | none, y => y
  | some i, none => some i
  | some i, some j => if i = j then none else some (i + zech (j - i))

/-- Multiplication in `F_32`. -/
def mul32 : K32 → K32 → K32
  | some i, some j => some (i + j)
  | _, _ => none

theorem add32_assoc_one : ∀ y z : K32, add32 (add32 (some 0) y) z = add32 (some 0) (add32 y z) := by
  decide +kernel

theorem add32_comm : ∀ x y : K32, add32 x y = add32 y x := by
  decide +kernel

theorem mul32_add32 (k : ZMod 31) (x y : K32) :
    mul32 (some k) (add32 x y) = add32 (mul32 (some k) x) (mul32 (some k) y) := by
  rcases x with _ | i <;> rcases y with _ | j
  · rfl
  · rfl
  · rfl
  · by_cases h : i = j
    · subst h; simp [add32, mul32]
    · have h' : k + i ≠ k + j := fun e => h (add_left_cancel e)
      simp only [add32, mul32, if_neg h, if_neg h']
      rw [show k + j - (k + i) = j - i by ring]
      congr 1
      ring

theorem scale_inv (i : ZMod 31) (y : K32) : mul32 (some i) (mul32 (some (-i)) y) = y := by
  rcases y with _ | j
  · rfl
  · simp only [mul32, Option.some.injEq]; ring

theorem assoc_scaled (i : ZMod 31) (y z : K32) :
    add32 (add32 (mul32 (some i) (some 0)) (mul32 (some i) y)) (mul32 (some i) z) =
      add32 (mul32 (some i) (some 0)) (add32 (mul32 (some i) y) (mul32 (some i) z)) := by
  rw [← mul32_add32, ← mul32_add32, ← mul32_add32, ← mul32_add32, add32_assoc_one]

theorem add32_assoc (x y z : K32) : add32 (add32 x y) z = add32 x (add32 y z) := by
  rcases x with _ | i
  · rfl
  · have h := assoc_scaled i (mul32 (some (-i)) y) (mul32 (some (-i)) z)
    rw [scale_inv, scale_inv, show mul32 (some i) (some 0) = some i by simp [mul32]] at h
    exact h

theorem add32_zero (x : K32) : add32 x none = x := by rcases x with _ | i <;> rfl

theorem add32_self (x : K32) : add32 x x = none := by
  rcases x with _ | i
  · rfl
  · simp [add32]

theorem mul32_comm (a b : K32) : mul32 a b = mul32 b a := by
  rcases a with _ | i <;> rcases b with _ | j <;> first | rfl | simp [mul32, add_comm]

theorem mul32_assoc (a b c : K32) : mul32 (mul32 a b) c = mul32 a (mul32 b c) := by
  rcases a with _ | i <;> rcases b with _ | j <;> rcases c with _ | k <;>
    first | rfl | simp [mul32, add_assoc]

theorem mul32_one (x : K32) : mul32 x (some 0) = x := by
  rcases x with _ | i <;> first | rfl | simp [mul32]

theorem one_mul32 (x : K32) : mul32 (some 0) x = x := by
  rcases x with _ | i <;> first | rfl | simp [mul32]

theorem mul32_zero (x : K32) : mul32 x none = none := by rcases x with _ | i <;> rfl

theorem left_distrib32 (a b c : K32) : mul32 a (add32 b c) = add32 (mul32 a b) (mul32 a c) := by
  rcases a with _ | k
  · rfl
  · exact mul32_add32 k b c

theorem right_distrib32 (a b c : K32) : mul32 (add32 a b) c = add32 (mul32 a c) (mul32 b c) := by
  rw [mul32_comm, left_distrib32, mul32_comm c a, mul32_comm c b]

/-- The ring structure of `F_32`. -/
def ring32 : CommRing K32 :=
  letI : Zero K32 := ⟨none⟩
  letI : Add K32 := ⟨add32⟩
  letI : Neg K32 := ⟨id⟩
  letI : Mul K32 := ⟨mul32⟩
  letI : One K32 := ⟨some 0⟩
  { add := add32
    add_assoc := add32_assoc
    zero := none
    zero_add := fun _ => rfl
    add_zero := add32_zero
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg := id
    neg_add_cancel := add32_self
    add_comm := add32_comm
    mul := mul32
    left_distrib := left_distrib32
    right_distrib := right_distrib32
    zero_mul := fun _ => rfl
    mul_zero := mul32_zero
    mul_assoc := mul32_assoc
    one := some 0
    one_mul := one_mul32
    mul_one := mul32_one
    mul_comm := mul32_comm }

theorem root32 : ∀ a ∈ ({some 0, some 19, some 11} : Finset K32), ∀ x : K32,
    add32 (add32 (mul32 x x) (mul32 a x)) (some 0) ≠ none := by
  decide +kernel

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_360945.main) := by
  intro h
  letI : CommRing K32 := ring32
  have hF : IsField K32 := by
    refine ⟨⟨none, some 0, by simp⟩, fun a b => mul_comm a b, fun {a} ha => ?_⟩
    rcases a with _ | i
    · exact absurd rfl ha
    · exact ⟨some (-i), by show mul32 (some i) (some (-i)) = some 0; simp [mul32]⟩
  letI : Field K32 := hF.toField
  have hcard : Fintype.card K32 = 2 ^ 5 := by simp
  have hne : (some 0 : K32) ^ 2 ≠ some 19 := by
    rw [pow_two]
    show mul32 (some 0) (some 0) ≠ some 19
    decide
  obtain ⟨k, -, hk⟩ := h 5 (by norm_num) K32 hcard (some 0) (some 19) hne
  apply hk
  have key : ∀ n, seq (some 0 : K32) (some 19) (3 * n) = some 0 ∧
      seq (some 0 : K32) (some 19) (3 * n + 1) = some 19 ∧
      seq (some 0 : K32) (some 19) (3 * n + 2) = some 11 := by
    intro n
    induction n with
    | zero => exact ⟨rfl, rfl, by rw [show 3 * 0 + 2 = 0 + 2 by rfl, seq]; rfl⟩
    | succ n ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      have e0 : seq (some 0 : K32) (some 19) (3 * (n + 1)) = some 0 := by
        rw [show 3 * (n + 1) = (3 * n + 1) + 2 by ring, seq, h2, h1]
        show add32 (mul32 (some 0) (some 11)) (some 19) = some 0
        decide
      have e1 : seq (some 0 : K32) (some 19) (3 * (n + 1) + 1) = some 19 := by
        rw [show 3 * (n + 1) + 1 = (3 * n + 2) + 2 by ring, seq,
          show 3 * n + 2 + 1 = 3 * (n + 1) by ring, e0, h2]
        show add32 (mul32 (some 0) (some 0)) (some 11) = some 19
        decide
      have e2 : seq (some 0 : K32) (some 19) (3 * (n + 1) + 2) = some 11 := by
        rw [seq, e1, e0]
        show add32 (mul32 (some 0) (some 19)) (some 0) = some 11
        decide
      exact ⟨e0, e1, e2⟩
  have hseq : seq (some 0 : K32) (some 19) k ∈ ({some 0, some 19, some 11} : Finset K32) := by
    have hk3 : k = 3 * (k / 3) + k % 3 := (Nat.div_add_mod k 3).symm
    have hr : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hr with hr | hr | hr <;> rw [hk3, hr]
    · rw [add_zero, (key _).1]; simp
    · rw [(key _).2.1]; simp
    · rw [(key _).2.2]; simp
  have hirr : ∀ a ∈ ({some 0, some 19, some 11} : Finset K32),
      Irreducible (X ^ 2 + C a * X + 1 : K32[X]) := by
    intro a ha
    have hp : (X ^ 2 + C a * X + 1 : K32[X]) = C 1 * X ^ 2 + C a * X + C 1 := by simp
    have hdeg : (X ^ 2 + C a * X + 1 : K32[X]).natDegree = 2 := by
      rw [hp]; exact natDegree_quadratic one_ne_zero
    have hp0 : (X ^ 2 + C a * X + 1 : K32[X]) ≠ 0 := by
      intro h0; rw [h0, natDegree_zero] at hdeg; exact absurd hdeg (by norm_num)
    rw [irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    refine Multiset.eq_zero_iff_forall_notMem.mpr fun x hx => ?_
    rw [mem_roots hp0, IsRoot.def] at hx
    have hx' : x ^ 2 + a * x + 1 = 0 := by simpa using hx
    rw [pow_two] at hx'
    exact root32 a ha x hx'
  exact hirr _ hseq
