import OMAReductions.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1
import Mathlib

/-!
Verified 343-bit bitboard constraint-propagation and transversal-forbidding
proof that every order-7 Latin square has a transversal.
-/

namespace OMA.LS7

open LatinSquare

/- ### Part 1: Isotopies, normalization to 4 row-1 cycle types, and lex-min orbit -/

def Isotopic (L M : LatinSquare 7) : Prop :=
  ∃ (p q s : Fin 7 ≃ Fin 7), ∀ i j, M.mat i j = s (L.mat (p i) (q j))

private lemma isotopic_refl (L : LatinSquare 7) : Isotopic L L :=
  ⟨Equiv.refl _, Equiv.refl _, Equiv.refl _, fun _ _ => rfl⟩

private lemma isotopic_trans {L M K : LatinSquare 7}
    (h1 : Isotopic L M) (h2 : Isotopic M K) : Isotopic L K := by
  rcases h1 with ⟨p1, q1, s1, hLM⟩
  rcases h2 with ⟨p2, q2, s2, hMK⟩
  refine ⟨p2.trans p1, q2.trans q1, s1.trans s2, fun i j => ?_⟩
  simp only [Equiv.trans_apply]
  rw [hMK i j, hLM (p2 i) (q2 j)]

private lemma hasTransversal_of_isotopic {L M : LatinSquare 7}
    (h : Isotopic L M) (ht : ∃ σ, IsTransversal M σ) : ∃ σ, IsTransversal L σ := by
  rcases h with ⟨p, q, s, hLM⟩
  rcases ht with ⟨σ, hσinj, hsyminj⟩
  refine ⟨fun i => q (σ (p.symm i)),
    q.injective.comp (hσinj.comp p.symm.injective), ?_⟩
  intro i j heq
  have h1 : M.mat (p.symm i) (σ (p.symm i)) = M.mat (p.symm j) (σ (p.symm j)) := by
    rw [hLM, hLM, p.apply_symm_apply, p.apply_symm_apply]
    exact congrArg s heq
  exact p.symm.injective (hsyminj h1)

def IsReducedWith (r1 : Fin 7 → Fin 7) (M : LatinSquare 7) : Prop :=
  (∀ j, M.mat 0 j = j) ∧ (∀ i, M.mat i 0 = i) ∧ (∀ j, M.mat 1 j = r1 j)

def r1Table : Fin 4 → Fin 7 → Fin 7 :=
  ![![1, 2, 3, 4, 5, 6, 0],
    ![1, 2, 3, 4, 0, 6, 5],
    ![1, 2, 3, 0, 5, 6, 4],
    ![1, 2, 0, 4, 3, 6, 5]]

def r1InvTable : Fin 4 → Fin 7 → Fin 7 :=
  ![![6, 0, 1, 2, 3, 4, 5],
    ![4, 0, 1, 2, 3, 6, 5],
    ![3, 0, 1, 2, 6, 4, 5],
    ![2, 0, 1, 4, 3, 6, 5]]

private lemma threeSlots (m : Multiset ℕ) (total : m.sum = 7) (large : ∀ x ∈ m, 2 ≤ x)
    (kinds : Fin 4 → Multiset ℕ)
    (check : ∀ a b c : Fin 8, a.val ≠ 1 → b.val ≠ 1 → c.val ≠ 1 →
      a.val + b.val + c.val = 7 →
      ∃ i, (([a.val, b.val, c.val].filter (· != 0) : List ℕ) : Multiset ℕ) = kinds i) :
    ∃ i, m = kinds i := by
  have weight (q : Multiset ℕ) (h : ∀ x ∈ q, 2 ≤ x) : 2 * q.card ≤ q.sum := by
    induction q using Multiset.induction_on with
    | empty => simp
    | cons x xs ih =>
      have ha := h x (by simp)
      have hb := ih (fun y hy => h y (by simp [hy]))
      simp only [Multiset.card_cons, Multiset.sum_cons]
      omega
  have hlen : m.card ≤ 3 := by have := weight m large; omega
  let q := m.toList ++ List.replicate (3 - m.card) 0
  have len3 : q.length = 3 := by simp [q]; omega
  have sum3 : q.sum = 7 := by simpa [q] using total
  have hnon (x : ℕ) (hx : x ∈ q) : x ≠ 1 := by
    rcases List.mem_append.mp hx with h | h
    · have := large x (by simpa using h); omega
    · have := (List.mem_replicate.mp h).2; omega
  have keep : q.filter (· != 0) = m.toList := by
    have h : m.toList.filter (· != 0) = m.toList := by
      apply List.filter_eq_self.mpr
      intro x hx
      have := large x (by simpa using hx)
      simpa using (by omega : x ≠ 0)
    simp [q, List.filter_append, h]
  have fields (xs : List ℕ) (hl : xs.length = 3) : ∃ a b c, xs = [a, b, c] := by
    match xs with
    | [a, b, c] => exact ⟨a, b, c, rfl⟩
    | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => simp_all
  obtain ⟨a, b, c, shape⟩ := fields q len3
  rw [shape] at sum3 hnon keep
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at sum3
  obtain ⟨i, hi⟩ := check ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨c, by omega⟩
    (hnon a (by simp)) (hnon b (by simp)) (hnon c (by simp))
    (by change a + b + c = 7; omega)
  exact ⟨i, by simpa only [keep, Multiset.coe_toList] using hi⟩

private lemma normalize_to_4 (L : LatinSquare 7) :
    ∃ (k : Fin 4) (M : LatinSquare 7), IsReducedWith (r1Table k) M ∧ Isotopic L M := by
  let r0 : Equiv.Perm (Fin 7) := Equiv.ofBijective (L.mat 0)
    ⟨L.row_injective 0, Finite.surjective_of_injective (L.row_injective 0)⟩
  let L1 : LatinSquare 7 := {
    mat := fun i j => r0.symm (L.mat i j)
    row_injective := fun i => r0.symm.injective.comp (L.row_injective i)
    col_injective := fun j => r0.symm.injective.comp (L.col_injective j) }
  have hIL1 : Isotopic L L1 := ⟨Equiv.refl _, Equiv.refl _, r0.symm, fun _ _ => rfl⟩
  have hL10 : ∀ j, L1.mat 0 j = j := fun j => r0.symm_apply_apply j
  let f : Equiv.Perm (Fin 7) := Equiv.ofBijective (L1.mat 1)
    ⟨L1.row_injective 1, Finite.surjective_of_injective (L1.row_injective 1)⟩
  have hfixed (j : Fin 7) : f j ≠ j := by
    intro h
    have eq : L1.mat 1 j = L1.mat 0 j := h.trans (hL10 j).symm
    exact (by decide : (1 : Fin 7) ≠ 0) (L1.col_injective j eq)
  have hsupp : f.support = Finset.univ :=
    Finset.eq_univ_of_forall fun j => Equiv.Perm.mem_support.mpr (hfixed j)
  have htot : f.cycleType.sum = 7 := by rw [f.sum_cycleType, hsupp]; simp
  let kinds : Fin 4 → Multiset ℕ :=
    ![({7} : Multiset ℕ), ({5, 2} : Multiset ℕ), ({4, 3} : Multiset ℕ), ({3, 2, 2} : Multiset ℕ)]
  let leftInv : ∀ k j, r1InvTable k (r1Table k j) = j := by decide
  let rightInv : ∀ k j, r1Table k (r1InvTable k j) = j := by decide
  let perms (k : Fin 4) : Equiv.Perm (Fin 7) := ⟨r1Table k, r1InvTable k, leftInv k, rightInv k⟩
  have hct : ∀ k, (perms k).cycleType = kinds k := by decide +kernel
  have hpart : ∀ a b c : Fin 8, a.val ≠ 1 → b.val ≠ 1 → c.val ≠ 1 →
      a.val + b.val + c.val = 7 →
      ∃ i, (([a.val, b.val, c.val].filter (· != 0) : List ℕ) : Multiset ℕ) = kinds i := by
    decide +kernel
  obtain ⟨k, htype⟩ := threeSlots f.cycleType htot
    (fun _ h => Equiv.Perm.two_le_of_mem_cycleType h) kinds hpart
  have hconj : IsConj f (perms k) :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr (htype.trans (hct k).symm)
  obtain ⟨e, he⟩ := isConj_iff.mp hconj
  let L2 : LatinSquare 7 := {
    mat := fun i j => e (L1.mat i (e.symm j))
    row_injective := fun i => e.injective.comp ((L1.row_injective i).comp e.symm.injective)
    col_injective := fun j => e.injective.comp (L1.col_injective (e.symm j)) }
  have hIL2 : Isotopic L1 L2 := ⟨Equiv.refl _, e.symm, e, fun _ _ => rfl⟩
  have hL20 : ∀ j, L2.mat 0 j = j := fun j => by
    change e (L1.mat 0 (e.symm j)) = j
    rw [hL10, e.apply_symm_apply]
  have hL21 : ∀ j, L2.mat 1 j = r1Table k j := fun j => by
    have hf : ∀ x, f x = L1.mat 1 x := fun _ => rfl
    change e (L1.mat 1 (e.symm j)) = (perms k) j
    rw [← hf]
    have := DFunLike.congr_fun he j
    simpa [Equiv.Perm.mul_apply] using this
  let rowP : Equiv.Perm (Fin 7) := Equiv.ofBijective (fun i => L2.mat i 0)
    ⟨L2.col_injective 0, Finite.surjective_of_injective (L2.col_injective 0)⟩
  have hrow0 : rowP 0 = 0 := hL20 0
  have hrow1 : rowP 1 = 1 := by
    have hr10 : r1Table k 0 = 1 := by fin_cases k <;> decide
    exact (hL21 0).trans hr10
  let M : LatinSquare 7 := {
    mat := fun i j => L2.mat (rowP.symm i) j
    row_injective := fun i => L2.row_injective (rowP.symm i)
    col_injective := fun j => (L2.col_injective j).comp rowP.symm.injective }
  have hIM : Isotopic L2 M := ⟨rowP.symm, Equiv.refl _, Equiv.refl _, fun _ _ => rfl⟩
  refine ⟨k, M, ⟨?_, ?_, ?_⟩, isotopic_trans hIL1 (isotopic_trans hIL2 hIM)⟩
  · intro j
    change L2.mat (rowP.symm 0) j = j
    rw [show rowP.symm 0 = 0 from rowP.symm_apply_eq.mpr hrow0.symm]
    exact hL20 j
  · intro i
    exact rowP.apply_symm_apply i
  · intro j
    change L2.mat (rowP.symm 1) j = r1Table k j
    rw [show rowP.symm 1 = 1 from rowP.symm_apply_eq.mpr hrow1.symm]
    exact hL21 j

def cellOrder : List (Fin 7 × Fin 7) :=
  [(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),
   (3,1),(3,2),(3,3),(3,4),(3,5),(3,6),
   (4,1),(4,2),(4,3),(4,4),(4,5),(4,6),
   (5,1),(5,2),(5,3),(5,4),(5,5),(5,6),
   (6,1),(6,2),(6,3),(6,4),(6,5),(6,6)]

def lexKeyAux (M : LatinSquare 7) : List (Fin 7 × Fin 7) → Nat
  | [] => 0
  | (r, c) :: rest => (M.mat r c).val * 8 ^ rest.length + lexKeyAux M rest

private lemma lexKeyAux_lt (M : LatinSquare 7) :
    ∀ L : List (Fin 7 × Fin 7), lexKeyAux M L < 8 ^ L.length
  | [] => by simp [lexKeyAux]
  | (r, c) :: rest => by
    have ih := lexKeyAux_lt M rest
    have hm : (M.mat r c).val < 7 := (M.mat r c).isLt
    simp only [lexKeyAux, List.length_cons, pow_succ']
    have hpow : 0 < 8 ^ rest.length := by positivity
    nlinarith

private lemma lexKeyAux_lt_of_first_diff {M1 M2 : LatinSquare 7} :
    ∀ (L : List (Fin 7 × Fin 7)) (r0 c0 : Fin 7),
      (r0, c0) ∈ L →
      (∀ r c, (r, c) ∈ L → (r.val < r0.val ∨ (r = r0 ∧ c.val < c0.val)) → M2.mat r c = M1.mat r c) →
      L.Pairwise (fun a b => a.1.val < b.1.val ∨ (a.1 = b.1 ∧ a.2.val < b.2.val)) →
      (M2.mat r0 c0).val < (M1.mat r0 c0).val →
      lexKeyAux M2 L < lexKeyAux M1 L
  | [], _, _, hmem, _, _, _ => by cases hmem
  | (r, c) :: rest, r0, c0, hmem, hpre, hpw, hlt => by
    rcases List.mem_cons.mp hmem with heq | hmem'
    · injection heq with hr hc
      subst hr; subst hc
      have h2 := lexKeyAux_lt M2 rest
      simp only [lexKeyAux]
      have hpow : 0 < 8 ^ rest.length := by positivity
      have hstep : ((M2.mat r0 c0).val + 1) * 8 ^ rest.length ≤ (M1.mat r0 c0).val * 8 ^ rest.length :=
        Nat.mul_le_mul_right _ hlt
      nlinarith
    · have hrc_lt : r.val < r0.val ∨ (r = r0 ∧ c.val < c0.val) :=
        (List.pairwise_cons.mp hpw).1 (r0, c0) hmem'
      have hsame : M2.mat r c = M1.mat r c := hpre r c List.mem_cons_self hrc_lt
      simp only [lexKeyAux, hsame]
      have ih := lexKeyAux_lt_of_first_diff rest r0 c0 hmem'
        (fun r' c' hm hlt' => hpre r' c' (List.mem_cons_of_mem _ hm) hlt')
        (List.pairwise_cons.mp hpw).2 hlt
      omega

private lemma cellOrder_pairwise :
    cellOrder.Pairwise (fun a b => a.1.val < b.1.val ∨ (a.1 = b.1 ∧ a.2.val < b.2.val)) := by
  decide

private lemma mem_cellOrder {r c : Fin 7} (hr : 2 ≤ r.val) (hc : 1 ≤ c.val) :
    (r, c) ∈ cellOrder := by
  revert r c hr hc; decide +kernel

private lemma mem_cellOrder_bounds {r c : Fin 7} (h : (r, c) ∈ cellOrder) :
    2 ≤ r.val ∧ 1 ≤ c.val := by
  revert r c h; decide +kernel

private lemma exists_lexmin_reduced {k : Fin 4} {L : LatinSquare 7}
    (hred : IsReducedWith (r1Table k) L) :
    ∃ M : LatinSquare 7, IsReducedWith (r1Table k) M ∧ Isotopic L M ∧
      ∀ M' : LatinSquare 7, IsReducedWith (r1Table k) M' → Isotopic M M' →
        lexKeyAux M cellOrder ≤ lexKeyAux M' cellOrder := by
  classical
  let P : Nat → Prop := fun v =>
    ∃ M : LatinSquare 7, IsReducedWith (r1Table k) M ∧ Isotopic L M ∧ lexKeyAux M cellOrder = v
  have hex : ∃ v, P v := ⟨lexKeyAux L cellOrder, L, hred, isotopic_refl L, rfl⟩
  obtain ⟨M, hMred, hMiso, hMval⟩ := Nat.find_spec hex
  refine ⟨M, hMred, hMiso, ?_⟩
  intro M' hred' hiso'
  rw [hMval]
  exact Nat.find_min' hex ⟨M', hred', isotopic_trans hMiso hiso', rfl⟩

/- ### Part 2: 343-bit bitboard primitives and soundness -/

def ALL343 : Nat := 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def ROW_BIT0 : Nat := 0x0000040810204081
def COL_BIT0 : Nat := 0x40000000000020000000000010000000000008000000000004000000000002000000000001

def dom (B r c : Nat) : Nat :=
  Nat.land (Nat.shiftRight B ((r * 7 + c) * 7)) 127

def rowMask (r v : Nat) : Nat := Nat.shiftLeft ROW_BIT0 (r * 49 + v)
def colMask (c v : Nat) : Nat := Nat.shiftLeft COL_BIT0 (c * 7 + v)
def cellBit (r c v : Nat) : Nat := Nat.shiftLeft 1 ((r * 7 + c) * 7 + v)
def cellAll (r c : Nat) : Nat := Nat.shiftLeft 127 ((r * 7 + c) * 7)

def clearCell (B r c v : Nat) : Nat :=
  let kill := Nat.xor (Nat.lor (Nat.lor (rowMask r v) (colMask c v)) (cellAll r c)) (cellBit r c v)
  Nat.land B (Nat.xor ALL343 kill)

def forbidMask (B r c mask : Nat) : Nat :=
  Nat.land B (Nat.xor ALL343 (Nat.shiftLeft mask ((r * 7 + c) * 7)))

def rowOther (r c v : Nat) : Nat :=
  Nat.xor (rowMask r v) (cellBit r c v)

def colOther (r c v : Nat) : Nat :=
  Nat.xor (colMask c v) (cellBit r c v)

def isSingle (m : Nat) : Bool :=
  match Nat.beq m 0 with
  | true => false
  | false => Nat.beq (Nat.land m (Nat.sub m 1)) 0

def ValidBoard (L : LatinSquare 7) (B : Nat) : Prop :=
  ∀ r c : Fin 7, B.testBit ((r.val * 7 + c.val) * 7 + (L.mat r c).val) = true

private lemma testBit_ALL343 {w : Nat} (hw : w < 343) : ALL343.testBit w = true := by
  have h1 : ALL343 = 2 ^ 200 * 2 ^ 143 - 1 := by decide +kernel
  have h : ALL343 = 2 ^ 343 - 1 := by rw [h1, ← pow_add]
  rw [h, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hw

private lemma testBit_shiftLeft_local (x s w : Nat) :
    (Nat.shiftLeft x s).testBit w = (decide (s ≤ w) && x.testBit (w - s)) := by
  change (x <<< s).testBit w = _
  rw [Nat.testBit_shiftLeft]

private lemma testBit_ROW_BIT0 (k : Nat) :
    ROW_BIT0.testBit k = decide (k < 49 ∧ k % 7 = 0) := by
  by_cases hk : k < 49
  · revert k
    decide
  · have hlt : ROW_BIT0 < 2 ^ 49 := by decide
    have hge : 49 ≤ k := by omega
    have hpow : ROW_BIT0 < 2 ^ k := lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hge)
    rw [Nat.testBit_lt_two_pow hpow]
    simp [hk]

private lemma testBit_COL_BIT0 (k : Nat) :
    COL_BIT0.testBit k = decide (k < 343 ∧ k % 49 = 0) := by
  have hcol : COL_BIT0 = (((((1 ||| Nat.shiftLeft 1 49) ||| Nat.shiftLeft 1 98) |||
      Nat.shiftLeft 1 147) ||| Nat.shiftLeft 1 196) ||| Nat.shiftLeft 1 245) |||
      Nat.shiftLeft 1 294 := by decide +kernel
  have tsl : ∀ a : Nat, (Nat.shiftLeft 1 a).testBit k = decide (a = k) := by
    intro a; change (1 <<< a).testBit k = _; rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  have t1 : (1 : Nat).testBit k = decide (0 = k) := by
    have : (1 : Nat) = 2 ^ 0 := rfl
    rw [this, Nat.testBit_two_pow]
  rw [hcol]
  simp only [Nat.testBit_or, t1, tsl]
  by_cases hk : k < 343 ∧ k % 49 = 0
  · rw [decide_eq_true hk]
    have hcases : k = 0 ∨ k = 49 ∨ k = 98 ∨ k = 147 ∨ k = 196 ∨ k = 245 ∨ k = 294 := by omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [decide_eq_false hk]
    have h0 : ¬ (0 = k) := by omega
    have h1 : ¬ (49 = k) := by omega
    have h2 : ¬ (98 = k) := by omega
    have h3 : ¬ (147 = k) := by omega
    have h4 : ¬ (196 = k) := by omega
    have h5 : ¬ (245 = k) := by omega
    have h6 : ¬ (294 = k) := by omega
    simp [h0, h1, h2, h3, h4, h5, h6]

private lemma testBit_cellBit (r c v w : Nat) :
    (cellBit r c v).testBit w = decide ((r * 7 + c) * 7 + v = w) := by
  unfold cellBit
  change (1 <<< ((r * 7 + c) * 7 + v)).testBit w = _
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

private lemma testBit_rowMask (r v r' c' v' : Fin 7) :
    (rowMask r.val v.val).testBit ((r'.val * 7 + c'.val) * 7 + v'.val) =
      decide (r' = r ∧ v' = v) := by
  unfold rowMask
  rw [testBit_shiftLeft_local, testBit_ROW_BIT0]
  have hr := r.isLt; have hv := v.isLt
  have hr' := r'.isLt; have hc' := c'.isLt; have hv' := v'.isLt
  by_cases h1 : r' = r ∧ v' = v
  · rcases h1 with ⟨rfl, rfl⟩
    simp only [and_self, decide_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, by omega, by omega⟩
  · simp only [decide_eq_false h1, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases hle : r.val * 49 + v.val ≤ (r'.val * 7 + c'.val) * 7 + v'.val
    · right
      intro ⟨hsub, hmod⟩
      apply h1
      have hre : r'.val = r.val := by omega
      have hve : v'.val = v.val := by omega
      exact ⟨Fin.ext hre, Fin.ext hve⟩
    · left; exact hle

private lemma testBit_colMask (c v r' c' v' : Fin 7) :
    (colMask c.val v.val).testBit ((r'.val * 7 + c'.val) * 7 + v'.val) =
      decide (c' = c ∧ v' = v) := by
  unfold colMask
  rw [testBit_shiftLeft_local, testBit_COL_BIT0]
  have hc := c.isLt; have hv := v.isLt
  have hr' := r'.isLt; have hc' := c'.isLt; have hv' := v'.isLt
  by_cases h1 : c' = c ∧ v' = v
  · rcases h1 with ⟨rfl, rfl⟩
    simp only [and_self, decide_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, by omega, by omega⟩
  · simp only [decide_eq_false h1, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases hle : c.val * 7 + v.val ≤ (r'.val * 7 + c'.val) * 7 + v'.val
    · right
      intro ⟨hsub, hmod⟩
      apply h1
      have hce : c'.val = c.val := by omega
      have hve : v'.val = v.val := by omega
      exact ⟨Fin.ext hce, Fin.ext hve⟩
    · left; exact hle

private lemma testBit_cellAll (r c r' c' v' : Fin 7) :
    (cellAll r.val c.val).testBit ((r'.val * 7 + c'.val) * 7 + v'.val) =
      decide (r' = r ∧ c' = c) := by
  unfold cellAll
  rw [testBit_shiftLeft_local]
  have hr := r.isLt; have hc := c.isLt
  have hr' := r'.isLt; have hc' := c'.isLt; have hv' := v'.isLt
  by_cases h1 : r' = r ∧ c' = c
  · rcases h1 with ⟨rfl, rfl⟩
    have h127 : (127 : Nat).testBit v'.val = true := by
      have : (127 : Nat) = 2 ^ 7 - 1 := rfl
      rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hv'
    simp only [and_self, decide_true, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, by simpa [show (r'.val * 7 + c'.val) * 7 + v'.val - (r'.val * 7 + c'.val) * 7 = v'.val by omega] using h127⟩
  · simp only [decide_eq_false h1, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases hle : (r.val * 7 + c.val) * 7 ≤ (r'.val * 7 + c'.val) * 7 + v'.val
    · right
      have hgt : 7 ≤ (r'.val * 7 + c'.val) * 7 + v'.val - (r.val * 7 + c.val) * 7 := by
        by_contra hlt
        have : r'.val = r.val ∧ c'.val = c.val := by omega
        exact h1 ⟨Fin.ext this.1, Fin.ext this.2⟩
      have hpow : (127 : Nat) < 2 ^ ((r'.val * 7 + c'.val) * 7 + v'.val - (r.val * 7 + c.val) * 7) :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by omega) hgt)
      rw [Nat.testBit_lt_two_pow hpow]
    · left; exact hle

private lemma testBit_dom (B : Nat) (r c v : Fin 7) :
    (dom B r.val c.val).testBit v.val = B.testBit ((r.val * 7 + c.val) * 7 + v.val) := by
  unfold dom
  change ((B >>> ((r.val * 7 + c.val) * 7)) &&& 127).testBit v.val = _
  rw [Nat.testBit_and, Nat.testBit_shiftRight]
  have h127 : (127 : Nat).testBit v.val = true := by
    have : (127 : Nat) = 2 ^ 7 - 1 := rfl
    rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true v.isLt
  rw [h127, Bool.and_true]

private lemma dom_lt_128 (B r c : Nat) : dom B r c < 128 := by
  unfold dom
  change (B >>> ((r * 7 + c) * 7)) &&& 127 < 128
  exact Nat.lt_succ_of_le Nat.and_le_right

private lemma isSingle_eq_bit {m : Nat} (hlt : m < 128) (hs : isSingle m = true) :
    ∃ v : Fin 7, m = Nat.shiftLeft 1 v.val := by
  have hall : ∀ k < 128, isSingle k = true → ∃ v : Fin 7, k = Nat.shiftLeft 1 v.val := by decide
  exact hall m hlt hs

private lemma dom_eq_bit_of_isSingle {L : LatinSquare 7} {B : Nat} (hB : ValidBoard L B)
    (r c : Fin 7) (hs : isSingle (dom B r.val c.val) = true) :
    dom B r.val c.val = Nat.shiftLeft 1 (L.mat r c).val := by
  obtain ⟨v, hv⟩ := isSingle_eq_bit (dom_lt_128 B r.val c.val) hs
  have hbit : (dom B r.val c.val).testBit (L.mat r c).val = true := by
    rw [testBit_dom]; exact hB r c
  rw [hv] at hbit
  change (1 <<< v.val).testBit (L.mat r c).val = true at hbit
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, decide_eq_true_eq] at hbit
  rw [hv, hbit]

private lemma eq_of_dom_eq_bit {L : LatinSquare 7} {B : Nat} (hB : ValidBoard L B)
    {r c v : Fin 7} (h : dom B r.val c.val = Nat.shiftLeft 1 v.val) : L.mat r c = v := by
  have hbit : (dom B r.val c.val).testBit (L.mat r c).val = true := by
    rw [testBit_dom]; exact hB r c
  rw [h] at hbit
  change (1 <<< v.val).testBit (L.mat r c).val = true at hbit
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, decide_eq_true_eq] at hbit
  exact Fin.ext hbit.symm

private lemma clearCell_valid {L : LatinSquare 7} {B : Nat} (hB : ValidBoard L B)
    {r c v : Fin 7} (heq : L.mat r c = v) :
    ValidBoard L (clearCell B r.val c.val v.val) := by
  intro r' c'
  unfold clearCell
  set v' := L.mat r' c'
  set w := (r'.val * 7 + c'.val) * 7 + v'.val
  have hw : w < 343 := by have := r'.isLt; have := c'.isLt; have := v'.isLt; omega
  change (B &&& (ALL343 ^^^ (((rowMask r.val v.val ||| colMask c.val v.val) ||| cellAll r.val c.val) ^^^ cellBit r.val c.val v.val))).testBit w = true
  rw [Nat.testBit_and, hB r' c', Bool.true_and, Nat.testBit_xor, testBit_ALL343 hw,
      Nat.testBit_xor, Nat.testBit_or, Nat.testBit_or,
      testBit_rowMask, testBit_colMask, testBit_cellAll, testBit_cellBit]
  have hcb : ((r.val * 7 + c.val) * 7 + v.val = w) ↔ (r' = r ∧ c' = c ∧ v' = v) := by
    have hr := r.isLt; have hc := c.isLt; have hv := v.isLt
    have hr' := r'.isLt; have hc' := c'.isLt; have hv' := v'.isLt
    constructor
    · intro h
      exact ⟨Fin.ext (by omega), Fin.ext (by omega), Fin.ext (by omega)⟩
    · rintro ⟨rfl, rfl, rfl⟩; rfl
  by_cases hrr : r' = r
  · subst hrr
    by_cases hcc : c' = c
    · subst hcc
      have hvv : v' = v := heq
      simp [hcb, hvv]
    · have hvv : v' ≠ v := fun hv => hcc (L.row_injective r' (hv.trans heq.symm))
      simp [hcb, hcc, hvv]
  · by_cases hcc : c' = c
    · subst hcc
      have hvv : v' ≠ v := fun hv => hrr (L.col_injective c' (hv.trans heq.symm))
      simp [hcb, hrr, hvv]
    · simp [hcb, hrr, hcc]

private lemma forbidMask_valid {L : LatinSquare 7} {B : Nat} (hB : ValidBoard L B)
    {r c v : Fin 7} (hne : L.mat r c ≠ v) :
    ValidBoard L (forbidMask B r.val c.val (Nat.shiftLeft 1 v.val)) := by
  intro r' c'
  unfold forbidMask
  set v' := L.mat r' c'
  set w := (r'.val * 7 + c'.val) * 7 + v'.val
  have hw : w < 343 := by have := r'.isLt; have := c'.isLt; have := v'.isLt; omega
  change (B &&& (ALL343 ^^^ ((Nat.shiftLeft 1 v.val) <<< ((r.val * 7 + c.val) * 7)))).testBit w = true
  rw [Nat.testBit_and, hB r' c', Bool.true_and, Nat.testBit_xor, testBit_ALL343 hw,
      Nat.testBit_shiftLeft]
  suffices h : (decide ((r.val * 7 + c.val) * 7 ≤ w) &&
      (Nat.shiftLeft 1 v.val).testBit (w - (r.val * 7 + c.val) * 7)) = false by
    rw [h]; rfl
  by_cases hle : (r.val * 7 + c.val) * 7 ≤ w
  · simp only [decide_eq_true hle, Bool.true_and]
    change (1 <<< v.val).testBit (w - (r.val * 7 + c.val) * 7) = false
    rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, decide_eq_false_iff_not]
    intro heq
    have hr := r.isLt; have hc := c.isLt; have hv := v.isLt
    have hr' := r'.isLt; have hc' := c'.isLt; have hv' := v'.isLt
    have hre : r' = r := Fin.ext (by omega)
    have hce : c' = c := Fin.ext (by omega)
    have hve : v' = v := Fin.ext (by omega)
    subst hre; subst hce
    exact hne hve
  · simp [hle]

private lemma eq_of_rowOther_zero {L : LatinSquare 7} {B : Nat} (hB : ValidBoard L B)
    {r c v : Fin 7} (h0 : Nat.land B (rowOther r.val c.val v.val) = 0) : L.mat r c = v := by
  have hsurj : Function.Surjective (L.mat r) := Finite.surjective_of_injective (L.row_injective r)
  obtain ⟨c', hc'⟩ := hsurj v
  by_cases hcc : c' = c
  · exact hcc ▸ hc'
  · exfalso
    set w := (r.val * 7 + c'.val) * 7 + v.val
    have h1 : (B &&& rowOther r.val c.val v.val).testBit w = false := by
      change (Nat.land B (rowOther r.val c.val v.val)).testBit w = false
      rw [h0]; simp
    rw [Nat.testBit_and] at h1
    have hB1 : B.testBit w = true := by simpa [w, hc'] using hB r c'
    have hR1 : (rowOther r.val c.val v.val).testBit w = true := by
      unfold rowOther
      change (rowMask r.val v.val ^^^ cellBit r.val c.val v.val).testBit w = true
      rw [Nat.testBit_xor, testBit_rowMask, testBit_cellBit]
      have hneW : (r.val * 7 + c.val) * 7 + v.val ≠ w := by
        intro heq
        apply hcc
        exact Fin.ext (by omega)
      simp [hneW]
    rw [hB1, hR1] at h1
    cases h1

private lemma eq_of_colOther_zero {L : LatinSquare 7} {B : Nat} (hB : ValidBoard L B)
    {r c v : Fin 7} (h0 : Nat.land B (colOther r.val c.val v.val) = 0) : L.mat r c = v := by
  have hsurj : Function.Surjective (L.mat.transpose c) := Finite.surjective_of_injective (L.col_injective c)
  obtain ⟨r', hr'⟩ := hsurj v
  simp only [Matrix.transpose_apply] at hr'
  by_cases hrr : r' = r
  · exact hrr ▸ hr'
  · exfalso
    set w := (r'.val * 7 + c.val) * 7 + v.val
    have h1 : (B &&& colOther r.val c.val v.val).testBit w = false := by
      change (Nat.land B (colOther r.val c.val v.val)).testBit w = false
      rw [h0]; simp
    rw [Nat.testBit_and] at h1
    have hB1 : B.testBit w = true := by simpa [w, hr'] using hB r' c
    have hC1 : (colOther r.val c.val v.val).testBit w = true := by
      unfold colOther
      change (colMask c.val v.val ^^^ cellBit r.val c.val v.val).testBit w = true
      rw [Nat.testBit_xor, testBit_colMask, testBit_cellBit]
      have hneW : (r.val * 7 + c.val) * 7 + v.val ≠ w := by
        intro heq
        apply hrr
        exact Fin.ext (by omega)
      simp [hneW]
    rw [hB1, hC1] at h1
    cases h1

private lemma validBoard_init (M : LatinSquare 7) :
    ValidBoard M ALL343 := by
  intro r c
  have hw : (r.val * 7 + c.val) * 7 + (M.mat r c).val < 343 := by
    have := r.isLt; have := c.isLt; have := (M.mat r c).isLt; omega
  exact testBit_ALL343 hw

/- ### Part 3: Symmetry transforms and BitStream proof checker -/

def getAt (p : List Nat) (i : Nat) : Nat := p.getD i 0

def checkPerm7 (p : List Nat) : Bool :=
  (List.range 7).all (fun i =>
    decide (getAt p i < 7) &&
    (List.range 7).all (fun j => if i == j then true else decide (getAt p i != getAt p j)))

def checkSym (r1 gi smap smapInv : List Nat) : Bool :=
  checkPerm7 gi && checkPerm7 smap && checkPerm7 smapInv &&
  (List.range 7).all (fun x => smap.getD (smapInv.getD x 0) 0 == x) &&
  (((List.range 7).all (fun j => smap.getD (gi.getD j 0) 0 == j) &&
    (List.range 7).all (fun j => smap.getD (r1.getD (gi.getD j 0) 0) 0 == r1.getD j 0)) ||
   ((List.range 7).all (fun j => smap.getD (r1.getD (gi.getD j 0) 0) 0 == j) &&
    (List.range 7).all (fun j => smap.getD (gi.getD j 0) 0 == r1.getD j 0)))

private lemma checkPerm7_lt {p : List Nat} (hp : checkPerm7 p = true) {i : Nat} (hi : i < 7) :
    getAt p i < 7 := by
  unfold checkPerm7 at hp
  have h1 := List.all_eq_true.mp hp i (List.mem_range.mpr hi)
  rw [Bool.and_eq_true] at h1
  exact of_decide_eq_true h1.1

private lemma checkPerm7_inj {p : List Nat} (hp : checkPerm7 p = true) :
    Function.Injective (fun i : Fin 7 => (⟨getAt p i.val, checkPerm7_lt hp i.isLt⟩ : Fin 7)) := by
  intro i j hij
  by_contra hne
  unfold checkPerm7 at hp
  have h1 := List.all_eq_true.mp hp i.val (List.mem_range.mpr i.isLt)
  rw [Bool.and_eq_true] at h1
  have h2 := List.all_eq_true.mp h1.2 j.val (List.mem_range.mpr j.isLt)
  have hb : (i.val == j.val) = false := beq_false_of_ne (fun h => hne (Fin.ext h))
  rw [hb] at h2
  simp only [Bool.false_eq_true, ↓reduceIte, bne_iff_ne, decide_eq_true_eq] at h2
  exact h2 (congrArg Fin.val hij)

private lemma symTransform_exists {k : Fin 4} {M : LatinSquare 7}
    (hred : IsReducedWith (r1Table k) M)
    {r1 gi smap smapInv : List Nat}
    (hr1 : ∀ j : Fin 7, getAt r1 j.val = (r1Table k j).val)
    (hsym : checkSym r1 gi smap smapInv = true) :
    ∃ (M2 : LatinSquare 7) (rowP : Equiv.Perm (Fin 7)),
      IsReducedWith (r1Table k) M2 ∧ Isotopic M M2 ∧
      (∀ (i j : Fin 7),
        (M2.mat (rowP i) j).val = getAt smap (M.mat i ⟨getAt gi j.val, by
          unfold checkSym at hsym; simp only [Bool.and_eq_true] at hsym
          exact checkPerm7_lt hsym.1.1.1.1 j.isLt⟩).val) ∧
      (∀ (src r : Fin 7),
        (M.mat src ⟨getAt gi 0, by
          unfold checkSym at hsym; simp only [Bool.and_eq_true] at hsym
          exact checkPerm7_lt hsym.1.1.1.1 (by decide)⟩).val = getAt smapInv r.val →
        rowP src = r) := by
  unfold checkSym at hsym
  simp only [Bool.and_eq_true] at hsym
  rcases hsym with ⟨⟨⟨⟨hgiP, hsmapP⟩, hsmapInvP⟩, hinv⟩, hcases⟩
  let giFn : Fin 7 → Fin 7 := fun j => ⟨getAt gi j.val, checkPerm7_lt hgiP j.isLt⟩
  let smapFn : Fin 7 → Fin 7 := fun x => ⟨getAt smap x.val, checkPerm7_lt hsmapP x.isLt⟩
  let giE : Equiv.Perm (Fin 7) := Equiv.ofBijective giFn
    ⟨checkPerm7_inj hgiP, Finite.surjective_of_injective (checkPerm7_inj hgiP)⟩
  let smapE : Equiv.Perm (Fin 7) := Equiv.ofBijective smapFn
    ⟨checkPerm7_inj hsmapP, Finite.surjective_of_injective (checkPerm7_inj hsmapP)⟩
  let M1 : LatinSquare 7 := {
    mat := fun i j => smapE (M.mat i (giE j))
    row_injective := fun i => smapE.injective.comp ((M.row_injective i).comp giE.injective)
    col_injective := fun j => smapE.injective.comp (M.col_injective (giE j)) }
  have hIM1 : Isotopic M M1 := ⟨Equiv.refl _, giE, smapE, fun _ _ => rfl⟩
  let rowP : Equiv.Perm (Fin 7) := Equiv.ofBijective (fun i => M1.mat i 0)
    ⟨M1.col_injective 0, Finite.surjective_of_injective (M1.col_injective 0)⟩
  let M2 : LatinSquare 7 := {
    mat := fun i j => M1.mat (rowP.symm i) j
    row_injective := fun i => M1.row_injective (rowP.symm i)
    col_injective := fun j => (M1.col_injective j).comp rowP.symm.injective }
  have hIM2 : Isotopic M1 M2 := ⟨rowP.symm, Equiv.refl _, Equiv.refl _, fun _ _ => rfl⟩
  have hr10 : r1Table k 0 = 1 := by fin_cases k <;> decide
  have hM2_red : IsReducedWith (r1Table k) M2 := by
    rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hcases
    rcases hcases with ⟨hc0, hc1⟩ | ⟨hc0, hc1⟩
    · have hM10 : ∀ j, M1.mat 0 j = j := fun j => by
        apply Fin.ext
        change getAt smap (M.mat 0 (giFn j)).val = j.val
        rw [hred.1]
        exact beq_iff_eq.mp (List.all_eq_true.mp hc0 j.val (List.mem_range.mpr j.isLt))
      have hM11 : ∀ j, M1.mat 1 j = r1Table k j := fun j => by
        apply Fin.ext
        change getAt smap (M.mat 1 (giFn j)).val = (r1Table k j).val
        rw [hred.2.2, ← hr1 (giFn j), ← hr1 j]
        exact beq_iff_eq.mp (List.all_eq_true.mp hc1 j.val (List.mem_range.mpr j.isLt))
      have hrp0 : rowP 0 = 0 := hM10 0
      have hrp1 : rowP 1 = 1 := (hM11 0).trans hr10
      refine ⟨fun j => ?_, fun i => rowP.apply_symm_apply i, fun j => ?_⟩
      · change M1.mat (rowP.symm 0) j = j
        rw [show rowP.symm 0 = 0 from rowP.symm_apply_eq.mpr hrp0.symm]
        exact hM10 j
      · change M1.mat (rowP.symm 1) j = r1Table k j
        rw [show rowP.symm 1 = 1 from rowP.symm_apply_eq.mpr hrp1.symm]
        exact hM11 j
    · have hM11 : ∀ j, M1.mat 1 j = j := fun j => by
        apply Fin.ext
        change getAt smap (M.mat 1 (giFn j)).val = j.val
        rw [hred.2.2, ← hr1 (giFn j)]
        exact beq_iff_eq.mp (List.all_eq_true.mp hc0 j.val (List.mem_range.mpr j.isLt))
      have hM10 : ∀ j, M1.mat 0 j = r1Table k j := fun j => by
        apply Fin.ext
        change getAt smap (M.mat 0 (giFn j)).val = (r1Table k j).val
        rw [hred.1, ← hr1 j]
        exact beq_iff_eq.mp (List.all_eq_true.mp hc1 j.val (List.mem_range.mpr j.isLt))
      have hrp1 : rowP 1 = 0 := hM11 0
      have hrp0 : rowP 0 = 1 := (hM10 0).trans hr10
      refine ⟨fun j => ?_, fun i => rowP.apply_symm_apply i, fun j => ?_⟩
      · change M1.mat (rowP.symm 0) j = j
        rw [show rowP.symm 0 = 1 from rowP.symm_apply_eq.mpr hrp1.symm]
        exact hM11 j
      · change M1.mat (rowP.symm 1) j = r1Table k j
        rw [show rowP.symm 1 = 0 from rowP.symm_apply_eq.mpr hrp0.symm]
        exact hM10 j
  refine ⟨M2, rowP, hM2_red, isotopic_trans hIM1 hIM2, ?_, ?_⟩
  · intro i j
    change (M1.mat (rowP.symm (rowP i)) j).val = _
    rw [rowP.symm_apply_apply]
    rfl
  · intro src r hsrc
    apply Fin.ext
    have hgi0 : giFn 0 = ⟨getAt gi 0, checkPerm7_lt hgiP (by decide)⟩ := rfl
    change getAt smap (M.mat src (giFn 0)).val = r.val
    rw [hgi0, hsrc]
    exact beq_iff_eq.mp (List.all_eq_true.mp hinv r.val (List.mem_range.mpr r.isLt))

def mapMask (smap : List Nat) (m : Nat) : Nat :=
  let b0 := match Nat.beq (Nat.land m 1) 0 with | true => 0 | false => Nat.shiftLeft 1 (getAt smap 0)
  let b1 := match Nat.beq (Nat.land m 2) 0 with | true => 0 | false => Nat.shiftLeft 1 (getAt smap 1)
  let b2 := match Nat.beq (Nat.land m 4) 0 with | true => 0 | false => Nat.shiftLeft 1 (getAt smap 2)
  let b3 := match Nat.beq (Nat.land m 8) 0 with | true => 0 | false => Nat.shiftLeft 1 (getAt smap 3)
  let b4 := match Nat.beq (Nat.land m 16) 0 with | true => 0 | false => Nat.shiftLeft 1 (getAt smap 4)
  let b5 := match Nat.beq (Nat.land m 32) 0 with | true => 0 | false => Nat.shiftLeft 1 (getAt smap 5)
  let b6 := match Nat.beq (Nat.land m 64) 0 with | true => 0 | false => Nat.shiftLeft 1 (getAt smap 6)
  Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor b0 b1) b2) b3) b4) b5) b6

private lemma mapMask_single (smap : List Nat) (x : Fin 7) :
    mapMask smap (Nat.shiftLeft 1 x.val) = Nat.shiftLeft 1 (getAt smap x.val) := by
  fin_cases x <;> simp [mapMask]

private lemma lt_of_pow2_lt {a b : Nat} (h : Nat.shiftLeft 1 a < Nat.shiftLeft 1 b) : a < b := by
  change 1 <<< a < 1 <<< b at h
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, one_mul] at h
  by_contra hge
  have hle : b ≤ a := by omega
  have := Nat.pow_le_pow_right (by omega : 0 < 2) hle
  omega

private lemma eq_of_pow2_eq {a b : Nat} (h : Nat.shiftLeft 1 a = Nat.shiftLeft 1 b) : a = b := by
  change 1 <<< a = 1 <<< b at h
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, one_mul, one_mul] at h
  exact Nat.pow_right_injective (by omega) h

/- ### Part 4: Streaming 6-bit certificate runner and soundness -/

inductive BitStream where
  | mk (cur rem : Nat) (chunks : List Nat)

def BitStream.next : BitStream → Option (Nat × BitStream)
  | .mk cur rem chunks =>
    match rem with
    | 0 =>
      match chunks with
      | [] => none
      | w :: ws => some (Nat.land w 63, .mk (Nat.shiftRight w 6) 63 ws)
    | r + 1 =>
      some (Nat.land cur 63, .mk (Nat.shiftRight cur 6) r chunks)

def read7 (st : BitStream) (c6 : Nat) : Option ((Nat × Nat × Nat × Nat × Nat × Nat × Nat) × BitStream) :=
  match st.next with
  | none => none
  | some (t0, st1) =>
    match st1.next with
    | none => none
    | some (t1, st2) =>
      match st2.next with
      | none => none
      | some (t2, st3) =>
        some ((Nat.land t0 7, Nat.shiftRight t0 3,
               Nat.land t1 7, Nat.shiftRight t1 3,
               Nat.land t2 7, Nat.shiftRight t2 3, c6), st3)

def colAt (cs : Nat × Nat × Nat × Nat × Nat × Nat × Nat) : Nat → Nat
  | 0 => cs.1
  | 1 => cs.2.1
  | 2 => cs.2.2.1
  | 3 => cs.2.2.2.1
  | 4 => cs.2.2.2.2.1
  | 5 => cs.2.2.2.2.2.1
  | _ => cs.2.2.2.2.2.2

def checkColsPerm (cs : Nat × Nat × Nat × Nat × Nat × Nat × Nat) : Bool :=
  let c0 := cs.1; let c1 := cs.2.1; let c2 := cs.2.2.1; let c3 := cs.2.2.2.1
  let c4 := cs.2.2.2.2.1; let c5 := cs.2.2.2.2.2.1; let c6 := cs.2.2.2.2.2.2
  Nat.blt c0 7 && Nat.blt c1 7 && Nat.blt c2 7 && Nat.blt c3 7 &&
  Nat.blt c4 7 && Nat.blt c5 7 && Nat.blt c6 7 &&
  Nat.beq (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor
    (Nat.shiftLeft 1 c0) (Nat.shiftLeft 1 c1)) (Nat.shiftLeft 1 c2))
    (Nat.shiftLeft 1 c3)) (Nat.shiftLeft 1 c4)) (Nat.shiftLeft 1 c5))
    (Nat.shiftLeft 1 c6)) 127

private lemma surj_of_or7_127 {f : Fin 7 → Fin 7}
    (h : Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor
      (Nat.shiftLeft 1 (f 0).val) (Nat.shiftLeft 1 (f 1).val)) (Nat.shiftLeft 1 (f 2).val))
      (Nat.shiftLeft 1 (f 3).val)) (Nat.shiftLeft 1 (f 4).val)) (Nat.shiftLeft 1 (f 5).val))
      (Nat.shiftLeft 1 (f 6).val) = 127) :
    Function.Injective f := by
  have hsurj : Function.Surjective f := by
    intro y
    have hbit : (127 : Nat).testBit y.val = true := by
      have : (127 : Nat) = 2 ^ 7 - 1 := rfl
      rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true y.isLt
    rw [← h] at hbit
    have tsl : ∀ a : Fin 7, (Nat.shiftLeft 1 a.val).testBit y.val = decide (a = y) := by
      intro a
      change (1 <<< a.val).testBit y.val = _
      rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
      by_cases ha : a = y
      · subst ha; simp
      · have hne : a.val ≠ y.val := fun he => ha (Fin.ext he)
        simp [ha, hne]
    change ((((((Nat.shiftLeft 1 (f 0).val ||| Nat.shiftLeft 1 (f 1).val) ||| Nat.shiftLeft 1 (f 2).val) |||
      Nat.shiftLeft 1 (f 3).val) ||| Nat.shiftLeft 1 (f 4).val) ||| Nat.shiftLeft 1 (f 5).val) |||
      Nat.shiftLeft 1 (f 6).val).testBit y.val = true at hbit
    simp only [Nat.testBit_or, tsl, Bool.or_eq_true, decide_eq_true_eq] at hbit
    rcases hbit with (((((h0 | h1) | h2) | h3) | h4) | h5) | h6
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨2, h2⟩
    · exact ⟨3, h3⟩
    · exact ⟨4, h4⟩
    · exact ⟨5, h5⟩
    · exact ⟨6, h6⟩
  exact (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hsurj, rfl⟩ |>.1

private lemma checkColsPerm_fn {cs : Nat × Nat × Nat × Nat × Nat × Nat × Nat}
    (h : checkColsPerm cs = true) :
    (∀ i : Fin 7, colAt cs i.val < 7) ∧
    Function.Injective (fun i : Fin 7 => (⟨colAt cs i.val, by
      unfold checkColsPerm at h
      simp only [Bool.and_eq_true, Nat.blt_eq] at h
      fin_cases i <;> simp [colAt] <;> omega⟩ : Fin 7)) := by
  unfold checkColsPerm at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  have hlt : ∀ i : Fin 7, colAt cs i.val < 7 := by
    intro i; fin_cases i <;> simp [colAt] <;> omega
  refine ⟨hlt, ?_⟩
  apply surj_of_or7_127
  exact Nat.eq_of_beq_eq_true h.2

def checkWitness (B : Nat) (cs : Nat × Nat × Nat × Nat × Nat × Nat × Nat) : Bool :=
  checkColsPerm cs &&
  let d0 := dom B 0 cs.1
  let d1 := dom B 1 cs.2.1
  let d2 := dom B 2 cs.2.2.1
  let d3 := dom B 3 cs.2.2.2.1
  let d4 := dom B 4 cs.2.2.2.2.1
  let d5 := dom B 5 cs.2.2.2.2.2.1
  let d6 := dom B 6 cs.2.2.2.2.2.2
  isSingle d0 && isSingle d1 && isSingle d2 && isSingle d3 &&
  isSingle d4 && isSingle d5 && isSingle d6 &&
  Nat.beq (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor (Nat.lor d0 d1) d2) d3) d4) d5) d6) 127

private lemma checkWitness_sound {L : LatinSquare 7} {B : Nat} (hB : ValidBoard L B)
    {cs : Nat × Nat × Nat × Nat × Nat × Nat × Nat} (hw : checkWitness B cs = true) :
    ∃ σ, IsTransversal L σ := by
  unfold checkWitness at hw
  dsimp only at hw
  simp only [Bool.and_eq_true] at hw
  rcases hw with ⟨hperm, ⟨⟨⟨⟨⟨⟨hs0, hs1⟩, hs2⟩, hs3⟩, hs4⟩, hs5⟩, hs6⟩, hor⟩
  have ⟨hlt, hinj⟩ := checkColsPerm_fn hperm
  let σ : Fin 7 → Fin 7 := fun i => ⟨colAt cs i.val, hlt i⟩
  refine ⟨σ, hinj, ?_⟩
  apply surj_of_or7_127
  have hd0 : dom B 0 cs.1 = Nat.shiftLeft 1 (L.mat 0 (σ 0)).val := dom_eq_bit_of_isSingle hB 0 (σ 0) hs0
  have hd1 : dom B 1 cs.2.1 = Nat.shiftLeft 1 (L.mat 1 (σ 1)).val := dom_eq_bit_of_isSingle hB 1 (σ 1) hs1
  have hd2 : dom B 2 cs.2.2.1 = Nat.shiftLeft 1 (L.mat 2 (σ 2)).val := dom_eq_bit_of_isSingle hB 2 (σ 2) hs2
  have hd3 : dom B 3 cs.2.2.2.1 = Nat.shiftLeft 1 (L.mat 3 (σ 3)).val := dom_eq_bit_of_isSingle hB 3 (σ 3) hs3
  have hd4 : dom B 4 cs.2.2.2.2.1 = Nat.shiftLeft 1 (L.mat 4 (σ 4)).val := dom_eq_bit_of_isSingle hB 4 (σ 4) hs4
  have hd5 : dom B 5 cs.2.2.2.2.2.1 = Nat.shiftLeft 1 (L.mat 5 (σ 5)).val := dom_eq_bit_of_isSingle hB 5 (σ 5) hs5
  have hd6 : dom B 6 cs.2.2.2.2.2.2 = Nat.shiftLeft 1 (L.mat 6 (σ 6)).val := dom_eq_bit_of_isSingle hB 6 (σ 6) hs6
  have heq := Nat.eq_of_beq_eq_true hor
  rw [hd0, hd1, hd2, hd3, hd4, hd5, hd6] at heq
  exact heq

def forbidAcc (B skipR : Nat) (cs : Nat × Nat × Nat × Nat × Nat × Nat × Nat) :
    Nat → Nat → Option Nat
  | 0, acc => some acc
  | k + 1, acc =>
    match Nat.beq k skipR with
    | true => forbidAcc B skipR cs k acc
    | false =>
      let d := dom B k (colAt cs k)
      match isSingle d with
      | false => none
      | true => forbidAcc B skipR cs k (Nat.lor acc d)

def applyForbid (B skipR : Nat) (cs : Nat × Nat × Nat × Nat × Nat × Nat × Nat) : Option Nat :=
  match Nat.blt skipR 7 && checkColsPerm cs with
  | false => none
  | true =>
    match forbidAcc B skipR cs 7 0 with
    | none => none
    | some s =>
      let msBit := Nat.xor 127 s
      match isSingle msBit with
      | false => none
      | true => some (forbidMask B skipR (colAt cs skipR) msBit)

private lemma lor_lt_128 {x y : Nat} (hx : x < 128) (hy : y < 128) : Nat.lor x y < 128 := by
  change x ||| y < 2 ^ 7
  exact Nat.or_lt_two_pow hx hy

private lemma xor127_lt_128 {x : Nat} (hx : x < 128) : Nat.xor 127 x < 128 := by
  change 127 ^^^ x < 2 ^ 7
  exact Nat.xor_lt_two_pow (by norm_num) hx

private lemma forbidAcc_sound {L : LatinSquare 7} {B skipR : Nat} (hB : ValidBoard L B)
    {cs : Nat × Nat × Nat × Nat × Nat × Nat × Nat} (hlt : ∀ i : Fin 7, colAt cs i.val < 7) :
    ∀ (k acc out : Nat), k ≤ 7 → acc < 128 →
      (∀ v : Fin 7, acc.testBit v.val = true → ∃ i : Fin 7, i.val ≠ skipR ∧ L.mat i ⟨colAt cs i.val, hlt i⟩ = v) →
      forbidAcc B skipR cs k acc = some out →
      out < 128 ∧
      (∀ v : Fin 7, out.testBit v.val = true → ∃ i : Fin 7, i.val ≠ skipR ∧ L.mat i ⟨colAt cs i.val, hlt i⟩ = v)
  | 0, acc, out, _, hltA, hcov, hf => by
    simp only [forbidAcc, Option.some.injEq] at hf
    subst hf; exact ⟨hltA, hcov⟩
  | k + 1, acc, out, hk, hltA, hcov, hf => by
    unfold forbidAcc at hf
    cases hb : Nat.beq k skipR with
    | true =>
      rw [hb] at hf
      exact forbidAcc_sound hB hlt k acc out (by omega) hltA hcov hf
    | false =>
      rw [hb] at hf; dsimp only at hf
      cases hs : isSingle (dom B k (colAt cs k)) with
      | false => rw [hs] at hf; cases hf
      | true =>
        rw [hs] at hf
        have hk7 : k < 7 := by omega
        let kf : Fin 7 := ⟨k, hk7⟩
        have hd := dom_eq_bit_of_isSingle hB kf ⟨colAt cs k, hlt kf⟩ hs
        have hltD : dom B k (colAt cs k) < 128 := dom_lt_128 B k (colAt cs k)
        refine forbidAcc_sound hB hlt k (Nat.lor acc (dom B k (colAt cs k))) out (by omega)
          (lor_lt_128 hltA hltD) ?_ hf
        intro v hv
        change (acc ||| dom B k (colAt cs k)).testBit v.val = true at hv
        rw [Nat.testBit_or, Bool.or_eq_true] at hv
        rcases hv with h1 | h2
        · exact hcov v h1
        · rw [hd] at h2
          change (1 <<< (L.mat kf ⟨colAt cs k, hlt kf⟩).val).testBit v.val = true at h2
          rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, decide_eq_true_eq] at h2
          exact ⟨kf, Nat.ne_of_beq_eq_false hb, Fin.ext h2⟩

private lemma applyForbid_sound {L : LatinSquare 7} {B B' skipR : Nat}
    (hB : ValidBoard L B) (hNo : ¬ ∃ σ, IsTransversal L σ)
    {cs : Nat × Nat × Nat × Nat × Nat × Nat × Nat}
    (hf : applyForbid B skipR cs = some B') :
    ValidBoard L B' := by
  unfold applyForbid at hf
  cases hpc : (Nat.blt skipR 7 && checkColsPerm cs) with
  | false => rw [hpc] at hf; cases hf
  | true =>
    rw [hpc] at hf; dsimp only at hf
    rw [Bool.and_eq_true, Nat.blt_eq] at hpc
    rcases hpc with ⟨hskipLt, hperm⟩
    have ⟨hlt, hinj⟩ := checkColsPerm_fn hperm
    let σ : Fin 7 → Fin 7 := fun i => ⟨colAt cs i.val, hlt i⟩
    cases hacc : forbidAcc B skipR cs 7 0 with
    | none => rw [hacc] at hf; cases hf
    | some s =>
      rw [hacc] at hf; dsimp only at hf
      cases hms : isSingle (Nat.xor 127 s) with
      | false => rw [hms] at hf; cases hf
      | true =>
        rw [hms] at hf; injection hf with hB'; subst hB'
        have ⟨hs_lt, hcov⟩ := forbidAcc_sound hB hlt 7 0 s le_rfl (by omega)
          (fun _ hv => by simp at hv) hacc
        obtain ⟨ms, hmsEq⟩ := isSingle_eq_bit (xor127_lt_128 hs_lt) hms
        rw [hmsEq]
        let skipFin : Fin 7 := ⟨skipR, hskipLt⟩
        have hne : L.mat skipFin (σ skipFin) ≠ ms := by
          intro heq
          apply hNo
          refine ⟨σ, hinj, ?_⟩
          have hsurj : Function.Surjective (fun i => L.mat i (σ i)) := by
            intro y
            by_cases hy : y = ms
            · subst hy; exact ⟨skipFin, heq⟩
            · have h127 : (127 : Nat).testBit y.val = true := by
                have : (127 : Nat) = 2 ^ 7 - 1 := rfl
                rw [this, Nat.testBit_two_pow_sub_one]; exact decide_eq_true y.isLt
              have hxor : (Nat.xor 127 s).testBit y.val = false := by
                rw [hmsEq]
                change (1 <<< ms.val).testBit y.val = false
                rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, decide_eq_false_iff_not]
                intro hval; exact hy (Fin.ext hval.symm)
              have hsbit : s.testBit y.val = true := by
                change (127 ^^^ s).testBit y.val = false at hxor
                rw [Nat.testBit_xor, h127] at hxor
                cases hsy : s.testBit y.val
                · rw [hsy] at hxor; cases hxor
                · rfl
              obtain ⟨i, _, hi⟩ := hcov y hsbit
              exact ⟨i, hi⟩
          exact (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, rfl⟩ |>.1
        have hfv := forbidMask_valid hB hne
        convert hfv using 2

def checkSymColsEq (B : Nat) (gi smap : List Nat) (r srcR c rem : Nat) : Bool :=
  match rem with
  | 0 => true
  | k + 1 =>
    let dA := dom B r c
    let dB := dom B srcR (getAt gi c)
    if isSingle dA && isSingle dB && Nat.beq (mapMask smap dB) dA then
      checkSymColsEq B gi smap r srcR (c + 1) k
    else false

private lemma checkSymColsEq_sound {L M2 : LatinSquare 7} {rowP : Equiv.Perm (Fin 7)}
    {B : Nat} (hB : ValidBoard L B)
    {gi smap : List Nat}
    (hgiLt : ∀ j : Fin 7, getAt gi j.val < 7)
    (hM2 : ∀ (i j : Fin 7), (M2.mat (rowP i) j).val = getAt smap (L.mat i ⟨getAt gi j.val, hgiLt j⟩).val)
    {r srcR : Fin 7} (hrow : rowP srcR = r) :
    ∀ (rem c : Nat), c + rem ≤ 7 →
      checkSymColsEq B gi smap r.val srcR.val c rem = true →
      ∀ j : Fin 7, c ≤ j.val → j.val < c + rem → M2.mat r j = L.mat r j
  | 0, c, _, _, j, h1, h2 => by omega
  | k + 1, c, hle, hchk, j, h1, h2 => by
    unfold checkSymColsEq at hchk
    dsimp only at hchk
    split at hchk
    · rename_i hcond
      simp only [Bool.and_eq_true] at hcond
      rcases hcond with ⟨⟨hsA, hsB⟩, hmap⟩
      by_cases hj : j.val = c
      · have hcf : c < 7 := by omega
        have hjEq : j = ⟨c, hcf⟩ := Fin.ext hj
        subst hjEq
        have hdA := dom_eq_bit_of_isSingle hB r ⟨c, hcf⟩ hsA
        have hdB := dom_eq_bit_of_isSingle hB srcR ⟨getAt gi c, hgiLt ⟨c, hcf⟩⟩ hsB
        have heq := Nat.eq_of_beq_eq_true hmap
        rw [hdB, mapMask_single, hdA] at heq
        have hval := eq_of_pow2_eq heq
        apply Fin.ext
        calc (M2.mat r ⟨c, hcf⟩).val
            = (M2.mat (rowP srcR) ⟨c, hcf⟩).val := by rw [hrow]
          _ = getAt smap (L.mat srcR ⟨getAt gi c, hgiLt ⟨c, hcf⟩⟩).val := hM2 srcR ⟨c, hcf⟩
          _ = (L.mat r ⟨c, hcf⟩).val := hval
      · exact checkSymColsEq_sound hB hgiLt hM2 hrow k (c + 1) (by omega) hchk j (by omega) (by omega)
    · cases hchk

def checkSymRows (B : Nat) (gi smap smapInv : List Nat) (diffRow diffCol r rem : Nat)
    (st : BitStream) : Option BitStream :=
  match rem with
  | 0 => none
  | k + 1 =>
    match st.next with
    | none => none
    | some (srcR, st1) =>
      if Nat.blt srcR 7 && Nat.beq (dom B srcR (getAt gi 0)) (Nat.shiftLeft 1 (getAt smapInv r)) then
        match Nat.beq r diffRow with
        | true =>
          if checkSymColsEq B gi smap r srcR 1 (diffCol - 1) then
            let dA := dom B r diffCol
            let dB := dom B srcR (getAt gi diffCol)
            if isSingle dA && isSingle dB && Nat.blt (mapMask smap dB) dA then
              some st1
            else none
          else none
        | false =>
          if checkSymColsEq B gi smap r srcR 1 6 then
            checkSymRows B gi smap smapInv diffRow diffCol (r + 1) k st1
          else none
      else none

private lemma checkSymRows_sound {L M2 : LatinSquare 7} {rowP : Equiv.Perm (Fin 7)}
    {B : Nat} (hB : ValidBoard L B)
    {gi smap smapInv : List Nat}
    (hgiLt : ∀ j : Fin 7, getAt gi j.val < 7)
    (hM2 : ∀ (i j : Fin 7), (M2.mat (rowP i) j).val = getAt smap (L.mat i ⟨getAt gi j.val, hgiLt j⟩).val)
    (hsrcRow : ∀ (src r : Fin 7), (L.mat src ⟨getAt gi 0, hgiLt 0⟩).val = getAt smapInv r.val → rowP src = r)
    (hsmapInvLt : ∀ r : Fin 7, getAt smapInv r.val < 7)
    {diffRow diffCol : Fin 7} (hdc1 : 1 ≤ diffCol.val) :
    ∀ (rem r : Nat) (st st' : BitStream),
      2 ≤ r → r ≤ diffRow.val →
      checkSymRows B gi smap smapInv diffRow.val diffCol.val r rem st = some st' →
      (∀ (r' c' : Fin 7), r ≤ r'.val → 1 ≤ c'.val →
        (r'.val < diffRow.val ∨ (r' = diffRow ∧ c'.val < diffCol.val)) →
        M2.mat r' c' = L.mat r' c') ∧
      (M2.mat diffRow diffCol).val < (L.mat diffRow diffCol).val
  | 0, _, _, _, _, _, h => by simp [checkSymRows] at h
  | k + 1, r, st, st', hr2, hrle, h => by
    unfold checkSymRows at h
    cases hnx : st.next with
    | none => rw [hnx] at h; cases h
    | some p =>
      rcases p with ⟨srcR, st1⟩
      rw [hnx] at h; dsimp only at h
      split at h
      · rename_i hsrcCond
        rw [Bool.and_eq_true, Nat.blt_eq] at hsrcCond
        rcases hsrcCond with ⟨hsrcLt, hdomEq⟩
        have hr7 : r < 7 := lt_of_le_of_lt hrle diffRow.isLt
        let rFin : Fin 7 := ⟨r, hr7⟩
        let srcFin : Fin 7 := ⟨srcR, hsrcLt⟩
        have hLsrc : L.mat srcFin ⟨getAt gi 0, hgiLt 0⟩ = ⟨getAt smapInv r, hsmapInvLt rFin⟩ :=
          eq_of_dom_eq_bit hB (Nat.eq_of_beq_eq_true hdomEq)
        have hrow : rowP srcFin = rFin := hsrcRow srcFin rFin (congrArg Fin.val hLsrc)
        cases hreq : Nat.beq r diffRow.val with
        | true =>
          rw [hreq] at h; dsimp only at h
          have hrEq : rFin = diffRow := Fin.ext (Nat.eq_of_beq_eq_true hreq)
          subst hrEq
          split at h
          · rename_i hcols
            split at h
            · rename_i hdiff
              simp only [Bool.and_eq_true, Nat.blt_eq] at hdiff
              rcases hdiff with ⟨⟨hsA, hsB⟩, hlt⟩
              have hdA := dom_eq_bit_of_isSingle hB rFin diffCol hsA
              have hdB := dom_eq_bit_of_isSingle hB srcFin ⟨getAt gi diffCol.val, hgiLt diffCol⟩ hsB
              rw [hdB, mapMask_single, hdA] at hlt
              have hvalLt : getAt smap (L.mat srcFin ⟨getAt gi diffCol.val, hgiLt diffCol⟩).val < (L.mat rFin diffCol).val :=
                lt_of_pow2_lt hlt
              have hM2lt : (M2.mat rFin diffCol).val < (L.mat rFin diffCol).val := by
                calc (M2.mat rFin diffCol).val
                    = (M2.mat (rowP srcFin) diffCol).val := by rw [hrow]
                  _ = getAt smap (L.mat srcFin ⟨getAt gi diffCol.val, hgiLt diffCol⟩).val := hM2 srcFin diffCol
                  _ < (L.mat rFin diffCol).val := hvalLt
              refine ⟨?_, hM2lt⟩
              intro r' c' hr'ge hc'1 hbefore
              have hrFinV : rFin.val = r := rfl
              rcases hbefore with hltR | ⟨rfl, hltC⟩
              · omega
              · exact checkSymColsEq_sound hB hgiLt hM2 hrow (diffCol.val - 1) 1 (by omega) hcols c' hc'1 (by omega)
            · cases h
          · cases h
        | false =>
          rw [hreq] at h; dsimp only at h
          have hrlt : r < diffRow.val := by
            have := Nat.ne_of_beq_eq_false hreq; omega
          split at h
          · rename_i hcols
            have ⟨hrest, hlt⟩ := checkSymRows_sound hB hgiLt hM2 hsrcRow hsmapInvLt hdc1
              k (r + 1) st1 st' (by omega) (by omega) h
            refine ⟨?_, hlt⟩
            intro r' c' hr'ge hc'1 hbefore
            by_cases hrr' : r'.val = r
            · have hr'Eq : r' = rFin := Fin.ext hrr'
              subst hr'Eq
              exact checkSymColsEq_sound hB hgiLt hM2 hrow 6 1 (by omega) hcols c' hc'1 (by have := c'.isLt; omega)
            · exact hrest r' c' (by omega) hc'1 hbefore
          · cases h
      · cases h

def checkSymNode (syms : List (List Nat × List Nat × List Nat)) (B diffRow : Nat)
    (st : BitStream) : Option BitStream :=
  if Nat.ble 2 diffRow && Nat.blt diffRow 7 then
    match st.next with
    | none => none
    | some (tIdx, st1) =>
      match st1.next with
      | none => none
      | some (diffCol, st2) =>
        if Nat.blt tIdx syms.length && Nat.ble 1 diffCol && Nat.blt diffCol 7 then
          let (gi, smap, smapInv) := syms.getD tIdx ([], [], [])
          checkSymRows B gi smap smapInv diffRow diffCol 2 6 st2
        else none
  else none

private lemma checkSymNode_sound {k : Fin 4} {M : LatinSquare 7} {B : Nat}
    (hred : IsReducedWith (r1Table k) M)
    (hMin : ∀ M', IsReducedWith (r1Table k) M' → Isotopic M M' →
      lexKeyAux M cellOrder ≤ lexKeyAux M' cellOrder)
    (hB : ValidBoard M B)
    {r1 : List Nat} (hr1 : ∀ j : Fin 7, getAt r1 j.val = (r1Table k j).val)
    {syms : List (List Nat × List Nat × List Nat)}
    (hSyms : syms.all (fun t => checkSym r1 t.1 t.2.1 t.2.2) = true)
    {diffRow : Nat} {st st' : BitStream}
    (hchk : checkSymNode syms B diffRow st = some st') : False := by
  unfold checkSymNode at hchk
  split at hchk
  · rename_i hdr
    rw [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hdr
    cases h1 : st.next with
    | none => rw [h1] at hchk; cases hchk
    | some p1 =>
      rcases p1 with ⟨tIdx, st1⟩
      rw [h1] at hchk; dsimp only at hchk
      cases h2 : st1.next with
      | none => rw [h2] at hchk; cases hchk
      | some p2 =>
        rcases p2 with ⟨diffCol, st2⟩
        rw [h2] at hchk; dsimp only at hchk
        split at hchk
        · rename_i hcond
          simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hcond
          rcases hcond with ⟨⟨htLt, hdc1⟩, hdc7⟩
          have htMem : syms.getD tIdx ([], [], []) ∈ syms := by
            simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htLt, Option.getD_some]
            exact List.getElem_mem htLt
          have hsymT : checkSym r1 (syms.getD tIdx ([], [], [])).1
              (syms.getD tIdx ([], [], [])).2.1 (syms.getD tIdx ([], [], [])).2.2 = true :=
            List.all_eq_true.mp hSyms _ htMem
          obtain ⟨M2, rowP, hM2red, hM2iso, hM2mat, hsrcRow⟩ := symTransform_exists hred hr1 hsymT
          have hgiLt : ∀ j : Fin 7, getAt (syms.getD tIdx ([], [], [])).1 j.val < 7 := by
            intro j
            unfold checkSym at hsymT; simp only [Bool.and_eq_true] at hsymT
            exact checkPerm7_lt hsymT.1.1.1.1 j.isLt
          have hsmapInvLt : ∀ r : Fin 7, getAt (syms.getD tIdx ([], [], [])).2.2 r.val < 7 := by
            intro r
            unfold checkSym at hsymT; simp only [Bool.and_eq_true] at hsymT
            exact checkPerm7_lt hsymT.1.1.2 r.isLt
          let drFin : Fin 7 := ⟨diffRow, hdr.2⟩
          let dcFin : Fin 7 := ⟨diffCol, hdc7⟩
          have ⟨hpre, hlt⟩ := checkSymRows_sound hB hgiLt hM2mat hsrcRow hsmapInvLt (diffRow := drFin) (diffCol := dcFin) hdc1
            6 2 st2 st' le_rfl hdr.1 hchk
          have hlexLt : lexKeyAux M2 cellOrder < lexKeyAux M cellOrder :=
            lexKeyAux_lt_of_first_diff cellOrder drFin dcFin (mem_cellOrder hdr.1 hdc1)
              (fun r' c' hm hbef => hpre r' c' (mem_cellOrder_bounds hm).1 (mem_cellOrder_bounds hm).2 hbef)
              cellOrder_pairwise hlt
          have hle := hMin M2 hM2red hM2iso
          omega
        · cases hchk
  · cases hchk

def runBranch (step : Nat → BitStream → Option BitStream)
    (B r c m v : Nat) : Nat → BitStream → Option BitStream
  | 0, st => some st
  | rem + 1, st =>
    match Nat.beq (Nat.land m (Nat.shiftLeft 1 v)) 0 with
    | true => runBranch step B r c m (v + 1) rem st
    | false =>
      match step (clearCell B r c v) st with
      | none => none
      | some st1 => runBranch step B r c m (v + 1) rem st1

def runNode (syms : List (List Nat × List Nat × List Nat)) :
    Nat → Nat → BitStream → Option BitStream
  | 0, _, _ => none
  | f + 1, B, st =>
    match st.next with
    | none => none
    | some (hdr, st1) =>
      let op := Nat.land hdr 7
      let arg := Nat.shiftRight hdr 3
      match op with
      | 0 => -- CONTRA: arg = r, next = c
        match st1.next with
        | none => none
        | some (c, st2) =>
          if Nat.blt arg 7 && Nat.blt c 7 && Nat.beq (dom B arg c) 0 then some st2 else none
      | 1 => -- FIX: arg = v, next = rc
        match st1.next with
        | none => none
        | some (rc, st2) =>
          let r := Nat.land rc 7
          let c := Nat.shiftRight rc 3
          if Nat.blt r 7 && Nat.blt c 7 && Nat.blt arg 7 &&
              Nat.beq (dom B r c) (Nat.shiftLeft 1 arg) then
            runNode syms f (clearCell B r c arg) st2
          else none
      | 2 => -- HROW: arg = v, next = rc
        match st1.next with
        | none => none
        | some (rc, st2) =>
          let r := Nat.land rc 7
          let c := Nat.shiftRight rc 3
          if Nat.blt r 7 && Nat.blt c 7 && Nat.blt arg 7 &&
              Nat.beq (Nat.land B (rowOther r c arg)) 0 then
            runNode syms f (clearCell B r c arg) st2
          else none
      | 3 => -- HCOL: arg = v, next = rc
        match st1.next with
        | none => none
        | some (rc, st2) =>
          let r := Nat.land rc 7
          let c := Nat.shiftRight rc 3
          if Nat.blt r 7 && Nat.blt c 7 && Nat.blt arg 7 &&
              Nat.beq (Nat.land B (colOther r c arg)) 0 then
            runNode syms f (clearCell B r c arg) st2
          else none
      | 4 => -- FORBID: arg = skipR, next = t0, t1, t2, t3 (c6 = t3 &&& 7)
        match st1.next with
        | none => none
        | some (t0, st2) =>
          match st2.next with
          | none => none
          | some (t1, st3) =>
            match st3.next with
            | none => none
            | some (t2, st4) =>
              match st4.next with
              | none => none
              | some (t3, st5) =>
                let cs := (Nat.land t0 7, Nat.shiftRight t0 3,
                           Nat.land t1 7, Nat.shiftRight t1 3,
                           Nat.land t2 7, Nat.shiftRight t2 3, Nat.land t3 7)
                match applyForbid B arg cs with
                | none => none
                | some B' => runNode syms f B' st5
      | 5 => -- WITNESS: arg = c6, next = t0, t1, t2
        match read7 st1 arg with
        | none => none
        | some (cs, st2) =>
          if checkWitness B cs then some st2 else none
      | 6 => -- SYM: arg = diffRow
        checkSymNode syms B arg st1
      | _ => -- BRANCH (op = 7): next = rc
        match st1.next with
        | none => none
        | some (rc, st2) =>
          let r := Nat.land rc 7
          let c := Nat.shiftRight rc 3
          if Nat.blt r 7 && Nat.blt c 7 then
            runBranch (runNode syms f) B r c (dom B r c) 0 7 st2
          else none

private lemma runBranch_sound {M : LatinSquare 7}
    {step : Nat → BitStream → Option BitStream}
    (ih : ∀ B st st', ValidBoard M B → step B st = some st' → False)
    {B : Nat} (hB : ValidBoard M B) (r c : Fin 7) :
    ∀ (rem v : Nat) (st st' : BitStream),
      v ≤ (M.mat r c).val → (M.mat r c).val < v + rem →
      runBranch step B r.val c.val (dom B r.val c.val) v rem st = some st' → False
  | 0, _, _, _, h1, h2, _ => by omega
  | rem + 1, v, st, st', h1, h2, h => by
    unfold runBranch at h
    cases hb : Nat.beq (Nat.land (dom B r.val c.val) (Nat.shiftLeft 1 v)) 0 with
    | true =>
      rw [hb] at h
      have hne : v ≠ (M.mat r c).val := by
        intro heq
        subst heq
        have h0 : (dom B r.val c.val &&& Nat.shiftLeft 1 (M.mat r c).val).testBit (M.mat r c).val = false := by
          change (Nat.land (dom B r.val c.val) (Nat.shiftLeft 1 (M.mat r c).val)).testBit _ = false
          rw [Nat.eq_of_beq_eq_true hb]; simp
        rw [Nat.testBit_and, testBit_dom, hB r c] at h0
        change (true && (1 <<< (M.mat r c).val).testBit (M.mat r c).val) = false at h0
        rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow] at h0
        simp at h0
      exact runBranch_sound ih hB r c rem (v + 1) st st' (by omega) (by omega) h
    | false =>
      rw [hb] at h
      cases hn : step (clearCell B r.val c.val v) st with
      | none => rw [hn] at h; cases h
      | some st1 =>
        rw [hn] at h
        by_cases hveq : v = (M.mat r c).val
        · have hv7 : v < 7 := by have := (M.mat r c).isLt; omega
          have heq : M.mat r c = ⟨v, hv7⟩ := Fin.ext hveq.symm
          exact ih (clearCell B r.val c.val v) st st1 (clearCell_valid hB heq) hn
        · exact runBranch_sound ih hB r c rem (v + 1) st1 st' (by omega) (by omega) h

private lemma runNode_sound {k : Fin 4} {M : LatinSquare 7}
    (hred : IsReducedWith (r1Table k) M)
    (hMin : ∀ M', IsReducedWith (r1Table k) M' → Isotopic M M' →
      lexKeyAux M cellOrder ≤ lexKeyAux M' cellOrder)
    (hNo : ¬ ∃ σ, IsTransversal M σ)
    {r1 : List Nat} (hr1 : ∀ j : Fin 7, getAt r1 j.val = (r1Table k j).val)
    {syms : List (List Nat × List Nat × List Nat)}
    (hSyms : syms.all (fun t => checkSym r1 t.1 t.2.1 t.2.2) = true) :
    ∀ (fuel B : Nat) (st st' : BitStream),
      ValidBoard M B → runNode syms fuel B st = some st' → False
  | 0, _, _, _, _, h => by simp [runNode] at h
  | f + 1, B, st, st', hB, h => by
    unfold runNode at h
    cases h1 : st.next with
    | none => rw [h1] at h; cases h
    | some p1 =>
      rcases p1 with ⟨hdr, st1⟩
      rw [h1] at h; dsimp only at h
      set arg := Nat.shiftRight hdr 3
      split at h
      · cases h2 : st1.next with
        | none => rw [h2] at h; cases h
        | some p2 =>
          rcases p2 with ⟨c, st2⟩
          rw [h2] at h; dsimp only at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, Nat.blt_eq] at hc
            rcases hc with ⟨⟨hr7, hc7⟩, hdom0⟩
            have hbit : (dom B arg c).testBit (M.mat ⟨arg, hr7⟩ ⟨c, hc7⟩).val = true :=
              (testBit_dom B ⟨arg, hr7⟩ ⟨c, hc7⟩ (M.mat ⟨arg, hr7⟩ ⟨c, hc7⟩)).trans
                (hB ⟨arg, hr7⟩ ⟨c, hc7⟩)
            rw [Nat.eq_of_beq_eq_true hdom0] at hbit
            simp at hbit
          · cases h
      · cases h2 : st1.next with
        | none => rw [h2] at h; cases h
        | some p2 =>
          rcases p2 with ⟨rc, st2⟩
          rw [h2] at h; dsimp only at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, Nat.blt_eq] at hc
            rcases hc with ⟨⟨⟨hr7, hc7⟩, hv7⟩, hdomEq⟩
            have heq : M.mat ⟨Nat.land rc 7, hr7⟩ ⟨Nat.shiftRight rc 3, hc7⟩ = ⟨arg, hv7⟩ :=
              eq_of_dom_eq_bit hB (Nat.eq_of_beq_eq_true hdomEq)
            exact runNode_sound hred hMin hNo hr1 hSyms f _ st2 st' (clearCell_valid hB heq) h
          · cases h
      · cases h2 : st1.next with
        | none => rw [h2] at h; cases h
        | some p2 =>
          rcases p2 with ⟨rc, st2⟩
          rw [h2] at h; dsimp only at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, Nat.blt_eq] at hc
            rcases hc with ⟨⟨⟨hr7, hc7⟩, hv7⟩, hzero⟩
            have heq : M.mat ⟨Nat.land rc 7, hr7⟩ ⟨Nat.shiftRight rc 3, hc7⟩ = ⟨arg, hv7⟩ :=
              eq_of_rowOther_zero hB (Nat.eq_of_beq_eq_true hzero)
            exact runNode_sound hred hMin hNo hr1 hSyms f _ st2 st' (clearCell_valid hB heq) h
          · cases h
      · cases h2 : st1.next with
        | none => rw [h2] at h; cases h
        | some p2 =>
          rcases p2 with ⟨rc, st2⟩
          rw [h2] at h; dsimp only at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, Nat.blt_eq] at hc
            rcases hc with ⟨⟨⟨hr7, hc7⟩, hv7⟩, hzero⟩
            have heq : M.mat ⟨Nat.land rc 7, hr7⟩ ⟨Nat.shiftRight rc 3, hc7⟩ = ⟨arg, hv7⟩ :=
              eq_of_colOther_zero hB (Nat.eq_of_beq_eq_true hzero)
            exact runNode_sound hred hMin hNo hr1 hSyms f _ st2 st' (clearCell_valid hB heq) h
          · cases h
      · cases h2 : st1.next with
        | none => rw [h2] at h; cases h
        | some p2 =>
          rcases p2 with ⟨t0, st2⟩; rw [h2] at h; dsimp only at h
          cases h3 : st2.next with
          | none => rw [h3] at h; cases h
          | some p3 =>
            rcases p3 with ⟨t1, st3⟩; rw [h3] at h; dsimp only at h
            cases h4 : st3.next with
            | none => rw [h4] at h; cases h
            | some p4 =>
              rcases p4 with ⟨t2, st4⟩; rw [h4] at h; dsimp only at h
              cases h5 : st4.next with
              | none => rw [h5] at h; cases h
              | some p5 =>
                rcases p5 with ⟨t3, st5⟩; rw [h5] at h; dsimp only at h
                cases hf : applyForbid B arg (Nat.land t0 7, Nat.shiftRight t0 3,
                    Nat.land t1 7, Nat.shiftRight t1 3,
                    Nat.land t2 7, Nat.shiftRight t2 3, Nat.land t3 7) with
                | none => rw [hf] at h; cases h
                | some B' =>
                  rw [hf] at h
                  exact runNode_sound hred hMin hNo hr1 hSyms f B' st5 st'
                    (applyForbid_sound hB hNo hf) h
      · cases h2 : read7 st1 arg with
        | none => rw [h2] at h; cases h
        | some p2 =>
          rcases p2 with ⟨cs, st2⟩
          rw [h2] at h; dsimp only at h
          split at h
          · rename_i hw
            exact hNo (checkWitness_sound hB hw)
          · cases h
      · exact checkSymNode_sound hred hMin hB hr1 hSyms h
      · cases h2 : st1.next with
        | none => rw [h2] at h; cases h
        | some p2 =>
          rcases p2 with ⟨rc, st2⟩
          rw [h2] at h; dsimp only at h
          split at h
          · rename_i hc
            simp only [Bool.and_eq_true, Nat.blt_eq] at hc
            rcases hc with ⟨hr7, hc7⟩
            let rf : Fin 7 := ⟨Nat.land rc 7, hr7⟩
            let cf : Fin 7 := ⟨Nat.shiftRight rc 3, hc7⟩
            exact runBranch_sound
              (fun B' s1 s2 hB' hrun => runNode_sound hred hMin hNo hr1 hSyms f B' s1 s2 hB' hrun)
              hB rf cf 7 0 st2 st' (Nat.zero_le _) (by simp) h
          · cases h

def initBoardRow0 (B : Nat) : Nat → Nat
  | 0 => B
  | k + 1 => initBoardRow0 (clearCell B 0 k k) k

def initBoardCol0 (B : Nat) : Nat → Nat
  | 0 => B
  | k + 1 => initBoardCol0 (clearCell B k 0 k) k

def initBoardRow1 (r1 : List Nat) (B : Nat) : Nat → Nat
  | 0 => B
  | k + 1 => initBoardRow1 r1 (clearCell B 1 k (getAt r1 k)) k

def initBoard (r1 : List Nat) : Nat :=
  initBoardRow1 r1 (initBoardCol0 (initBoardRow0 ALL343 7) 7) 7

private lemma initBoardRow0_valid {M : LatinSquare 7} (h0 : ∀ j, M.mat 0 j = j) :
    ∀ k B, k ≤ 7 → ValidBoard M B → ValidBoard M (initBoardRow0 B k)
  | 0, _, _, hB => hB
  | k + 1, B, hk, hB => by
    have hclr : ValidBoard M (clearCell B 0 k k) := by
      have h1 := clearCell_valid hB (h0 ⟨k, by omega⟩)
      convert h1 using 2; simp
    exact initBoardRow0_valid h0 k (clearCell B 0 k k) (by omega) hclr

private lemma initBoardCol0_valid {M : LatinSquare 7} (h0 : ∀ i, M.mat i 0 = i) :
    ∀ k B, k ≤ 7 → ValidBoard M B → ValidBoard M (initBoardCol0 B k)
  | 0, _, _, hB => hB
  | k + 1, B, hk, hB => by
    have hclr : ValidBoard M (clearCell B k 0 k) := by
      have h1 := clearCell_valid hB (h0 ⟨k, by omega⟩)
      convert h1 using 2; simp
    exact initBoardCol0_valid h0 k (clearCell B k 0 k) (by omega) hclr

private lemma initBoardRow1_valid {k : Fin 4} {M : LatinSquare 7}
    (h1 : ∀ j, M.mat 1 j = r1Table k j)
    {r1 : List Nat} (hr1 : ∀ j : Fin 7, getAt r1 j.val = (r1Table k j).val) :
    ∀ m B, m ≤ 7 → ValidBoard M B → ValidBoard M (initBoardRow1 r1 B m)
  | 0, _, _, hB => hB
  | m + 1, B, hm, hB => by
    have hm7 : m < 7 := by omega
    have hval : M.mat 1 ⟨m, hm7⟩ = r1Table k ⟨m, hm7⟩ := h1 ⟨m, hm7⟩
    have hclr : ValidBoard M (clearCell B 1 m (getAt r1 m)) := by
      rw [hr1 ⟨m, hm7⟩]
      have hc := clearCell_valid hB hval
      convert hc using 2; simp
    exact initBoardRow1_valid h1 hr1 m (clearCell B 1 m (getAt r1 m)) (by omega) hclr

def checkCase (r1 : List Nat) (syms : List (List Nat × List Nat × List Nat))
    (fuel : Nat) (chunks : List Nat) : Bool :=
  (runNode syms fuel (initBoard r1) (.mk 0 0 chunks)).isSome

theorem solve_case (k : Fin 4) (r1 : List Nat)
    (syms : List (List Nat × List Nat × List Nat))
    (fuel : Nat) (chunks : List Nat)
    (hr1 : ∀ j : Fin 7, getAt r1 j.val = (r1Table k j).val)
    (hSyms : syms.all (fun t => checkSym r1 t.1 t.2.1 t.2.2) = true)
    (hCheck : checkCase r1 syms fuel chunks = true)
    (L : LatinSquare 7) (hred : IsReducedWith (r1Table k) L) :
    ∃ σ, IsTransversal L σ := by
  obtain ⟨M, hMred, hMiso, hMmin⟩ := exists_lexmin_reduced hred
  apply hasTransversal_of_isotopic hMiso
  by_contra hNo
  have hB0 : ValidBoard M (initBoard r1) :=
    initBoardRow1_valid hMred.2.2 hr1 7 _ le_rfl
      (initBoardCol0_valid hMred.2.1 7 _ le_rfl
        (initBoardRow0_valid hMred.1 7 ALL343 le_rfl (validBoard_init M)))
  unfold checkCase at hCheck
  cases hrun : runNode syms fuel (initBoard r1) (.mk 0 0 chunks) with
  | none => rw [hrun] at hCheck; simp at hCheck
  | some st' => exact runNode_sound hMred hMmin hNo hr1 hSyms fuel _ _ st' hB0 hrun

/- ### Part 5: Certified 6-bit proof streams for all 4 cycle types -/

def r1_c0 : List Nat := [1,2,3,4,5,6,0]
def syms_c0 : List (List Nat × List Nat × List Nat) := [
  ([0,6,5,4,3,2,1], [1,0,6,5,4,3,2], [1,0,6,5,4,3,2]),
  ([1,0,6,5,4,3,2], [2,1,0,6,5,4,3], [2,1,0,6,5,4,3]),
  ([6,0,1,2,3,4,5], [1,2,3,4,5,6,0], [6,0,1,2,3,4,5]),
  ([2,1,0,6,5,4,3], [3,2,1,0,6,5,4], [3,2,1,0,6,5,4]),
  ([5,6,0,1,2,3,4], [2,3,4,5,6,0,1], [5,6,0,1,2,3,4]),
  ([3,2,1,0,6,5,4], [4,3,2,1,0,6,5], [4,3,2,1,0,6,5]),
  ([4,5,6,0,1,2,3], [3,4,5,6,0,1,2], [4,5,6,0,1,2,3]),
  ([4,3,2,1,0,6,5], [5,4,3,2,1,0,6], [5,4,3,2,1,0,6]),
  ([3,4,5,6,0,1,2], [4,5,6,0,1,2,3], [3,4,5,6,0,1,2]),
  ([5,4,3,2,1,0,6], [6,5,4,3,2,1,0], [6,5,4,3,2,1,0]),
  ([2,3,4,5,6,0,1], [5,6,0,1,2,3,4], [2,3,4,5,6,0,1]),
  ([1,2,3,4,5,6,0], [6,0,1,2,3,4,5], [1,2,3,4,5,6,0]),
  ([6,5,4,3,2,1,0], [0,6,5,4,3,2,1], [0,6,5,4,3,2,1])
]
def chunks_c0 : List Nat := List.flatten [
  [
    0xd61959901b098d1ac1050b3371d05e456055241583b2cd11cc7ca9a994870820564b1ca9aa18876873a93713072c7287,0x949d59b61b01911ac98c10198b571ca54c5bc53a4319531c54158978175101e362b01b846acd0922b8b5d99ba1989b51,0x89c781b8c41db4bba2d2a7316e94f158156150a0cd0b4901706aa401e36290066e89c791747ca1a878b560dda1b91999,0x4f1ac98c1cd16c701d3a2901626a9c019d6271e45d1f2669d0276d8b3a9bc5ca54c5505685328066ad1c0c19aa703235,
    0x8b547687426c4640433354248d205ab84714cb3a9ca63a88d7686e66625606d46567525586445426c041756124d2a731,0x901d11729c6b885d625415a1509901b110c558c92b0807a545cd2a4f27316c70c43aa9033858a40c8ba271e0742d5155,0x8397171ccb3a94a6e88b1630405a565cd2a6f25314c706b132900a63c9cb625a1547ca1a878b2487735445cea531b09,0x2852a0cdc732cea52981dc8d94b1728c87266b568599a22cd2a6f25314c714c0f290505cc9cba2581a7409d782b028c1,
    0x858d6c0557849005a52dcd2a6f25314c7d625a1547c99a5681dd91999789741949d59b51b019116d18c114e8d07342ab,0x901d11d89193161d01ac2d2c063172b005352e4053b8471ccb3a94a439a956309e05d25c46c0642c405dcb41716a0d02,0xd34101772d02988aec1a96a0b0215e32408e943734a9bc94c531f689604508225eb919997817496d18c9951b59ac1b09,0x235b89999791741951b59d49709901b11ac1cd1145296991789959751701b11b41b99d49cd1ac918cad07242e31c505a,
    0xd0322e8b4181b1ad2c46b1f266a1e2c9e0ac35d0c0c5d89c073950734475242cc586c08cd439020ee31c732cea529aa3,0x26446306526d67585d45504142ccec01d3a2b01d446acb01463a35b999018d1989b61959d51da1741791549581085333,0x65bc6b2631c50547b402a333b01c14aec029d1ab14ab3a931f26420815b286a1e21c20815b22688ce57646e86665e056,0x951b09901d1102e4cc91b26b44422bc9cb5a99a143332d1ccb571037645e25685d45527585c07426c46e066664c6506d,
    0xa6408bba091bc63064c81cec424d625a1542058b16b008ae66c0c2116ac702a333b00a746ac52acea74e885b81791741,0x34ad19168b64758805ac2ecac7019d62b331c5214cf414e11ad34a860805b626e06665e45d26546d67446c25c0420e6,0x8c70c8d15d01434aeccd422d5a1959981b997898f16c1732912d91d6175101ea54b350a176d66c46e26665e0c1cc4aa4,0x815b22420815b286a1c508205eda1d49561509582103d51d1cc8508205e509581561d49da1789959931991b996f1ac9,
    0x9598d1ac1081af4724c5ba5c054a53c81625c9cb0a74979154158908632bd032358b401e315b344731f2a6a6521e21c2,0x8f24c7ca1a872f51157298f16c14e9532054d5892b29e25605d455241434aec01e362b3424508205ed99ba1981b51d61,0xcac62c142296d99991589561d49959901b11b41ba178170ad2acd16e9751019ba2b2b1c508ccf407052bb01625cac532,0x4162c5ac062b83b2b1c508ccf4058972b14ca3c8508a5b666e86645e05626565d46d05586c25ca6407445b273a75241,
    0x932a62635d91ba1999581b49561941d59d09911b0105d99091ca5e25d45b073a4c41dd7666e85e26406645606565585d,0x6d85c46c041d5462450ad29d896e9cd1118c6a72667566544182bcac749019ba2b0172e42cac78c70c4372d01a14cec,0x8205ed99ba1991781589729501b09b41561d116c9ce9d49959751058b16b0152e0ec05cb90b061420c19ae45e056855,0x45407427549ca5d25e45b073a4508205ed99501589d51561b11b49ba1981791959741058b16b0066e8acac71488b3d05,
    0xc2666c06446504182bcac062b98b2b1c508ccf40c1972d01c14aec5328f24c7c991420817b666e86605626566d05586c,0xcb45328f214414c7b646e26665686506d65527586446c05c25ba73274a431a546405e95091e05d44066ad2c05ab84b05,0x1c1a14cec05c172b24c99ab415ca5d25e45b073a5983557589d2550568860ac2f4102b99d016ae12cac7142333d03065,0x27526d05585406c244156664b9a781ce96c972ad12991959751058b16b0152e62c62a3a5999b59741951060af2b2b1e3,
    0x1ea1d9ab415ca5e25d45b073a4559997686e65e45405626607545586c46d26565d04162c5acac71488b3d0508a5b6856,0x5319014e98f16d110e75072629d28086e6acb09ac71062abd00b8a8ec019d62b344731f2a521c20c15b28420c15b2a52,0x6b5876656855093c63064c94a8bd5096645e25d4417a542c53272a4e98f16c77a540dd99b917815a1541d61b59951729,0x9899015314e98f16c9729741b49d5956158108ea23d1e4a544086e6acb11ac7148ca3d033858b4060cabb34250ae1d6d,
    0x655856093c63064c94a8bd5097685607565586d06e66625e46c46406545d2417a542c53272a4e98f16c72f5425da1b99,0xd24b09ad18c70c8d62d008756ac045d1a9331f2a6a6521c2081592c72a6a8621da1cdc4e6420815b2254631b6e6b6875,0x7017515419490e0c6ab1ea94c9bc531c0c6b52c0298b3b2b069d1077686e06626d85d05cc5e45ba53c56a552540410ab,0x2631c4233574029cd4b010b3b241a8b61d19b119099595015497317417916e9b1e215da1b91981589d59b61b09d11919,
    0x911d195096e91031830a6d89ba1991581d61d19909959549741711b01b5106ace0b1ea94c9bc531c086acec03195ab2b,0x1c318409ed89ba17a9581b51d61549741b097116f14e9531022c5d9256640746411ac6a4991ac11a8b61751541731b01,0x5b626e87546d26c06426b463066456055853283225c9c0e2b88725694cb3a9bc5ea7465c1c4646ab401e36291d1f286a,0x7060835b6a6e86605e45625587325ba6346526b06d441b9382c501b090352e29356a46b44817161640454f4913c86080,
    0x65506d875240d4b8ac045d1a71426c041153d2405d5a091cc839aa36c26326b4416ae81c532cea7a97016f24c7019574,0xce9042cec71cc9404e95075ea94c5bc73a634531c422acf4021b9ab2b1c33858b4046b1a7341f264c0f5556874664465,0x7016f2ce94c70262d5b01193b1c0abd0d6f25310cab8491eab3a43951d6e07587645525686625d05b4630433a541c7aa,0x1c5222cf4011973b33062b76a5686e25d45e07587325ba6b44422acdc9938c70604f5b010e5c9c732614d4d7a9751531,
    0x66d25d46406c65425507586b0732460825b625685507586d66525426c064643305ca498301cd5192e49ea5d473a6b25b,0x7027246b56858f222c14c0f29014e0d5c043ab472e89ccb3a93c56a558541f286a1e2c921ce750976a6e46625e056865,0x303ca4ba2cea5a95614c70606b5b0115ad246f2195665d89981791949741b51b09d1114e8d091b26346b040cab31c171,0x6d45c27446466c06b26578857646605e26566445c06c26d0752746453a3424752ad18c7171503b05644cac14650b905,
    0xba1989791581b51561ac18d1941749919701d11d59075518b0674c42cb09045d1a9331f6a960e997626605e47566525d,0x7465c46c26b04579196645d05e25585606e86d49c4410e6aa4b01ac98c7148ca3d040b567406acc4b010f2b24a5e425,0x3634248d1ac1043ab471b2860ac2dc04397273689ccb3a93c56a558541f26632a8d6e86645e25606d45585d075265664,0xec18550b9368b3a96a558531c181ad6c0456b490111dca46f2a5c435b89981791959741b51d49909b19d110568e8906,
    0xb89ac711078dd0541e874190b0b7358950568b6a88ba275e06e4e62eb256a631754742415a3a24ad18c71a142bb06a54,0x8ec02645d7256ac6744411ac6a4ac7c99a878b232a635991b59751949919d118c1cc9b9460d8c9cd1d0a959749b51b19,0x2f4532358d1595a5a9b1950154a7324f1ce96c70708eab231c086acec86a19d7928d114e8d072e85d06d47585524058d,0x454c5c25bc531c2c21aec02999ab022c5d2408bb84916ab3a620f1b6466546d66c0840ceaa498b14c0f29358ae8860a5,
    0x82056c89183016d89ba1981791d61749951541919d11509b01b590ab988b1cc9b07474857626e86466c06d675855274,0x44c83a740735289062a50dcd625495a2daa0c2116da2cea5a9561ac14c718232bd010ac79c507c99082056ca1a87887,0xa5d473a752558531c5283d3408632bd0078c56cd1146662db91789b59951741b09919d116d1ac1cc9053d6071cca3c66,0x26645e06566d45d25cc6406c65b463c6b040ca98dc0728e8736a568550758732450855ae25cc5e06b45b263c664b6856
  ],
  [
    0x25d0c08f2364d1a95a031b1ab2b1c32358b4068ce2b008756accc7ca9a99487887082056c89082056ca1a871420c17ae,0xa9d95ad1a08cb9891ea9625b053a550816ae12c8f2531042b1e9010abd245a17459815a99315018d14f16e9011774715,0x10b0b59264440b56745321420817ae056a6d86c45c05d45425507467527685e264c65666453c5ba6b2631c3234574831,0x549919941d59da1d0a1420c17b626e86d47586565d06c25c4640746443956247a96c94e9549582ac713205db04a8666c,
    0xb005a176c129583b00ba266c10558b934693ca4c656631c4646aac987ca1a8735c435b817895a9b61b114c16e9701751,0x24046ccecad14c7142333d040ae2dc102d59714c8508205eda9ba1791589d51501cc96e9709b11ac1b49561741058535,0x42dd91b897a9b61d49d19911959b01709ad16c17515415a1ce9182156da97097916e9cc9058d2a71d0ad86c06e256855,0x6c9ce9129cd072d89685524046ccec05aba0b2b4531c4c8176c5321420817b549c4b4693ca4c6566b4631c422acdc666,
    0x7496c1ce9182016d897a95815619417499197016d1ce9d11d59b51ba1b09ac7019574b01153d241820167a9b09b81d89,0x8f14c153170108bba091529e2ab2423a88dc5a26eada9d61cc70ce162d341f264508205ed51959b09901d19d897a9711,0x2f405681db03885c6c06e898b14c83a2c66b453c5b25c454064c656664631c1634aac0cea147033a541c7aa2e8535751,0xab6a758731c218caf401e315b060835b686e45627545585d25b46b2440ae65cb42959981911b190cd58491c0d30c21a5,
    0xd49da118b162d00ace8ac023d51b1c1c3581b2c7aa53074d95a931b197015094f15420ae0e1b0099d46c18d11a91689b,0x5627526566d055864c6c654053c6b2634410e5c9c6c17511820d6b81991b59941561b099198f1ad14c15315896c9751,0x2e4055ce09158b684622a8f4058aa6b0112a7a4ac7029d1ab331f2a521c20c15b28420c15b2a521ea1c60835b686e466,0x958b6896a8685ab5eab46ad66e26c094c93a63c5b1c162a9ac044a9e90d6a0d5eaac6b5674496063c5b453a54c8612a,
    0x7a9581b19531901d09d595617417118f16c94c7058aa6b00c6c6ac044a9e92b1c52328f4043cac922c1d354c53063c65,0x359082056c898ae60d952711043972923c94c8510ace4b914e6a0dda15a9b19711d09d595619315016e98c9560c5dda1,0xc2c55d05ca5e45bc53a55c560542402abd24b0100d99a92b4631c40756b4cc7ca9a994870820564b1ca9aa18876873a9,0x654b1dcac294a9ba44c1e45626525d06d47587446465406c241543d2457272a6f14c7181ad4d05062cf400cb9a92b04b,
    0x62457272a6f14c7101ab3d060656b40688d6b2b2631c507353439382d581549941989791919701d11d99ba1b51d61035,0x6e70855e05c46c06e45626d85507527686666427464199562495277252a6e91a8b61949911d19509b010550f4901535,0xc83b2c507ca1a874e5235da1b91999781589d49b61751941911d19501b090550f491ca9bc53a55c81625cac00b8b592b,0xa24b6272acea6f25715a14c7142333d01ad4d666ab09e07647464098b564941022d59b00ce951c72acea03274c735241,
    0x9c91ad9a11a235d0468637419a360d01625c9c772182016d89b81999791741d519498d1ac9b11901d1906e503902333,0x89cab3a9bc95c568531c1c83b2c507c99102316b899917815a1541b61949d51d29711b01cc96e98c1ad1198a6270172e,0x1c508ccf41b05a1549d61d0a030192782b52942ac711a385d0668587405c1729016ae11c7720c53168d1ac1072b03735,0x86526d46b2a30ac09505685e043115c74158c62705622c5c91ab9a11a235d1dc8b42cd5cab5876274473a9bc95c56853,
    0x503901ac4ca408477192d89bc95c568531f3aaa621d766ad8a46b4a9bc93a55c568541f286a1e2c921c5599976266475,0xad16c9711b01909951d19d49032959b003a27648c705d0b4901625c9c772d19155d99d51d0991908c635900b322e406e,0xc993a3a15d99b919817895a1711d09919949541b61d5107511ab1b06b26c041766424735215d91b899997815a1541b61,0x26e45e05d46d06526c65c27346b263064466685c9887406a784b02318d6407282b701cac0dcd62d2a6f24e95715a1507,
    0xd4d4892d29e2b64742423a3a24073b1092b4631c421ad74171423d01d10ae407550393589bc95c568531f3aa1598b76,0x817a851c00e7627017a541cd0711a171d01742d2405c17291dca675036529c2b6274481cec424ac9154675999b81b1a,0xc8aa671e4ad4a34403a275c05e950732708b7646e66625e05685507585c46c06466545b26b46d241b846ac02a999b23,0x86666c664441535624942572d2a6f1cd14c71418b3d01626aac00b8b59231c406e6b4ac7c99a878b2af15057096c1ac9,
    0xa2479170200cd5a914a93c73a5b25dc81425cec00b8b590a77415dc94ab3a5b47475037625e45607585425c05d26d46e,0xca52ec0589aab33a94a803a56a48c7101ab3d0142ccec00aaf490dd1857686e65625506526607546d87426c464643332,0x56ca1a87887082056c89129795da291ab99b61b0208bc2c9003356a458b52ace986b435949d51d0902e8d19368ad880,0xd03234ab402a333b00353d2400dd1a914ab3a850835b6456855275841c14aecd0900e51d9003746a452acea4c7c99082,
    0x423d7685e46d06c66e26665585604206ccf4058b16b008ae66c0c2116999561581d09d51da1789b91b19b49ac7101573,0xd2400bd629332450855ad065c5d46305bc5c0462ea82478ada1581d49561050d2bb142402b4764cd1ac700eb1a734aa9,0x8b4101d5ad331f2a6a6521e21c20815b22420815b286a1e317236666446c65c2418f54246f18c197205ab84b140402ab,0xe157646e85e256055c5d06d275865454253a63c5b45ca440ea3a4901b111052f29346a668606c6b4058b16b2b1c5233,
    0x6e9ac98c7050d2bb002b476482e45dba1781589751541b49d61032959b1c2ac0403666a452a4f16e98c1972050b33b35,0xda1d19d4a672165582d1a999741951902ac7150c63d03435874058972b014f51245728b10edba2972581d615295494f1,0x5715a1ce94c718232bd01a847ac00ad1d7141f286a1cd99856e06c46406545d05c25e454a5625305ba44a5e09c99ab62,0xba1991589d51561749729d09919b118c16d1ce9ac9b427810c8535d03886374062b8370181dc9c972ab42c5b6272a8f2,
    0x70606c69c91ad997890c8535d068817740e218dd0181dc9c062d58725caa83336d8a3c95c568531c1a83d2ca33465d99,0x8caf406a11eb002b475c507c99102316ba1991581d51b49561741d297116e98c1ad1cc900dd1a72c04335682418266c,0x6b40589aab231c388e174063172925c860c05ae66605e47585d265463c5b06b46d05ca6c264674476255c56873a531c6,0x25ca6c45b073a6b26d05525685e2660646441475ae65e074473a5b25ca5d46d06c264666485a1d05ca5b473a6b1c5066,
    0xac98c70c8535d06881774062b98725ca888bd7629d26546d06b240ca98dcd628f25715a14c706a0f4b06c2e67585d474,0x2f58a4cc7ca9487083056ca1083056ca9487a8711666db1990199ab92142156da1d49d29701cd16e9751789581561b41,0xdba94a802ead242b0b1d9719895416e98d14f1529901084c6b90032e6a408dce093589685e0eb1c50746b4058d2ab00,0x5715a15014e98f16c70f4a557029715295419118c94f16e91087aa7358968660eb1c1832aec00cc9d90ac2c77589685e,
    0x56c898f540dda1b99989791581561741b514f18c1971709b01d19d49074ad0b2444031dca452a42e2e5982d62b4272a,0x44195e0a45aa72a5326f102668d7256ab8b58766731c098d6acd07ca9a994870820564b1ca9aa18876873713a1307082,0xb0178aa25999751541949d59d928d202c79172c4641c4073ab40ee310d2d893b08d6e26645e05d46d05525306326406c,0x16a63b008f236495aae2d61d99cc702e2d4b22358d7646e26665e056a54c5ca6b45325bc5d455065275640d4b52c8c3,
    0xa9bcb6254c56a756552531c2b8c0f4101cead00b918dcb62d1521db919817a9589731529909b01b498d16c17514f1541,0x9160a31c32358b4141d1ad331f286a1ccd4276e06c26406b46326646567527665ea5b05d455056254a9cc9676036669c,0xa5c45ea6e46c2a404111dca45324e16f1ac1b620118f5b011635a411dc8d74290ab61b01b895496f1ad14e1532083d4c,0xd49959b41751561731d29b099115014f1ae18c96c7108cd5d02a0ccec589081cecd0d99077666625607546565525d074
  ],
  [
    0xc99cec215da9b91999781b495617294c1ae1b01911941d59d0909e06c92328066ad1c7520620f5b0111dca45321307a9,0x8b0a5dd91b99981589d49b519599115018c9ac1b090d513190055e864562d2a4f27317a9ce16c71183aad0067589c747,0x684d64019ab471888eb6e6a56752d417549586b453273842073b1c582b028c715a384d066858740620f5b016a615c532,0x25e05ca410e6aa48c715a384d0405dcb405a985714c9d5a037645ea5625587525cc74a6c264454053c7386326b45b1c1,
    0x561701d29b11909941b594c9ce1d49031ae2b2b04608125eb99991b41959b09901d11d495614c1ce1ad1198b11736a96,0x741b49951d59731b01909d11529ae16d14f15615828c70c8d62d050746b4cc7ca1a878b24871851d6d91b899997a9581,0x96ab4a94c999a857666605e45d27546566d06e256a6c464254074a4059d8645627324f1ae16c7cac21dda9b91999789,0x45d06d46527565cc6c064474254a6b85b253c558560a31c3072b34148ca3d0087276c044cab904772376675465664266,
    0x8b4a9bc93854c56a551f2642d59954c5305bc42c58b1c562ae108cb83736656a66074a75265664473a21576a6e26665e,0xc56a531f3888aa3d7646b07324294bd5d2b626427346b2631c405dcb41716a0d02a58d2c0547859005a52dc056b03735,0x6c4e42eb271b185764752817ac42c013ba192b4631c505ad3410e543d0405dcb40a9634b009952ec06e503b34a9bc94,0x15670872e6a564097346c05d5a0b0055e85cb11907142d0bd34a96a541c18c2d6c732c6c615d89791d5174905eb10b1c,
    0x741d09d51b4bb9a95a0abc21b021742e4083b8c736a9605c58535d08094e6ac02ccd1b0175682cb09168741ac98c16d1,0xd095294f16c97310439569010acce40439aa900ba34648c11488f27256b38ad86e66b1c094e6acb07c99a878b2cc5855,0x8d78471d29509e096ab4a80ca52e40439aa9231c306ccb4031762700d6345cd62b8c41dda9989791581549741d51911,0xa5526b8531c2343d340252b3b01154cdc32b435d895a9549531d297099114c16f1cd14ee845d89909711531cd14c96f1,
    0x31075e25d45b080d6345c54ad623330ad90395ace2b61b99ac70c1574d0415667405d5a0b1cc957a03758b4a9bc94c56,0x587c991420417b286a1c508105eca9a99487887082056c89082056ca1a871420417b26420815b286a1e21c20815b2275,0x999d93532d2a7a98f11831d699ab5a942d2a7a97517020447aa91b1c322e8b4043b1692b1c2c0caec08e11d90206c79c,0xb1692b1c206bd1c1a07295094f1ce16d18c1931952b59b01b91999108ab3d0066ad2c1831d6b59951741709901b11b89,
    0x108ab3d0322e8b4019ab4b0a943d76a95864c5ca5407385b26344308a5ac29d25b47324047475cd628f25315414c7043,0x1f2a521c20c15b28420c15b2a521ea1d1ae0d5585c25d074a7527645ea7384571636c4463446a4da979172ad0a7496c7,0xd91b999895815297017a9b49d59751941021b9ab158a4c93c73863441162cdcb11ac76c70ce162d00b8c6ac04672a734,0x1c43827740468ab714645d64c93c81162cdcb5ab12d51d9999111622bd0445ea34562ce15a98c5743562b01ce151e22d,
    0x99275178272a5315a98f16c9ad14c71560e1d0358ca34016a6371588585ad6c2640ed69caa3c93854c56a55075876673,0x564b1ca9aa18876873a1347082056c89a118f5d89b99991b51d598c96d174905c0b5b2c26b04112acdc94393245ea25,0xa1d46d07346b86c46e2454262f40c89aad002e2d6400d99a9231c52139b40540f590111dca45726f24c7ca9a99487082,0x8cdd766a46631c3055d340540f5901154ce4044772915c9bca579036666525ca6407466c454256a83425c74055983904,
    0x9231db1c4213d74118372d1dcab508d7666625e056a5d46507525405ca74464645506664143d1192d86e46c26b073850,0xac9b62d52791729b110458d6901766424182016d89941d19911999b817915a954950172900b8b592c2403666a405d990,0x241766424b62ac1ce141ea65781d19729b015095a95419499119998c7081774d0031ad641820165a9d19d89999b81ce1,0x84386e41c7aa919991d99d290468ea9252631c40756b40352d49354731f286a1d6318b666552644650746754762ae46c,
    0x9497411307a9589949b41d29919501b0971101397191589dc53c6b85b1dd1a156e25605586d05dc6c45425c05b453c6b,0x65ca41cd58247725624f1ae18c96c7141cd4d00d0d6a4d49a63435da9b89791581d19729b115099019995714e1ac1b61,0x25d46505406c26446326b0444ee21c99a72ada9d1a02c2f29138ad895c9c390b76a5605426c06e26665e46d465064474,0xd09729053985900d622e408e760923082c688dcd626f25714c70a8333b0221cd5c0819737162541f265e8a836e45e056,
    0x4c705a135b0088dcec042b3371604b972176a5e45ca823ac624772561ce1ad18c96c1223ab5da9781949751b41ac9cd1,0x9252631c40756b4d51cc7ca1a878b2487688d2db9a91a09dc2192b28262635c772ce2561a9e80d6f2d61b51949741571,0x78971107356091dc95893c6b85b1cdd1856e25e05dc6d05586c45c25b453c6b8460ac65c919991d29d995a9501032959,0xca0ae49518c703435a93526e62155e454a56074676a6666e26c4814f58244e1ac1b625722b462db91529581d19da9999,
    0x92e29e45c241cd58247725624f1ae16c7374615b91781771b41561b097114f1ae16c90a0771724666274a76656a54041,0x5a9951741501d299197111531a191e2ae46c2814f58244e1ac1b625727a8465d999815a9951b41b11501d2991915c390,0x89584408125e7099119498c2116a1972c6a6685c98874062785b02358d24d626f25714c7d2a5a9507c99374615d99981,0xa2373589bc95c531f6a9604408225ed91b89781b41d49951b19ad16c97118c190999a15ac21d02705c6405a98571dcb3,
    0x5ad1c70319462972e6a468277086409898d70262e85c772ce2561c630add118c1cc9ad1194a1972e6a4682d588640b1,0xd2a5a95091327489045ab224d62ae1110af17266ac68111dca45726f24c7c99a878b21820897a506625e46346b05b245,0x738634650817509ac1284ceb0458d624110af17266ac68111dca45726f20e8711901cc98d1949b4106a7a0b0199d42c,0xb52ae2cc71604f1b05688d24158c627246ae68460dcb404457391dc9dd0857626e45e056a6d87545d25c454074a6426b,
    0x9158b38931f26420815b286a1e21c20815b2261cc2b66455265063285c5a81cd52b62156665992da9d61711d09529b01,0x589b49b01919941d51529d0905eb1091e06b45b25c4817161647728d614d9727126f1ac98c70d1135d0054cce404652b,0x5dc6c67425b463c6446665c05e256054a803ac6a4013ba192b1c3444d74101573d0054cce4562ce25a322dda9b99991,0x533d002d4d64d62142156b89999781971911b197097516f18c11a88d1716a6d054074a752764943a8776a6e46d275465,
    0x7b6a6e65625506d274454a6c06b45b05e4660646654408d636c05cc1591dca3c40ce155c0439aa71c2402f58a4cc7141,0xa6b05b25c054a74243394a2479377277280d791541749702b51b19b819999120358d1925c9bc6b2631c10b4ae4102081,0x6b4681518d646c7150333d014c4d6404652b9010e5ca45728f24c7ca9a99487887082056c89082056ca1a871020817b6,0x2ab824d61cc9ae1190a637364a66b464159d824182016d89b817915a9d61b49741951cd1ae1b1150972990100c6b5926,
    0x2b4675273876484213d740c1574d0540ccf40531359010e5ca45728f21430c67ae05ea5626d46505d26c26445c054a46,0xd646c904571672c0403666a48c70c8535d0380dcb4045533925c9d99036665e256a6d86505d46445405ca5b06b46e06c,0xd51ce1d8a0888f5d05062cf400b8b590408205e7a9581d61b51549741711529d09ae1cd1105cd173666e26646464031a,0x66c26e454056242c0caf4148ce2d040756b4d51cc7ca1a87b9421db919997a9581b615497417115296c9ac1b09901d19,
    0x398b15d99b899917a95817516c9701d29919b11509042d2b901d438a403435a9352427a9976a5d25b45e07465ca64466,0xce25618c187262db99981749919951b41b0a053ba091b06b442c688dcd628f2571cc94c70819737010b4adc589507c99,0xd628f29415714c7022373b02c0caec581142156da9b99991781d49919d11729751b41b0a016a6392b45b24189e15c972,0xc15b28420c15b2a521ea1e635075cab4476a9e2ab28281e35c972ce2d495613ac6857aad2a702ac1032a63702c688dc
  ],
  [
    0x9710e4972ce2561c8386db1ad9ab9302b531b02d610e403270d7358a3c95c531c02ead1c00b97271ca96a541f2a521c2,0xb0270342cc5cd628f25714c70e90b4b03845cac7aa581c21ad5981d49d119098d119382972c6b66858f223401ad0db02,0x1416b47240c35a0a5cb9ad1a0e5c8890282e2dc972ce2561d6221dd99b91989901d09b19711749951b416c1cd1ac90f1,0x715c9bc931f2a6a6521c2081592c72a6a8621da1ce6420815b2263350d7626647545d25b06326b46d05c46c242946664,
    0x41423d5c5726f2a466a5981d59b49951741d09919711b010cd13290239d8247aa58952a00b9729015666248c90508f5,0x772546665b899917a9581711529b0190901cb9193686d47527346b8407aa85c741058535b256b46415a076400e8d5923,0x529b0190995998119aa659917a9959529b09901d1971100b9729231c181eaac00e76291b1c460dcb40604f5b01153d24,0x1746a4cc7ca1a87d5a845d59b518c1949d11919991781729b015095a9081774d1504141cd6c7463157a9541589d19711,
    0xb1100d8b3926268711d76a5e05dc6d06567545527465ca6b85b453c568850b42f400e8d59140a31c40756b400bd62901,0xc99182096b017137aa91ad89d29d5a022c5db0068dd2c00ccd59142410b3b2488ea1d792b4ada9d51959509901d19729,0x39c91ab5a022ccdb016b416c5a21820d69918c1ad1b817a96f17414e1571589da1711d29d51cc714a0e6d010b3b1c507,0xa1c7aac4589d5a1729781da9ce1d49d070ca135d0088dcec182116da9989791729143d1190531a19c14199a72e0c212b,
    0x45d1a9331f286a1e2c921c408125e7019135a2d91ce20f550872c6a56438853ac0f1a14735243c81b2c0e1172b032a6,0xa64065666254cc8b7646e86625e056a7566545d26d074a6465c46c25bc6b453855c540a31c40756b4060ceab002f58a4,0x709b116f1ac94e15715028c7043cac9003728e4ccc42dba1791581571741709b11b494e16f1ac1131ad0736a74675454,0x425da9b81789771711b09b51d19d499599919025a15295414f1ae16c787342dd89ba19917815a9d59949751b41d29919,
    0x90111dca4182b0b7368b4a9bc96a53855c541f2643856b6e85386b04406acdc992b520606b5b1c46c24115ad24572c6b,0x9062ec424ad18c71a850bb068550ec18d50390111dca46f25714c7ce25a2daa1020497ac65c264465686a9886c0456b4,0x53d0590674232405dca090642c2dc19194371dc9505605d96629c2b52744862ec424ac98ae645991b5994191a00d8f2,0x8b20f446d7017896d1ac1b919811460447b546d26566446c67424478d424b819897917016c9ad18c7151c23d04685c74,
    0xac1ce12ec435da9ba15895715297094c16f1ad1b01ce1d1102e85a900d1a35cb5a91a00d8f29231c1c23a9cd47c99a87,0xb91989781b41b199119597098c16d105662c71dc95253c54082d44664034ad1916aab8b6874a731c0ccd524c6342dba2,0x19032bd151f26420815b286a1e21c20815b2253d60355c9bc532410d5d1cad18c1992711173310905c6341cba2c6b425,0x5662c7060a1adc191a23734a94256ab6895819d656ac6867152247726d18f1ac1081b337064650dcdaace25a15294c7,
    0x4ddca3c46421adcda95a1ce1d095294c71510f4d02c0caf40143739354688f235e2ac69dc6d265663c81c9d81cd51cca,0x8c712919ab042c6aa4101d5a7261f2a6a6521e21c20815b22420815b286a1eaccc16d6b6856a64654074a7325e350966,0xd0454666405073570442e2dc5721020817b645ea7426c05c46b25b05d26d455056254a85cd4224ba2d5a4f2971919ce1,0xaad07386b46e86c254056a5b0460c35b647386b46e85ea5626d05d454a6c25c040cd5324d1991195ad4a6c94c7150333,
    0x5ca5b47327446c26b86d45525d041614d6c03531a904ccaa24d5a4f29719198c71190b5b04283d64101ab370d83355c,0x5ea7526d46565d06c25c46407466b873476856254a5b2531c454666411635890141cd5c5721020817b686e05e256a54,0x10b54671cab6a664440756b4068ce2b002f58a4cc7ca1a87168941919501729b09ad1ce1d111066a991d45b0460cb5ae,0xd29919501ae14c7150333d054318f405478590039d8a45728f16c700bd1592bc5415b4b566d46c274464654044283d64,
    0xc64666453c6b8631c111eaa4128751501709d29919144cd192d06c4814ee824ba2ac91820167a9d59d89941991b815a1,0x6e84540ccf41591a2d260dd0c34358740557a0915c8408205eda9b89781751b41549729b11501d090a67489168b56a5,0x25ca63c64440d2a664d51070ae2b002ee8a4ac7042b1e7141f26460835b6a5e45627527465ca6446566d45406c25386b,0xa75265073453863c5b04531a19c991b59b81b1191900cab392b988576a6e46605e25686565d06d255c6c65b453273874,
    0xc5d45505c074a6c46465b263453c6b04406e69cce25a198110a0f5d0088dcec042af47060835b685ea5625d455c5c274,0x8d83390609ca5c193b0873689caa3c96a53855c541f2a521c20c15b28420c15b2a521ea1f454877646e25ea6d675265,0x9722240d0b0e70181ad5c972ce24f15a15470e90b4b03845cac7aa12b475911d09ac1cd16c919562172c6b5686ae222c,0xb010e5ca40d417190342cc5c8f28cd435d89b81991d51749901711b090e5c1191b063243a2239cad20ce8a872d6b4683,
    0x1cea4d84c1c20815b2254199b734b686545c46406626e45604a728d7629685d26425c07385b46b2531c52a0cf40588b5,0x73252a7818adba25314e9541589729771781ce16c710635ad01b846ac00e7627341f2a6a6521c2081592c72a6a8621da,0x1c518b5340560ecb003a355c616a65781d597519419995894c18c902999a72d240b9952c911b010550f49015a561c572,0x7297717916c70688d6b1dd1037666645e056255c7526565d46d05ba6b453054a5cc402e5ca414671172e8ac264073863,
    0x1f286a1c5d0b55607385326b06e85e45d06d46c26404031dca457273252a393a25999581531b01909941d59b514e9549,0x31dca4d2a735215d89b919995a14c9ae1b49951d59d11909014d599150ac094cb3a9ca5dc6305b1c3c0d8ac0c19aa71e,0x656865275655c5306b86d05d45425cc6c440362ce4901cc955e225999571949d59501b09b417517319118c70ee214b00,0x31dca40ceb10734aaa0f436d4a426c07444039d8a40cdd10923441625c9c532cea7297716c70c2374916ac897646e266,
    0xac1b09d117297717816c707511a900c5d89cd47c99625c8d77153170106b990923281a14cdccd2b5102c791b244ac280,0x6566305327386b441ce851c73191150157101578cb00362cdcb09035654934a840c111eda1589541531901ce94e18c9,0x443c8587405c172901ca50dc772284d5d7915717417326ead295071302d5d01c83b241820497b646e66625e05685d46d,0x5a1547ca1a878b2487182016d89b815a1941549d29b09ad14c1ce18c99117016e91306a972d6a6644c817740caba071e,
    0x5a150710b0b5d01ac2d2c7321742d5781b0191170900bd6293325b44059d31c8c10169597027a521c772d2aae25314e9,0x4445ab224901952d5a9996d18c908397172b8968531c42f50b4ceab0278db91b41b09911054a339020e5c5cd2aae24e9,0x41dd89999951d599018c9ad1b09b417496c1792d1208dd03905503c6414173272e89605eb1037626e45e05d26d06c274,0x4752764662e56ae645650d3415e08cd0458d0f4159ca0d015740e405c1729005a52dc772d2ace25314e95a1547c99374,
    0x1cc55b0097346c05dd10b0155e11cb11907142d0bd34ab3893a568541c42c2d7406b0b4b018c5cac73218204979e06d,0x999781941b598c9ac16d174ad89d5205dd10b0211ea5cb091420497b646e06665e27526546d65b46b2630407a545c741,0x789b59ac16d1741951999b098c9901d11d490b3161b02330ae408dd039022e615c083b8c7368960538b3a8508325eb91,0x4615c45cae1b91da1cca02e85a713ab4a84c8d6241304e97266ad675441d446ac00d7a272c1f266a1e2c8508125eb91,
    0x42c1857117368a873235b263440ba169c99ad2a4eace2ba1b59ac71052b3d19ca0b5e25605dc5526505c454c6426345b,0x5b224e82b574a6426308bd5096e66645e06d06566325b45d273a7545cc64074254a55c531c26689ac58a0c1b32d0694b,0xba292b24308305ed895a14e9ce1d29d5154950100ab3392c24035e8a4ad16c70589aab231f26420815b286a1e21c2081,0x1706a1d35440c5d8ac00e71592b25b1c1a22cec0c20c17968b4ab384308305eda2b0252ace94c7068716b0182acec00b
  ],
  [
    0xd2ace10c2116792da252ace94c71416b4d0162c5ac0607aab2b04608059686c46e05e476253a73874a41ba2624b5a99a,0xa55c560531c0a666ac8c7ca9a99487887082056c89082056ca1a871a8b51959549711931501b090853339020e6a645a2,0x571d49959751b41501931ad1ce1d11b0b6c714b816d00354ce472a1a346dba1701d11b09b41ad1ce1084d59724c9ba94,0x6e91066a97266ab8b68756744731c0662d6c0c20c17ae86c06b273840af151cb51068716b0308305ed99ba1991781589,
    0xa47297916c94e915942671d04162c5acac70c1d2ad050e15a4ba24ee225b91781709b01b497519319415295715894c1,0x398976466665c75655264054c7426c46d05ca5d45b053a5605e2c60c05b625607567446c26d454c55265c66664041735,0xc20817ac2b4a7625ba73444631a9c99ad590b18c5b0278d82474b08394e90214cce45a2ae24c70c19aad231f286a1d5,0xca6664465c8142ccec0f0581741d49959b517116e9cd1d29509b01055983915ca4c4032ace4ac7019535b051a3464ba2,
    0xd51959741b01711509ae14c106c433724c95c6d2c53a3434016959b002f58a4d2a6eacc700d8b390681b273a76275494,0x572060772b02c15c6507565d26d46b253854264c6c07444039d8a46c708b946d00ae646c72a1022d6d99b919817895a1,0x67525d454c55065c666644820e6a645a2d2ace16e9ad14c70589aab231f264408b59685425306b86c0744415a5624932,0x46b1c0362ce442635dd4a57150993119c0a991e2960ac06b24162c59c019d6271d040654d6c1858d19368b274897646d,
    0x1306a973548066ad2c1033729266ad68182bcac00bba2910ba1755ca4c83284d64792d52058b16b01543d2c00bba292c,0x6731c518c6b4d07ca9487083056ca1083056ca9487a871022d6d89b917815a1749941571d29509931b017114c1ce16e9,0xcdb02b888ec08686b716891b9896645e25d06526d45c46c0461634648c1ac9184a8b72e6a4c9ba93854a55c56076875,0xc94c5509e084390af40ce528d002ecc9c72a32e41dd91b99981789741b49d59951571529931711b016e9ad18c94c70a6,
    0x9310cc1aa91e0c219ca5c5a2b01ce1ac705e0acb003aa8dc8f222dd91b99989b49d59751b01911ad18c16c9066750725,0x3a1347082056c891a1ad55a2ce18c9056943724c95c8182acecab3225d99b91989941d49b597515717096e98d14c1529,0x62645c9427715497015310c237490518b524791b811484e6d0521ccb45aa6ea4c7ca9a994870820564b1ca9aa1887687,0xae18c1cd114ace072e454c5505c45dc5e043214d74148732d00655d2c045533916a9ba860805b627466c264466663245,
    0x941cc9ae115a3a599ad19b0900d99a9033a2a248c71087aad1b1c380dcac00d4f490322cc9c7aa62646dd61951b01b49,0x45d05cc6307326b86c054255c5604221cd74011774b0031ad645ac21dd91b89581d61b51771549d19711531b01909999,0x45c073a7447665ea6e46c294c810e5ca48c70f0362d05c446b403195a7351f286a1f354897666e46627586d274464665,0x673276a6666e05e4c20cdd24088735716242c43b34031ad473521475eaac0960a505b073a6539075626546605dc6465b,
    0xb99981589571b49b119199517415017310439aa92326b04322cc9c7aa4e2d61d91cea6c700e7627341f264608459bab4,0x46a0ccd6526d06346b2405a98dc772ce1d515615314c7084373916242398b34148732d01b9c42c1888ea736a850c211e,0x439aa7002f589c7725327071462d4d26298b6605e45dc65455054c5c045ce222491ab99b110b570893586d26b063273,0x8c1ad1cc9daa0e6350d0086e69c94a02e463b138b5895ca6751176a5e45605586507525327385ba6346b0ed481883d6c,
    0x72e09d0a3040a62cdc04397272d89ccb3a95c53856a541f286a1e2c921c608125eb99991781589751501b09b419196e9,0x951d49d12055d039017350a40ab131902625c5cb62cea4e15a95471590b4d01702d64772360795791b096c9ad108ba34,0x5c26406665e46e25605ca315766a646466505b463242625c5ccea5a94c7021ab3b0032bca4ae250e15dad279291ad99,0x5dd10902626a5c75206ad03b028c5c6c08ba3473589ccb3a95c53856a541f2659990b76a7546d07326346527466c45b,
    0x6c66d46526b06345b1c1983aac05e81570039d89cd071590b4d04645cb405c0b591dca82f296d2650e66ac681732a24,0xadcca322dd91b999817895a95414e1ce9d61b49951b11919701ac18c91020c97b646e26665e056a55053873a7585c464,0x8dc5727325070660eab341f266a1e2ca07a956b45b05e49c2ad26546324666541c4e1541ce9d61d895a909e161d011a2,0x8157010a5cdc7720b466dda99817915894e98c96c1cd105dd1072e67586b86c46466545d26d0c558333405a166b015a8,
    0x66c088766713ab6a960c558b12c1602f2b0578a82c14651972e6a46ac1c318d534a6668578aae2549b41d619518c905e,0x9524eab91581da97896d104573270419aa5c99a2ac635991789751731509571d49b61ce18c9ad1026ad171b0a5040956,0x253a73843234a9c78250100aaf492d06b45b1c6223ab402999ab010e6aa48c7c99082056ca1a87887082056c89845795,0xce1168741549b11919731501d09d91ce94c704571690112ace4ac90c20c17b6a66475265c5d46465cc7446c26e655856,
    0x941561931b19501709771d49ce14e902953372d4b444039d8a4791ac96c70c88b5d00465cec0458b390308305edaa562,0x26465cc5407426c440563c64daa562ce1128701931b19d11509541ce94c7043b1690111eaa4ac1182116da9b81999589,0x5aa6ea4c70c89aad00c656ac00d99a9231f2a6a6521e21c20815b22420815b286a1dc342d6e66605e456265c5d07546d,0x742582b010cd88691ea860805b626e06665e47586d265464c7465c27346b86c454055c5d0426253ac019574b02a0ccec,
    0x532971021d5ab358ab8b31c2223d740298b3b002e2d64950675d99b89971991549531d0991904477291c45b24115c59c,0x14ace092c06b2410ec59cb92d5271102b99192d88508b5b666e46606d05d47446465c040cd58646e94c15aa54a78ab0a,0xa3471eab3a9b4810accdc072760714ca5c75440c656ac8c7ca1a87a9c235d997897415496e94c15a9971981d09919531,0x2e66272d8938ab08119ca9cd1a9995810888f5d14cc8b7666e26646d05d26c45c074264643316a245615814c9ae10ca,
    0x2d4d6403588b93588ab18d76aa5c9c095854c5606d07385ba6b4531c0a666ac0439aa9231f264308205eda9d51cc96e9,0x183096d897a99517495715099316d1ce9d1114e4e09160ae46d040ad686c99ab1a044af292b2410ec59c00bd6271c040,0xce9168971749561d09711901531ce16e9ac14c7b930a911eb017621ac10337290217331cb1a9995810888f5d00465cec,0xd629326ea5714e15a9507ca9487083056ca1083056ca9487a87183096d897a9d61b49941751931ac16c9701d11509571,
    0xcc706b0a6b002f589c7070e1172d018c2d6497239382db19d09d9ab92712cd295206a706b02705c6c00d6b4902d290dc,0x6e98c900d99a72e66b46c2746644c4a8667406e0e2901aa60dcb425620f05a9d61751d09b199116e98c9ac1b495414e2,0x581b11d19d51561741ce18c96d14e902c58b72d280c6c6ac044cab7240ab1c18ee41cd4c615d89981d517497915a94c1,0x82056c89a73425d91b997a9581b51741b01d196d14e98c191100cb9a90421ea9c98ace2562d4aab421dd89b999917a9,
    0xba2ce1029cd4702a342dcb410684e6b01a1ccac0464ec90031dca45aa6ea4c7ca9a994870820564b1ca9aa1887687399,0x2823a0ae48c7019574b01a1ccac00c772916a9ba96708b6607546566c26b463264474676254c5525dc5e45c081133aa4,0x47566525d055c5cc74464654041ab3824ba1b09b51ac1ce1c6c41dda1791b81cd1ae1b52d4a959989911d1900e8d592c,0xb41d49959b11901d19ae1cd1102c6b72645cc5d455c560542a31c039d8a46c70e0372b03344ca47aa1460407b626605e,
    0x26b86d280c656ac00e8d59231c045dd2c746315541589959981531909d19b017117720d0971b032a51a4d5460dda1b89,0xaf2b01193b245a2ae24c7ca1a87313a35589951919981d59d91d090ceb0292e86d26c46b073869710d76865675474673,0x2403a35640b52e0923042c63a1c91ad5a021af2b168ab89ca42d76a7345ba4045dd1cb8a77291a8ca549531d09d5a021,0xa1ed0382a3b401ea8cb0032ace4ac71a14e8d003ab89c95ad1a1442f292e8b2a21776a5e05dc5507345ba5c454c6c074
  ],
  [
    0x9118c96c1ce9045d1a72d26c040d518e4174283900cd5864d53168541b11531701771791d499096e98c1cd1da95890a1,0xb19901959549711531ce16e98d14c7021b9ab0032ace400bba292b1c4c0b5740b10ecd011ac69cd51d07c990e8509731,0x46c6540410abd241820d6da1b817a9b59949741571b119195017316d18c1991589ce9772225da9b919897815a1771b41,0x5a2da9ce16e9ac18d14c717111ad003a355c0464ec7352460845b6a6e06625e45686566d255c6305327385ba5d05cc64,
    0xb09ac16d11a970272d6a4683d542248ca0ceb1071eab6873a6bc8896625e05d45cc54055c6466506d66e46c242d5c224,0x7246b56858f222c1540f1905460cdcba2cea5a94c710b0b5d010ead1c732571507ca1a878b24871820d6589951981b91,0x9816c1cd18c918b9427020e5c5cdaaae25a198b42dd89981791949741b51d11b090557a091b26346b04032bc9c171702,0x701b0991115cc1192326b0405ab31c6d209ea447256b4685732224ba2cea5a94c71590b4d01622d5c772541a740d5b42,
    0x97271cc95c541f2668711d6325b07347526d4c694a6241a066a7256b468672a224daaae25a1d0b42dd91981789d49b51,0x89684508125eb89981791b59949741d51b11919d0905676091b26346b0460ac2dcda2cea5a94c710b0b5d010ead1c043,0x71dc9504518115eb81989791941749d51d09b11ac96c11947487234e46ad641ad0d2c1ab08cb0688d0ec06bca0b36ab3,0xca090642c2dcdaace25a10d6a65701789b818c1ac9102b9972649b48646c0dcda2cea5a94c71590b4d04645cb40588b5,
    0x363d04383ab40317547011ac69cd51d07c99a878b2363c859018ca1a27487264e56ac641750d2419d08c90650d0e405d,0x25dc5525c054c530632423a0adc5aada1ce9ae16654357729895a9549531ae18d14c1ce9da2171710d0035e8a46c70b0,0x455c6426c65405cc5e26e473a6b85b0634531c318d53417111ad003958dc0708ea73526a8c8d6e06d66506c46466645e,0x815b286a1e21c20815b22752a076569e46d46c66b06345b24519c45c17171072e8b6a73866358576866056a6566d05d,
    0x4308305eb81789b59971741b119197316d1ac9042b1e736a56853a73844431adcd09d515495011023739264631f2642,0x86a1c60855ae25e45dc6d46565c064c6c66b05b24039c55cda95a1ce14e913142b714255075274444383aa410539a926,0xb0100d53391eaa8656956aad29ba931c1626aac03195ab04283d641052b39264631f2a6a6521e21c20815b22420815b2,0x92d4c4173464ba26685a5da274aae2cc70508f5b00a62cec10b1aa90418d6a498142539d741b51549582d5a971919531,
    0x95ab04283d640439aa9264631f286a1c60c35b645ea56275265655c54064c7465c45d053a5b24435859cac1b0a06ace0,0x1a3464ba20c20817ae25e05c46c06d454c55064665c7565ba73476a742407a98a409e36091689d2ab8931c4a0acec031,0x423d6c1191aab00362ce410635a92604308205eda9781589d51571cc96e9749b41959ad1b09711501931d1910646b905,0x571501931d19b11b41ac94e101957471d45b05c2842b0ae47aa0a85317094c1ae1b01d119191ac05a936aad29bab31c1,
    0xda2c60ad5752d49d120839a9904173464daa5a2ce16e9ad14c702999ab0408dce49918c7c991820d6d91ba1589d49959,0x711501931034a99934275441c2b8ac00bba292b1c0465cec10539a92605912ad5d0c40d6a641858d1904373424cea7aa,0x56ca9487a871820d6da17a95896c1ce94e1502b19b4193195957115111eb002ee8a4b9198a62db91741b49959571b19,0xce25a186b435949992cc9ad108ca3372308612a2dcda26ea5a94c70cc0b5d0111dc9c932571507ca9487083056ca1083,
    0x906460adcda26ea5a94c70e1172d0181ad5c972541163c558d1ac96c103276172c6b5683b3222c0d5d0890342cc5c7aa,0x711b090e5c1191b063243a2239cad20ce8a872d6b46839722240a1a3371eab38968698c2d630829a865cb5ad1a1a5688,0xb1950102ad0b900af44645aab62cea4e2ac74b1ca1687a878873713a13072c7082056c892d4a35d89b81991d51749901,0x8359cc96a54073a5b463c531c058d8e40119737158860405b6266665475664c7445c26325bc42358d1c793742b81549,
    0xca94870c1196732182016791589501709741d19d49b59b81b129319519996f1cd18c7108573d06508ae4193129936a83,0xcc70f112ad3588b17455c482b03c6402e711916aac2167642dea94c93a63c5b1c4a43cb4021ab3b010ec5a4b62ce2ac7,0xae4225cd55a99319897816e98d10b0b51549741531b01d199117098f16d14c70a0ccdd03872a34023c8d925680a746ac,0x900d5c46408cd58916a830465b666e06645ea7426466526c46d655056254c5c05d453a63c5b1c22358f4019d54b010b4,
    0x5495810a9833d06a888f41290f2d060ac674021573b010ec5a4b625328f24e2ac7ca10c20d65418f14c95329120b3129,0x681163ca49328c90c20d65315818f14c7016363900465cdc5620c22967896e9cc9da9b99991b01d19909711741d51959,0x820966a90820966b1487c87182016b81999791589951b59501709741d496e9cd1daa0cd990d0179582cb12013875934,0x275440d4b52c06c0f2b1425c0410e55a4b110458b393468115cca49326f28c74b1ca1687a870823166890810d66b1487,
    0x4e1ce9d120756a0935640c5d52c04475691b1c1cc58ac732182016da9b89999581561941b59cc94e9ae1074ad071e45d,0xce4562932ae24f28c7ca1081116ca94870c11965620c11565aab624e1ce9ac71810165a9b61549919501b09b99d89ad1,0x26506d67546c27465c4540562b3263ab115405626606565d05c4833ac4247aace96c71488b3d03129cb4013875901154,0x256042a60cf41aa223d040ae2f4044af292d8ab24308359585606b8531c1684d6c042b33714cac788576a6e46665e05d,
    0x72e42c045533924c96a55854253c7385ba6b2631dac521f2a431085b6a6e46666547567426c67345ba5c45e2a409d055,0x47426c66405c45e256a5d05525ba734531c30a9d34188aa3d01684d6c044af292b2410accdc532a99d05b520b4a58b01,0x9033a54240cdd1091ea958a4c9bc53a7386b2631da051728d5eaa56ac6b665585627385b471ad097666e06647586566d,0xc8d8ec131a98b142440a97a4993063b90b0112ace4ac7732181016d89b91999581941b59d51749d19711509b01045732,
    0x7325014f1ce16c7042b3392b1e31c308a596a9385ba7327588046ccec168959541b11901d19cd14e16e975206a0e6b00,0x5b58aa8b21f3a531c30a9d345320810d6aa168148956202a98bb008ae66ccaa5a9083a74d050b42f4182b19d00ca176c,0x66605625506c27467525d46445c052a5a25ea4388e17495a03195ab010e55a4a870e9816d06a888f414298bd2d882046,0x86506c27466445c05d25e4a6685223cb4198b11b36a9aab21f386a0e1d55056266052a5a05ea7646c06e6420865b646e,
    0x91c1aa37665d26c65c474275464065666486223574031ad4b011a3aa4687062b83b1ea860445ae05627546d66a852055,0xa521c2a607b4b5a021af2b1a1c0c656ac04395692a1d8531b7526565d47466c25c06444232e624d91b99589983044ad6,0xcecd62c890810d6562ca14871488f2d020865b52ac26e45585cc54056253c7284204459cc5405ba53c56a552b58b3472,0x5740458d69011a3aa4687a1cc555aab5a952732ce96d1168959911701b09b91531541589d196f1cd14c70b182bd00a62,
    0x29626446c65407424058d8e45627324f1ca14c598d7a95895417497116f14e953118a81d935876674273472a521c6223,0xc96a74654273a5b44ca83d650644463056a499adaa5315896f1cd14c71488f2d004e1d6401636391589207285d3a215d,0xd5195954174979170290a5324e96f1c89081116ca9687ce24870e9132d010e55a40298b352d8ea1eb1d3d4896d6a669c,0x752b5ad62cc9ca9487021af2b1a1c10e55a4a870811960821967aa5324e16f1ce9ca1689182156da9b99981589b11d19,
    0x4297390308359505bc53254c410a6ae4b090b53039023666245aad62ce9c890810d6562ca1487082196562ca1081116,0xa74b05843cac032b19b2e894ab3a938ab1d2c7285a1ea1e21cea4d848973556a9ba7325285a072a75880465cec4f2732,0x40dd19709b01b5a9719119998c99aa60dd99989791581549b41b19701911959d51d0a05cb9091dca3c5b1c4055cf401a,0xa8e8ec01478d7246542550405ac2ec02635ab007ac46c00c573934a8308359dc94a55073a5b463c531c2065cdc5a28ee
  ],
  [
    0x72a4e98f16c7101ab3d0162c5acba2ce2ac7ca94870c1196b81991789771949d51b117018f1cc96d106a6347366ad640,0x26c06d6a5c66664463243083595c56063c531c5883c6c032b19b0031dca452a4f522594999991215666090551e224572,0x45e25605526d06c674475665c54a5c064263453c5ba5d44460eaac99a141d1ad002f4564cc7199162b368ac6b117465c,0xca4ba25728f24e2ac7ca10c20d6b425715814c98f118386a71ba94a9c0c3075534050d2bb002f456400ad639050855ae,
    0x5b625e46d66c074673a5b25ca5d0754652644666862ab834058b16b02c2b86c05317491605428032ace41562239050e1,0x6b1487c877a9885b82d0a7297897416d1ce900ad637152540418a8ce49728c90c20d65715018f14c7081973716886040,0xcc9d2a032959901d62624d5a068732b019856a49726f28c74b1ca1687a870823166890810d66b14870820966a9082096,0x52ace9ad14c7060756b0039d8a46c7198315d1dc8579196e66605e25d46465c05425506d26c4429732245a2d914e9ae1,
    0x8b5453a6b873274a8629ca2418d6a093664605d5340c11965a2b52d2aae1cd19aa60dd99ba1589959541b49b19d09d52,0x58b91d0a605525ba73274a646540418a8ce408632b9019856a40858f19168a5cab893ca31f28420445b2a521c3046596,0xce900ad637160542855888e414387292e8ab24308359685406b8531c142ccdc572181156d99b89791d51b59709b11105,0x5721952e578a98191ad0a063172902958c649725a15295494f1ce16e9ac98c76b1487ca90c1156d4a9027297417896d1,
    0x709b01911d1906642b9250c15350e4193a6090655c224da25295896e9cd14c7110b8bd0182bcac00eaa392b24142ccdc,0x65cc29021a3a645a297272a6f14e9ce1ac98c768129ea2599ab5a72a5a1d19509ce16d12e642db91999781d49b59751,0x875b686e66645e25606d455254a6c06466507565c47425ba734531c182acec00eae292b1c660c5747721011d698191a,0x5414f1ce16c7050b33b2b1e31c604559689e453a7385b25ca802acce480ea9d95ab1a09cb889168b665ca5e27385b444,
    0x405b626e666056875472a5226a86d26566447466c054a5c25e45a1c34299b419181dd054708f405581e9005a1764772,0xba2081196b9a992da2aa2c87ce94c70d0875d15c820445b646e86665e05627525c46406546d674654a6c26a052872a46,0x1f385a131b6506d66c09c25e054a5625205aa45c43894d4a75305317490682c26465c4c16255aca8715622390152e0e4,0xcb468718195ad016255aca87081196aa25a2159990d062ec43405dd1090162559475372a363c85b1a054b98934a9aab2,
    0x2420435968b28521c0363ca4181016d8a5a27724f1ca108111658a95ada1b09b51d49d19cd1ca948714631a92e68406b,0x6871420887ae66645e05625506d265675454a6407466c45c253c73a5b45dc4666056c199162b06a6342c18386a9368b2,0xd99789b9305d99091689dc93c728752a316406c441d446a4073b10936874675273472a521c1a235ac0708eab003a3564,0xa87ac7735215b9a77291ad59529549ce96d153560d91ad2a5715096f1cd14c70708abb00363ca45a2481ca160d8b5981,
    0x8119608219657272a4e16f1ce9ca16896468ad74294a572d2a4e96f1c89081116ca9687ce2487058956b05062cd4ba3,0x7240802e6564da252ace9c890810d65a2ca14870821965a2ca1081116792b9ada2cc9ca9487101af2d1a1c16255aca87,0x4c7ac74b1ca1687a878873a9371307065cd55a2ca16814ab4f2772050973b002a5ce40c20d67425715814c96f118466a,0x58d74a031ad4b0046e8ec0252f2b2c6440855a56a4c6c65c45bc8606569cd9b032accb009a96acd2a5090c1116cea529,
    0x86546665e056255054c64253a63c5b45ca5d24078d8ac01eaa1b3466c4c5073534101cabd00a728eccc7ac7ca948762c,0x27446c663c7325eaa116e66646d86565d4752768746ac4415731240c4ca991e096255041434aec0830867b646e86d675,0x481c14aec0295a3b018ae0ec8f25314c7ac7ca11831d6da1b81999791589b61541749951d59074ad0b14c53a5b05ca64,0x85d074a6c65c47325ba4405ea9c9998d1949062a1eb01a83d2c060573b24c942430885ad8b4a9505685e05c27345ba5d,
    0x5d982b14c840885b666645e27526565d464c5ca74454253c5b073a631c606b5341052f2d0162c5ac011ba3b2c645a15,0xa931c422bcb4031ad4b0182acecac74b1ca1687a870823166890810d66b14870820966a90820966b1487c87685d0d751,0xd49959026a5ab34a94273463c88b7666e86605e45625d05c25bc63464c7446c66d4558752656408ae2ec029d1ab14ab3,0x8f045cba294256206b132b1cc9cb9035689e05c45d2ad8950a4c9bca31c162c5ac031ad4b0046e8ec1040d678ab1ad99,
    0x8f24c7181ad4d0422acf4060af2b2b1f28420445b2a521c41035b646665e25607565d46d274a6446c654253a5b073245,0x8ec18101674ad8999b932509181016b917815a1d59549b617517096e9cd1d29d89941b19911999102b8bd01c14aec532,0x6ad89ca9685b073a532550818ae0ec072b18b14c84b9175e0ad86e2568550a4cac654253ca31c606b534058b16b0046e,0xa9ba8d19a965666064474645394624b9b02b332b2c294c9caa3c931c52328f4060cabb331dac521f2a4cd43566064465,
    0x561011d63b060455b666e25e45686d45527586c65c27444439d0a49818d1ac1058b1672565d041705cac05cd50b24c94,0x4531c4233574148ce2d01833aaccc76814e0c6d98179372a8f25314ea14873272e6844731740991acb06a438acda2589,0xb004758ec0c2116da25815619418d1ac110ab987266dbca4c9ca9426cc9836507466446666d66e06c29cc94a9ba63c6b,0x1da1c50845ae66645e25606d06565d47525ca5bc6b263064c74654253a8635c41cb1118d0e2900573864da2561050d2b,
    0xd00a728ec060ceab3324e0e2b7666e86605e45625505d26d47587426c664465681c23aac02999ab334631eb1f2a521ea,0x909d11b198c1cc90cdca599978958175154994190a73252a6e9685d0d99978958175154994190a53272a6f14c7141d1a,0x6ac063b82b1bab4a9cc9424304459ca94c5bc73a634531eb1f284dca077686e06665e45626d85505d265475641d03aac,0x74a060ad6b0046e8ec0352e2b2c64d79097666625e45d27546d66c4646732634450e1c9cba2581561941060573b009a9,
    0xca1081116ca9487a8708119699a22dd99ba1981589d51959b41561531d099117296f1ce98c94c105d43470335681c791,0x654c5c253a5bc63073474a7566d86c46e68422bcb4181b1ad00c6a8ecac7a81081196aa1487c87081196481ca9082196,0x5c294cb4a9bc734531c5223cb4019995b01c22aec8c7ac7a894870e9d15589541050b33b13c9cc94ab3a6bd10376864,0x56c0708abb030445a665e05625585d26506446c66d46e87647567429cc94ab3a5b45686876607527665585626e85e45d,
    0x2b4a94c53a5bc63073242a342dcba1589b41561011ba3b0094bcacb196459957825a1941549b61d59751058956b00666,0x5ac070aa3b060815b6a830445ae89d0b3a96a558540531eb1d2c7285a1ea1e21cdc4e0420435aa044672b5e06425c45d,0x6c7083a74d040cdcb404695a91cc860405b626e86666547566d07446c65c05e45d2a4c96a5585425bc53073a631c182b,0x1c6a2d65d06545586c064674454253073a460805b6a6e65685506d874473253a5426c06466625e45d265475640c5d52c,
    0xae48d622dd99ba1989791741b51d619599317095016e98d14f15a9549016363b3446c641173524044cab9331eb1f2a52,0xd99ba1989791749b51d619118f14c9531d09b190256b1916a9ba4181ea9c95a033362b00af286c702542019d54b01132,0x1f2872a6077666e86645e256a7586565d45525305ba5c06426c66d041ab08ec029d1ab344411a56a45328f1cc9c6541d,0x12e474070563b24c860405b626e46665ea6547565d26426c65b473a74441b838a404695a92d89c0a3c94c550568531eb,
    0x182056da9b91999949b19d11d597018d1cc96e975154150a78a1290f2d01b838a406cc8372d89684212e2f4184a5ad03,0xb01d197111b0ba1991589b41561d49959751709d11b19507188762d03d0d42c7aa9324f16c1ce98c7108ab3d011ab524,0x687a870823166890810d66b14870820966a90820966b1487c871820d6ba24c158956206e883b344411a56a45321a8749,0x805ae66d86565d453a55056876a6c474673480c5d51cd4a509102a5e91e26644422bcb4060ad6b01c2a8ecac74b1ca1
  ],
  [
    0xd1a589ba1b11b5a999108ab3d01c2b8ac046ad492b1f28420445b2a521c6081593ab3276a968ad88046ccec070aa3b06,0x65d45505425c05b273a421352dcb89b1ad129324f28c708b13590212bc645a2b62011b33b011ab5241820d6562d4a70a,0xa338ac045cd49331dac521f2a46a1526445305b25c06c274641ba20e47537aace906ac23714c851075b666645ea75265,0xda1b99589d59b51561749ac16d1701d11b099199410e2d48b033705249930ccd5091ea94ca3c931c52328f4060cd5b01,
    0xa6b2631c52328f4045cd49060c759e45d26d46e26666507565c07446c66346b04152e0dcda29326ea5a956150939462d,0x959751ac96c1709b11901d191062ab91ea93a8521cc9c991b99142333d14c84a8bd5e2a4cb6856a75255874654253c5b,0x66c46d65d26405cc5b463c65455056853a6b0442ae61c50910ac1d926644233574148ce2d01a328eccc7681a86665b41,0x815b686e46665626d06547565585d26c65c4540742433a50a47aa9326f14e9ac98c7068ca3b060815b646e25ea75874,
    0x5d26446c66d45586b053254074275676896a8508559ea5685405527586506d65d453a6b05b1c50cccb4073162b1cc86,0x93324ea1475d25c47426c64214cce47aa9025415896f14e9532043d549334631eb1f2a521ea1da1c60815ae26665e465,0x52e664542b01045d1a923073269d1077686e66625e456a7546d865664054255053c5ba5cc5d2407aa86cd19b11045d1a,0x474070563b010f551c7320c11167aab629025315415a16f1ce98d14c7ac7ca137051d7aa5315894e96f101674c734680,
    0xa53254c6c07466426646565d275440c656ac8c7108ab3d00c6b52c0c1116ce96c97a9752b625a18d1989103372d040ee,0x959d09901b19b41561711749d51070762b03aa622c04675491ea94c9305bc73a460405b626e65ea5685506d85c45bc73,0x673a744411ac6a4ac7a81081196aa1487c87081196481ca9082196ca1081116ca9487a870811961820d6d99ba1991589,0x25506d27587446c64094bca40a33a8925681cab12c021ab3b01a1e8ac6f2532043b9490232e6245aace90c2044796aac,
    0x854c5c26406c47467525bc734531c5223cb40688d6b01c23aac8c7ac7a894870c204b7b666e86645e25d45c064263053,0xa6ae41460817b646e86665e256a5d07526545cc6407466c46d655854273a5b469d18576a6e86665e45625d06546d655,0xaa3d0182b5ac181156da9b999897915a1b61959901709741d51b11d19cc94e9549011973b01c1d8ac04675491bc94c41,0xa74d0408dcf4046754914cb44c8b7666e86627527446466546c06d65cc5d05e456a55854253c73a5b1c0c656ac8c7188,
    0x8b529d45e29cc96a5585425b053c73a460455b6a6e65685526d85d05c26c074673253a43856a1cd529899599127910c2,0xca3c7345b1c09a96ac00e754734a830445ae89c0b3a94a560558531eb1d2c7285a1ea1e21cea4d0420435aa0450455ae,0xb0182acec00ead49002ae8e4181016b617097515015495a1781d598c9cd1d89188762d0682b4740e6350d25c8308659d,0xcc7ac7ca948772e40d90b772141156ba1d49b5956158a972b0278170a7515296f14c1ce98c7108ad6d0622a8f4058b16,
    0x95a033362b00ab466c5827026ea52a00bd549020c219e7815895717497295014e98f16d100e75472427446c6403728e4,0xc568540531eb1f285518c76c09e25ca5b053a560542a529d44162c5ac0531749002ee5245728f1cc981d3958f14c9572,0x6d86c6540402ae8e415467556291aba1b11b5ad99188563d0682a2f49720c11167297496d1ce90c1d5471e0ad8a3c95,0x1c208c59a24204359ac521c208259aa4208259ac521f21ec0f23642744451a16a45714c98f102b87271689cab3a9b0ae,
    0xd899996f18c197205cb90b2c6644f4ab347052b3754d4ab3a931c422b5b4188aa3d0182acec00ead492b1d2c7285a1ea,0x9017137721411567526f2d919719999118c70d1135d0052bc64562ba2081b33d0622a8f400ead49002ae8e4181016d59,0xd8ab61d597498f19515715a15094c7188ae2d0182bcacac7ca1081116ca948773046dd91999ce9d49951b59b09d19529,0x4059e05685d45c25405526d874a7567627344682466c46d65585d273a5b1e31c1a14cec06615a9018ee424972181016,
    0xa6ad0b1660ad89ca96863c5b073a53255c818ae0ec50100aba392b33216e86665606407466c46d65585429ca9b073a46,0x97252a6ea170789d61751b497296c1ad1b01d198f19119819595715a15094c7108cd5d052338b4060cabb331dac521f2,0x7266852b313418872ad00a8ccec6ea52900ad639052f296e06666b463064474641b94624b5bb0a7010631729018f5424,0x9516e98f1ad14c7148ca3d01833aaccc7681181016d89b917815a1571d61d19b09b597117499019514c98f1ac110aa1e,
    0xd6390b12ad558b6874475680acccac72a1420d6d91b819997895a1549d61b59901d19711b0905dc1490197262477252a,0x82acdc95202a333b14a830865a606e65ca5e454053a6b05b1ddca2d4336e0a5cb429ca9405bc53a6b2631c52328f400a,0x25ba53c54a6407465c2402f5524b1100d99a9334631eb1f2a521ea1da1c30865b685c45e26e46406665605585326b041,0x833aac00bb94923073250973355c9ca93a5bc4039d51cd11b1900dca39332460405b626e86665e45605dc6546d675855,
    0xc1116982b6272a5715a15016f1ce98d14c7ac7ca123455d7917499510262d5b344415ab12472a6f14e9571050b33b01,0x50100aba3929898d6e86d4558752e3281833a9c00d7a27256ac6b66462158f4198a62d01815cec05ea1490172e0a4772,0xca1081116ca9487a87081196330ad5d1190902ccd1915c73a5325bc5ca823ac0e406b13290035e89c5a28c2b81b61b19,0x9995895070d614cd15cb4a9bc734531c50666b48c7101ab3d003aa8e4ac7a81081196aa1487c87081196481ca9082196,
    0x999789581771549529701909b11d19ce96d11830810a6989d61d99ba1749701791581183081226781b61b19b91d59da1,0x5814c98c105895671d4406a9d2c054b9891bc95c4142ccec52ace90c2044794aac474673a4608109ed91ba1b59d61951,0x85d265474a6466c46e655c5685c05425bc734531c52235b41888ead01c22aec00b9959231eb1ea2521c30812de701789,0x933a94a402ae8e40c111652a4f1ce96c9772050973b01c22aec00b99590304459dc94ab3a5b4460405b626605e47566d,
    0x7516f18c14c9571b6102cc99b1c26c0746644c42857b4108ad6d006a9d2c022373b0142ccec00bd549003ab52400cd5a,0x8f16c7188563d0050dce4562ae24c70c8d15d00a7352ccc74b1ca1687a878873713a13070810d6a811307815a1959d49,0x65d45e25cc6446c66b45b063c42225cdc02e711734a96a55054240ab42e4b62503c6d782b41b19b929328d10c1196732,0xb07ca94872b562599ab91d59d09b1918d5039138ab06d8804758ec02ad19b36a94a410b4ae41440437b646e066665275,
    0x738631c621c5741810165a9d19cd1d89999791541729749951b59b820b50e1d04d4b434d62ae16c70252b3b0115c59c,0xb01163c9c0c1196d91b81999789d61951b59741549909d19ae14c1cc908dd03716a9ca94c86c24c6566646d86e653c6b,0x8b1d028457ac05d982b01ce542c08d634716a9ca94c8a958d7665ea6e466256065654a5524056666c9324f28c703531a,0x8b404475691b1c3234574141cd4d331f2865cc857646e05e27567386b46d85b05d4532550742644652666860656b40c5,
    0x64c7465ca6c46e65585605426b8634460475a666547567645d274a5c45ea5505626d86e054c6426c663c6b4531c621d,0x91385b26b06d8804758ec8f2531042d2b90304659585626b853040c558dcb12992d51072760b14ca3c43c2565d27546d,0x823166890810d66b14870820966a90820966b1487c87181016d89b919997a9581951d59549741d29909b1971102bd11,0x29504046e8ecb62ad1503c6d7126f18d1932153c609354ee4c054cce404652b9158ab8931c0a7352ccc74b1ca1687a87,
    0x9326f28c70c8d15d022358f4029cd4b060805b6a6e66605e456275665464663c5b05cc74454a6c24057332405eaa091d,0x26d86c4a4641d1a1646c7d59073162b1cc861005ae46665e26d86546c65c47427565525386b24672845c52adaa742582,0x36d894ca3c6b4531c621c57404571690119caa46c7141cd4d331f28420445b2a521c4a1d06d45306b84571636e65386b,0x63c6507566d4c054cce40167619158ab84608059e45ca74476a7565d26d46e265066655856064c6c65426b863442b33
  ],
  [
    0x25c999356a5094ca3c5b1c50735340a8ce1b020f1b24581088d63d030465b6a6e66645e056254c6c26467445ca5d253,0x8f24e15315a95476b1487ca9181016b919997a9b49951b19711d29d59d8a7429325615098c14f1ae1c1aa65b9999191a,0xd05b52062b83b02c650ec6d1ac1088b3371caa3c94c56a531c067456c0153339338b181575e2ac2b32404758dcd6272a,0x729749b41951021b9ab344ab258a6655ea5625c454a74245583864b81b49741ad16c7b1901598b9231c51322f4932ad1,
    0x9997915a9b51941d59749509729d11b19ac96c70c1956d064631740138759011a2ae4181016d89b919997815a9d59509,0xb1104573290222ccdc5aa6f293272a50768151e22dd917a9589d49b51d19711529b09b9a981959741ac1181016d89b81,0x1c37290066e51c749019d15b018c6aa494202ad0bb03374424ce25620f112ab1ea860405ab2b625e45d242705c6cd19,0x27467326b86305b45d296254a9cc93c550415439ac0352d4b0094acec0458d6701154cdcb07ca9487a876871811d699b,
    0x6647586566d47447326b863064241115ce45294f15897317a95417496c70457327060475b646e06665ea7586546d664,0x44cea9331f284445eb742644453066a45414c98c102b8727338ad86e06b48237311c088973716a9ca94c9ab08d7666e,0x4538630410a5cdc53257421dd99b919897a9581561b41d51959749731d29b199115094f1ae18c16c7108cd5d050746b4,0xa5d45c2b4a80ae1ca40468ea914c9385bc6326b06d8804758ec1811d67a9d91d290ae6609356a665505626d86e06c66b,
    0xc6a8ecac7b620c20427b58ab8b31ea0420465aa8521f21c2046592072a420865b28420445b2a521ea1c204659999515e,0x6f14c9531d290ee302900ba34645427828c7088ba3d010acce4182042796ab6474a6466c46e68422bcb403435a935640,0xd050746b4029cd4b01132ae4cc7a8948718204b796a5525c25bc53054c74a6446c66e245223cb404395690308219e5a9,0x6d18c11439917158b545cc6c46d66b8ab13155e256a6d85d055254c74a6426c65c45bc6306b4531c52c68a4b81148ca3,
    0xd6a81181016b6270ad29d896f18c9ac14e15315a9d59549011d63b01132ae4a13c65d999917895a9741509d29919949,0x66c654055253882c6c0dc7728f2188762716ab4a75476684233ab4141d1ad00373524cc74b1ca1687a878873a1347081,0x1c460dcb47721420d6789581b617515494e1ac11a3a11736a75674294a5c0e5c9bca31c3075534042d2b9050835ad865,0x5e560913ca5c9d4551f2a521c60805b6a6e66d86c46466547427565526b053856066254a5c05e44304659585326b85b,
    0x72a9244dd45b1d31c440dcf48f2181016d89b99991b61d59b01919ad1ce1d117096c18c90c895671ea96054a818c5ca4,0x42474995304475691b1c1194ae40c1196d62749cc9ae11811d6d91b819997a9589949d59ce1ad1b61b19701529d09046,0x11d5a46c7108cabd050746b4cc7ca10c2196b62749ac1ce10c1196b91d61b59ae1cd10e1d5072c094a5605ea5c481766,0x12a9017a2a2474a972562ae18d1182016791729d11da9d59749951999571589b61501909b19b818f1ad14c7181754d01,
    0xbd549162540410b4ae40c3116b19b914e1ac1b625727498f1182016da9999589501909b19b81791b51d59729d1105e,0x6890810d66b14870820966a90820966b1487c87141156b819917a9971919b11b595618c94f1ae16c1709751d49d99d2a,0x901b19509d297117817496f18d1971d59b53562ae24c70c1d54d052328f4101d5ad00373524cc74b1ca1687a87082316,0x2d58ab8868550dc8f2772951062d43b008b566c52adaa088d2bd052328f400dcd49010b4ae41420d6b62549ad11305a9,
    0x5099019595717114e18f16c1ad10f1b1071ea9d274a754766852338b4101d5ad331f28420445b2a521c30465b427566d,0x5a95076b1487ca91a8959571ac94e18f16c174905a166b01883d6c06ace0b160542410b4ae4103156b89991581b61b19,0x163c11d25cb3895860af155e25d46d26b45b04189ea1cd628f2959571cc94c70ca1acd0088dcec08d11e9002b58dc72a,0x8a3c95c531c52847b408b1ac90322c59c0889ab71ea9624504559d4ae4b44860405b629d25b46b24382e45c782b028c7,
    0x54cce4ce21420d64e2d6254768181e46db82972d0a701749561ce16d1ac98c1168959751d197096c1cd1ac9032b0b735,0x30277405c0b5b244803958e472e40d6d1ac9b51d49d92b9a772d1ab029819598f191204652b9131c3444d7400bd15900,0xa6c06d66e265c6665d46b4630430865b667547426c66d26e45ca5e254056a6606565dc63c6b05b1c51117b41542c6d06,0x47566d86e46c66b0805a175cd120550e69014c4d64044573913c9dc951f2a521ea1da1c50455b645ea5607527465c254,
    0x67647326b8468ea3746803666a48c74c7110373d0621d8b404477291bc860405b626665ea5605c254a6407385b463265,0x405b626e05e47565d265466656a6427446c65405ca402ee52400eaa392d8b386b1c10e55a48c70455339168c5375874,0xa5605d45c254a6406527567447626d86e46c66b0738460405ae46665ea5607586526d65d46445c254a6c074676273446,0x7aad2a00bd549060475a30a665ea5405626e06c6b4a75676483234574141cd4d04232af4044cea9331f28460405a665e,
    0x82196ca1081116ca9487a87081196128751919501709b110d598891386b06d895c9bc632c4232af40660eab03306aa4,0x95c9bc634531c406acf400eaa392b1c4a43cb40e91a2d2d88308109ed62ae2cc7a81081196aa1487c87081196481ca9,0x5295828c7042b3390508121ed99b919815a9d51959501d29b197118d16c104475672429e29dc95253c21b6e66c49c0a6,0x182016b899997915815494f16c1771951d59709901d11b1918d11a914ab6a460656b41a98d0d010e55a4aa62c5daa702,
    0x66406626346b06e46c68111dca40ee30291e0c0af18a4572b626f24c70c8d15d04233ab400dcd4901132ae4cc7a89487,0x7a9815da9b999918c16d1781589b51d59529709d11026a8b92c0646e529dc958ab884791b76656a5d25c454274a75465,0xa5c253c6b85b05dc83421d6c35e885b51b1991115c38292e09c053c5b25dc958ab8631de4432345740c1d54d01132ae4,0x8ec060ceab002f4564cc74b1ca1687a878873810810d6a816a622db99981b51959b0191119ca11936a56255875274654,
    0xb596f1ac18d19711610f2b0587342cba2182056da9999d59b41909d11b19701789ae1b915a15295494c7141d1ad01a32,0x454a5326b85b1c460dcb404695a91dc860815b6a75674294a819856a49726f28c700bd159002b58e40c2116792d51b11,0xb995a15494c1ae1b41b11919951d59529d090ce95092625c05e4460805b6a6e66645e25686526d47565506c06467425c,0xad1b01ce1d119198c94f1541110373b264c18857ac0b032bb02303d640ce12a9002a5cdc52a7aa587ca9487182016da9,
    0x354902730a64ba2ce2ac26d17417890ca166d002b58dc50718b12ad02645d2c72a1830d6d99ba1d49b599717517096c1,0x29d05e255c5b453063c4616345cda2ae2ccb0b50ccb2c0860815b646667526546d655c53263c6426c47464039c56401e,0x453855c56242a708f40e91a2d2d09409b1c077232cb1b141d1ad01832aec068ce2b002f4564045cd49331f28430465a5,0x414358ecae25a150900ad639030465b666e46625ea56855c5306b86d06445425c074a7546565d263c460835ae863c6b,
    0x810d66b14870820966a90820966b1487c87182056da9b91999789b59751d49729911d1906615a925cac09b063253c55,0x941771b09d11529549701ae16d18f14c10c454e7246de2664440756b4068ca3b01833aaccc74b1ca1687a87082316689,0x16d89ba19997915a9741d29709911b19b51d59ac94e15495026f28c1972058d15b01a328ec00bd159002b58e41a8b59,0x5527445ca5b463053c6b86d46c264654044283d64991101d5ad01832aec068ce2b01173524cc7ca1081116ca9487181,
    0x159955ca505d474a63c5b05c25ea6c4646664442b31740c1d54d0117352450100ad639061005b6a6e65e256875665c5d,0x6d26c464066465646888aec1a30a9b06ae046c09e948b0239ca1cd1904652b93689caa3c96a53855c541dac521f2a56,0x9717117415498d14f1ce1d5107262cb0181eaac04475691b1c606c6b40f1a14b2b1c1a847ac00ab3371ea86a3345b26b,0x66507546d643a21cac022771b168532738403728dcb120d6a44903505c645728f1181016d89b919995a1901d19b09b59
  ],
  [
    0x46665626506d65d46c05c264474675263c5b073453855c83829cac070ae2b033285a400eaa3906c2e26645d25c074264,0xc531c14c6b24014373901426adc182056da20c204c7a40ab04206ccdc7aace25a15294c719032bd151da0460475b686e,0xa973714a9ea961f2a521ea1da1c60815b56b686e65ca5e266464654056a460405b629ea5685dc7386b25b45c254a63,0x7326b86c06d65dc5505b459990b6e8ab4738414358dcd4a6f17515718c94c706215eb02a0ccec08d0e691c2422c4d64,
    0xac1ce1045d1a72c643151d244f15496d17717890ca166d002b58dc507099174b1ca860475b686e466664474675465263,0x26d46467447566307326b86c083306aa44f15416d17717890ca135d01c8476c182056d91ba1999941d59b51d099118c9,0x56729789da99935a2772b994f1ae18c16c7141cd4d0163456c060cabb00333564045d1a9331f28440475b686e666465,0x46305b253c550414358ec084ce992b8968542402b58e41820568d2b12729791da9d51d1a054c1d90119d524572749182,
    0x465aa8521f21c2046592072a420865b28420445b2a521ea1c20465860815b6a6e66625e45dc6d46567526c07465ca64,0x8e4d0d6859999098d1941d59b51b1a00caf29011ac6a4ac71610f2b056468acba20c2042796aab8b6874a756731ea042,0x58d15b01833aacb0100dca39011746a4cc7a894870c208679c05e46305b24035e89cb19b4a5434f2772050ba3b002ae,0x66545b263041c23a9c772ae2da94f15a1d09d59529549050d63b210f2b5d055c6527546d65385bc6306b46e8821742f4,
    0xd5071cca6464665c8176642cb1100d8f29231d2c7285a1ea1e21cea4d84c1c20435aa0460455ae66625e45c06c46d064,0xa521ce883b6e0b4aab85b073253a568550542402a5ce48ab235d99b817895a1751d49b59541d295094e9ae16c1cd110b,0x845b686e66645e07526565d46d07346b86c47465c2414c5d2400e563924c9ba94a55c562531c6062af402999ab231f2,0x116d99ba1d49959571931b19ad1ce1d1150912a1999017a2a2499375178ab425826c714b816d062c4ab400c57391ca85,
    0x375694ca5c81425cec02b8b1b13a9ca802a5ce4102216d99ba1991789581571741d49959d11509931b19b51ac1ce1142,0xb0550e76b06d45d05e2960ee88d42676e06d45d05e2968ab8931c614c6b405581eb0066656cb1900d8b39231f2872958,0x5a1d51909d19ce94c9ae16c172974905a174b005a17645410550f4b019560dc06579072c46d681ca562c532972050973,0x297a2b0039d8a46c78c74b1ca1687a870823166890810d66b14870820966a90820966b1487c87181016d89b81999791,
    0xae25a2141716d2c4c8d7666e85627546565dc54a7425c464c6c66d26b453873a41434adc5427819911017aad0085e56c,0x240a7469cb59068716b01c1caac00e71591b1c2066af4019995b01a22cec0c2156ce94c952a0ce12a90055e864542782,0xa5cab896855054c531e31f28420445b2a521c308c596854a55253073a6b846a25c5d455074a6465cc6c454253a6b873,0xb59531b09d19d8997199991272ace9ad16c718152bd05c438ac1468d190505c59cba20c31567297496d1ce9050d2b71e,
    0xac70819abd0066656c00d8b39030ca5ad65c46c26b473275476694ca5c6646468035cca4d2a181016791581549741d51,0x92b1e31dac521f2a4533356c442163c645a24ee225d91ba1999789581571941729509931d19d49b11b597514e16c1ce9,0x46d65d054c55265c754d689cab385b444a8bd76864c66665454a55c5625ba734531c606b534019b94b0086e6ac00eaa3,0x931d11b19509571d490b3829b00ce546c084af1916893a7385b25ca802acce400eaa39040475b666e06645e27426466c,
    0xca457293252a1811565a29827297917414e9ce16c7058b16b2b1c30655b40708abb0614111ed99b89991781959751b41,0xb9ab003ab8a4ac78c7681181016d8a9325a15095717297497916c14e9ce10c3296da1589cc94e103156373547468035c,0x7915a1771951d59b495414e9ce16c9729931d11b1950900ab3390308a5b687567425ba73453854a9cca5c4182acec021,0x27446465cc54a6c2415447a410b1aa900566664982ac25410d11acb1e4430655b40688b3b003a3564181016d89b81999,
    0x274675242c0d8ec0f52a0b0216179c78a58108d0e6d0614b5341052b3d2c1f2a521ea1da1f589836e66d475665c5ba5d,0x6e90746a87266ab8b68756644742731c037389c142116da1b99991b41959cd1ae18c105695871ba5d45cc53254a55c64,0x6a4b4173540dd91999789581549941d59d099118c96d102979471dc94c9ca93a41a14cdcb51ac7ba257310d572529731,0xd0176641cb0777257310d8cacd100dce272c66444031dca4050973715c9bab4a9cc941f2844a5e5560a3064274441b84,
    0x541181156b81989d51b59941919d09d997915497296c9ce98d14c7062a33b0277181cae25a108d0e6d0614b53409d1a1,0xa4157461cae25a15494c705d43470037389c05d98270308c5b646665e25ca6427465b473a41ab311cb81d498c1951b59,0x81196481ca9082196ca1081116ca9487a870811960c1116791729d119096c9ce98d10688d672e86d46b095ccc15cab3,0x919711531b09ad1ce110204a79ccab8b3a76874654a55c531c2d4b1245810b0363d00c6a8dcd47a81081196aa1487c87,
    0x1c0cd5324034559913a8408109e57273252aae2ce9da1d070f0362d0408111ed99ba1991789b597716c18c9941549d29,0xd019427ac00dca372c1ea2521c608109eba1999951909b19b497715418c1ad16c9711531589781d910c20427ab8b6873,0xcd1181156d527916c18d105598371d2dccb3a94a55c531c26459ac5a20c1116732cea4e1529571589ba1b59ac70cd0a6,0x4e9ae16c1cc9d2971153100a9739242457315568ab85b441558d1c73257205d982b231c0363c9c18115679295291ad2a,
    0x8ead002e65640458b39231d2c7285a1ea1e21ce84d1c20435aa072a6077666e46606566d075441ca562c7895a1771549,0x4c1562b535aace9181016d89b819997915a9771951d59b61709931b19501549ad14e1ce9d1204475691b1c52235b4188,0x1c508359e0ad8b3a5b26b053856a54055240465cec0439569002e65641a8749d19911731b0108d81e9003356a4509ae1,0x754b0111d5a46c70e0372b1ea887569664c280dcec08c15e90039d5245aa6ea4c71888d5d00a62cec00d99a9231f2a52,
    0x531b01711d0991906c782901ab3824d62b59cd1181016d89581d59d11709751531549919971991b61b99b01ce1ac7031,0x256a66265681ca316c02a999b140810e55a4055983915ca4c810a5ce41a8951931d19509571701749b11ac1ce10e8549,0x273a8421d59c991b9bb62868cd5972ae25615315894c71888abd002e65640458f29231f28690f295e0ad89ba6b073853,0x820966b1487c87a43ca5701509581959989b99b11d1900e5639015a88e44e2ac1b6257293204297390604059ea56076,
    0xc7447565525406c273a6b4531c0c5d52c00c79590035e8a46c78c74b1ca1687a870823166890810d66b14870820966a9,0x16b89999791581771951b59d49701931d19b11509042d2b936a958ab8734460405b626e66645e056a6d865c5d46465c,0x71409e043c0d8b40756a09356c645ca340167619158860405b62ad8a4c9e056a5c25dc54055253873a6b1c0c5d52c182,0xb1904571690119caa46c71488d6d002e65640458b390518101eda9b91999589b49951771709931b19d11cc94e90f142c,
    0x1c60405ad2b6296a55854253073a6b8461005b6a66656065c7566d25d45585426405cc74453a6b87324037469c789b91,0x2e88b92d8830c559ea5b473a4067551c74905a135b00ce98ac00d5a3925c9c0ab895854c560531e31f28420445b2a52,0x25405c25e06565d455c75264c6c4746734460405b62a4c9ea56054255c5c05d273a5b1c112bca4ac70e9816d06a630b4,0xd002e6564143256da9991781959d51cc96e9749931d19711b09b99571589501042b339002ae8e41460407b6a6e666456,
    0x5e8a891d241684d6c532972562143256d99b919817a9589b61d51959931501571749d09b197114e16c1ce9ac71888ab,0x8b400bb9490032e6a4ac78c76b1487ca9183016b99981791589b51d59b09919701d116e94c1cc9da9182959d066a9834,0x42b339060475b646e06665ea65c7566d45587426c664454c5625c05d27385b446040596a7587467625ba734531c622b,0x6ea5a90889abd00465cec0468ab911b18d7666e06645e26565d46d25c07446c6415708e4d629325716e9cc94e15a9509
  ],
  [
    0xca4c4112ace400cb9a92b1e31da0430ca5b6666075865664c6c65c054255c732538403958dcd1208d11e9010ec5a4ac2,0x59e2b58ae05ba73253856a6c26d65405524046ccec00bb9490631ab6e06666546d66c45405c2402ee524d1a05d98291d,0x8131eac1b8a0889abd03845cb418b162d058730b406b990b25c9cc404e1d6400bd15933895840465cec0458b3905083,0xcd18c906a98372b8b586566d4c52c29b41910ecd015439a400bb9471c2414c4d64042973714c9dc951f2a521ea1da1c3,
    0x37409cb1901d47490159d8244e95896d17a974905a166b141c3445d34732181016d89b999817915a9911b01d194c16e9,0x7326b8435a911cd11056760913a5605b45ea5d241684d6c042b33723b8857666e06647586566d46427446b863073243,0x255c9d4ad899982b6e66d49dcac0a30ab895854c531c28457ac0b0363b161f28604e9d7666e46627586d66546c064663,0x733a9ea764c2af181cb627325015711a3a8d70ad19d4a8c901197371dcab895854c531c2c43b2c08e11d91a13535cc54,
    0xaa1487c87081196481ca9082196ca1081116ca9487a870811960c1116b99981b11919951d09d597498c9ac16d11a9710,0x507a894870c204a79b0831a2a5c4eada97910cd0a6d0314e53404553370408111eb0710635ad0408109ed07a81081196,0xb817917016c7159982d00c656ac0439569017a05648c704297371dc8304459e0a40ab0402ae8dcb62732cea5714e15a9,0x911d19d514e9cc902bc8c72c06d66e45e05c28031e564562ae1181116da9589b59b11d19ae1cd14e9561d4995199990a,
    0x46b06c481735424b625a95494e1ce9158ca172e6450a62f41888ead0566643400b9959011a2ae4aa0675da9999589949,0xa7447525cc5d45e265c6646468039d8a46c70688d6b01c23aac00d8f29231d2c7285a1ea1e21ce0420435aa04304459b,0x14a8c6d01583b245495010429ab9030445ad66c45386b06e896a9e273a440c60819b666e856a6d65505426c06b453873,0xca45aa6ea4c70708d5b00a62cec0468ab9231f2a521c30445b5465c6d66c49d05cc5e456a53873a5b26b06e8454447b4,
    0x70ad49d190ce12a91ea962450845b686e666475265655c54264c7346b86c474642b83324b427017897520a0373b0031d,0xa762ee8b38ab1c1c2356c0509abb011a2ae4182056d91ba1999951b59741571501931b11ac1ce16d100e7627023ab81c,0x8460475ae45ea6c67447565c25d465266654056253a5b046b1845c932571b431858d19368b32460405a665e45ba53256,0xc22aec0429ab9060835ae8962460815b6aac09d05e27345ba5c48210dce400e5639168ab8931c1c22aec00d8b39231f2,
    0xce91820567a9d59d916c9ce9d09919989b99161583d019aa0e49725495314c70858f19168860835ae8a66562538ab1c1,0xe76290418d6a49997916c78c74b1ca1687a870823166890810d66b14870820966a90820966b1487c870c33167aa6c1,0x86b26e896ab3a80354cdcb120cc0b590318d524789181016d89ba15a9d59b49951771541b19509701931ad14e1ce9d11,0xa521c60405b626e856a6b253873a430b1b1c79170a05d1a291dc9b0a5055264c540410a6ae410635a9266430455ad653,
    0x6a49991820d6ba2589182056daa932501571741789cd16e9712085333901116ae400e56392b8968531e31f28420445b2,0x4531c1c2b8ac00eaa392b1e31dac521f2a4533356d66e27466c442163c645a2ae210354e71c280362ce40429ab90418d,0x81690212bc647aa5a24e9ce16c700eaa39060405b547467629ea968b385b444a8bd5e2a4cb6856a54255c7467525ba73,0x194ae400d7329060e1aa44e1cc9da25aa181016d89b99991959d51b490ac788b1d07465c46c04357422493257150a0cd,
    0xb59b89b11d1905611d91c0ab08409d39c9319415095710509abb040cdca49990e8549b0970191153103285d935474641,0x181016d59d11d8a7aa5a2ce16d118205678ab42da15a9d59549501d096e9cd14c7070aa3b003ab8a4ac78c76814c632d,0xb8295ccab0a4065c54255041426aec00e8d59040cdca49991820564e1cc9da25aa0c204c79ea96893a7385b1c1c2a8ec,0xa1d455c6426c65405cc7385b1c380dcac0e60a9b011a2adcd1208d0e69022c4d6400c573913a9ea961f2a521ea1da1cb,
    0xcc9ae1306a9d789901991959b410a88ceb00a62cec8c700e5639131c280dcec00c77291bab195a17687567326b863044,0x46c66d06564086acec159132b2e8b386b1c0c656ac08e82b9231e1ca875e46566406626d06e66c442d44664da1d51d19,0x9266ad66c4746411a2ae408eb0392e8ab073860ce956e6b68656752746734450845b666645e27525d455c5405cc64274,0xc5525dc5e27345ba5c480362ce48c700e5639131c210dce4ae21820d64e2ba2587ca1aa66459415719095017310abd08,
    0x571b41b99b126d1ce9d510b182bb00c656ac8c23a354598a7a97715497115316c9ce9d090868e99060815b6a74275654,0xd07a81081196aa1487c87081196481ca9082196ca1081116ca9487a87081196181016d899917a9d19909959731749501,0x45325b05e443c6c43409eb08b00d2b464ae2ce9da15a90b0363d0418d6b40720ec90039d89c046b1a73544408109ed59,0xa6b85b45d083846aacb020d418d91e243445d340720ecb010a6adc050d6371cc95c541ea2521c3a15c6c45405cc64263,
    0xc1116942702ac71620f1b05730464ba2cea5a94c70560ec91dc95263588b76a6e66645686526d464674475663073253,0x51d18b6e6a4674275671b1075e2b54642746731c210dce419ca11936aab89687511956506d66c0a325b045c5c41cd52,0xd29d91d59b61b995495a198195174178ac87084a73d01d056ac933887058956b231eb1ec1ea1cea4dc4c1cb1c20435aa,0x81b1ed0162c5acc9a88718195ad01560cec081196c9a1810167915a1981952d89b99b61d59d11ce1081096711501ce1,
    0x854a5505629cc5e05d45b25aa450475b686e66645e05627526d86565d45ca64074473a5385b24055e31c5435326b1487,0x89acd1c8710e15ad0304c5820445a26b2af31f41c20445a40744420425b21c60805b686e66647526d865664074473a53,0xcf44f1ce16c708195ed016255ac8c7ac7081196b826659827425016a94b14ea0256727256ae66d440b8c6ac887081096,0x181016c99d8a792d52741019ab4b34a820445b646e66605e25686525506d87565d464c54a5c074272a6265ac521c4151,
    0x45606526d65586405c25d075453a73874a94ca2c726521c422bcb40352d4b2b21696e66d880ce546c54a98ad0972b687,0x4dd09609e2b26a40621c2161cf418195ad02042596893a73874a6267227566d86e69d4b648306ad34054a33b24c84c1e,0x31ab221c20425a26b34721c43856b408111689acd10c1316cebc8708ea23d341c20445a40742420425b4a721c599955b,0x487887c87081196181016d899917815a1751541d617315099016c98f1cd1065c9871aa52c53a8521cc9c95ab99b4902e,
    0x5b4a860405b626e86d67587446426546665d05ca5e454c55256073a53863c5b1c206bd34108ab3d0066ad2cb01ac76b1,0x561b41b111055999053a2624b9a9919598c70c1574d01815cec054a33b0172e0ac9320c10d65328f24c7101af2d04044,0x4204859aa521c208859aa4404359686d65425507585d46526664508459e05627545d25ca54074273a5b446b1845cda2,0xc157471d25e44306ccb4031ae2b2b8460405b4a93c9ba5cc9429d25e4762462235741488b3d06063ab40688d6b231da,
    0xa63264c6546607567387427646d86e65525684206bd34188aa3d043466b4b01ac76b148789a0c10d65327296f1ce94c9,0xc66465041832aec066ad0b34243046594c53a63c5b45ca642c19ab42cb01d11cc7101af2d0404459e25d05c454a53c5b,0x59687626e66d875673881794a1c542d129519817497910c1ab4d043466b4060ab3b2c06b1da04e09d954a53c5ba63264,0x93388708ea23d00a666acae18c7cc7d07081096c871012166f293272a0c10d673252ad096e98f1cd14c7031ae2b06040,
    0xb49561729b115016f14e9689101116b89b51749b01711781959991d61d995295415a14f16e96b14870c8d15d0153562c,0x561b49b1190101cb9191cc54a5ba53c4079531c7917416894870c1b32d017ac42c182016da1b81999791589741951d59,0xd2bb040445ac0644621c1625cac101116d99b89981791d619595415a1911b01b51749681181156da1b81999589951d59,0x6808e9cac72a4c7021b9ab2b1c30485960d4a9cc5ba5e25d45a04304659d05e453a6b85b25ca94c9ac521c3234574050
  ],
  [
    0x7a156c01674cb14a9ba634440445ae85e25606d45585d06526c06445ac62052254ca3c5b4c4791a2c188aa35266b6475,0x8a56b66758804e5c6c026559b1ca9bc531eb8631c32358b4cc7101116b01528ccd9317016b206e11a5158ae86c46d080,0x941999108772d0419567405e544b00aa1cec066558b14a9ba460455ad45d05e454c55252062c5a241833a9418bb02516,0x5a98ec021b9ab2c06b1c0a052ac264040c060ad2ac0642621c21a5674058972b015a562c1811d6da1791d59561749b51,
    0xa666ac8c7181156d99ba1981791589b51561d499596f18d16898b148153190905cd4291ca93a4179511c05e0ac51d080,0xb61b099011010d6d99b89991781d49959751729b015096f14e94b168906e8d05168ad8950a4c621c21a1af401e855b00,0x2ac2640450475b665686e26645506d87526565d45e0ac0642621c21a5674058972b015a562c32e0d55a1681489542b81,0x693ca4c656660631f26621c20465a2c7265a1c20445b2a626420465a2c7265a1d21ea1cdc4e64504759d4a5666476675,
    0x8562423847741462d4d0218caf406e898b344411a56a4532181016daa6e9ac9ce1058d2a71d0940410a57a4021d5a72c,0xa5574250104295e916ab3a4087569c10dcc272c69bca4c656660631f26621c20445b2a6265a1c20425b2246043595053,0x781ce94e15a9d49959751541b61901b19509042b1e92b45b1c238477408632bd01a23cacd1104695a9010ecc9c732626,0xd24ac76b1487887c87081096c89181016d89ba1991781959b51d61749541ce94e15a9509901b19ac9182016da1b89991,
    0x16daa181016d89ba17a9581b41d61751b19531701d11909959549ce94e18f16c711115eb04c0aaec991108ab3d010ab,0x2166a91812d6b815a1d61749b51701509541016363b015ab82cd12023ab19256ac6a4c83043594ca3c931c112bca4181,0xd11709751549941919b01b590ea988b2649ea94c9bc73a6b4531c62235741488b3d00a666ac8c76810812166a9487082,0xac76b148789a1812d65435a2d62011973b010a57a4043b3292b84604b5a646e0568c14e0d6c732181016d89ba1581d61,
    0x7097418f16d14c7b81148ca3d00a746ac043cac9331c066ccac044af2902a739662c18ae62c044a9e923c94c410abd24,0xc6526d06c664454c742407aa864701751019d54b010f2b241a8d19b11b597515619317015096e98d10c11969027a9531,0x5585407426c6433740a49327a97497116f14e9ce18c7050ae6b00c6b52c043ab492b1da0450455b686e466075655863,0x7895a9d59751949b41d09b195014c96e914c7907244851a3464ba2ce2561053b84b1cc860435b646e86605627566546d,
    0x256a7526d66505585cc6426c47465405ba63c734531c266c1b401cb919017aa8240588b571d44066ccac0c10d6d91981,0x2732634460405ae46d65505426c06446526605687627587465cc63c7345b1c4215cf40f032ab1ea860805b686e06645e,0x919ad1ce1d11d59b494f15615096e9731b0101d39491d441626aac04589e9231e2c5a1d21c20425b21c30825a4c5405c,0x5e46525d06d46b27384117469cd5ad11919b0108d0f491cc96a55854253c9b1c11627a4181016d89ba19917815a9941,
    0x4f15a95615099319599818c788982a39dce1ac90e2a317260642b46a5683c22a6c06a998b1ea94c93a860405b626e866,0x5a9b61b01cc94e16e9709741792ad2102d5972604440eaf415098bd0646563405599890045dd1c547532598a65d1a6ea,0x6ea5aa0c8972d231e2c5a1c604359ea9624304359e2b6896a5ba7346b8531c5460cf405383590046ccdc183016da1b89,0x29cd4b008756ac043b3293324504559d4b646e85586d06c47386b1c62235740298b3b011627a44e0d4d7325615014f2,
    0x82316881a342d5da2982b427325a95615016e9142116da1b919897a9581d51561b41959749531901d19b097116f14c7,0xd49b41561b115017097510588b5b03b01cac0f4342b04a1e46c0d6868b043466a47aad1a4ea6f29319599818c7889687,0x542410ac7a40c219691a7a9d59749ce16d10c21965aa6e9cd14c7031ad4b2b1c10ecc9c7321810d6d91ba1589ac9ce1,0x4f28c7c998870811968b1c99687081116ca98990811968b1c99687487a873a93590823168814ee10d982541011b33b2c,
    0x405b626e46665e05685d45507585ca5426406c66d274473a6b85b1c3214d740888f5d016255ac068533b019856a4972,0xd24054b9892b2430435b589685406b8531c142ccdc572142156b995415097017895a198191ab12752d9214e518d34a86,0x445b2a6265a1c20425b22430485b685d46466506646e674a7526d86c4b344304559cab3a5b1c5054cf4101b9ad002ea,0x74454a6406c66d440ace8ac0539a8b002f589c70b0c88b5d0621d8b4058956b01a22cec06615a925c9bca31f26621c2,
    0x29ca2418d6a093684605d53481d58d5429510607aab1b1c660c5741583a2d1dc86c2e86665e456075873a6b25385525d,0x54b98915c9cab3a53863c5b1c162c5ac00bab492b1dac521e21f21c20425b224308259586d265075453a6b873274a86,0xd628f25715a15014c70c12168f25720e6a50b1e2f4a860c05b686e66625e45605d06547526d86467445426c041558d24,0x956b050845b685e05626d07425ca5b473a7545585d241626aac8c70caa26d006ae86c501062a339018ee0a49720c10d6,
    0x14199ad01a235ac8c76810812166a94870822166a90c2096da1b91999781589b41d51561d29909b19711cc96e9749058,0x60573b1dc840475b686645e25606505d47526d86467445426c06e6454e6234033354b003356a457272a6f1ce9ad14c7,0x50190999a1588b1d0172e0a44f2772050973b003ab8a4ae11709997915a1d51d29709911b19501549ce16e9ad1b61941,0x4249724f1ce18c7022a73b14aaa83336d89ca95c56854253a73863c5b1c322a9b4ac76b148789ab1660db81b19b51941,
    0x263c5b4531c50746b4060cabb01634aac00cc9d9331c306ccb40c1216572141196ba1b4156158ad9ab1900d99a9018f5,0x52a168b11901951729741d195094e98f16c77910c1d54d01832aec00cc9d9050465ad0a5c94a9ba63444a1d25ca64054,0x1c222b9b4181ad4d0182acecac76810c10d6d99b819895a1571d61d09b197017499414c98f102a8737244ad440ab466c,0x805b686507545ba73253854a552560b46ad86c06e68660d8b4118b91d1dc9ad283542b525d45e2a5c9ca9bc53a73863,
    0x6c7033354b1ca860805ae666255856076875294a9dc7465c25ba63c734531c386e42c0c88b571e44306ccb400eae2906,0x6a48c78b1687487081096c870c2096d99b819895a1d11b19b51971901509541d61749cc98d10c1196b9a771d198f1cd1,0xc22aec00e89d9060405b626e06665e45687586d25d06545ca6407467346b86c454253a9bc95c81625cac00e89d900366,0x8891011d6d99ae1cc9d61d11919b010550f491ca95c56854253a85043596855280aa1cec94277252a4f26c70688d6b01,
    0xb9a92d8b52ab1c1625cac050b33715c85043595256842223d74068533b00aa1cec0708abb003a276497252a6ea4f28c7,0xcac00d99a9231e2c5a1c30465968ad2b58830485b686e46665e056254a5c27345385ba5d46506c064474641ba20e400c,0xd51d0a91a0868e99022e6a24b625a2ce1ac71418b3d01a235acca0acdd62cd1ae100bab471ca96854053a9bc95c81625,0x94a77252a6e9181156d99989791941749d11919b09b51b82d6272a5715a15016f14c7141cd4d040756b4cc9d0a745d99,
    0x315d0660d8b47721011d6d9a98191900cb9a93386b2402ecc9c97272a4ea6f28c78896870823168816a8c65d1a901999,0x70404459606e854a6c07425c45ba84615c5cd9a7899910c119656272aae24ea1a17427346b68666641c58466b4947198,0xc7265a1d21ea1cdc4e64c1c208c5a20430465860455b665507387526d86c06e2568660646b449e4ab1c280eaf4060ab3,0x66606c65c274a641c50666b404695a923c840435a56ac693ca4c941f26621c20465a2c7265a1c20445b2a626420465a2,
    0x234d03a22c741aa318d00d0d6acb5a1810d6da1b91589541d49b617514e16c1cd110bc1572b2438a8c5c102b9971eaa5,0x25b07345385607626b26e85c274a4604059ea5686546606e46b873476274a5c441ce50a4031715735841d6262cb070ea,0xc521e21f21c20425b22460405b6a84043596ab4a941f26621c20445b2a6265a1c20425b22460405a645ea7586505d455,0x4460405b6ab426446625e45ca5d280d4c6ac0234759256ac641153d244c76c7042774723c840435a56ac693ca4c941da
  ],
  [
    0x9ca5d45e0931c621c5741487a2d00a5e8ac182016da1b819917a9589541909711749d29d51b61068ce2b256ac67326b,0x91ab07181754d1bc8404359eab4a93c9cc941da04204859aa521c208859aa430c45ae8b58ab0734460405b6aac6a56ad,0xda9195621d15080b0e6ac044cea7241c4159cb41a02ead0581ac7495a181016daad097297497921286b1d00d4b52cb5a,0xb5ad1ab076b148789a181016749791729d09da9589ba18c9981181016ba19817915897498d1ac1b51d617294e1cc9d11,
    0x2e31ab0119ab1cd07d5a0c1196ba19815a9d615317299098f1951549ac14e105d58471d08098d6ac0454f4700a6669c,0xa64c5c454a53c4079435c7420607aab030465b686e05e456a5d254c5ca64463c7346b86d4558532a626509b1c4382774,0xce1d89ac1ba1b51941991781561729749c6b115ad2088973716a9ca80c9d3246c710e09dd0078d52c0466ac70357435e,0x58acc90ecc88723ca425cc5d25b483a7211c02999a703a22c5cb5ad1ab077aa1010d65aa6f293272a5076811810165a9,
    0x19ad2c1c20425b21c60435b685505626606e46d8ab0460435b68962558ab8531c4c0bab40f142c703c6a11cd5a1810d6,0x9895a17496c16b14894f1541d61b51cc9ae18d1887b820a521ed004cdd2c0234757256a4c7465c1c3225c9c7aa50710d,0x26b863064474676466244151cf4065598b010ead1c4f28b148718d0e2d00d4b52c6871810d6da158b8c1991183116d91,0x741b51b81ae2cca4f28b148714a0f4d060405b5673876263c6507446466646224604a5ae05686d45507586565d25b473,
    0x2e50b5da1d499595614c9ae18c1989911d19cd2042af471bca2c5a1c116279c4875aa72a0823168f2881ab460d8c16d1,0xc541f68731c098d6acd5a91ad070823168f288118204c7b68ae09bca2c5a1c52c2d341011d6d5a8f1941d11919991889,0x53254c5ca5ac811ac694184a9952b1c06758acd911011d65aa7290823164b18818f16c168a19c2a851d4a526649ea9c,0x549b618f16d17315294c18814b1689741019b94b0606b514188aa35030455ae86605e256a6d26545d055863c5b462252,
    0x9d4b64a60634430465a3c664621c31295b4014b8bb241c07a98acac7021b9a70095665c95a1420d6b819897a95a1951,0x72606344608059e056a7525d45505425ca53852c5a25bc7347686326646e26d840b8c6ac04551e7221c504759a052255,0xb89b429318896b14871a141dd04151cf405d584b01153d141411d6992752cd14c7142156d925427514b16816f110666a,0x8b1c99687081116ca98990811968b1c99687487a87399347181056371381182016da1991581561b41b8a7aa529b8c685,
    0x6ae86c00bba2906a2d65587425ca5d253c7385b463065c6c46466644406e6b4032a63b2b1c10ac79c507c99887081196,0x883aa622c7aad29cd2050735715c9533315eaad696053c55865c5c074a6c4646664631c02a675c042af471aa2635d240,0x74454a5bc7326b86c2646660631d31c3444d740153339050435951f26621c20445b2a6265a1c20425b22460405b6275,0x654074a7527344bd1515c4ee8b386b1c16159ac00c59d9050815b5281a23cac0538359011a56a4058d6271dc86a25c5c,
    0xb5a4f2971b119199918c704295e7141dac521e21f21c20425b22460c05b686e46605e256a6d665463c5b05dc5c46c264,0x45cab429d29b0ae05325686624440dcf418294bd050a667407281db15c9eb1116e05ea7346b85b05d45c274a40b8c6a4,0x873d15c860405b625ea7546d65d25c074a6c47385b46b06e853c56055865c646664631c02a675c042af47060405b6a5e,0xa579c5076810812166a94870822166a91821167a9d617496d1cc9d91d2a702b815a14c1ae1101b9a72624440dcf4142,
    0x273440ab18dcb19b5195999190a15e0629051166644f277105aa26b006ae86c00bba29050495a56ad86c66b1ee0a31c1,0x4f1ce1045d1a7160ad6a46ac0a31c628477400a99d7010b3b1c226a9d7aad2a70a046b1a9260ab0a6419b5ea5c474a5b,0xd1c00bd54716a9ca941dac521e2685a1586406c67445ca53c6b05b45dc752654408b336cce162e855772ba15616c9ad1,0x9260ae4b31c42857b40c8956703234a9c7aa7a9885ac1ba17817496d20a88f173466c46d680d0d6ac90108c15e9010ab,
    0xd5ab62014373b244c387542c181016d895a1d61b599517499097116c14c9ae1b01d19156318923c95c818b562c043cac,0x6c98f1909b01b59ac7058566b131c050dce41410d65476811410d69895a19717515498c14f16c9ad1b81d91b19701d09,0x26d66c483814a6426c06d66e4450746b4cc70c1b32d060d4a64da2142056d91ba19817a9589d49951771d19711529ce1,0x9095015aa0ce42cd04a56634016ae17346ad641a139ac0464ec9060805ae06625e456a6546405425ca63c5b25dc74675,
    0x44282b39c0226757008e9c9c00eae27256b4642383b245aa72a5078b1687487081096c87133a8dce2ac1ba1981729b11,0x4c339512405aa34713c9dc5b1dc1c6283b347aa181016d89ba1981791771d51b495618c96c14f1ce1045d1a72446c06b,0xda15894e10585357334814ee11c0d0971715c9d44414305eda1b81991589561909b11b498c1cc9ae10f0b117346a56b5,0x88d2b716a9ca941e22460405ae06566646c2640746762568552414e6a2c8ca043cac7002ee51c4f26c17711810d6b62,
    0x589aa703a7441cb5174714a11ed03a44cac0c8b1671ea8662b253863c66074664465680d4c6acb0108d11e9010abd1c,0x911959571b09701ac14e1cc98f1181016d89b819915a1571d61d19b099019594c98f1cd1043cac72b8402ee51c7116c7,0x71bc95c531c62c2b345aa72a5078b168760c5adae1b82992cd202a8737016b4a1cb13b491810d6d91ba1981589d61d19,0x2dcb09b5106b434b016ae11c09897171dc95860ce956607346326b0408ae65c95a911d19b090456b490239d124053a34,
    0x5bc5d455c538802f589c0ceb027256b465c1c3a42d2c0ce0ac91ea86c2e86605e27527466446566b07385b463240566,0x2b991715c6d85d2440445b686626546467427566307346b86e453c5606c06d25585dc5b1c52c29b400bb94705047596,0xb026f29719199818c74c70d1135d0054cce41410d65478896870823168811812965a14c1ce1ad1053b84723243425c5c,0x27686605e256a6566447466c05425ca460435ab873476854a5625c45ea5b1c66158740538359015a3164772d4c685d5a,
    0x1cea4d64c1c604158e04208c5a2043a2305bc5c474264666456054a6c06d241a139ac0464ec9050815ae46d27546b873,0xac718152bd002d4d640c20d69725314c70589aab231f26621c20465a2c7265a1c20445b2a626420465a2c7265a1d21ea,0x509931d11d89ba1b19b490297a2b33a5b25ca402ead240c4216972d29531709cd10c1156b62da1581729789741ce96c7,0x6d855c6c674473a5385b05ca5d465064c9429e2b52ab1c2223d74058956b0046676c181016999791581d61571741951,
    0xaac8c7c99887081116ca9899687081096c89128741931b197115095715a16e94c1cc9d2a00bb329040435b686e466656,0x805b686e26665e45605585d074a6446c654273453a6b86d4752c19856a4732971060756b00a5e8ac6c71888ead01626,0x2d6da29727417317895815621410d6b61d09d515295494e1ce9da258297274173178aac7141716d0205eb34031715b06,0x85e45625585305b25d06d454a6b86c274473a4587309cb9a73297198191a0758989352816255ac01199db01a22cec141,
    0xd89b91ae2d611304cdb03d4a12c99ab190c585690318d524782b424c70589aab231dac521e21f21c20425b22460805b6,0x99a72ab196c1ce90c3116b61709751d29d49da1cd16e90817ac71e0a5c94c562550ab1c0c558ec1810165a16e9cd1d29,0x19ba271d2416255ac01199db01685d2c532972050973b060405b626e85e456055c6d07585d265454264c74444199aa4,0x6a46ac1c66458b47721010d65726ead2a7325076810812166a94870822166a962a3a5542999781d29909b197116e9ac1,
    0x942549582ac11410d6d615495a2942b51b82ae14c705d43470462ac5c99a181016d89791d297096ea09cd487260968ae,0x7299090ccb82900b9989cb41ae18c70c686a71e08418d6b406509eb01543d2cb9ad1ab076b148789a1410d6d61b51ba2,0x75cd07198362b3669cd5035d473875276456855c6b06d865064c662450c209eda1991589971d517495615314e9cc96d1,0x72d07587324077285c75105e0acb003a275c4c5d0d571d61cd27815299317116ea19942c70066e51c74905e0acb003a2
  ],
  [
    0xb2e6b46ac1c0c5d52c6ea1010d67729324ea72a5076810c3096ba19917815895719495299317096e98c1ad14e102e519,0x588725c9cc5e25d486a5a12c025672b0688d62cd9a1a8b614e1cc98d1ac101ab3170337281c9729097317897521606b1,0x487d1a99a18531ad221c3226ab4058972b231c036669cb07081096c870c20d64cad49ce20ceaa07344642c66a1a1c0e5,0xb61ad14c1ce1022d5971225a0e66650644746415a56247326ea5295721811d69716e97419117317915296890823166b1,
    0x10aa1ed14a840475b666625585225606d46e85e47525ca74464654c53a7385b1eb1c20657b40c5856d0308131eb815a1,0x4c7cc90c1116789d19711931999581cc9130791581b515614b1881971d49689731d1191905cd4291d0c0373894ce14c7,0xd366a46b41c40475968b667585ca74464654c5b04397157667446465cc40cd58646810318d5501d63414d6252a5a16e9,0x6b4500d5c4545297311850457ae05686d265c5d45505226205ac5e26645ca54c53a6b86325b1c0c5d89cd61cc710635a,
    0xc6d26e8a209609d0417a852cac7019d62b3544304a5ae85e05d465066456255c6d26b05385a252062c63241ce509c00d,0x69c907115398b266850435ae06645e25685526d865c53a5206226305b45d054c5ca5ac8606c694074a9850504b595865,0x353d1c101cea71a2521c208c59ca5ac52254c53a9b0ae0550568420657b414631ad02946674060772725c634621c032e,0xa9c254a5ac521c518c6b4887742d0d7729518c27295314ea00d6b471a0460475ae095cb349e45d065463094a5cc5ba80,
    0xba15717094e15295896b1487085333d0518c6b405511eb0604059b05e4b629dc93a9425ca5a24604059d05e4b6295c9b,0x31762b1409e05b1c31615b48c7ac7b07a873a93411412d65827725616810c3096781d61b497519416e98d1ac1cc9d91,0x27586525d45cc64452a62c72674a9409e05a1c0959cac1420569924b29317116a97714e9ce1d29d5107262cb00ca98ec,0x67587666646525d45e256055c54a64c5c074473253872a626521c206bd3418d0e2d030825b646e86665626d655c53873,
    0x5341c20465b2685c8b952ca4c6606545dc406758acce100dd1a7221c16255ac0c20d64c9ce303588bb34a830825ae86d,0x5b3a94a860805b686e66526d4756558562a4c9dc73272a6265a1c438277405d0b4b0304c5b3a9ca921c318d53400eaa3,0x9117316d1cc900dcd472309e093a9405aa4eac296666e46d680959cac6ea6b148788710539ad020425a26b34721c304c,0xa5ac5ba73474a5c2e4c621c1626aacc8700d5a35131c31615b48c7ac7081196142056da1b91999589971b59d51561749,
    0x95198989a791529701931d096e9cd10811964a96896e9cd1d299091460407b686e66645e056255c7526d86565d454052,0x8195ed016255ac081116771729931d09689ca90c5394512c403728d48990c1d2a503174454502781ce16d1081116581,0xc5e48622a8f4075684b00951cec4b100dca353384604959d4a409e27587646d66e866656072674273a531c41595b46c7,0x99568a00d7945003728d402973252d86e6568530738460405b626e66605687545526d874a64c5405c27265aa6226565d,
    0x45ca5405b253a5ac52255c7586d664c630652664a26b344304c5b3ae56ad26e6b21c318d53410635ad019856acd07343,0x695ca4c66465681a23cac8c76b1487887c870811961010d650a88700bba29020425a26b34721c20445b666e25e05685d,0x1c208859aa4304c59d4ae45ca6b86c074473a80b19c9cb5a532999909972050973b002a676421d5a5d2a6ea111d5872e,0x65e44306ccb400bba29060495960ad66e86666446306528066ad2c050b33b2b1c414e6b407511ab2c1da04204859aa52,
    0x5e25685d45cc64254055c6d865674a7527647385ba634531eb1c43427b41852d4d060405a569309687626607586d46e,0xc997254632930a404510e6a406873270507469c99ab81b59181256d62902999581789d91ba1b5a0654c6b050815ae666,0x87427646d86e65684206bd3400bb9492b1c614c6b4b076b148789a1410d6d917895a1771549d61729531d096d1ce902c,0x53190b066ad0b344732402f551c72a1307815a1571d61b59951749529931711d096e98c1cd14c7101af2d040445b5673,
    0xda1981791589d596e9cd14e18c9951931701529571b61b9914e0e2d2b0c518c6b474905e0acb0035e51cd099aa0cd972,0xc6b8ac1a09117314e16e9cc9101cea7160a626304316159c7910c1ab4d0182acec00bb9492b1c614c6b4b07681181156,0x81096c871410d68ca54a021b9ab2b0c518c6b40c585671e2c1742d2c00d79473424404459ba94a742430825b44731c0,0xc9dc5525a04404459e06c05c4414f51249325295716e97496b148788701e855b015a0aec02999ab231f31c418d6b4d07,
    0x59ac521c1434aec887058972b0404459e456055c5225a05d254a5cc5385ba6b26e8656662766758ad4ac0644450435a4,0x4896810550f452c4640dba94a9cc95c840445b686e46665e05625cc5ba53054a6b86c064465c7566d25d45585a24208c,0x7719018b168706509eb01782b2c065c83b121c035e51c00dca35040445ac1c50475b666645e26565d46d275841c23aac,0x789d59d9199988968710e09dd01742d2c1307915a1d519599317016e98d1ac14c9529571b6174988973508d4ea531729,
    0x8686bd007a156c02999ab231f31c208c59dca4c620430835ae85606d265c5d455854a6405cc5325ba6346b04622a8dc,0x1c2226af41410d6d99b89991781d61959b51771729531ae16d14e95a168948154ab019090c20964b168177254a931887,0x116581b09ac118115679295ad61d995a1b51ae14c702a873b14a8b9465568a56b667588059d86c00eaa351ca93a6b85b,0x99ab231c60405a66b62756808e9cac72a1a89594898b1681749b5102c58bb14a6425cc5ba634531eb1ec1c02f58a40c1,
    0xd89ba1999791581771951d59b495616894b15094e96c17298819311411d64829915a1781959751571d49d99b89b61029,0x7296817717916c9959c85d99d49959066558b14a9ba531c31615b40889abd005a98ec021b9ab234ab1c035e51c181016,0xc54a5cc5305ba5225a062c6326404232e0e41462d45168ae06d84314229ed99ba19899018b1489531581d49b51959561,0xa666ac10d09e904232adc9918c7c998870811968b1c99687081116ca98990811968b1c99687487a873993470c204c795,
    0xa742441ab4641810d658bac71888abd01423d6c00a99d90414e6a4981153c65b1a9319595710c20d6b8b4c711115eb00,0x501549d610708eab00a666ac02e8d1b34444382764108ad67264631f26621c20445b2a6265a1c20425b224304c59eab3,0x876473a53856a552b42403ab524ba3ac71488d6d060a1af406a8c6b01622d6c6c250100a99d90414e6a4981142056782,0x1087567264631dac521e21f21c20425b22460c05b685e256a5dc5c453273a7427545586d265664c6c66e44508159e275,
    0x1c142b9acac70ce0acd0518b534046b1a7341da04204859aa521c208859aa4895675eab3a8421ea9c989226a9d7aacea,0xb2e0460405b6a6e866456053263065264654c6c06d65585c45dc5e275473846a2d85d45cc6446c654055c73a5386305b,0xad1d7010abd1c5729325076b148789a0c13167aaae2cea00e7547003958dc0c20d6d627328c25a14c950157215e062,0x22559c042774703234a9c7aa4ea060772725c8604a59ea968430c25a605e256a5c05d46525ba6347326b0531c3286b34,
    0x79c50768199066d991d19909b11b59ae1cd105ad6072e09c05d46306888e76d69d45c2b46803666a48c96c7066558903,0xa7261c98977195193170b0c686ad06a0b8b4022b8bb01626aac14668c73466b86c46d680c656ac14631a92e0a31c10a5,0xa6b4738632531c3286b34042cec700465cdc561366685d5ab1a10635a9260ab0850815b645ea5685527585b453a73244,0xd899019917496d18c9ac1062b98725c9cc420f4a64ba2ce10c8d2a71ea960450815a607527467646e85e256a6c06d65b,
    0xd1c7721411d695a911b01ad2d19d911990acd0668d834058aa6701423d5c5727517325078b1687487081096c87181016,0x4e10c8566733482625c5c5aa7911410d65a1549b61ac9ce1159c1472e0a304116279cb1100d794913a9ea5b1dc1c10ab,0x716a9e0460405b626e06645ea7587466c26406566d455256853a6327346b85b1c22c6b34043cac7002ee51c1410d6549,0xadc9918c7889101116da1b89949b01919d09d595614c9ae18c106a9987264ad441a1ccac0f0362b01ab382ccd2098971
  ],
  [
    0x4589e90418d6a498135e505b11b49ae1cd1043d2a72e093a9ea5c05b28162a99c7510589aab00c656ac108cd5704216,0x6764460c109ed91b897a95a1d61b517497116c14e9ae1b01115199915cb46a5664c942f31c62235740889abd01423d6c,0x7aa5a10c12966ea5a94c7043ab4715c9cc941e2c5a1c50475ae25ea56855c6d86c46b05b25c05d475265653a54264c74,0xb0109d18c903544c64098d6171ea9605598b16c0a605e45c2414e6a246ea5a98c94c71590b4d01622d5c772561181296,
    0x1c1626aac03195ab043827641085ab7264631e225a1c208c5a204308231eb51709ac96d105562672e8b384117469c8c2,0xd01622d6c10635a92605857195dcb46a4c65684c13a6c0c8b1671ea860805ad87326b46c29baae07685e256a54055253,0x3168811822d6789771712d1a93195a0b08e9b023447a45aa181016d897a9b61b91b0a5015495a14e9ac1ce16c70889ab,0x25ca5e4b3a6b4538ec09bc92ca4c660621c6421af40458d69015a0ae48c79475477476873713a13072c7181056381082,
    0x74454a626642660856509b419181dd05621cb40254739138dcc92c860475ab49e4ae0a667446c264044043596a74454,0x9095014f15a9099a26d0070e564ae2ca1a87198315d22c921c50475820425b665ea7586d65b473a7226a86b26e45626c,0xd0666a834ae2ca1a870117357221c1702d64081196ce2d51c99182016d99b89981791d51959b41d29731b11cc96e98d1,0xac98d16f11a0b095299016e98f1ad14c70b032bd05c0a8f4159ca0d00c8d8e4ce2d51c990c12566f28d1931503099a26,
    0x2a88f401587370055cc5cb11503099a26d0666a83401636392b8b286a1c660cab4181016da9791589d09729b11931501,0x8b24f209897172a1c1983aac01e354534a86040594ab6a961dcc5b1de1c20425b4af38b22460805ae06d665075476646,0x4894f1ce1ad18c90c19727033a541c081096d91b81999b61b09501549911941d594a1c89ce18c9ad10c1b327017ac41c,0xb49b99ad1aa20cd1a252c0c56215b41888d5d01ae05ac0458d6900662d548c7729141156d91d49561b099115018b1c99,
    0xb62ce94e15a9542063a16b00c6b8acac70e8856b011635a4181016991581561941931d115098994b1c89d594e9ce1da9,0x32ab050455958f4a93a40654d5c8871416b4d01702d644b20c125652a8b24f1ce9ae18c77316c70c1256141156ca2a99,0x458d6900662d540c89725231dc2420425ab4722440825b646d854a7426446c073a6b453840655d1cb9ad59ca1a870f0,0xa73874a7644622b8b4031ae2b0322cc94ac71888d5d050435a6456055265064c74473a6b453854a62652c41742994b01,
    0xc1ab4d0322e8b4043b1690112ace4ac74b1aa1887c870c1256141156589561d499315014b1aa1c9988905eb1052c493,0x6c7081b1ed0112ace41010d6b99989581561b41959d495094e9ce1d290ce95093649d46c45c05bc63464c43305ca47a9,0x8c78b1a99487083116a81081196aa1487181016d61d89d1272ace94e15a9084b99d010e6aa49328c90c12167329118f2,0x8f5b00c6276c0458d69011a2ae41a8959d097297417910c8972d03066ab40620f5b00c6276c0468ab91bc94c810e5ca4,
    0x4359cca3c531c26689b40118f57158850435ad8552538ab1c066e89c747a998871a0b116f1ce9ac94e15315a9549011,0x182016d9a50ab8a991d499598c718435ad24c830485b4aa3c96a6445cc5e05b1c260d9b401c3959040435ac094256043,0xcdc5320c1256562932ae24f28c7ca1a878874870811d6a81142116561b41ae1b8ad5994999ad92b110458d6901162ce4,0x8ab9158a4c93c7385ba6b2631f26430465958850435ad89e273a5b45cab4296a5d0552538ab1c1684d6c0439729010ac,
    0xaf2d0058d8e45621410d6d5a8f24e15315a9549b61b99b01ac7ca1a870c1196ac9042b33714c840465ac041154ce4046,0x901531d0972b0d5306d0614b53405d0a6b00561cdc0157317040445840445962b41c33468b41950e1d01d438acb07101,0x88454e75e0ae26c06b48233561c9090ac0f1902a5c19cb628f24e15315a9547ca1a87887081096c890c11969498f1991,0x276a6665e4ec4c545c1b40296b4b0304c5b3a6325b1c610d6b405c0b5b0111dc9c9320c11968f25315814c7101af2d2b,
    0xa76253854c56a5506d86e66b1c614b5340cd1a2d2c1ea0728420c35b26460405ae25607566d06545d254a5c063273474,0x465a4ca32430465b565d06d46e663c65264066454c560531c406bcb4015873715883c3566525d45ca64074463c5b273,0x2ac90614c6a4d9a91a0468ea9231f286a1e2c921da1ce84d1c204a58304c5b4273a8055cc5c562932ae24f20458b3704,0x2564f27725620c1296942572b624e16f1ce9ac70458d69060805ae25ea65066456075273a7445c254a6c0411635a4183,
    0xb42562141196542b624e1ce9ac70c88b5d01162ce49726f28c7ca1a87887081096c89081196c99a878b2081196c990c1,0x47596aad8a46b6673a938802ecc9c0c1196562d49cd2ae200b53571c1c660c574198362d010e5ca4772141196b89b11,0x181ad4d0262e87405aba09017ac4240c1196ac7198315d0560e8b477206e6a5b9a98191a045732925c9bcab2631f2644,0xd19729509b01b995a99719119816f1ce98c7088ae6d04055cf41a90e2d0112ace4b624e2ac7ca1a87181016791589da9,
    0x5b224504b5958860405b6a6e66625e46c07467325ba5c264465075454a5525604262cc747721010d6789751d49d91541,0x88404759e096a9ca80cac2e4cea17170272e6a4680d4b8a4d624c7043b1690112ace400eb1a92b1d2c6a8621f21c2042,0x420465aa8521cb97215ca819ab4249728c90c12165aa772d2a8f26c7088ae6d002abd24044ab39060405b6a9589cab3,0x6c70458d69011a2ae41412964f27725620c129699ad91d19d4a572b624e16f1ce9ac70468ab9231e2c6a6521c20c45aa,
    0xcd4d010b4ae4cc71702a3d01cc4aa4d47a998870c129699ab81d19b114e1ce9ac9b625720c1096772562d514f1ae1cc9,0xb6d89c0ae056255053880cac2dc7aa52a181016da9999791581771561d19529701b11b419514c96e98f190aae1b89141,0xae24c700dd1a9060c05b666e45ea5605585426c06d25c45d074a6465bc53a6b863465c662b31c2c447741702a3d31423,0x66e06625e45d05bc63465c5526466c454074240b8b8a45aa729033561900af4464acbb620c10d67416f18d1971b4b562,
    0x46e06b1c5054cf40e9132d014c4d640439729138ad895c830495a5c958ab893ca31f286a1e21d21c20475aa0460805b6,0x533d00ccc5644e2d625721412d69725624f1ce16e9ac98c7c991010d6d4ab895a9b01509ce96c9729043b169030465ac,0x190363d0342cc74572b628f24e2ac7ca1a87181016b4ad895a9d11509ce96c9729043b169014ee8240c119674aac7141,0x8f25714c75a9507ca1a87887081096c891412d64f2972562991a1dd51949912792742d1ab01b99981101573d04429cf4,
    0x196b91aca02ad0b70035e89cb02742b628f25714c75811412d6972ae25612e60ad72ace90a9d0370523389cb82742b62,0x455b66b4a6c65c45ba8033569c08c7a8724242b03c64b628f25714c75a9507a81ca10830d6c991412d6972ae25610c1,0x741ad16c9ce9d51d09b190458b39021662e40ae0e1902a708dc02a73172d8a3c95c531d604504b5a609d0a5cab895844,0xce9ac700e8d59002e5ca48c7ca1a878b24876873990812961412d6902742972ae2561182016d99b899917a9949901711,
    0x91bc95c81622d6c04589e9003a35641812d65a2181016ba17a9d51b41959749711b09901d19d8999157158152a4e16f1,0xd5a6f29719199818c7ca1a87887081096c89081196c99a878b2081196c990c1096d5a5a1919501cc94e9ae1b090456b4,0x86d5426f2b59b01b91971919981ac98c7c99181016da9198315d0660d8b47720c1296ba2ac94e113141d733a4407569c,0xb59941549b09919501032363934a84685c6410157371c4b54a646e04304659e2eb1c660c5741583a2d010e5ca477241e,
    0x971749911509ce98c96f1729792982d1ad51b01b59541050ae6b05c438ac043ab490505cc9cba24e2ac7ca1a87101156,0xb1e9040825a62b42754540552404ee32c729043ab49002ee8a4ac74b1aa1887c87081096c891812d65a2181016d895a9,0x1e2c6a6521c20c45aa0420465aa8521c404759bc5ea6d65d065c646632802f455c99271201439d93545524142b9ac042,0x746754656660642ab87325ba53c56854a55241423d6c04589e9060405b62852c29b408b135d1c4402e5ca40439aa923
  ],
  [
    0x19111dd0054e8e41812d65a20c11967828f24e2ba1771b01b51ac7050ae67151ea6621c60405b6a6e25e45dc5c06c46d,0x5b56ab893c56854a55265c646660631f286a1e21d21c20475aa04604b5ab89686c2540460405b62a64ae8931c340d9b4,0xb09701529162cc89256660644746451a22e4ba2ce9ad14c70686a6b0119ab240447aa90155e8246c7050735715c83049,0x6e9ac98c7c990c1216181016d89b919817a95a1951741919711d29d59b49b01509ae1cd11810d6d917a9589d49b41751,
    0x567609015ac624ad16c704397290141cd5c572181016da9b919817895a1971919b01b59711741d09d515295494f1ce1,0x5b325ba4505cc9cba25728f24e2ac7ca1a870c1216181016da1b819917a9589b49b19901959711741d51ce94e1529d09,0x46426565d25e066476256a531c50a62f4182959d01ca076c05a985b23c95c541f286a1e21c20425b224604b596883042,0x7058b321c95ad191562239021662e408695992e8a3c95c560531c30465ab8968460405ae87546d074673a5b45ca6b26c,
    0x8f2571507a81ca10830d6c991812d691ad5a972ae25a1541181016d899917a9d51b49741909711b016c9ce9ad1086acc,0x1662e404695a90505cc9cba28f25715814c70c1196ae2b915a11812d6ba25a94c714298bd01ca076c05a985b011a56a4,0x7476873713993070812961812d6972ae25a1541181016daa1810169917a9d89ce9ac96c718a943d01622d6c1620f1b02,0x5b564604b5968860405b626e86605e456a54253c5ba5cc73474a6466326b06c452862c7266a1f586d1c098b564947547,
    0xd8ab0a0c109698accaad1b0904589e900b8a8e40686a67160ad0a31c53838a401999572e8b286a1e2c921c5047585049,0xd51c990c12164c2b428f19817916e973215c0729053838a414171672e8b286a1e21c1622d5c181016da2d51c99181016,0x1c60405b68b22430465960a50ab05b45ea434459b415e850923c9cc85701ca414e0e29004758dcba2ca1a87181016da2,0x1dcc5b1c40475a46c3888d6c0c5332901614d5c8b21010d64b2932507729181016daa529042cec9030425b31dcc5b1de,
    0xab450067551452ace9102056d2a5098f1cd14e91810d65415295899814f1ce98d18b2487118a56d033a8524058aa652b,0xa98d2c053c2cb01833aac06ccc2b03a22c6c8d2043ab47006755144b2932cea5077091810d658b050ae6b01833aac043,0x16d89991d59949919cd1ac9b11ca1a9901e95152308162a99c48715e310d13ab4aa2c850475a606226565306b26d041,0x4551e9040815b4241193b244c714a0f4d040435941d2c6a8621f21c50435952560662442c2d7411e0a9d017a2a1c181,
    0x156d627a95415a17516c1ce9ad1b8114199ad1cc86a1585d064c6c67425c45bc73a6b0631c3056b3402159db00c558ec,0x5968b32a625d06466547565526d86e0ab4631c33468b40352a3b0116279cb078b1a99487083116a81081196aa1487141,0x2630404e5c5cba25610557a0b0116279c5327296f20454f4703044594c5bc73453a441562dc982ac2741019995b03042,0xb090c11968f2731b11ac70684e6b01193b244c714a0f4d040435ac4541ea6621c60405b6a6645e05625d46d073453a6b,
    0x1d6a810c21967a97317516c1ce98f1ad30295a3b0115ad1cb0904551e9050435ae05685d07545526d840b8b8ac95ad19,0x18195ad14c85a1d055853c5b273a7527465c454a64c6566646b4631c33468b40352a3b0116279cb07ca1a87887487081,0x5b40352a3b01153d1c1810d6561589ba198302558bb0604b5ae86566605e27525ca64474673a76456a558531c508ccf4,0x405b6a6605e45d054a5c25ba6346b07324097265c95ad51d1a9321410d6b625495a10b5858d35694ca4663c931c314c,
    0xa5a93568604059ca96a76273a4157381c562d1ad51b59ba1b07070ae2b2b1f286a1c60405b68850435968b58951f2646,0x82c70952b0b4a19d0312e47401ea54b0119ab1cd12043574913c83046594cae85d06d455863c652660641c414bcb4034,0x96c89143116ba1b41561011ba3b0112a7a4042af49356ac6460405b625ea5d05b473a6326546606e45685526d841ad6,0x8b5b23c8504759ea5d46b25b063466276473a75240ccc56cb117090232b590087275c95ad1a4f2932507ca1a87887081,
    0x1ea0728420c35b26460405a625e4dcab6a430425b31c50845ae86d06466547565d25e066276456a558531c60656b4058,0x7815618f16d14c15315aad891812566eb992712b19b51d591710e2b00529ce4ba2562029ca3b331c606b5340c8b32d2b,0x7527466446c26d654c5ca5d455863c5b2531c0a746acd910c1096cc7181ad4d0162a9ac181016ba1941909991729749,0x3471810563713810812961840427ae26605ea5686545506d86c67427566325b05d25c4a4c94a450455ae86625e056a65,
    0xd19d516e98d1cc9063d427008b565cac2942b627325714e1581507ca1a878b24876873a1347307181056381141056399,0x26505586345306b85b24231ea1c99acea5a9b81d19729b119071591a2d01702d64772181016da9b89999791749b11909,0x465b264504a5ab896a55853080d2969cd4bb0b1a82e2b0662235c1816ac701133a9c181b1a7366860405b625e47546d,0x9abd015439ac019995b2c441162ce4ca0acdd49032959b040435ac4541e31f286a1e21c20425b22420465b266a1e2c82,
    0xa40c5c55cd624c7044ab392b1c10e6aa48c7c99168ae14c1561941509729931d196c9ce9d4ab8a0c88b5d0614b534081,0x90304858308c593873a75840d616ac0756a0b2c6a664421ad746c7088ae6d040435ad09585605427385b4430485b345b,0x56d91b999817a9589d61b49751731529d09b11919971541ce94c7043b169003ac6a4ac16c70c88b5d0046676c0458b3,0xc5506b07324504b59587386b2531c3056b1c791181016da9b89999791581771b51d49561941729931b19d11509ce1102,
    0x6ac46e6b6a99d541562a5c9d45cca42b5241c9ca2c7aacea6c700a7747040435941f286a1c5a1d25cc54274a6c464665,0x22b99b016a6a2c52b0b182bd358931c112b5a4ac70c88b5d01162ce400b9729231d2c6a8621f21c20425b22460405b4,0x4a66958b3874aac6542402abd24160919731509ce16d1181016d89b999917a9581b515497417316d1ce9d11b09919971,0xb1b1c17429ac00d7a272c1e2c6a6521c20c45aa0420465aa8521c504b5b3895880c6356c0458b39040815ae26d075276,
    0xb33475241d5c42c181016d89999941911d19d51b61549ac14e18c908d81e733aae45dc5e05ca54c56a4221cd74021795,0x25473b0116359cb624e100d4f4701154cdc0c10d6d99b919897815a9b41951ae18c14c9561531d2991971177101dc54,0xa450e6464b81ce9ac96c10257917250450435a645e05dc6507545525ca54c74273a5b446a5c09cd9a5a9b89919ac18c7,0x72c441162ce4c0d89d78313066a701993a1c772d1a999d499519320439729231ea6621c5043596a75454c5525dc5e45c,
    0x791741d51731cc9103056d919997a9581971909d19d497515617315294c9ae1b89b42cea6c70819abd015439ac00d4f4,0x405b46644666b6aa5cab893a55854c5ca420cdd2458908d81ed017429acb078c7ca1a878874870811d6a810c1096972,0x5b6694ca6464665c958850435b665e256a54c5ca7425b473a75455265c6646468518c6a47424e2b61b81ac705d0a6b06,0xb91981789d49971b41751561b09729d11919531ae16c1ce94c70a8333b022e6a245a90819abd0066656c0468ab90504b,
    0x12bca4ac70439aa9231f26430425b666e46605e265c5d06c25c45ba6b073274a75455264654c40aa1ce4b62103056d99,0x99db011a2ae41020497938b5895cac6a6665464c810acce46215ad74b782b41b920c8aa6d0606b53403585ab266ac681,0x729751ac1b499415095711a8751d29709b11b49561919531ce16e9ac14c70c1956d02a0ccec0989a9b16a42223d74011,0x8a5055c6d86b0407aa85cd4975178210635ad017429acb9ad1ab07ca1a87181016d89b91999781d61931b19d11ce96c9,
    0x6d895ca4c810a5ce40468ab90304359e065c55864454c53256a6626b86e46d0a31c660d8ac0458f27366951a1764c93,0xa55c5386b06d85c26c4407715246e9741d49cc7019995b231f286a1e21c20425b224404359e054256a662650938ae46b,0xcc7019995b040c1596ab6666475454c5ca74264665c815740ec6d2b1100dd1a9060405b6a6e26665e456065464c74654,0x5b26450810ded91b819997895a9b61541531729909971d19d49751ac94e16c104571672c4403746a40c10966e9741d51
  ],
  [
    0x316d9ad29b199117071a109dd018c2d6497212accdad1084b8b702b310dc02a73172d8a4c95c538560541ea0728420c3,0x10b0b5d010ead1c572732507ca1a878b24876873990812961412d67425621420437ad8b3a96a550538ab1c02ead1c101,0xae896a531c56468b40588b571dc950754e11756ac47426464510ace41560e19054708dcba29895811812d6ae25a14c7,0xb010e6aa41015ab7264631f286a1e21c20425b22420465b266a1e2c820465b264604b5ae0a30ab89684604b5ab0a3266,
    0x10bd42933a5b1c2066af4019995b0418d6a49811010d6b815a1ae1b49541b11509181256b42529549582ba24c71302d5,0xa4408dce41017567264631f26430425b32460405b626e85e47546d25505ca6c454256a5386b0447a909c772d1a959932,0xca1a871010d650a00bba292b09504046676c00e8d590414e6a4981181016da1ce96d17a9541589b814e1ac900ab33714,0xa2c00e8d59050845b56ae85605526d06c66b4430435ae0ab8968550531c62a0af40439aa9231c02a5cdc1010d6541507,
    0xc6a8621f21c20425b22440815b566d46c6b42850ccca4ba2ac21812d6b81991942932ae25a17715494c702a98bb016a6,0x1010d6b8250aac96c107072a715075244c4276c10b0b592624604b5968b388465615c772b1a9599320439729264631d2,0x250735355254c5ca5dc5b1c3c0d8ac7810cd0a6d03344cb404589e7003728dcb078b1a99487083116a81081196aa1487,0xce90c1216572731cd1181016d51d89959991909d190466ac933a5b1e31c116279c00dca37030425ae86d06b463053873,
    0x5ab8968850635b413109db042c2d64989181256ba24e2101ad67264631ea6621e5c9916d0a566606427464039d8a46c1,0x2d6d5aae25a1971549919531181256b42782ba24c710a0f59010e6aa41015ab7264631f286a1e21d21c20475aa043049,0x598a5695d0ae06b25b1c408dce41017567264631f2655d18355ca5664c74673a403728dcb1104589e90418d6a4981181,0xac29318ca0454f47003728dc0297a270039d89cb5ad1ab07ca1a871020497ac6a4c65655c4046676c10539a926043048,
    0xd65070cc172d24c908f536606426348047475c01567470046e8dc060772714ca5c951c3c0d8b4d5a16278d5724e2ba1,0xd2910e6a891ba41a1a99c711b09b52cc7019995b002e5ca49918c7ca1a87887081096c89181016949b517436eadaa101,0x93195a03189db0066656c9891810167aa572d19d5195993252ad89181016d89ba17815a9d59971749ac14e1541919531,0xba25810c20437ab8968531c3302d74044d5a715ca4c941ea0728420c35b264e8a875eab6473a75244c8d62c572d1a529,
    0xa4d84c1cb1c604158e04504158e84d1c204a58604b5ab8968460405ae8b6256a531c68427740606b5725c950460810de,0x571941d59749b51729509931b01d114e16f1ce9ac70688d6b003a356400d8b39231f286a1c204a5b2a6a6521e21da1ce,0x19535b050cc5a41468d192e8830435968ab8931c1625cac181016959931981d99791b8b5a2181016d89ba1999791581,0x6e456864c66265683c22a6c00d8b39231c3066a9c787ca1a87081316ca9a994878870811d6081256c991012d6532771,
    0x6c70d0366b030815950ac094cb3a9dc5b45ca833a50a40c59919060405b667546d25dc55074a5c46b87325ba53c5426c,0xab4b0032ace400bba292b1f26430815a4cb3a95c5ca5d0460455ab8968ae09c05dc5504358d12c02635ab0031dca4d2a,0x8c7021772b34a9b1c206c7b400cab390404359e055064c5426c05c45dc407a546c5a2d2ace16e98d1181016da24c7019,0x1d60812168874870811d6181016da1b59b01b89999729741791581ce94e18c90c1196b9a9899599110c30565a24f1ce1,
    0x97290304959588308159eaad89385bc73a6b1c11635a48c7ca1a87081296ca9a994878876873a13470812960810d6081,0x5b264504b5a5095c9cc402d4d64b62181016da9b91999789b41951771b09901d19d49561ae1cd16e97115315814c7043,0x680d4b8a4d624c700bab492b1f2646083596242c43b341302abd050825b51f286a1c204c5b2a6a6521e21c2047582049,0x64204a5820435820475820485a21d21c204758608359624222b9b4181016daa562ce16e98d10c11968f217170272e6a4,
    0xd49959501931d19b11b417097514e16f1ce9ac71191aab003a356400d8b39260631f286a1c204a5b2a6a6521e21da1ce,0x589981912ad100eae27346a5685c630ac1433169051a3464ba20c10d65a2ae24c70c12565a2182016d91ba17a9589571,0xd594f1ae1cc96c70508f5b00362ce48c71302abb04646aac987ca1a87081316ca9a994878870811d6081256c991810d6,0xd65a2ae24c70c2056d59531d09919972cead917a9b11701751181016da9b917815a1b49971751541919731509b01d11,
    0x7316d2ae27a9b815a1d89cea10a7467010b3b1c50110a0f590408eae41430d6ba2771919951d59549532702b425810c1,0xac7a4042af490032ace4181016daa5a2989ce16e98d1181016743cea7aada24c700cab39002ee8a4ac7c99181016741,0x485a21d21c20475860405b686e06645ea56265675455c6d25d064c6c67425c473a538632460405b38968b6a9b1d4041,0x4158e04504158e84d1c404158c1c604158e04504158e64d1c504158ea4d04404158ea4d64c1c204a582043582047582,
    0x6
  ]
]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
private lemma check_c0 : checkCase r1_c0 syms_c0 51 chunks_c0 = true := by
  decide +kernel

private lemma solve_c0 (L : LatinSquare 7) (hred : IsReducedWith (r1Table 0) L) :
    ∃ σ, IsTransversal L σ :=
  solve_case 0 r1_c0 syms_c0 51 chunks_c0
    (by decide) (by decide +kernel) check_c0 L hred

def r1_c1 : List Nat := [1,2,3,4,0,6,5]
def syms_c1 : List (List Nat × List Nat × List Nat) := [
  ([0,1,2,3,4,6,5], [0,1,2,3,4,6,5], [0,1,2,3,4,6,5]),
  ([0,4,3,2,1,5,6], [1,0,4,3,2,6,5], [1,0,4,3,2,6,5]),
  ([0,4,3,2,1,6,5], [1,0,4,3,2,5,6], [1,0,4,3,2,5,6]),
  ([1,0,4,3,2,5,6], [2,1,0,4,3,6,5], [2,1,0,4,3,6,5]),
  ([1,0,4,3,2,6,5], [2,1,0,4,3,5,6], [2,1,0,4,3,5,6]),
  ([4,0,1,2,3,5,6], [1,2,3,4,0,5,6], [4,0,1,2,3,5,6]),
  ([4,0,1,2,3,6,5], [1,2,3,4,0,6,5], [4,0,1,2,3,6,5]),
  ([2,1,0,4,3,5,6], [3,2,1,0,4,6,5], [3,2,1,0,4,6,5]),
  ([2,1,0,4,3,6,5], [3,2,1,0,4,5,6], [3,2,1,0,4,5,6]),
  ([3,4,0,1,2,5,6], [2,3,4,0,1,5,6], [3,4,0,1,2,5,6]),
  ([3,4,0,1,2,6,5], [2,3,4,0,1,6,5], [3,4,0,1,2,6,5]),
  ([3,2,1,0,4,5,6], [4,3,2,1,0,6,5], [4,3,2,1,0,6,5]),
  ([3,2,1,0,4,6,5], [4,3,2,1,0,5,6], [4,3,2,1,0,5,6]),
  ([2,3,4,0,1,5,6], [3,4,0,1,2,5,6], [2,3,4,0,1,5,6]),
  ([2,3,4,0,1,6,5], [3,4,0,1,2,6,5], [2,3,4,0,1,6,5]),
  ([1,2,3,4,0,5,6], [4,0,1,2,3,5,6], [1,2,3,4,0,5,6]),
  ([1,2,3,4,0,6,5], [4,0,1,2,3,6,5], [1,2,3,4,0,6,5]),
  ([4,3,2,1,0,5,6], [0,4,3,2,1,6,5], [0,4,3,2,1,6,5]),
  ([4,3,2,1,0,6,5], [0,4,3,2,1,5,6], [0,4,3,2,1,5,6])
]
def chunks_c1 : List Nat := List.flatten [
  [
    0xca5d5a99ad82ac101cb9170332e41c92a4f25017316c70ca1a5901706aa47917478b1487ca1a876873a93713072c7287,0x766464ac9cd10c2d4c714ca3a9ca5bc931c065695c0c19aa71e04bb909766a62656b54ab4816b511c5328ea91172922b,0x5ae45685506d85426c074443195324cc1ac901cb91724a9cc6345ba440855b666e86645626d05587526567406426c440,0xcc1014d59724a9bc94c531c1ac29a4029ce272d8968551f286a1e2c921c20805a2a421435a2c521f26420805a2a44087,
    0x688b0232e0dc92a6f25314c714e0e290505a99cba25815a5645d1190902ccd191e0ac0b30420f585c7328ea529b322c5,0x645a2c06427446b45b273042833a5cd4bd9a95a173888b023660e414ac2371cca3a94a707623752c58b321cd9a95a174,0x95117407625e05d47345b26b0420ee85c7328ea529d2a2c5ac1014b99724a9bc94c531c0c5a95c031ae27358968551f2,0x8e9439062a88dc7328ea529a1e88db4b1a2ac872e6a5686b1a22c08cd43724a9bc94c531c62c296418d0e293689605e,
    0x453a5bc4519c45c99ad61d91ba1b59029ce2b340731c606c6b405d0a6b2c46b1f266a1e2ca981e56d2ee6a5686ae222c,0x264a94cb3888b6e66645e05626d86565d45507527685cc54a74064253c63a5b1f18e855e05625d455065264a54c5c263,0x86564095666c53292a4e96f1cc18c70c1aa6d01d446acb011b0ba1999791581b59d61549d01709741951062d58b13a63,0x25e45606d86565525d06445b273074275441cc58ac03195ab13c9cc94aac78857686e66645625505d25e05c47427546d,
    0xb019094f18e96c7185496999541589781b61b91da1d59031ae2b2c06b1c3382974141d1ad344731f224ab9897686e666,0x4e96f1ac18c7019ca5b01b846acd0159d10d54158a4e98c992a532105156d99991781589d61959751541b49ba1731529,0x162b5625d99ba1989791581d619595497419116c9ac1b09b5106b1a2b00a666ac4f273252a6b510d74258154a53292a,0x46b1a92b1c4646ab401c37290162cc9c7478b1487ca1a876873713990820d60820d68870830168aa0830168aa487082,
    0xb49561509d01919b1105d43491ccb28c8b7626e86645ea5607566526d455854c7406c26465c45bc63a734531c0c6b52c,0xaa6715131776266a5cc5e45605425ba53c730632ee86c06d25584046e8ecce222dd89ba17916e9cd18c99a9581d59951,0x274064654244686a64b12d91cc98d10c8972726a9cc5e05ba6358d16569ea74654c5c05bc63a734531c11ac6a4ac7058,0x23589c7aa225c9dd919a9731781d19d499119596e94f1cc18c7188aa3d00c6b52c011ba3b21558d6e25687565506d865,
    0xa558541f286a1e2c921c20805a2a421435a2c521f26420805a2a4ea9896626567526447467646c254c5c05325bc73043,0x7a291bc8d99077606625e46567525d06d46447466b07344117469cb0905573091b2850b42dc043ba272e89cca3a93c56,0x97606625e46567525d06d46c0644746411ac6a4cd1ac9053b3071c285310ce414e0e292e8a3a96a558531c1c1a96c045,0x624cc9ac1118a5673649d4ac4411627a4ca322d919951d59b4bba25815617430c8972d00c656ac0439aa9231e6aa9790,
    0x3438a405573091b2860ac2dc043d6273689cca3a93c56a558541f264b97056e25e05687565506d86525c274064646315,0xe29368a3a96a558531c1c1a96c04676291bc8e95076e06625e46d25d07547426444632b424ad1cc1015ce17256ac646,0x2f40708eab00a666ac05a970b231e6ab2ac4374475073246b1a3662b525c27407346b1c6850aec1aa0e1b062c296418d,0x92ac1995e4ad6a5464674473061750d7625e05687585d25504455e22cb91b59951b0991971110bd5093407346b1c60a5,
    0x959751701909b19d11cc1105056b91789b49751b19d11701909959021b9ab042f5424cc9ac7142999d016a5c2c04589e,0x5819099596f18d14e9532053a349152b31c162ccac021b9ab011ac6a4ac7c99a878b2105056da1b91789581d49561b41,0xd0050dce4541050ae6b00c6a8ec043aa69140e9d5e0a44b686c66e45507526d86565d44067552cd01362c1d78ab1a9a9,0xb011746a4cc7c89ae2235d89991781949751cc16c9146711723a96a5cc74454253c85518c5cd6291ab01b59ba2191b03,
    0xa5b4440815b646e866a5e25605d45526d07587466c454c5c06426565bc634531c0c6a8ec058b32b010ea9a4ac7021d5a,0xc93a5bc6b0631c0a728ec22e8d55aa8e90c897271e09508066e52c043aa692c05d4343662ac09cc5e056a5425505d263,0xc4ca992d8ae47685e0c421dc9c98b0a0c6bb01626aac08bd449023356245aa86e685d19701b0991195a132a19b26a94,0x2abd1c5078b1487ca1a876873a93590820d60820d68870830168aa0830168aa48708201642539d751549d19d41959911,
    0xb41951561909d19d498e96d1729b11ac9cc105ad4470163589c772ab40cdb6272a5715a16f18e9cd1ac14c70720ecb00,0xa5d455c6c05bc63a7326b4531c2c4396c02a87372e2c322cc9cb625a17810c2366d0029e95c182456d91ba1999781589,0x1c20805a2a421435a2c521f26420805a2a460915b646667526545dc55064a7467306b46c05c46325ba59990b7506525c,0xd6a6499ad1908e625900ba22e408676192d89bc95c568531e3aaa6319666ad8b46a4a9bc93a55c568541f286a1e2c92,
    0x701ac96d110a7a87366664742754646652408b566c00cc9d9331c568687405d1a290163589c772c1a365d4209e829b04,0xc93a55c568541f2669cd097666625e45686547525506d87406465c26c45b06b26e0450728f414ad18d0610229e789b11,0x3588b90215e864d626f25715a14c78ea99d40dd89d11709073b1092526346b241cac0dccc2131ac27266b58ac6a4a9b,0x8ae66c00bab492b1c668587405e16290162e89c7720d53a5949b19709d0191199a172621d01a1e8ac08e625901d10ae4,
    0x6465c27445b07327604606a8f418ab18d002ead241b0b899997815a1541d61d01911b19cc96d170906b58492d465240,0x55063a5b453c54a823287a400bca59162b31c322ccb4101b9ad2b1f266a1e2cb1ad096e66625e45685507586546d26c,0xd81ba1589b51d61541949b19911999791702d0900e95a914a93c63a5b25dc814358ec00bca590e95a1652b409dc5c25e,0xe95a914a86c2e86665e46d07586545d255c64a6c65c074454253a5bc730631c2645d2c581088ae6d0606a8f487342d,
    0xcb4ac7101d5ad331f226a78897686e66625e45d055c6465325bc5c27447526d86c04294b1a4cc2060756725480c8d8ec,0x581549b41d61951771529909d19b117017898e96d1a730a5b61571741d19d51da19299999496f18d14c7181aa3d0322c,0xca3d002f296486b435da1b81589d51b61541949d19911999791702b0900d99a914a93c63a5b25dc8142e8ec1b0ba1999,0xb111a8b61919b09711d01d9a101b9ad2b1c3226ab402a3a3b003666a452a06e6a5572d1a9299999514e96f1ac18c7141,
    0xa876873713a13070820d60820d68870830168aa0830168aa487082016102056999791589571749951909d194c16f1701,0x6b85b444c1ea5625507526d86565d454c5c064a7446c26e05bc6b4531c4233574141d1ad331c3066ab48c78b1487ca1,0x65606547565525d064a5c45ea6e46c2b404119d8a45324e16f1ac1b62011ce5b3086a77565586d264a6546665cc5ea5d,0xae1b09d11cc71417a2d01c8396c046762914c88d627558a4a9cc5ea5d453c6b87325b1c62235740458d6935508776266,
    0xa4d99076625ea5606565525386b06d85d45c074475076664a6c26e4450746b436641db917a9581561b417517019294c9,0x6d14f1ae1b11d0908e95892e096aa4a41132ae4cc70c19aad231f286a1e2c921c20805a2a421435a2c521f26420805a2,0x4c1ae1b82d01046762916aa4a94c8ea23556a6c474254064a4051dc645627324f1ae16c7a342d5789741b49561731501,0x85b24d98355e0a4a94c56a6d85506c05bc6b2531c52c2d24b91141d1ad331c5222cf403189db011a2ae40a62ed742561,
    0x972b010e6aa48c7c990a56755326f108e744716a76066664a6527567444c790b6d055874464a6c254056a5cc5d45e06b,0xd41749d11b09501929951063ab0b1589cc93c7385b1f475117509cc5d25585405b453c73843072b1c92a5a9783ac7019,0x45c274443584364d41ce14c1561014b99b02d4466c0b1b18b2c04115e8a47835aa92a5328cd435d89b819997915a9b59,0x45d07545585cc5405b253c7387426c44236662492a5a9d83ac71488b3d00c6276c0468ab92a39897626e66646d26565d
  ],
  [
    0x9aa9231f266a1e2c85a2565c26c07447525585307384073545c7520a87a1b02c6c62c5aa92a6f2532043ba2903951d5e,0xcd1ae1b1292904475691b1c1ce056c04656391cc91ce896566646d86e66c06b4738422358dc92a6f25315a95494c7043,0x88973d010e55a44ee225d91b999a9581d61b51959529cc1ae1b019110547a893429e25d05524045dd2c3666155aad62,0x95c01957473649d4ac440d63464d628f52159895a9549501929d0902e8d1913c5b25cc452e2c2495ace2b61b99b11ac7,
    0x46b84222e8dc92a6f25315a95494c70c8972d231f224cb8276e66625e056a6d065655254064a53c5b25cc74273040672,0x451d0575e45d2950ad8b386b1c421e5746c7073815b011568e47321850517ae06d45d06c25c45e265666475876674073,0x5819095294f26ca188ae27366a565524046676c0429ab91d13236c29525d05e2446a9d76666a75865664454a6c274073,0x656b49518c78b1487ca1a876873a13470820d60820d68870830168aa0830168aa4870820164e5c0db899a9731741791,
    0xc5386b06d87525d062a7315425609589dc53c6b85b1cac2c75ea5425606e274676466664a41133aa4d49cc71602d6d06,0x8ad895c9587315dcac296255854093c6b87325b1c11635a402635a925269cd096e266a5e45606465ca6c454274076655,0x2731c60656b49518c7ca1a878b24870820168a90850d68b1487c990820168a92e6a15d9a58950272a9a991a02e2e2913,0x71106357091dc95893c6b85b1e98d0d6e05e26d85d055c5c46c26b45385bc4409ea5cd19d919299995a9501022d59935,
    0xae4d51cc702635a92524ad18b5e454a56064666a7666e26c4814e5c244e1ac1b625726a8875b915295819199a9d99789,0x29e45c2418d5c247725624f1ae16c78d5c0db91781771b41561b097114f1ae16c90b0761734676264a66656a540418b0,0x9995a9501022b9992d26b1c6223ab414199ad010e6aa49518c7c9922cc9d78ab91b0a05397091386b06d895c88732b6e,0xc244e1cc1d6257272ac0db9a9a99195295827725624f1ce16c7d1d445781771d415617096d14f1ce1d11d89b19b91929,
    0x6c9771d410f10a5b1e4b44802ead24b51ac70e03aad01983aa402539a92527561196e65d06d26c094a56066a6468195a,0x22d4b913873075895c9d8b035dcac6a4a66656a55854093c7385b1c310129ed89b999a9581561b099195297014f1ce1,0x7729a99195295494f15820e0356d06223ab414199ad010e6aa49518c7c99a878b2d1846d741b51b82b1a9299995a9501,0x9518c7c8987342db61b91ac1ce1101d5a72c69bca4a66656a53255c540810e55a40660ea90094e6a4949621cad6c3b9a,
    0x6a494998aa1dd1ab81d919299995a978b06357091dca04e9d766a6a56264654a4189dc245726f24c70a03abd060656b4,0xac9b01d1191952902a8739003738a4b62168541929d19b116c94f1509062c2b91c080d63464d62ae2cc70429ab90098d,0x487ca1a876873990820d60820d68870830168aa0830168aa4870820164f5225d99b919a97815897516f14c1571d41709,0x65ca6b85b44550bd7629d0ae855c5606d25426c05bc6b4531c507353400ccd59011746a4cc718195ad010e6aa48c78b1,
    0xcc96c700e8d5910ce5355c9bc41a1cc9cb4a50a00dca393626057177645687565525407426c46d06e266a5dc5e065464,0xd1ad51959b4b150873d0162cc9c7430d0971d014e61640457a2915c8608b5a6a6e27605e45ca827352245a27724f1ae1,0x708eab010e6aa48c7ca1a878b24870820168a90850d68b1487c990820168a90c40427a6a5e45406425ca6c441d5a124,0x771529541ae16d11542f5d89ba19a9741791571581b49529b016f1ad14c714b132d1c2410f2b24045d1a9331c60656b4,
    0x741709b11b494e16f1ac11a1ad0726a64665454a74075676261ad0d7626e47566d2654646744447aa2249aab027815a1,0x7915a1771d51b495419095297016c94f1ae100eae27346a5641833aacb11045d1a9331c0362ce4ab460dba1791581571,0x4e6164b110457a2915cb2b0876e066a5e25dc5c46c26d464665275676474096854a55053c6b85b1c310109ed89b819a9,0xab39011ac6a4ac714199ad01c23aac8c7c9986b435d91b899a97815a1d59751b41949d019195294c1ae1053a3471c241,
    0x750966a5686d67526545dc64654a5507385b469c98976866a5606d675255c5d065464654a7405bc734531c162ccac00c,0x914aa6a4406e6b4058b32b011ac6a4ac700d8b3906654b7527449c2414e5c2415439891bc95c8560e8ac14b13292e271,0x96854a55053c7385b1c162ccac046b1a91dc8895dc9685505b253c7384037389cb1a909959062a1eb016a51ac10ba16,0x900315ce45726f24c714199ad01c23aac8c7c99a878b20c40427a6a6566426c654a5c07444119d8a4053970915c80804,
    0x6a6224ce1ad1ba2d826c7198855d0262637405d8b091dc86a2d66545c46c064654a74245583864ce1ad1ba2d8305681d,0xcc1ae1b01919529541d49d120cc58591c25e08605d53400a7a59264c8b5e256a5c47427545405526c66d065666464a85,0xb6466526d66c4842d6a2410e750926a95c56054a5325bc4505e89cba2ce2ac700a9739051813deda1b919a9589b59951,0xb19701d1190918466a91b2730c47a84647724f158954213115ab0466e0ac01aba1b00aa666c9aa52918286b9368a2788,
    0x5d8b091dc8e742954a56266a756654646b40d5c9bc931c60656b40708eab002e5ca48c7c89102056b81791d49b51959,0x45d1a9065438645724c96f11817627368ab8b31c02e65641605017096d1cc1d5195999192a19a94892b8b6846621574,0xc05a2a921c208059d8b035dc5e053c5b24615951cb09ac1181aa372d4b649c4450e15a4ba21542f59aa742581529b01,0x63589c5327297718e96c70e0372b03344ca40c19aa71e1e2c521f286a1da1cea4d84c1c20835820835a21c20c05a2a82,
    0x9a435c0b5d99ae1b49b01b915a19299899598d17a5215d99b919895a14c9ae1b49d51959911d090169599150ac0b3041,0x19c92a182356d81b899995a1949d595414c9ae105cb9072d4b426c06444031dca4cd1058d62714ca3a9ca5dc5b1c3342,0x5314e95a1547ca1a878b24870820168a90850d68b1487c990820168a91021d6ba27317415715814e150a00e762903315,0x2c297406b1a2b1cc9d99036e05e26d26c45c05b4632421a1adcd09056b039017468a4cc1014d5970273521c77292aae2,
    0x2420f585cae25a14c718b942d23a9674435b0732421742dc8d105695872c2744415a88e4083d61724aab893a568541c6,0xc45791741b516c9ac1b09911054d589334740423a0ae41560e190505a99c083d4c72e89605ab08d5e05d2a56b665b473,0xd516c98d1949b59b9115cc88d0286b1acb09055d039017858a4ac1014b9970272e21c77292ace25314e95a1547c99715,0x982d23a8d503d7547607426c4415708e4083ba1724ab3893a568541c62c2974073162b1cc8318149ed89999781711d01,
    0xb9a95a1ab888b06543864cca1916257020ee31cda2581468d1dd8978174a909054b9891b46b2420ee85cce25a14c714b,0xd1175e45b04415a39c99ace2ba1b59ac70cd132d0414e6b407511ab2c1f266a1e2c86a2d47406446c26b05b446898a5c,0x6e67685e2664c280dcec08195e7160423439b41852a3d017429ac18a8ed999b91b5ad0a94a6c918571171e0962b6885,0x685572b095297319118e9949026ad1b060cd8a410ace89266ab8b68756731c418d6b406e11ab341f22652b07656ab86d,
    0x79e25605d465255c64a54263453a5b06b26d05cc6c44614a8e4103c6a92667647568598b0ac14650b70519c45cba2d61,0x1662d0b0519c45cba2330ad5571589501731b0910539a901cec0a492a4e910e4e87266ab8b68756731c518a8f4184048,0x1c20835820835a21c20c05a2a820c05a2a921c20805b511a37665605527506566d45c06c26b093aa4a94c9dc8558386c,0x223ab40e539090382959c0e054e71eaa066ad7669ba9e466a646732631c3846ab4021d5a7251e2c521f286a1da1ce84d,
    0x47465426c05cc6b25b07347626446666e4ed8a9518d7666e266456055854c6c07426465c45dc6d47506b85b0734531c6,0x59c7aac65685b49d41d0a19570891dc95854c5626b873453046853a1cd9a6ea9a99198c71a02d5d26298b56055c7505d,0x47426c05c45b073453256066264680ba16a4ae2561b4b17111ad03c2c45c532771d410f0362b03886a640e5390903829,0xb3040a728dc043d6272d89cca3a95c53856a541f286a1e2c921c20805a2a421435a2c521f26420805a2a542f0b7666e
  ],
  [
    0x47465c25b47306b26e46c0405662e405e942902746864098d6172d8a3a93856a551c56468b405e0a591dc8b982b6e09d,0xb915810ec475999701789b81d91d19d416d1cc9098d61723a96a531c0c6a8ec00eae292b8ac2d0d7626665e075465264,0xb5d82742ac1031aa37010ee89cd627328ea5714e15a9507c9966642d9a99518c9cd1d49b41919b096c1711d01d99789,0x7072ab135d61541cc94e1ac10c8b3271e05c25b48262e85c5aa8e90468ab70666541cd91d07199162d017829647722e5,
    0x1e2caa07475e26526d45b06b24172ac1cb9ab019198c53955aa7898e96d1ac9021b9a725281ac4cac00bab47010e6a9c,0x751571b11501731781d91d0910e6a8904ccd424cc16c917170272e6b5893aa6a6466b8631c1983aa4021b9a7251f266a,0xa646631c280dcf41a8541709531b01919d1108eb1891325b040a5e89cb62ce2ad2088766702831adc5aacd086d589b41,0xd110ce8a891e4c02d5d2400e95a91305b24221d99c0a0c6b70281ea5c5aa816a5db12d917816d116168672e693a96266,
    0x466a5605426c05cc53a6b25b05e26d85d455c750744646738631c380dcb40660ea90087569c947c89a5e885b62ad1ce1,0x5742a662dd81b91999789701b09911d19d51771ac16d14c95415320a3d4890281d39cb62ce10a0c6b716a9c5a837666e,0x57205d990b2c4429417a400d99a916ab182b57586b873043131a9cd12b915817896d11087aa736693aa6a646631c380e,0x5820835a21c20c05a2a820c05a2a921c20805ab888d7666e06625e46d25d06b85b2734758740646542530418d5c1c732,
    0x7016d18e9911531b09045d1a90294bc24cc90a1ce87346a5680c6b8ac0464ec9168ab8931e2c521f286a1da1ce642083,0x569a97817715419098d16e9711531b01045d1a90294bc24cc10a1ce87346a5680c6b8ac5a2ae27aa2259897a9771549,0x487c990820168a9a540f5b41ac9b12d91d0a142d0b9011746a4143d1193308032bc9c1717027356a468518b8a4ba2102,0x6c4851195a41560e191b2850b42dcba28ea5a94c718b0a5d010ee89c732571507ca1a878b24870820168a90850d68b1,
    0x88892e8a3a96a531c56468b4058ca571dc9504ac2b96d0b605b0634732442f509c083d61726aab89686a98b16d27346b,0x11074e726aab89684610125ed81991789949b51701b09d1115e81193326b05b44051e35c17170270272e21cd5a91a15e,0x974043d6271cc95c541f2645c1e46d46526c05c27325b0634421a1adcd121131a99047a84641352989356a46847aa224,0xe46c18d1ac910bb827020ee85c9aace25a1ca52c5d49ad1cc1d121950e190231ea246ca182b0b7368a3a96a531c62c2,
    0x726ab389685477116d6a46867622246d2098ba17368a3a96a531c66458b4058ca571dc950466ac36567446426c644571,0x6a4b5a91a08d62691b1c2c0d8ec08b166900315ce45aa8ea4c7c99a878b2a1a3a56c209ca3172d6a46847722241107a9,0xb002d69645aa8eac5d505da1d11d41cc9ae1c6c41dda1b81989791741951d49b11d01ae1cd10abc2171cc95c54280ba1,0x9cb5a7819199899528f5215d81ba1991789959751731909ad1ce1d11d49501571b41b1a00c77291b1c1a139ac0b0363,
    0x25e454c5625509b1c1c23aac02999ab231c16159ac00e563926a9d811d7686e45dc5505c254c6c07447526b873043a74,0xd51d01cc9ae16c700a973905a2c66446567547425405cc5e25d08441ea6c10a7a890608f5ae07526b87347685dc7405c,0xd6b245aa8ea4c7c8971622dd91ba1781589771541d49b51959711ac1ce1d01531909b190456a69043585a4c5d505da1,0x79416e86c46d06b27386e85a16625e07507466446565d455c5425cc6c06d241a1ccac0456a691b1c2a0e8ec0589aab01,
    0x6b468231ea24b0ac1d989951b4953154177179170a03585a9356a464031e56400c77291b1c2a0e8ec0589aab16aa3aa9,0x93566546464031e5646c703195ab231c03568e410b1aa926aa9710d5dc6d255054c828ee224da1cc1ae1021b9a7354a5,0xa5e505ba1b51b01ac9ce16c7a5c435b49b92da2cc1ae1b010456a690109eb241823d6ba1791589d81ad1ce1d11026559,0xc521f286a1e21cdc4e84c1cb1c20835820835a21c20c05a2a820c05a2a921c20805b066a9562b56a526466c2443585a4,
    0x1f286a1d2a9a1c20c05820c05820c05921c2080592c82080592c9a1c208059aa4208559ac521f204208059aa4208559a,0x4758dc562c6c615b81999589541949d59d01b1901d9919364a4441732a2475170a0ccb9091eaad894c9385bc63a7326b,0x4c7188aa3d0422bcb4031ad4b0112b5a4ac7c8910105674a589b11d195019090143739011958e4044cea91cc93c73240,0x509b0191b0664c5b344d589ccb38840815b666e06645626d65506525d45c26c4740646433354247aad625326f18e9cd1,
    0x45c5627314f1ae1b1101dc8c901744ca4741019d54b008756accc7ca1a874aa46e8c5562ce1105056b59b91d41d99581,0x742133a11b043856a49aa5627324f1ae18c96c7148ca3d040c15b666e266a5e45607546d65427406466525ba63440766,0xca40ee30290332e424b62ac90c21d6b4b561581ae14c7102d59d03c8532c0ea1a1b033468a47aa5328ea6223adb99791,0x6f18e9cd14c791b118a8ed0622a8f401ea8c91d04066e52c021b9ab2b1f2044c1606547565525d06c65c474064240b0b,
    0x7324f1ce18c96c7188aa3d29ce21766ad641b13c2c562732ce2102056d99b919897a9581d61b59951549531d09b01711,0xb03c8586c062af0b033858a47aa5328ea103056b89b59d49951b01919d11d9974179158150a11622b9043466a49aa562,0x4e18e96f1cc9ac7ca1a87487102056b81589b595414e1cc9d61d99991949751b09701d1191b102b99d034299ac0ea18c,0x466a6525d46465c25e054c5625bc634531c34459b4148ce2d004f1964044cab9332404758dc56246e8c5b625a9531549,
    0xc96a55854253c73863a5b1c422acf4188ae2d2b1f2253948d6d6b669cc96a64654263a5b44504b5b667506d67446c06e,0x676056a5d055263a734531c168696c0457a2914ca9d1076e06665e26d45d06526446c640d62664d59d91d0201598b91c,0xa870811d646e8c5562ce1101056d81791d51959909d19701749b41b1110d19a92e6a6a95856273863451d6316c0b5874,0x54974105a1a5b0115e8a4532d4c0d5b89b59b120b4668902d5c2245aa7324f18e96c7019d54b00a728ecd62ae2cc7c89,
    0x7328e96d1a83875d92b11b9a9aa7525326f18d14c7188ae2d00c6a8ecac7b62533a0d9a9b5995191ad01d995818c94e9,0xaa40ae708916a9cc93c63a5b1c066e52c031aa3b2d8b38ab1f2048ba3556a93c63a5b25cc810ae8e4ce508d5aad5a952,0x45c26c064666456a6527565d455063a531c4a88cf41aa0e1d040ae674046762914caa13175405525d05e46e06c68111e,0xc9bc634531c52338b4029ca3b331f58840815a6a5e47565d06546465c27447626c06e6560552a32440815b626e65e074,
    0x6b1487ca1a878873a93612358d55aa4f18e96c9732042d6392b982356aad6a549cca3a5b4720e1b6e4b44766a6a9d494,0xac7ca1a874aa6870830160830160830164870820164b20820164b26870820166a90821566b1487c810820166a9082156,0x8e4085d0b91dc93c732420758dc5a2560675d99581d41b59b01919509142d0b934485503c64ba257272a4e16f18e9cc9,0x936895c9ca9bc63a734531c606b534060ad6b003aa8e400caf292b1f225837295e2a66b5681833aac00ccd592c640372,
    0x101056d81b99991789b419595498e96d1729b11d195019090b40e9902729c24d535a2772ce2129795581911509182b0b,0x6d25ca5d45385bc63a6b44606b89c95ad9ab190cd13291e043075534101d5ad003728e4cc7ca1a874aa06e8d55a2ce1,0x959b51549d095010c2c6c91e05c4ac6417664245a277292a4f1ae18c96c700dca39040415ae866456255c54064274475,0x5a625e45d06546467427567606d26c46e65685406b8531c64252f41531a1d052f443457272a8ea182356d99b89991d41,
    0xa833285a47810c1b94d0406e6b400eaa392b1f204274cd6627527665d05e4560542740451998a41568c892e8ab243087,0xa8b99515e05c4b46417a54245a277292a4f1ce18c96c700eaa39310e555689dc5b453c73875443c21aac0f1942b23a9c,0x4e18e96f1cc9ac7ca1a874871598b594ab091958c89368940732538562854262f410b1aad064c587418bb10d15c9caa3,0xd197015096f18d14e95719490a52c6b01832aec09d131b2c4421742e400dce29332420758dc5a206e8d5ba2571529589
  ],
  [
    0x25e0662654646827662247725a15295494f1ce18e96c700cab39003ab8a4ac7c8986b435d91b81999789b59d41751929,0x99836c6a4a96854273863441d63576854a56275674063a734531c1a1e8ac572105096d91b99b41d59d01b11025cd191c,0x47565c47406464172e42477252a4f18e96c918566272c2c50728f41a90e2b368ab8b31f226a1c2047581ba35568b3855,0x6a649dc94aa3a5b45599837449e495cad46c6a4a9bc634531c606a8f400eae292b1ee8ac59836e66645e05625506526d,
    0x5cd5091dc94a93c63a5b24519989cd0b181aa3d05c438acba2ce2ac7c8142e8cd5724e96f18c992a00aba3918395976,0x6d15a560db12792572d51d1a92a6f18d14c7141ca3d003738a4cc7da2105096d99991781589541949d51b59711b01919,0x3a93713074358cd5724e96f18c992a00ad6390404159e25607545526d06565c06427466c446760464b9a99277252a8e9,0x830160830160830164870820164b20820164b26870820166a90821566b1487c810820166a90821566b1487ca1a87887,
    0x5b606e46665687565506d86446c64195e424d0a789751949023b91b018b562c72a5316f18e9cd14c7ac7ca1a874aa687,0xc94c9ca840875a645e26565d475276664a5cc7445425ba53c730631c622a8f40252f2b2c64408759baa4a9cc94244083,0xd51b018ae62c72a5316f18e9ad14c7cc7c891020d6989791749d51d0991118ca98913273041833a9cd9a95a03195ab1b,0x789959751b49b99929731b115096e94f1ac18c7148ca3d0418bab4d191021d66ea92a73250982b58db0a789751949023,
    0xc9ca9bc63a734531c622a8f4181b1ad2b1f286a1d2a840415ae69d45e26c464266465680a666ac6f253272a1021d6991,0xd040875a526667625ba73063464a9cc942440835ae65e46d85d06c4646654742756760552568662440b567410bb90d14,0x58a14b1a2d042ee4346f253272a1021d6b899917815a1959751541b61d49d99929731d11b195096e94f1cc18c7188aa3,0xae67410bd50d14c9ca9bc63a6b4531c52328f4141d1ad331f20440835a666526d66446c2746453a3424ba2561cc94c1,
    0x4f1ac18c7148ca3d040875a526666e25ba6b063464a9cc942440835b665e47585d07446466546c26d66e055256866244,0x424da2561ac94c158a18b162d042f54346f253272a1021d6d899917815a1959751541d61b49b99929731b11d195096e9,0xb91b01ca562c70a53292a6f18d14c7141d1ad00a7352c060cabb331eb1f286a1d21c40835a666527566447426c646363,0xaec1709917895a1b11d19d51741549b6195990a73252a8e96d1b1e215d81999589561949b59ba1791b11d19d5174101c,
    0x22acf40352e2b2c662b833666654418b562c4e98c992a532766445d82b12791741951063b82b1cc94a93c63a5b1c1832,0xb2b1f31f22440415b44642c18ee42c4f273252a0f446d781d0971174a561589ba1b4201cb91b14ca4a93a5bc730631c4,0xd1d215999589561949d59da1b81791d11b19b5174101cd51b01aa662c70a53292a6f18d14c7108ab3d0606c6b4031ad4,0xa63264a94cb3948555856276874475680a666ac063d42b1cc94a93c63a5b1c422acf410105695199990a73252a8e96d1,
    0xa83b11d5e06c25c45d29585627687508073546c53292a4e96f1ac18c7060cabb00b8b8acd198b50cd999951062b98b13,0x52c021ab3b2b1f226a1c20475840415b606e66645e25686565d45527586426c45b06b26d040a666ac02e899b13c9cc94,0x90a4f273252a1b0ba1989791581959549741d11b19b51d610738a8b01aa662c70a53292a4e96f1cc18c7181b1ad00c6b,0x46c66d241ac68ac02999ab1cc94a93c63a5b1c086aceccc1101056da17895817515496c1cd1d41b61d19b11b9a991959,
    0xd11b7646e86d67586c27465c4442eac24999951062b98b13a63264a94c840415b666e86645e05627586565d455064274,0x999781589d61751541949d19b11b5906a983b01ca562c70a53292a6f18d14c7101cabd050746b4029cd4b331eb1f2043,0x65d45506426c474675241cc58ac03195ab1cc94a93c63a5b1c4072af410105695199990a73252a8e96d1181256d91ba1,0x915b626e85e45606d67585525d07465c26c440956664999951062d58b13a63264a94c840415b686e66645e05626d865,
    0x1c208059aa4208559ac521f204208059aa4208559ac521f286a1e21cdc4e044041594a53c5b05cc6427446c663a73246,0xb1a084ce991eaad8b4094c5505685bc63a734531eb1f286a1d2a9a1c20c05820c05820c05921c2080592c82080592c9a,0xa1587465406426565d24163456c060cabb2c4411746a4cc9043d5471cc840415b626666547565d26425c4452e6424b91,0x32e4247aa1822d6ba19a9589b41959561911b19501d09d51d9979174a7326e94f1cc18c7188aa3d00c6b52c011ba3b05,
    0x5685bc63a6b4531f31f22440815b646e66625685506d875665454c5327307426c06465c45bc5d2416255ac0f0b11b03,0xb2c063172b344411ac6a4ac9043b9471cc840415b646e26666546d65d27465c4642433350a40f446891eab58ac094c55,0xca1a874aa63454d74a029cd4b01832aec011d63b040415b666e466a5e25685527586d06c65406426566345ba5d441782,0x102056d99ba1991589d41b59561949751701b11919d090cea1490332e4247aa5326f18e9cd14c7188aa3d011ac6a4ac7,
    0xe21a9b140833a85240ccb9091ea8608b5b666e85627546d65586526467426c4431568649aa5027417916e9cc18c7732,0x6433468a40ccb9091ea8608b5ae866a7665405625585cc5d05e45ba53c730631c622a8f4031ad4b0046e8ec0a97a5993,0x4649930ccd50923a9ea84631ab4741058d15b01832aec045d1a9331f20541a977566526665686e26d89509d4b64a446c,0x5625585cc5d05e45ba53c6b0631c52328f4029cd4b01832aec011d63b040415ae65625586d2754768656642746407a5,
    0x7316c7747787142456d99b91d61d09b197015314c96f1ac1b499119597515415a198b0ccd5091ea8608b5b6866a6e654,0x949b51561919501489aa1b09d11d59c81da2143c62d01833aac045d1a93326b1c2a199ac0f0465b01c1c56c5aa8ea4f2,0x5a41c3c8896c532711101056da1b91d59c894a1549a81b61b19d115019099999520abc44b011ac6a4cc10811d6b99991,0xd157020475ae866456a65275455853063a5227287326b46a08615a314d01b0b188ae270070dc940c43aa5366ad684041,
    0xac9088ba37264e3a96a722420475b28521c310d5a4a870f2225b01685d145327016299955aa7314f18e9ac9cd16c7058,0x1c20475b347205314e966a9686d065653a5527587308066e51cc89487101056da1b99d41b61959549b11909d19cd14c1,0xc8701c3955241c1ac4cac532709c8c15d5030f08a95356a5482a199ac0f0465b01c1c56c068732b16aa3a93c9cc5b1dd,0x46a1c070dc940811d68ea4c15a9d01b19489a810d116652e895885a2565527326b46a252843342d145aa8ea4c2b01d19,
    0x1c163455c816acd9a98c94e9481c890233955254c10e559c0cc570705519d76656a6e86546626d653063a7347406b26c,0x9099598d14e9ac1199b10732076858a66563a6b453256a84631ab4cc719a225d14c9c058a66556a9cc53c63a6b47325b,0x820166a90821566b1487c810820166a90821566b1487ca1a878873a9341101056b999a95895414a1a89b61b11d19d51,0x1e51c5621cb48f208301670179158108301658948715a226d0661197452a6ea4f29725477470820164b20820164b2687,
    0x108cd570070e5549891010567819919078f1a155a17297816d14e9cc9ac311523390423355c01c3725262440415a6664,0x787083016a8148913109d5168ad8754420c05b686e65e45607545286a06d854a5c05325ba6b46c2746730721c4548ce4,0x1c310d59490718b12ad14a9c26a0f19540c5622c54b61b9a992148716d0641997418872ad03a21cac5728f24ea7296c7,0xc05a3c93055c6c074652272042646954d625a21b0b91999589949d59b61ac9cd1c894a105e0ac515ca3c930b406c66a,
    0x5a5c63253c5206a2440cd59499300b995701716a1cb94645b59571d61d999919494c18f1ad1b01cc9d11c870c43aa502,0x43a7441ca81b6143195d8f1cd14c95720e0a72b2b1c3a889ac52a70143195d5727294e98f1cd1ac96c70c8b167020c0,0x3760ad89ca95c5685405bc63a734531eb1f286a1d2a9a1c20c05b686e466656065c6426c674475672252855263453c73,0x463a7327445405526d86c6819956249521284f1b042d6164999108573d04629cb4070563b017a852405cb8291dcaad03
  ],
  [
    0x362b003a56a472a306a9d71178a77292a6e94f1cc18c7181ad4d0206e8f4060ad6b040415b606e45e25687565ca6425b,0x5dc149017350a4772cac0cdb82d6272a5715a15016f18e9ad14c7cc7c892c6aa579198b509182b199062d0b1cd9b033,0x581b49959d51561711509b01d1905e95091ba63264a802ee524ace8857297898e96d11087aa7266b46ad66b1c1a168ec,0x8b409ca5e055c5685d45425bc63a734531eb1f286a1d2a88d1575e285073534108cabd020758f4c6262dda1b99991789,
    0x8ead06625474062a1eb01c83b2c50272a73046dba2999561949060ceab24a9ba730631c17a852405cb9091dc86b0b56d,0xc730631c606b534081ba3d0404159e45b07347605625587527466c46d66e8654642666440a97b41488d6d042c6ab4188,0xc7325b1c42c6ab41888ead1ca860915b626e86665e45606547566d25587445425c0402e6564b1905d1a291dca4a9ba53,0xcabd331f2044c2567526c274664440b322e405c5a89027a1a245014c9cc102bc62715cad89685e05d446c2665dc5e453,
    0x735424772502ac2182356d91b999895a1571d61b49b01d199119597297515096f18e9ad14c70e1172b1e043234574108,0x4f1ac18c7141cd4d04232af4081d63d050c85b646e66c27465c45ba63464a6625686d4552758656408b176c0720ecb01,0x4f1ac96c71488d6d06223ab472a143216d89b99d615495a1b51501b09711781991959026a99b346417858a477292a6e9,0xcabb2c640373524cc7ac7ca1a87487101056991959571909b115014c9ac1b49b99d61d19d895a1781751170999771791,
    0x3ab52477210db1a00e95a90172e0a452a4f18e96c9772050d63b3109d95e05686566626e46d874075476684233ab4060,0x22b5b4d1900ead492b1f31f22440415a42a3a94a83306aa478a108ad6d06a438b4083a6690232b1a4b625a1081ba3d00,0x5cd42914a93c63a5b25dc8142e8ec29d1a599ab5902e899b1dc94aa3a5b454a58d75876455c56864a5425bc634531c4,0x455253c6b25b05dc5c294aa3a662832345741710e2d0264696cd625a1081d63d01832aec00dcd491ea843746803666a4,
    0x865655c64a5425c05d27547686c474653a5bc730631c422b5b4181aa3d003ab52400cab392b1f226a1c204758604b59e,0x8e96c94f1529581549050ba3b0032ace4cc17a850dd025817715496c14f10605ab7334e54d4a9e8a836e66625e45606d,0xc64a5425c05d25bc63453a4199561c95aba1b51d61d9a108cead3446c640373524cc7ac7c8177050d98ab0a771701791,0x56709b0191900cab39344403a56a452a8e9cc922559d7717017918e96c94f1529581549050d63b14a19d6625e456055,
    0x830164870820164b20820164b26870820166a90821566b1487c810820166a90821566b1487ca1a878873713a1307102,0xc5e45ca54c5a052a6a84078d51458ac891191aa51d241744cac0468ab504346694d11b079a99079478c7083016083016,0x5079998e9c1574aae24f15615297314816a9a89ca10a03ab5162421617b402645d70116359410e15a5342440835ab49b,0xaa0cec6f2c8c62db92b19d11d59ac1ce10c22565a94a15427916a97496c712a21eb04c5076c073815b042b075c4f2732,
    0x26e05e456a7585527205285aa5d05c26c46a2440b5654b5ad19cd10ae8cdc89102b9953386b1c1d10aec10e41d9131c1,0x5a97415494816a90468ea532241b1e094d1ab5ad62d1d08dd59711ca1d09d91b61b19b89cc1ad1a8702157352c688d76,0x85a25ca5bc5e05d482c4476cad30ae318b0212979c58908e81dd01744cac0468ea504346694b9ad19b079a9907706a8d,0x493c94a5b45cc4408359bc9ca54c52a7285a1c111d59ca8710e15a5366b42440835b647526d855054c53873052a6a072,
    0x6d25386b07347585d454c52a5a25ca5bc5e0432265740e03aad0439d41cc811020d6b61ac1ce1c814a11488b35354ae,0x25507305285aa6a06b85b44421e55cc8716221ed06850774073815b040a979c10a19d513c9cc941e64440835ae456255,0xc860c125ed817895a9cd14816a96c1751b41d19b11b99a891131715352d58ab8a3b8857666e25e056a7587446c66d45d,0x66d25586c47466b87345227284380ea945aad427517816a970a02635a92a1c1d10aec10545e904215cd44c706a833b1b,
    0x7417116894a9034a8b5358aa8ab0734721c4056ad4a427a57a95894a918ca985366ae05586d26c67386b4420475b626e,0x70116359410d19a53446c1e6a641e51e357116a041d1d414712ad1cc1d52019995b04a83c54b621031167a9581b51549,0xce1c81aa10119735158405a176c0468ab504385694d098507754f25297316aa18d89852d6b66ae49d441744cac02645d,0xc93845d5585209aa96a760c0ca176c063c157010a6ad4063172513c9cc941e6642047593c56054a5cc5225aa44373414,
    0x84168695401cb9151c25d4446a8c6c0811d648a5a9d897816aa10ea9853445c25d4b56ac66e46b1c5819cb4062a3371b,0xa81ae16c9cc1d61d11b190455a39321c58887b403285db04a50cec0429ab513c9cc941e62440415a6a641c504b5958b2,0x7a975168704395651c1c4c5856c128672b1bc9197316d0ea28086bc94562ae2142456d99b917815a9b497515414a16a9,0xac1ce1d49c814a10666855366ac6744423a5624a870a1a1e716a8504b5ad25585327386a87224072e454ac2d424aa581,
    0x414ae1a81ca114299950551e214562b52d92b9ad19b07b322c5b4ace1c894814c9562ac1142456b91781b617515414c9,0xa5605585d05a252a5326b06d27387206a8460a56540747505354ae4b66b424204759e056a5d27507325305225aa4632b,0x12a91d1c2080592c82080592c9a1c208059aa4208559ac521f204208059aa4208559ac521f286a1e21ce84d1c40c459e,0x489c81d0901e3629040415a6474663c64265655c6d86e66b4b5440c9d32c0f1162b0322559ca87b0252a7a97076c705e,
    0xd194a1c89d61b59b12184ad19360aa0402f5514cd10c2c6c7140430a99a4ae1098a6670322c59c5aa791083016581919,0x158872d15c888f2b6e6a646d47566467444059996405e425925c95853ca31c521c5b4083016b899999515714c98f1909,0x582c810e1b8252b0c189d1940627a850404959606624404159627607566d87446c66e4666641e51d4a9ea5c1c6419974,0x66444151e16401d3949321c42e859c10b1aa526296a9e0420c05b666e46d87547426c67385326a25284382a39491198a,
    0xccd8ac0f1162b2b10e56d8c07ac45c582d02a8705a166514a9ea5c1db1c20c05b58ac09426a85205386b2730e07a9565,0x7ac464ae1098a6670322c59c5aa789083016d99b81991589949919b11b59ac9cd1481c89d020f5811915ca3c938b5840,0x5940ac46e09287207586d6420c05ae466665c6426c66d274475655863453c5227287324307551cd82502a87033a62b00,0xce1ac1489c81aa1063172514a9ea5c08199856418266c90605d5140455a352c4b64a5c93ca31c521c5b418872ad020c0,
    0x54a7226a06c27386b45305288505e8941588b152e6a4666486a5c4340650f292d8652756c1598964572083016581561,0x1888ead14a9cca836c4ab0734538d2a9ca5e45a1c1744ca4118c6a71bc95c9d1e6a641e51e31c20c05b605ea5627445c,0x275673452a7286a06b86c45405ca5e45a1f42c4c19aac0447aa51b1c6310774158872d017a05644f22a07add59b61b9a,0xcc1ae1a871087565041425b666e47586d65525286a26b8734438b1a1cc82581789529b017110c40427b606e65625586d,
    0x4c714285ed04a887ac507999c5d425d99b91c81d49b59b09d111166689158b386b04404959605e25c094a9aa41133a94,0xc6cd331c6284774022c5d721cd0b5c29aa96a6e24573047410e41d9338846a8c5c772711a35ad1cc1d925717117496f2,0x7228421dc9405c1aa515c9d2430895b626e45607566d25dc7406c672852a6a05a25ea5585c453c6b85b1c32345740c2,0xa5606d255853c6b05b45dc6a87205a252a40ce23540468ab5356ac65c0744d4c58b6e26c45aa5c05e456a6d675874676,
    0x6421ac2e411ea1190032acd4ae309c17151dcb4645555caa8b589bc931c2a60cec0a521e9161e6a641f1898b7626e45e,0x86b0b93346b84212979c0a1c1d70222ccdc4e1a35d91789d49561729509cc16d16814a9ca114459952e66d46a26c074,0x4c716221ed00ca176c5079910c2256d81b99791771b51b09d19d495614a9ca1a816896c14f150172910ba169020f1b24,0x26e66a044215cd406c58352b8c4685c54b52772d03a8d7a9a896814a958aca2b61709751d49132645b0421e5545726f2
  ],
  [
    0x554054b83515cb2318b7466a86c06e67545dc6d25585c453c7385b1eb1c58887b4102a5e71ca11d760b467345b05c46c,0x6c718c41dd01950ce44f27725479a99079478b3a0dd626aa4a15a96f1cd14c157211aa70b2a67096d89387307284421e,0x66c4742eb87307288031dc940447aa50204759e256054a7405c45225aa4032bc94cc9ca1a81ae1b0911564690111ea94,0xb59d61d9ab9266e4254e1cc1ac9ca1a8119435853566d86e6b64ac4b41c5819cb406661591bc9d44d58395e4b667546d,
    0x2539a90406e69cc8714285ed010a6ad4507999102056781589529709b01ae14c14a16a9a89119d5053327204550e614,0x18a11dd002a5cd40429ab51aa31953cab89585dc5c4402e65640e8b097116f1ac14a9aa168906a8c65003a2754b5ad1a,0xca1c8c62dd89b917a9581b61751571ac94e1cc16f14a9ca16890728e851c0744f56ac68098d6a4101d5a72a1c50a17b4,0xad0735440ca176c13222bb02226ad46aa5a95079891010569a9907233aa5789d81cc9101d5a716a5205aa4580b594b91,
    0x1c58887b418a11dd002a5cd40429ab5020475b666e45e05587426c65c453c7385b25dc7205226a86b06d244a833ac131,0x7a9581b49d51561d01b197114f1ae1cc96c1771ca1689b162c55a9b61d517496f1ac9ce14c15716a9c89487118356b2a,0x59ac521f286a1e21ce046c2e65dc5585b253c7307526d46b86c07465c4410e55a402635a90089e35cca11032d6d99b91,0x4561e6a641e51e31c20c05820c05820c05921c2080592c82080592c9a1c208059aa4208559ac521f204208059aa42085,
    0x8766440815b686e66d27567407346b86c454a53c6a05285505dc5c25aa5b04181e55c0c1b947321c2b087ac0a03ab51e,0xd110a6645904390ae40a567090181e5545726f24c70a9833b2a81e354a5205aa46853154a8918195a515cad69bc938ae,0xce16c1ad10d04a9c89ce1d11d41b59b09a8707441db02761c2409ca31701815cd47721812d6792742aa2b01ad1c81ce1,0x7a9589d59d097117496814a9a89ca1cc1ad1b41b1a05681d90181e5545726f24c714285ed04a887ac507999770465b03,
    0xea51c4b28ab89ea6e476256852a842b3a14cc712a21eb008b175c530acdce211aa31701815cd477254956621dd91ba1,0x75c7915879a9907a8c635789d19d91d49b59c81a890a1d435128ae89aa96a838b1a341032d6d59b49d01b19a8168918c,0x51aa95c52854a530830895b666e86d26b47387545dc6a07227406c65aa5c252854a55053c9b1c29487a4084a5e702870,0x51dc82047594a5225aa4112b594ae1cd1ca1a830a5631901506754060772515c9bc931c2a60cec50674dc89a81060772,
    0x770464044cab5338840c125ed89791d41549d19529709ca14816a96c1cd1ae1b01b99b51a8706641d90273115c09c171,0x81dc945726f24c716221ed00ca176c5079916b086dd91b99d41b51549529b09d197016a94810e0a8e53229e25b46b0c4,0xb997895a9711b09d196c1cd1ae14a16a9a81c8906c583504685c54771b51d415491a8b49cc1ad1a81ba1b1a05681d901,0x4740415a0764a8106077251bc73453055c846a9c2c298975d9a572d11b196f1701752ac707211db040a979c0c2256da1,
    0x792b51d59d11c8715421ed005a1764058995513c9dc951e6a641e51c50495b666e25ea5686d45d05a252a7287526c65c,0xb002a5ce411615992a1c153075c05097351bc820475ac25c454a5225aa5e2b40aa0b325b04111ea9c5a2ae231615db9a,0x42e2dcce25a178b0811d678ad0a529ac94c14896a9044cea5168b38721c10e55a41984c1ca14895a16a9789d93130751,0xa6b25385225aa44433354ca3742cc2a8714285ed06888af405097351bc95c541e665ac6895ca5d45425a052a5306b244,
    0x641c8476c03285db002a5cd40429ab50514959ea5687546d65d06c27465c46b05a252a5327387207626e4420475ae896,0x5141e62440415a6a641c414b5b646e25ea5686d45dc7405c47386b05b25a052a55053c81d1d09caa1c8902539a52c6b5,0x25e45ea8897646e65ea5685dc5525b053c7327506d46b86c27465c452a7285a1c460d5ac02635a92a1c0ca176c00a973,0x429ab522c29773892a9685ea5c4410e55a4141256da1b99571cc1c894a14c9ae1b49b11d19d517416f20e0571716a9c,
    0x307c6342dd99ba17915a9771701d11b19b515416c94f1ac16a9a894a10708ab533872075241c8476c03285db002a5cd4,0x79c00e8d5501946694d11b079719079878c70820166a90821566b1487c810820166a90821566b1487ca1a878873a9361,0x243845c947890ce12ad00362cd406615a5342420c059e2b3893a56854c5ca5205ac7226a84440dcd454901685db04151,0x7516b17896c716141ed052e05b41a221dd018a879c4ea72a507959082016cd26e97517315296814b1ca10c53945152aa,
    0x709d11c89022b995366ac67386b1c5310cf406541e9131c62a0af46eac8c62dd52d19b11b99cc1ae10830164a1582572,0xda1b99711aa1b09b51d19d49ac1cd1c871015ab50ad6316a2408b5654cd1083016ba17815897516b1a814a1571b49d41,0x416255ac118372b2a1c1946694b5ad19b079719070830167815715894816b100d8f252a24631d094b1ad9aba231e0ad,0x6615a5356b42420805b686e05e45d25ba6b47307545cc53854a5a052c5505628318d8b406674273225415e37545525d,
    0xda1b89581b515294e1ac14b1c81aa16897316e974179215111ed03384ab4cd3195318d0053175c54911621db01c23a94,0xd49d19b11b59ac14a16b1c81ce16d106075672a1c52e05b412941eb04c8876c022c5d7018857944ea72a507951082016,0x18a82bd1ba820c05b605e45d255c5205ac5b06b46d06c6744756722428c6a54b8b5a2ce2083016d91ba1789581571741,0xc05b625687566d27446c67386b45226a84460dc94b825727917416b170a10539a9321c5310cf402645d901816ad44c7,
    0x5415897717817116894b1144c8b52e8b28b306b46a1c0855cd40820167715494b106cc9852d69687507627466b873442,0x589771541b097116894b11ac68853466b07347207526d646a888ec03294bb06644aac1ac611b06883a54da2082016d91,0x593a55054c5ca5225ac419ab414ae1a81ca10819ab5168421617b400d8b3501946694d11b07971907987082016b91781,0x72a5079590830165a17295316c94e9ae1cc14816b1a89ca10509ab5152405a176c10545e7003a355406615a5342420c0,
    0x6b46754731c4c19aac10ac2b71bab38685568b52b286a26b85b2730c688877403285db042e859c00a9735042c6a944ea,0x9719071412567417097910e2c29d015708e46b2572119c15b046b1a2c08301648a571b497416b2065c9852c45c25e4ae,0x655c5d05285ac7207385b26b06e87546c4746403958e4a8714285ed06850af413221db002a5cd44ea72a507949101056,0x805b30ae092c9505dc5e45a1c02e6554707161616d06819ab46ea066ad5d83c8a101cea5168b38820c05b625e45606d,
    0xae1a894814c95a2cc1083016da1791581741d514c9cc1ae1b89a814a110d68652d6b466c441566624c87111c1d715c82,0x5a2d92b52d5ad090820167815a17715416894b14c9cc1d89ae1a81ca102a99950531e414b92d52b5ad19b07083016d8a,0xc84087595c9baa4a9cc941f286a1d2a9a1c20c05ae05e25d055c6b25305225ac41b33414ce1c81aa1032959502d1d214,0x12c0cd53071e44314e8b400d8f270604b5968ab884751c1c98a7910cd0a6d0614b5340853a3d003728dc05d99072c1dd,
    0xd1dc84087595c9baa4a9cc941f22440835a3a6445b25ca74245782864ba21a8959ae1b51b815a15494c70f10acb03d4a,0x92a732507ca1a874aaca521dd815a1d595414c9ce1ac100eaa3723a9b45ca7444318d8a40c195671e243286974119172,0x5695199990a0c635491e45b1c56660b48ea10311695ad996e9781929d09b1970718a0e5d017468a47721021d65726ea,0xd6d99989911d09b19b91cc14c9541b49959d530c6b11916885a2567545387306b1c388636c072744b03c21aac781101,
    0x1c66650b4158991d23a840c459ba5e064a6c27465c1c6283974119172d017858a47721021d65726ea92a732507c81102,0x1d21c608d59687627384507469cb9a992781101056da1b81589b59541d49951909b11d19cd14e1ac910aaf072665e45b,0x88eb6d06e65e05d25b4730414358dc7328ea5295714c709d131b0215999cae25a10853a3d019427ac00d8b372c1f286a,0x6e11a92d09e043445d34732571015cccb331c314e8b400dce270604b5b606e65e464a6627546d06567467325b063458
  ],
  [
    0x5718e94c70819ab73389684218d8f405e0acb341f2243c1685dc55253a6b85b063264a5c454c402b58e4d0918d51dd11,0x32cac70c6362d003ab89cb322c578ab4a73150957205e950b2c6a4aa325e95117607565d05b46b04142e8dc78b732529,0x9555a2d41d91749781ce10f18adb895a1b119295098d14e9ce1063d507266652ad68085dcac6c711119dd1cc95c405ab,0x5eb10b2b8b68756731c318d5341462a3d341f226a1c2047583c1685dc55253a7385b063264a5c454c402ae8e4b09788,
    0x89c58386d7328ea5295715894c214671172e8860495a6656255054c53a63264a5b45c25dc5e06e46c66d265446843aac,0xaac05eb02b368830895b645e25605dc55275065464a5c454c53a5b063240a6669c99ace2ba1b59b09ac710635ad003ab,0x8e96c918571172c441d446a4034ad1935073b1036e66645e056255054c53a63264a5b45c25dc6c46d2656754731c6843,0x484072adc98a79158108d0e6d0314e5341852a3d017429acb07c81101056b99991781589571b499597515299097314c1,
    0x8c903195a7266ab8b68756742731c414e6b400dce271cc88b7686e675455254c5c25dc7465b053a7326b86d064a65663,0xb415352c57825895424ea92a532771b51ac7159132b017740acba20c2256b91789581771549b419519297115314e96c1,0x59ac521f286a1e21ce84d1c40415b666645e056255c7526565d454a6425cc53063a5b24519c45cd1106e11a900b33464,0x25ac5b04421d59c019d5472a1c650877411037351d4551e5c641e61e31c208059aa4208559ac521f204208059aa42085,
    0x594c5205ac44a53194c8902999a516ab669ba938b586d6420c05b626e66d87566c06b473874454c53a7205285605ea5c,0xc29704216ad47aa1412d6782752ca2d01cd1a81ae1b11115646901950ce411666890421d5945aa6ea4c719182bd020c0,0x1a221dd00ca176c5079599a845dd03ae16c1cd1170531581b59aa14896b1749ce1d51d99d09c8714c41ed035a1a240d4,0xc29704216ad47aa589082016b99789d61771711b09b515496814b1c89aa1ac1cd1d81d1a08d81e90421d5945aa6ea4c7,
    0x9070830164a2d626b257211aa70b0208059c4aa8b389dc7546d255852c818abc14ac71a221dd040a979c328cd5ae20e2,0xc530820c05b626e45ea6d66b87347587206a26c07465ac5c252854c56053a9b1c4588764111a1e70053175c751547971,0xa547aa0830165314896b100ccd553386b46a8720c4598a6408c15e50421ea945aa6ea4c719182bd020c059ac96a52854,0xc39a846400cab352b8820c05ae05626d25d46c654c5c26a85205ac5b06b4738740756764721c43507a40d4a46703506,
    0x90421ea945aa6ea4c714285ed04c8876c507951083016d91b81589d59b51531d09b197016b1481118c8d52a29d25b473,0xb196c1ad1ce14a16b1c81a8918c543503886a547a9d91b815890e85714896b1709b11aa1b89ac1cd1c81d61d1a08d81e,0x1087aa51ba6b453056a838b1a34a9898d5aab5ab11d196e9701792cc714a11ed008b175c083016d59b61749571711d09,0xcc319421dd005a176411839551d4551e5c641e61c20805b646e25e06d655852c6a85a25dc7527465c46c0423607a4c81,
    0xc9ac4032bc94044cea5328ab8b31c4548ce4111c2b7160e5354c9ac85132654b92b59d61d99d11c8a019d54501133a94,0xb02226ad46ea5a95079590830167826e9ac14c95a9481c89d026b253210b1729040f1aa400c77272a8820c05aa0522d4,0x771561d09b19711cc16894b14c9ae1a81b49d51083016d62571cc94e14896b10a0ace52a8de0ab0b21c0ca176c12a233,0x711b01b516c94e9ae1ca1a8910635a5330f46b646e6452847b414285ed0688877400a9735010a6ad4082016d99b91781,
    0xd09b197114b1aa16870e0395d0414e6a4c8714285ed010a6ad45079491010569719070820167a9581d495614b1681771,0xa7567386b05325286a26d87446c66e45e05ba84616a5c572709751082016d917a95896c14e9ac9b81d59b51771561ce1,0x5ac72252845222cd4ae1a81b8914a11ed050a17b400a9735010a6ad4082016ae24b256177171100b9959020c05b6256,0x682728c64772b02cc2ae25615314c70a0373b161f286a1d2a9a1c20c05b645ea5607587466c46d65c05d455c5b253a73,
    0xb2c08e11d90214e8e4088b337202f2b6e6b565d45cc54255c65264640315ce40ac233902ac4c640a9d0372d89e425374,0x911cd1d09501571b19ac157421dd91b819997a97096d18e9911949b51b19d01d59cc9011d6371dc95854c6b8531c2c43,0x21b9ab021742e409c17191dcb40ab0b3895854c531c2646b2c587c895a162dd81b919997a9b617516c98e9949d59731,0x8e99520295a3b02cc43640b182b702c6c0dcd62102056d91b999897a9b119197096d18e9951b49d59031563b02a740ec,
    0xb819997a9771709ce16d18e9911949b19b51d01d59561531ac94c7099166b02c43b2c08636390222ccdca0e89d7aab5a,0x747ca1a874aa101056d91b819997a9951b59909b11ac9cc16d18e90468ea7017a2a1c732d61749d1950157194a635d91,0xd056468b40720e5b01705ca4532143456d49959063172b017429a40560e590079196401c57190067551c4e2b62732572,0x102056d919897a9581b61951549d017114e16c18e9ad1031ae27246ac2b56732450b331c1427a170563285cb9914a0f4,
    0xd066458b40720e5b14c991ac55625404608d8e4d91cca05e8a873464158396401e46590066e51c4e2d62732572747c81,0x4a34842b50dc118b91726ab665e4440415b46642666ac4b64a54ad641aa60ec05d982923a9ea5b1c1ac4cac70714a0f4,0x4871709897a9581b599515494e16c18e9ac9cd1d61919d09d991852d4d01ac29ac0458d672c0840415ac6642656b44ad,0x6c7021d5ab01730564cc70ca174d010b58dc7722e60adb9ad5a91900c5739003a56a4b627328ea5714e15a9507ca1a87,
    0x4746431ac464b0278170a0166659158ab869710d7646e666256a6d87566545526b453863a411a2adcd09b01919711781,0xb196d1ac1011ba372d8a3a96a552531c5670534108cead00373524044cab9060495b626e466656a6d675453263a65264,0x7530f2868d01ae642c00d99a900c9995cd627328ea5714e15a9507c890f0561589ae16c18d1130789951d59d11701909,0x18294b71c0b6083885c74951062a33b0086e6acac710a19dd010ae8dc772c8435d781b016c9cc1ad1098a6670066e51c,
    0xcc1011d637358a3a96a552531c666853400ead49040415ae46665e26426c66d27565585b4532738744817664245aa8e9,0xba3714c9dc951f226a1c204758310105ed99b819a9d51b59949b11d01919709791561589ce16c18d10c12d6d91d196d1,0x8c5cac732c60ad5d62ae18cb9aa581d488d5d62b0aae16c9cd1102d4b7262e3a96a531c440dcf40550e6901705ca4042,0x118c6a70457161c9aa74ab0a5898c92d0d2db9a9590664e8b01ae642cd190569439003666a45a98e94c70429ab7141c1,
    0xb617496d14c18e9ac9ce1062ce872566446c66e476646283b341560ccd01a839acd020c2256d81b61b997916c1ad1ce1,0xce16c901567471e0ac0417660a405e950923a96a531c3446b340550e69010b58dc532772547c815732259897815a9d51,0x4c7507732101056d91b99d61b51959b01909d197118d1cc9ae16c110875670462e45c9aa789581ae6445b61b99711ad1,0x24646561c95ad9ab1911519990421d59c088b33726a962440415ad8b3874464241116ae4b190559839003a56a48ea5a9,
    0x463547646744403a56a40c2c6c71e096a53063a41560cdc0429ab72c0830895ae05e47585d26d47426447346b85b063,0x77419182bd005a17641103735151e5c641e61e31c208059aa4208559ac521f204208059aa4208559ac521f286a1e21ce,0x45c6b2531b01a8705511e901434adc110373502080593a5685ea6e2dcc6c474054252c81a23c9402999a52d6b6646508,0x6d496a5c45e25ba931c688877403285db141e5656318b756ae66c2b44810e55a40631729020c059d092072873044173,
    0xce16c7058b16b006a9d2cac706a11eb040a979cc6b42570a6b2571d490f4a11b019507a4ae20e2c2971eaac47077346b,0x87527445ac5c05d455c6c66d06a28181ea945aa789082016d89b997a95a1d51b49541b01d194b1aa1c816897717114e9,0x9151e5c641c20805b625ea5687546d25dc7305b453a5507286a05a252c450e239400d8b352e6b465c06c4f4a5857666e,0xaa103455953567647227406c6405742e40e5c11901132ad4ce30d41a951ea94646b56ab28ae89ba931c6460af411621d
  ],
  [
    0x4e9501731063c159004e9d24015d0b92b44446879cce1014c5d701434adc082016b895a1b51749731509ac16d16814b1,0x1b406c433b0181d5945aa6ea4c714285ed04c8876c507951082016d91b897a95a1b41b19d09d597514b1aa1c816896c1,0xb42b19ad16c1711d09d59c810605ab5063150d4ce30e21a953649ea8208059dc7225a052c552aa8b685c25e46e245899,0xda24e1ac1aa10607565023350d45aac8c62db917a9b19ca1d01d59d895a17114e9ae16c7cc713221db008b175cb3045d,
    0x5a1764111c2b7151e5c641e61c20c05b646e85ac5e25c45d052855c5ba6b453056a838b1a3405cc15b00ab42ec899a35,0x856a768756744721c20c05b686e65e456a5325ba5d26d47565c06b86c25ac6a072252854c842f056406609d5344731c0,0x27546d65cc6c45425ba5a052c6a26b053844390adc00e8d55340c20c05ae65e45d26d45c05ac52254c6a86c25ba6b053,0x253a7307225286a06b86c244343ca410aa3371ac82080592c9cc7446c2541c15447a401685d9020805b666e85e456a5d,
    0x4e1549d097116e9cc14b1ca168918a8c55366ac68418d6a4021d5a72a1c0ca176c00a9735141e5646a2d65d45c07445b,0x675455c7326b86d05285ac7206a1c1a847ac03285db002a5cd40429ab522c29753ab389685ea5c4410e55a41a8b51ac9,0x65c46b25b05a252c720c398d0a4022ccd513ab389685ea4388dc3405c172b020c05b686e65e456a5d25305ba5c06c474,0x76c00a9735010a6ad40830167aa4e94895a21a20cdd05888cf405097351ac95c541e52440415a5c641c5a1dc5506c074,
    0x896a9ba81d150dcd1ab5ad5211a370b0409d39c083016da1789b915716e9cc9ae14c15a94a16b1c81a8706a11eb04c88,0xd1a70235cc1cb51b19ac7031563b0214e8e44e2ba2587ca1a874aa68731e42d789711b01b91ac9cc1c8a1314e85138b6,0x66c4421742e4045d1a9331c0315ce44c7099166b0218d8e4ae2c6b505d4b00eaa39050f4464cc286879595ad99cd1045,0x21d5ab01116ae4cc2101056d8a7a97715497115316c98e9909084ce990dd1075ea6625b463a654a46b407567646d06e,
    0x445ab90218d8e44e2da2587c89cea225d919897a9919d09d59731749501571b41b99b126d18e99510a1c2bb02a740ec,0x47666d06e46c68032bca4046b1a92b1d31c214e8e4ce2a73505b49b99b12183b1192b0b34c2c43b2c0295a3b06843aac,0x43436466c26d69cc94055c7447507666e4c1a14cec0b1b03b0086e6acac242cccd772549532043b94906b0b5656b4075,0x959541531d019097117716c18e9cd1029cd470235cc1cb51b19ac70a0373b0214e8e41462e29138ae8961f286a1d2aab,
    0x8ac044ad692b89e811b6645ea5c45b063a7327407549dc95054c460ac664d9b0b1b18b003aa8e4101056d999917a9d49,0x1c604b5ac4e6a9e4440815b666e46626546466c26d654c5525c05dc750744833744247a98e9cc96c74c70a90e6b00c6b,0x1f20591a2b6e27305b45c06c4405662e477254153206b98292d6838153ac0cd42691ea8604b5a6aac4b549e45ba73063,0x9040415ae66645ea6d265655054c6c06425c45dc5b063a6b440c6b51cd51d19cc70991acb0218d8e41852e29138b6896,
    0xa90e6b00a738ac044cea9338861475a645ea6d45dc5505b063a6b26c05c454c450b4664b9b0a9d18b020f1b2400dca3,0x8c7031563b0604b5b54a56e6a9e4440415b626e66646567547466426c4435742247a9531549701771b418e9ac96c74c7,0x344ca4787145456b99989959d49b09d190ceb109364ad095c5405cc6b45b05d4a4443306aa47aa1a8b499599096e9ac1,0x6c24314e8a47a046d9915418e94c95a94a1a81ba1ad2d99ce1d5206219db00a5e52c0589957321f4094c9dc5c1db1c3,
    0x265675276674480b33464b42c81043b9452b4406a9d1c50101ac6593384343195c058d15715c9d44204759506465226a,0xaac5aac23a8dd5ad91b99951919b110856669033509a49aa5a14ea8c7070715b040415ae866456a6c66a252853263a64,0x18d524a87063c157018c5c9494a57274110105690bb42899c2dba3023a727028c539494a5475327717070a8666b03c21,0x4c4375da30c5d117150ac0b21c32869545327717076c70c12d6ba2d02509ca14814e1cc9ac341dc6599991108c746903,
    0x70163455c5727490c40817b666627507446466546d65527326b45206a26c0857a04645aa8ea4e2ba11433a2d056468b4,0x6e8766440415b626e666a5686c474675464265663453a5226a86b24066e51cb42502c87143c62d03174464ce10d0c65,0x10b1aa514c9dc5c0843585a402a674900a5e51400e563526ab44ad493aa31c1c1c56c068732b06711b540b447509286a,0x873453052880c5d8940f08a95356a4665486a5c42c10e0ea93686626e6c23589a45aa0811d65a1541cc1ae1489a81ca1,
    0x729b115098e94f1ae16c7148ca3d340731dac521e26b21ea1cea4dc4c1cb1c40815ad05dc5526c45c054c6a27207426b,0xc5ba6b4531c50738b421e8adb9ada1d5a02c39ab01ab462c8f253292a0c3116da1989791581d59561741951b49b99931,0x59aa430c45b666e85e05625d47506d65587445406c26b45b24181d59c991949023d51b23a9caa4c83103594ca4aac263,0xa420805b686e66625e45d07546d86565cc74064454a5a252c62a4222ccd458154901578cb23c5b1d38b31eb1ec1c2080,
    0x931991d89b99b61959d51032a63b008b52ec507d0708201674a9325298894b16a9011af451505624215e334075614b23,0xb060515a669e4958ae86d6a548073546c9071813565427825a2b99b61959062d43b018ae62c1813565a1541749781711,0x8968863508f410d598d0075632c035463b131f31c60515a666545d25e45c054a5607626e86d655875041d056ac054b98,0x52666e46d6a528665096c014d4b906343894da2562075423b0195662c0c20d69296f18d18b16a90750e2512254c550b5,
    0x86525cc64463c5325a252c40b9a3146ea8aa10eac25266ae46d6808b566c507d011a06d18e99115018b14a9689068ce2,0x6894b18a9050d2b51625504156662c8f16c74e2cc7ac71813565427825a2d89d61072a23b020805b625e05685d455075,0xd518ec4c70820169315298894b16a9081cec51605524056666c8e9082016da1b99991781d49b61959751731d01909529,0xba1999581949b595617419297098d18b16a96f1791d89d020730ac93548067296c062b98b14cd21c335613410d598d00,
    0xd05a2565585c05ba6345ac62a64c7427505d24067296cd93032a63b14ad21c61518f405d584b0195662c0820160c20d6,0x62c141356562d51da27425820cd584d043566344c7d01cc71689595619318e96d17298896b1749d51501d09d81188aa3,0x791581561741951d49da1b891813569917815a1d89b99959751541d61b47d071813565a2782d91d6254205d584b01956,0x6b14894f18c98a907312a51689c054a550b60758815350ec05cb82b060515a549e4a66ae26d640b0e6ac907141356999,
    0xa830c45ae86625e45606d65585d065475276664c5ca74454263a53c7385b1c622a8f4b01ac76b148789ac870830166e9,0x7264652408ee46c8ea72a9320c40d653292ad098f16e9cd14c7181ae2d08762d766ae86d680d0d6ac072b18b23c94ca4,0xb01ac76a94870820166810830166b14878870820166a90c3116da1b99789581b51d59561741509b01d11cc96d1108795,0x495b606e85626d65586526665e45d064474275440c656ac063d50b1cc94a93c73863a5b1c422acf4019ab4b01d446ac,
    0xc63464a6526d67446c06e4452338b4141d1ad01832aeccc7031ae2b11ce896566646d86e656855293a73863264a94c85,0xb13a63264a94cb316237589685529cc94a93c63a5b1c3072b34060cabb060495b686665e05625d475055854c5c253a5b,0xd61541531909d117294e16f18e9cc90c5d1171e45d28182b5ac011af4b01d446acb01ac7681b32645b5a999951062d58,0x8d11818ea736895881cc58ac034ad1b1baa4a9cc83047594c9ca9bc63a734531c086bcac101056d81ba1999589951b59,
    0x5318894a96b1081cec51605524059d32c8f16c74e2ac7cc7d07c870c20d6b99989791581749b51509b01d11d41959cc9,0x1c60495b686e46665e06527566d85d45ca6c064454c5a252a62c41434ad454158908674cd01b9852c8e908115678a92a,0x59509e0968b66758656418ae0ec062d58b0604d5b665685505d25e05c464c6646e27586566d440ab18ec022b8bb141ec,0x181456da1999951749791701529581b89d59561b4106c19ab0153562c18145699a792562da1d5a95201cb91b241c604d
  ],
  [
    0x881b908ec066558b030835a4a5bc63462c5aa41b83894489531542b625a214e423d0439563401e54cb00b918ec4c7ac7,0x3146ea8aa10dcc25266b64756808ae66c507b010830169316e98d18a96b14895295820c654cd0052e2e414e0e252e895,0x62c8f16c74e2ac7cc71813565427825a2b89b6106ac23b020805ae25e05685d45506d86525cc64463c5325a252c40d5a,0x741951d59b61729b019095316894a98b1088b335160552405a566c8e90811569295318894a96b10560ec5162550415a5,
    0x5d46526665bc6345aa62c64a6c25c0c1782b2c062d58b14cd21c339513410e558d00b918ec4c7101056da1b89999791,0x8a96b16e9751b49b0214b0b492e4c0ab18ec52b487146463d0179512c066558b020805830835b686e45e25607565586d,0xd131ec06b1c6a25655864c63a5b45ca6225ac5d26d45406c26e0452328f4083016d999897815a1541d619599317098d1,0x7626e85585d06547566d1ec1c604d59689e0ae46d89508179512c066558b0504d5958ad46e89d09608339513410e558,
    0xb62054b83b017350ac18145695279299ad89d5903435ab241c604d5a645e05686565d45507527666e24504d5a665e456,0x832aec06e11ab340731daa521c208059a0420c059ac521e21c208059bc5aa62263a53252c451322d45a2701529542b81,0x45c25d45e0664568552758656409ab46c4e9ae18c992a5320f585595ad61d995a154a73252a4f1ae18e96c70c1cacd01,0xab4b040415a665cc54a6425b453c63a654b566c47407644622b8b4181b1ad0066ad2cac7029ce2b0504b5b666e26d06c,
    0x5a154a4e98c992a532101056d81b89d59d11b019099519997915a1549b6174101ad61b1cc94a93c63a5b1c422acf4019,0x85324065695c5328ea7296f205e54471d45e284233574081cecd052328f406e11ab340731da0467615744822e5c24b62,0x56206b1a2b00b3346c6ea92a7320c11d653272a6f18e9ad14c7101cead030475b686e46665606c26446527565586d06b,0xd0143396c019d54b331dac521e26b21ea1cdc4e6430835b645e27565d46526665606d06346b26c45427404059d864ba2,
    0xd595617419319514f1ae18c79aa0c3116da17a9581b49b19509d01d59561711741931951989b918e94f1ae16c7148ca3,0xda1b91781589d59b61709d01b19911949751541ac90c40d678ab91ae14c75320c20d6da1b91789581b49b19711509d01,0x324b1ad59031b1ab01d2a62cac7084d4bd031354740585a5b24c831035a6ab5694cac663c5ba6b4531c11738a4102056,0xa4404b59c4542740764a54b56ac6430835b646e866a5e27405c45425606d45586525ba63441626a9c7430c8b32d00cea,
    0xb0181dcac6f2101056959991909b1908dc2392e8b38744405a52e4053c2571cca3a93c56a558541e2c5a1d21c208059a,0x101056d89ba1991781b51d61749711d0190908cb9892b27344087569c95ab190556349005666648ea5a95414c70706a5,0xba1789581951561741919711b09b5912e611b36474084cc1aa4d49ce1ac718294bd01c23aac8c71183aab043856a49aa,0x62cc9c7478b16870830168a910105678bb1a909959102056b917815a1b49b19911959709751541d61d89d01cd1101056,
    0x85525387327686566646426c64215e324582d025328ea7a97110c20d6502d819a97317914f1ce18c96c7188aa3d2b1c1,0x43491cc840415b686e26d46c66426566645ea56054c7407525585c45bc63a734531c46685b405ca869040415ae27546d,0xd0162a99c019d547040415b606645ea5686566d46426c674454055275863a7325b44521e89cb89159584d01c1396c05d,0x66e52cac76b148789ac870820160811568890c11d65314ca8ea7a97010c20d6b1a9a99119598ca4f27317816c7198315,
    0xd6711789d919314f1ce18c905897271d06544181eaac9aa0c31167a9711741931951989d918e94f1ce16c7188aa3d00,0x7aa86c02bc8c9346ad640a746ac06cc98b331c212e2f40c4b91d24c831035a6aad694cb4663c5ba734531c11ab8a40c2,0xc31167aa50a6c98e902999a72d6b46430c45b646625ea7585b463a6545525685405c26c46e045614c74742054c1db00,0x8e96c94f15a950a14e0e29014ecc24ba2ce2561050ae6b0112a7a4ac76a94870820166810830166b14878870820166a9,
    0xda1b81791589b59741d51561949d01b1191970910bb82926a94c9bc634531c10f2b24045d1a9331c066e8ac0f588d732,0x5a16f18c94e9531549011d63b010f2b24101056da1b819917895a9949919b11b59d01d517317415615098e96d1101056,0x4e16f1cc9d610f0b11b032ae1248ea7aa118356d0622a8f4751058aa6b00c6b52cac76811813d69a9789b91d61d81d0a,0x25cc7427507686c46e06466646526d643a3446ccd28ea7aa118356d0666c43405ab3091d44066e8ac67442dba2531709,
    0xc26a5cc5e453c7386325b1c622a8f4ac7058b3271d1e2c5a1c20c05a2a421475a2c5a1d21f21c4041596255854053c5b,0x101056d1a90995a031ae2b0172a1a4101056989951919d09d59d91ba1b495614c9ce1045d1a7160ac094ca3a9ea5c446,0x701101056b899a9d19b11909ae18d1cc9d91b41d619594f15495a15017317816c7198315d02646b3401a37490066e51c,0x5094f1ae18e96c7043cac9331daa521c208059a0420c059ac521e21c20805820455a224304759328323589c8ea7a9531,
    0x5aa1811d6da1b819a9791589d41561749d19701911959b51b0a4e9ae18c7142c63d01ab312c5320ee88dda27325a9561,0xa9e9031435a6a94ca3453a5bc5d44162ccac044a9e9011ac6a4ac7019d62b030475b686e06d45585326b86c282335624,0x47465405ba53c6b8631c4233574148ca3d00a7352c042cec9331da04604f5a6aad89685bc63253a54c5524046e8ec044,0x3a93590c11d67a9531b017096f18e9ad14c90585a571d4406758ac044cea90604759629eaa64430835a6a6565cc6c264,
    0xb19711509d01d995a17819719914f1ae18c792a0c311697272a8e94f1ae16c7088ce5d03075534cc76b148789ac87a87,0x5e45425606b2431035b606e66625e45687585d06546d25c26c47465406b8531c15746245720c20d6b89d61b51749541,0x9168ad86b1c380e5740685a3b25c831035ad8a4a95c56854063c5ba6b4531cc5a877686e66627506d86545d26c47465c,0x562b19b49ba2081ba3d040415b606e66645e26c47467545d055254064263a5b45ca428c636402b3329028c5c6408caf0,
    0x3a56a48eaa98c65b62709ce1d1111621d90407569c99ab1a92a6f24e95715a15078b16874870820166a91413d6992d9a,0x56b89999791749701d11d41909b19cc9ad11a1ad07368ad86544281e36c0687a2b02626a6c08578c91bc95c560531c0,0xb51919949992cc9ae11812d6791701d11d815a1541ce1ad1b61951d4b6c719a14cd0568e134198951d0162e89c772101,0x95a16529ca9627425bc63a73453855c8162e8acac70720ecb002abd1c5078b16870830168a9101056b99789d11701b09,
    0x74064a6c65c46345ba53c5685e04308eb341a02abd2524088e76c00a7747040415a3a9caa46ae6840ab3b4182b0bd0e,0x92a0c311697272a8e94f1ce16c70c1b94d2b1dac521e26b21c20805820455a22430835ae46d87546b27387626665dc55,0x18d9168b58731c1c158ec9720c40d6d6292a5715a15018f16e9cd14c70c20d69714f1ce18c90c897271e06644421eab4,0x1e21c208059aa4504f5ae6958b46752768820758f4181256d19d91b01b99749b5154150a98a782141d1ad01634aac0a3,
    0xb01919d09d91771d419515295494f18e96c71a90e2d2d8b389684222b9b400bab492b1daa521c208059a0420c059ac52,0xc1ba2d003ab8a4101056b99d09b019195298e94c902b5a171c4414ee12408c77090152e624572101056b99989781711,0xa6c65c454253a5bc632403a569cd01101056da1b999917717097815619198e96d14f152958a949060cabb00332764cc7,0x32bca460dca5ce24f2772110af1b04c6a62c99ab1950100aaf492b1da0460495b626e46665e056855c7585d26d065464,
    0x8b1687487c871812d6da1b819994f1589b19b51d4156177194906215eb03c0c56c072b03b140432acc247910c1ba2d00,0x45e05625d46d055c5385bc734758742646652408a9cec8ea729b11ac70720ecb002abd1c5078b16870830168a90851d6,0xcc9ad10c1b9472c0a3a9bc5ca5e45d055c560531c408d7b405a1acb002a675c0ab3a5d1a99a181ae2d040415b666e866,0x166b14878870820160811568890c20d69299518c96e9cd1ae1101b9a7046a9c1cd1a999118372d0163589c7722f0b15
  ],
  [
    0xa6b8631c14f5124572160711d019194f1ae18e96c71602d6d019427a4951060cabb00332764cc76a9487082016681083,0x415b666e06625e45685326b86d27585d054a5c26c47406464404b5b606e46665e25687585d06d264a7466c05c454253,0xd197115094e96f18c900d99a72c044a1d264a7466c45c054263453a5bc5e44322ccb400bab492b1c30758b400dce2904,0xbba271ca8308359dcb46a4a6666545ba53c6b8631c5073534cc7681181256d91b899997815a1571b61749d41951929,
    0xb095016f18e9ad14c90c85a571e4430758b4101056d99ba1b41d61d01919b1100d99a9160542815356245724e16f1ac9,0x3531ab0117351cb076b148789ac87a873713811010d6371399307101056d99b819895a1571b61d41d11919951749729,0x62654d751541055833b2b4418a8cdc5320f0589741b51d59561931729d115014f16c9cc1ae18c70e0356d252419427ac,0x16669cb070820166a91811d6531589cd14e18f101199d72b280561cdc6c254201d394b0054e8ec02e31ab0115479cd01,
    0x5aa92a5320c12567324f1ce16c7019ab4b2b1c63438b40688d6b1aa521c208059bc9a2420c0593c9ac521e4ce21e31c1,0x959c9cb9a95906509eb01c22aec6891b05a9d49561741789b91999929951b59181456d89999d11701791749951b59ba2,0x92b1c50495ae67585d06d465655256842225cf408d998d00561cecae1141256cd1ae1b527426f24c2531d0114e898900,0x532101056b999a95a1b61959d019095295427324f1ce16c703189db00c6b8ac6a9487088973d22ce31c322e8b4044b9a,
    0x415b626e666a7546d865655274054c6425ca7385305bc5d05e45685a245a2565585c253073874075242c6c62c5aa92a,0xb23462c521da1c1173514cc7d07083016d4a78a7296b14895315aad0190908201678a7326a94b15aa92988718195ad04,0x241833aac026ad1b0208059d093062a440415b6866a5e45625d075455854c6425ca5bc5304519331cb99959b4902e899,0x561d49da1b89b5a9524c16f1742015873b231c50495b686e26665e456a5d07546d65585c25bc53054c64a63452262c65,
    0x108772704199a9c99ab89b5a02635ab0504d5a665e456a6e25585305b25d06546d6752768460656b41413569997915a9,0x4411ab524ac703531ab2c1dac521e26b21e1cc557645685507586545d25c05ea5b45ac85074694105c9953308439075c,0xca3b568ad66e47667588058d8ecd11cc7181ae2d060475b666e85505625385b07327586d641ba20ec8f2531042b1e934,0x72974105e0acb0074e52cac302e31ab0115479cd0988d635d99b917a95a1989d61b59711929951060cabb23c94c74248,
    0xc56a552531c5222cf40688d6b00c6276c8c76a94870820166810830166b14878870820166a9781aa59aace24f2501931,0x911529549b61b01ad1ce16c1752959060573b010f551c73251e22dba1999741951b59d61b01ad1cc1088d63724a9bc94,0x46d86565d055254c64a5c27405385bc7327685e443342d34181b1ad2c46b1c0c6276c0c1256d91b999a97895a1d41d09,0x681101056b9ad629a95a1959909529549053985b1cc81762d76856a54c64a7427545585bc730531c50495ae666256a75,
    0xcc1ad1b016f1711531589d615414e1060573703816a5c7aab5a74992995199a1488f2d06063ab40708abb00a63cac8c7,0x709751929949060772b0119d524532782b0dd92b11501d0b92a4f27317a97516c71888d5d01c22aec1811d6d91ba1d09,0x7a96890830164f26b14879338870c8995d231c11a569cd07c871811d6d91ba19997a9589b59ac14e1541cc9d61b11d01,0x84e41d96c05bc5c454c530a665d065475641c22aec0740eab033a851c92a7a96890851d6b4a7896a948708201652a6f2,
    0x41db1b04604759c0ae86c46d09625585bc531c3856b5686e26d89c0950ac46b1c322657408e958d0046676c01e855b33,0xd15b010a57a48b38c70c8d62d011356a4cc71811d6d91ba1999589b41561b119295018b14a96897317a9d59751949066,0x14199ad01625cac1a89597415614a96897296f14c1531ae1b019099aa0a9d18d0158476c02b394900ab18e4792b52058,0x4c2741b51ba208e0e5d1a1c11ab514ac7b0708301678ab4a7296b14895315aab0190908201678a7326a94b15aa929887,
    0x2569915a17a9959751d49d99b89b626c14f154201e855b231c8ae2d656752766843730b40560ecb0097346c141356562,0x9d04074e52c1183aab266b627568094e6ac1413569997915a9d895614c16c9741951d59b49ba114199ad01625cac0c1,0x76c01e855b340860e1aa402539a9366a5681c23aac8c76a94870820166810830166b14878877911654f3106a9952b094,0x841583b2cd11cc71488b3d01a235ac04295e9050495ae86645e256a54c64a5c46c26d46b05385bc5d055273475840c62,
    0x254a417a2b6e856a54c64a6c26d45585bc6b0531c504b5b685e25d45c06c26d06e466656a6b85bc53254c64a65275655,0x6d118566272c24094e6a418d8989256b66462235741818ead01c22aec0298f2b231da04404159b06b2f669cca6a65664,0xb924f2929b09d115017317a97516c701199db010a57a41811d6ba1991589b51ac1ce1d414f1561929d115017317a9749,0x89ac87a8739934794e68595ad41d99d11b0104579492b2738530d4c8504b5b666625687506565526d86b07384337051c,
    0x9aacc27817297517354459297097aa992b1ad11d59ce1ad101ab3171d44660caac181b1a73609b1c109eb1c5076b1487,0x8b075c9725815614f28c714a0f4d010a579c00ad1d7040c25b646e85626d675855c6c274664465253863c6b44466e41c,0x166a9c0b8adb89d59b619497516cab19ad20507a5715c840c25b646e866a5e27567406445ca5d46d26c65b06b473841,0xcc1d61959911b19d0911615992b484232adc9aa5297030d098dd01c1a96c05681d91bc95c81625cac8c78b1687487082,
    0x7aa726a94a853027a4b914e8d0d9aa5726f170252a00cb9a9011ac6a4ac71488d6d0310109ed91ba1789581751b494e1,0x7724f26c718286bd00aa1cec50100a99d90505159bc95cac6a565d441625cac8c78b16870830168a906e89d78acca108,0x1e26b21c20805820455a22440415ae26c47427645687586466526d65326b84162a99c9aa572cc27817297510c2256d82,0x7281db15c840c25b646e866a5e05627566d45587426c66445ca5d26b07385b44181dc9c9724f28c704295e7141dac52,
    0xd1a01dca191d47384270eb7469606d66b46e86c09b1c5283d3400ad1d70109eb1c1813d64c95a1d89190363d060a52f4,0x7a48c76a94870820166810830166b14878870820166a91412d6d91ba19897a9581b59561b117019294f1ac18d1971d49,0x265464654a7425c46c06d67306b44162cc9c74a5726f24e2d611710e2b05c6342c14b13292e8452235b414199ad01162,0xd4b715c86a1586526c06465c2744447a846411dc5091dc93c7326b85b1c421ea9c9aa52900a99d9040415b6466a5e056,
    0x21d59c00bd5471caa6a83226ab414199ad231da0440415a565d25c46426c64354e124782d01116a439011ac6a4ac2110,0x8a90851d68b1687487c870a578d50100a99d9040415b625e456055c5387307585d26546467445426c06d66e86b49bc44,0xb24ad2188715736245051595ca645ea5d45bc5c064a6c44097266495ad19509042cec9331c6222af48c78b1687083016,0x971d0074e524058aa6715c9d44308959dc93c9b1c6222af41010569a97919197294f16c1771951d59d1200ccd59062c2,
    0x7a48c76a94870820166810830166b1487887082016081156889141456d91b49d61cca959989929d19b115097017a90d0,0x46d86547406465c454a6c26e09b1ddc860475a6a96254a8152e624ad1cc305681d915c9bc931c52235b418195ad01162,0x1acd14aa6a82226af404589e9050475b6466a56874664454a5526b87307586566d4c40415b6466a5e25687565527386b,0x415b606e45e25685dc5526d87546566427465b053c6b26c05c4c06b586c101056d1a909959060ceab331c52235b40ca,
    0x9ac7724f26c762a98dcc1ad1058b3271d2938ad895ca86a636d29dc95893c6b87305b1f6846222af418195ad231da044,0x26c0c54c63341503a3d0442e2dc72a9a9108772d15c840415a6a5e46425ca6c440d4b52450202539a9346a56b5481a1a,0x4599a915c831055b509b04181e55c9724f28c700a99d7141dac521e26b21ea1ce045c1e27566b26d85d465274464654,0xae16c94c70991a5b01a83d2c00a77470206e8dc5a1213975d915a14c90664c57008a9cdc95102635ab0550e624b9ad1a
  ],
  [
    0x9897a9d51971d01b19711929ce18d1ac9b616c1749541143256d99b919897a9d61d01b19711929951b497415718f1cd1,0x764949b8a8c5d12ad1b625720c12564f27717096c70f10a5b1e44380d5b49518c78b16874870820166a90c2256d99b91,0xce218c4e871c4b649eaa6664a6c66b1c19427a49518c78b16870830168a9101056b9a70252a5a19a991a04589e9003a2,0xb99729cd16c17919a9b1191905cb8291dc850c95b6256855c7585d07405425bc734531ed24304959dc5b053c4615465c,
    0x5820455a224504959407425c45d0b304357085c5726f102567270117469cb1a9299997a90e0356d019427a4949101056,0x666a5e45caa429d2406acc6c1811d6d99589ba1d11b19ac7181754d00b8c6a4b426c700a7747141dac521e26b21c2080,0x66e466256865c5526d863453c73875464a7426c65c45ea8421eab4181b1ad00c9c36c01e35491d0ab0840415b466c46e,0xb41951571ae14c18f1cc9d61749b19701929d11d9ab91142666d01a83d2c6d2042b1e7002a675c081d637168450475b6,
    0x46b06c4814c5d24046754915c9bc93841815cdc9518c76a94870820166810830166b14878870820166a90c33169897a9,0xc9d25bc81815cdc9518c76811413d64f2772561050973b003a276402539a9252440415b685e454a56264666a6e66d873,0xaa6664a6c6419427a402539a9252460475b645625407425387307586c66d06e864a6665ea5c4414ee124ad2058d15715,0x58972b019427a49518c78b16870830168a90851d68b1687487c87d62645d425020e606a92b07384407569c045d1a71e,
    0x7957254631daa521c208059a0420c059ac521e21c20805820455a224308959dc93c9b04181dc9c9491432566f2572741,0x99535dc93c9b24181dc9c949625c8d7724f26d10607957254631da04504f59dc95853c8181dc9c949625c8d7724f2060,0xc5c07445ba5327306b8631c4232adc98910d09ed0614c6b40750e2b2c1dac521e26b21ea1cea4d04404358ea4d64c1d8,0x8ea00d794734046a2d66545d254064c7445b45327306b8402ee51c72a14604c7b686e65e45605d26d475665c55864a54,
    0x887058956b231c036669cb070820166a91011d6571ac94e1509931084c6b93349b09608314e5340853a3d0518c6b472a,0xd116d1cc1ae1b5295999110d41ed052235b4035463b0037351c4ea6a948792b082016932771689083016d8a7496b1487,0xae11830467b626e66645e05685c47407545527386b46d865640951cec06a998b1308177051c5326ea771689995645b99,0x81eaac6c11411d6702d11d82d625495a16e94c7ce1545561d49da2702582d11cc708195ed031615b4058956b0156662c,
    0x191b18b060cd524182a6393649d4416255ac00a99d922ae31c162e8ac00cb9a92b1c20805b6056875874454052c55281,0x15674a72a6b14a95729318870c89aad00c656ac082016ba1999781589b59561d494b16897316e94c1529ce1d01909972,0x6ae26d6819ab0ac1813565a24c2781d91d620550e6b1a1c0373514cc7d07101056d8a74a7316a9489529572d01909081,0x9856ac1813569915a14c16c9781959751571b49b99d89d6103195ab06c2e27586d6552415a0aec055998b231e8ce2366,
    0x6b4b076b148789ac879887555827016aa029d1a500972654da1959cc1d51561b49b9a10635ad0175611c772056a23b01,0xd49b59ba2ce201d53171d4c32255b408bb06d1ca830c659e055854c5626d66e876664a65c6645ba530738631eb1c614c,0x45626d47565585d25ba63264a5c4402f5524972531cd1d090c635491e0931c02ecca4101056d99991561531909971d11,0x70615385cd9ab5906e0e2b342441425b686e66625e456065c5d26d47565585ca64474254c5b063a734430c65b686e666,
    0x11ab2c1daa521c208059a0420c059ac521e21c208059aa421013ded616c1cd1ae1b815715a17294c95019318ea02e662,0x8ea5295715a14c7101056d81999791cc96c17499517318e99094e1529571589ba1b59d61d1100ead492b1c414e6b4075,0x2666450475b626e67445c27305b45e066456854c5527585dc6d4656631c33285b401d58cb0095666c92acc588dd62732,0x529731d01909cd14e18e9951b59ba1148732d01d5c42c6c7181b1ad2b1c19427ac00dcd47060495b305b25e06d66e465,
    0x8181d59c99ab81951b59181256ba1999589951b59561d49d91781709d0105ea14913a63264a94c9dc4177442cce10e8,0x46325ba5d28182b5ac011af4b2b1c414e6b407511ab2c1da0450475b645e25685dc5527585c054c5b453a63264a74273,0x455854c4504759dc94c5529e2b58968b60931c086bcac1430867b626e86665606546d655c53873075864a7445425cc5e,0x7107266b58ae86d680953c6c1a8751929d095017316e98d10c89aa71e2b38931eb1c43427b41852d4d05a25674273075,
    0x8d5b645e256855c7585d46527305ba6345325405cc64a7424418d6a4141d1a7266ae06d671762164a9ba80d6345c075,0xa5c781959991d991888abd06303ab46ea6890851d64ea6a948792b0820166890830166b14878878c700e95a7341f21c6,0x781d59d9199958908686bd004e5c6414399192e895841426aec056958b338431465b545dc6c05c454c6b453073843832,0x65e05625cc5ba53054a64265c7566b86c06d25d45585a2420c059ac521c1426aec8ab8c7058d62b003356a4cc7181256,
    0x1c03ab514ac7b07101056b8a74a7316a9489529572b0190908115674a72a6b14a957293188702999ab020805b686e466,0x1a1af4056958b231f0ae23666b62756819730ac0820168d18a9181256999b61b915a1d89d5907511ab1e093062c521da,0x11c772055c23b019466ac1813569915a14c16c9781959751571d49d99b89b6102999ab04822a65c9d4a649305ba5e082,0x805a645e264c63a5b453254a52c622415ac0d45827016aa031b1a5009aa654ba1959ac1b51561d49d9a10539ad01795,
    0x9517318e99094e1529571589da1d59b61b1100dcd49331c418d6b406e11ab341daa521c208059a0420c059ac521e21c2,0x9598c902e8d172d896842330af401e54cb0099566c92aac688db627328ea5295715a14c7101056b81999791ac96c1749,0x746724a86a25663a6b47385b05d45cc6c064254a55c531d6842383b3405e0acb003ab51c1411d6d99991531549771d51,0xc6c25c05dc6d441b9c42c8d11411d6d81b89999791549b01531709771951d59b618c9ad1ce16c71085abd00b918ec08c,
    0x86c46e25607567686665e443234574081cecd331c418d6b406e11ab341da0450475b666e06625e46b873075865655254,0x771949d59b09ac1b51561531101056771549729531909b118e9ac96d10297a271e2ad8968ae0931c60515a54938ab06d,0x5a561c05eb10715c9ba5d25405cc64a6c24314e5240c15ac71e443382b341462d4d01583b2c182456999789d91ba1581,0x5ac2593609c0410d6b2405cca89338531eb1c162a99c019d5471d1dac521e26b21ea1ce64d1c6a2565327386b063441,
    0x3244c9cc10c12d69897a95819315097016d18e9951571cc10c32d6b919897a95a1571b61b19d11d596d18e9951931509,0x4c15a15499119718c7011ba3b2b1c2646b34058aa6704a24c6c26345ba5c454055c75841c1396c02cc9992d6b4680772,0x865c6d26c6807aa8641813d69915a1b89b62b1ad11d59ce1d827aa102056d91b899a9781b61b19709d01d59531ce16e9,0x11c8ea5a94c714b0b4d15c9cc941e2c5a1d21c208059aa440815b686e466a5e06446325ba5c274054c73453056275655,
    0x95ab1a01477190155cc246d2098ba1723a96a531c163295c05897271dc9584604f5a6aae2568739423758ae86b2422ee,0x27385b1c260e974058aa670143395c019d5471cc95c9d1e2c5a1c20c05a2a430895b409b04421ea9c9aa5818d135ad05,0x8f0b26a9baa31c5283d34058972714c8604d5a6a9685e0440415b606e26645ea5686d86c664265674475254063a6b453,0xb59d51561110373b04232adc992198951d03c8532c0e83a2b003666a40cab8471ea840415ac6642656ad484c8566c06a,
    0x1d658a18872ad0039d524019b94726a9ba81626a9c7476b148789ac87082016081156889101056949919d096d1701b11,0x101056ba1789b117019096e9ac18d19a9d19d91ce2971d49b595615314c7099b067160426459b4118395d02646b34181,0x4c718a0ecd002a675c043d62715c9cc941daa521c208059a0420c059ac521e21c208059aa450475a5c55254c81715c24,0x1813d69aad8a74ad62ae25a18c9101056991d619497516c9cd1d89b59ba1b119190c45a991e0b40ab0422ee11c8ea5a9
  ],
  [
    0xa5e056265663453a5b26b06d46426c674075245c8386c14a83371c4c509e85cce2ba21411d65470ca174d066458b4772,0x45d1a9331c066e8ac101056d82561589b59ba1b01919044cea91dc94c810f58a4ce2ac704455e9131da0440415b6466,0x1010569a9791b59951709b119198c96e914278c72e0b4081772124772531042cec9040415ad66c46464510e6a4b82d02,0x8ec043566900315ce4101056b13b5a94991a10d41e926aa344404159eaad6a46ac4a3a5b1c5214cf400c59d901193b24,
    0xb12d01101056d91ba19897a9b597716d18e9951d01b1191970953158154ad61cc7058b32b0086e6ac046b1a92b1c0c55,0x1f21d6958366495c9ea5d45cc63a5b24039d51cd12cc2101056d899a9791581d615499195318c96e9709771951b59ba1,0x66d8652646b44a3aab4a645ea5b1c460e5740991acd0143395c019b9471cc95c9d1e2c5a1c20c05a2a421475a2c5a1d2,0x27327587467644621c574182761d03a8632c0f0362b003a56a48ea7a96c770714a0f4d14c8604d5a6a9685e0440415b5,
    0xd1a72c0840415b567686547426466c4447714248c9cd10c8d157030b585c118b91726a9e4440815a626566446c26d455,0x5727325076a94870820166810830166b1487887082016081156889770465d929aa7816e94c10435ac73384177211c045,0xce2d815a1101056b89991b61949919d11d59da1781751b01ad16c9cc108bd44723a96a531c6283b3400a7747010ee89c,0x273063466a6527566d46c286303aa418336290609d85cae2da21411d654710a19dd056468b47721813d69aab626c2b02,
    0x6758ac044cea90ba16966a5dc5e454c6325ba5c2410ee8a4ae2cc70435ac9131da0440415ae05e45625c074464653a5b,0x574901193b241813d65a2b62011ba3b050475a625dc63a5b45ea6d86e45685c254c552809722ecd82b02046b1a92b1c0,0x57150a02cc8b9060cd8a4da2b61ac7021d5ab011746a4cc70295a3b0d794166aac4a344304b59eaa3a5b1c5214cf400b,0x42cec92b08404159e46465ba63266a6d86e2654756768744421ac664582b010c12d69898e96d17a974a732b01b91581,
    0x766731c03167644c70853a39060475961dac521e26b21ea1ce0440415a46b685606d85dc65455254c7407568086e6ac,0xca116645ea5d45b263a460e1a9cb89ad1031b1a700d6265cb1a702d99d41d1202b53192d885ce155d0ac69c4ab8b5874,0x8b16874870820166a9650b35742ae2d61571501931d11cc1043d2a71c28610d6a4085ce172c6b664621397400b57491d,0x5a46ae6a6a9684404159e4a666546c66424112a7a4ad108eb187344403a56a408bd44723a96a531c1ac2d2c572732507,
    0xc12d6541ac94e1cc1045d1a71c05e25b48262e85c09dc217040b565c8ea5aa99a101056b9a91ab0705d0b491dc84041,0x80dcf406509e901832adc101056b9a991b09919d110e606a9003a56a4060cab71eaa3a8181ea9c9478b16870830168a9,0x6e66b1c02d5d244c7099166b0218d8e41811d65876b148789ac87082016081156889101056b9a91ab110a52f0916842,0xc15b99b41951931b11d1950957174970103350d9358840815b6266a5e47546d865c5d055274664454c7386325ba5c26c,
    0x4878870820166a9101056d89b999718e99916c17a9749b01d19909531541053174b01cc2b2c71204551e90031676474c,0x59e4ae66d87446c06466544182b5ac0720ecb2b48109eb1c043d54701425cdc5727325076a94870820166810830166b1,0xe95a901832adc7aa8ea0607aa70086e69c9476811413d68ea4c95aab1a99ace2ba21411d6951547199162d1dc84041,0x46d86c094c9dc41626aac00e95a903816a5c7aa8ea060756701832adc101056b9a99191ab02532771058956b019427a4,
    0x90381539c8ea7a90e0395d019427a4060cab7251e2c5a1c20c05a2a421475a2c5a1d21f21c6a2467425c47305385b26b,0xd9a6ea7919a99198c706509e901832adc101056d99b899915a15415314c9ce1d09919711771d51b61ad26c2b0100d99a,0x6810830166b14878870820160811568890850907ae456855054c5326b86d26c05c45dc5b073475843c0d8ac7aa101056,0xb003666a4098d61716aa3a4162655c05897271dc840415b66a464150676404295e7010ee51c5727325076a9487082016,
    0x415a46b665dc75474094c818f0564025c8b933841832adc021d5a7251da04504f5b546d05325586524188676c0a83a3,0xc4e04404358dc4e64c1c304358b1f39423540a3a9ea5b4ad07587304163455c043b9470067589c57274973206219d904,0x6c074cc94cc2b02081256899011d1d5168d2c81634554470b1dd92b127317a96d2cc7ac2d070262d59251d51dd1da1cd,0x415ae4950ac26446b063a7347404418baa4058d1570422bc9c99b0812564b28870262d59251c504d585051598c6a966,
    0x4959d0754f66a5663441aa0cdc6f25314c705611d90045e95c050b337168ad8951f286a1d21c2051592ca21c5051584,0xd05d050b42e4143d119331c047395cba2101056d99b899a9791741d51959b116e9ac1cc9d019098d2083d6171cc94a45,0x901d03aa4050b337168b58951f2645814c6426b063453a5bc5d05e45ca81530ae4015c639052b08e41811d65897a90d1,0x8dd05cc18b407282b71cc94a440415ae666a6d46566c26446b06327347407625d05e45ca9bc94c531c04ce96405611d,
    0xc6390604759625ea43474174141d1ad331c047395cda2101056b999917a9b41959751909b11ac96c18e9cd1d01d8a133,0x55c947081156887081356101056b919997a9589949b59731529ac16d14f18e9911b09d01d51741058d15b01530ae4015,0x450495a64b666e85d05c47427546d65586c06b46a2521c18c6aa4771505b09703992752ad1046ad47344721f31c1833,0x26b46a0522550568860835a649b0b687566d86e65d45506b46c06a2420c85aa8521f44721c50738b4045cd49020c85aa,
    0x4ab49e466256a428731740a0c6bd00872754cc7060cd57040415a6a5e264463c53a54c5b05ca7407646e66d87565d46c,0x8f16c94e906057372a1c1543d2c04551e71e4ac46b1c1173524141256ba1b59741561d49d99b01a89481ca1088ba3534,0xc34083216d09c81141256da1b99741b49d59561d01c89487101056d99ba19a9589d49b59561531481ca1d01909729741,0x89bc95c568531d41f286a1e2c921da1ce64d1c60c35958a6256a7285224306a994d9a792b59b11a81ba2181ae2d0286b,
    0x4c7507c991813d6ba27725815611813d67aab628ea6f25715a14c70b42edcc9098d6172b0b60ae89dc96a5584604f5ad,0x4f5b689dc9605584604f59eab58a3a9bc95c568531c2b0bd6b24262e85ccc2b82da27725a95611813d6d626f25715a1,0x1813d6b626f27515715a14c70c2366d0628477400a7747141f286a1d21c2051592ca21c20495820455a21c204d5a2c86,0x5ad8a3a9bc5ea5c05d455c568531c6283b340c1156ba19919598c9ad1b49cc1d51d89771929d19b017116e97815a9561,
    0x2558b34ad4a648461ba7346b06c26d4558752656418d616c06b434b008cdcac0439aa71c1c56868740704e5b1dc83047,0x5e94273527407348262e85cda24f15a956177101a3a5b0109d99c00a9737141f26460475ae86c063a6b25b05ea76056,0xd2c7070704e5b1dc830475b58a3a9bc5ea5c05d455c568531c6283b340c1156b89991781959b51929b197116e9ac18c9,0xc2c06ad18b334ce5439744f30ae066a5e4440415a567446426c66d4b3063a6b26e06645ea5b1c50d63341033aad01ad0,
    0x1a56a4a87058972523ca544504d593ca5c951c074cca47470811568870813561811d6da1589d01d495610133a5b018d5,0xb61d59da1c811431169895a1d119295094e9cc96d17a9b19ac1b91d81b61d59ca1487193305d060ccab4702022373901,0x67226a0528c266cc3400ad1d9014e8d2401ea549334ab1c182bc9c8f25729471813d65a2d1ad61b59142116cc9d12b1a,0xd61d199116e94c9529b09025c5a91c0f31c64298f40d0b31d040825b606e86645ea5626d67585c25b053a54064a6c474,
    0x4f2102096d819915a1929d117095014e96c17a9b19b89b61d59489ca1a83141d1ad00771524101056d919a9789b59c89,0x9119898ea6c7108573d0181dc9ca894870991a5d0504759526a2420c85b689586a8521c070e564c87158531d01616954,0x5a14c7507ca1a878b2487687381083216ba2561a811411d69aab19b91b61d595495a152a01cb9192b0c195e0a4101056,0x7725a95610c1156d89b91cd18c9951749929b097117aa99ad19086b0b901ac4ca4086761900d15664ac2d42b626f2571
  ],
  [
    0xcc2b42d626f25715a14c7507c9922a99d8ea7a9b01b89ad100bab47022ecc1c71106b132901ab40dcb625a11413d6ba2,0xc5bc63a7346b2531c3c429741320e9d01ca0adc072b0373589684504f5b689dc96a5584515059d46526b263442a60cdc,0x429ab7141f286a1d21c2051592ca21c20495820455a21c204d5a2c8504f59dc95068d1176d06c66e46665ea74076255,0x4c70720ecb030455b646e26666d875264a7467306b46c05c45bc5d065463253a55c5685ea4308d9b407211db0029e95c,
    0x949ac1b51d41ccad99561589ba1919b09701d131884e5d0568687405ad44701625c9c7720c11d67aab628ea6f25715a1,0x8430455b626d26547407346b06324266615c032a6373589bc5d055c568531c068e96c07211db0109eb1c507c99101056,0x85625589c0b50ab1c668587405c1729016ae11c7720c11d67aad628ea6f25715a14c70720ecb0504f5b689dc9e456a55,0x181b1ad2b1f286a1d21c20455a21c204d5840415ae66645ea5625586526d46c06465c45b063a734750768742860475b6,
    0x46ad490404159baa6a64440332764529182acc92c6b66440415a42e5c93c54a460ab324d9ab19045cd49331c422bcb4,0x32ace4532772ae2547ca1a878b24876873a13471010d6307082396083216085456c8910105690a529042b1e9002ead24,0xd51959b018d16c9711929d09cc2581142116d59b499519997895a94c70c1aa6d042a8cf4119ab0d0086bcac05e0a5900,0x949d59501929d09b11b816e9ac9cc18c714b0b4d06ac18b4183561d01cc296c0298f27010f589c4e2b627321307a9b49,
    0x62e85c5a94c7101cead01782964532772ce2547c991010569099917a99596c9751d49d99b8958152a1b09997895a9751,0xcc18b41435a1d00c5a95c043ba27138b589cc8304559b4632411a2adcd02ac25810c12d67898e96d172a00cb9a92b242,0x5a2cb3a119740ab0418eac1c95a5295819a9b99171702d05c2d663a64465266654a5605ea5d45b1c42d617410b172d05,0xc830455b669e05bab526566328066ad1c043d627138ad89cc95c9d1f286a1d21c2051592ca21c20495820455a21c204d,
    0x5cd4292d4c274686405c570916a730531c42a8cf4011ce572b8850475a6693856a6d8654756551c5283d340720e5b14,0xd05654c340560e59010ee89c4e2d62732572747c991811d6b81589101056d99b89991781d499598e96d1729d11b01909,0x75c0317627338b5245047593856a758551c5283d340720e5b14c86047594a562b64842d6174199505d042c5cb41435a1,0x747081156887081356101056d917815a94c98e9909729d01b11b89ac26d2132a587266ad6654c467217400ccd5900c62,
    0xd61b59142116782c81143116b9a4e2b61d59ca14870a0373d2a1c173055c05c172524ca544504d594ca5c951c560ccb4,0x561635b59d61d9ab92d12b071888d5d26a631c1943ca4932572947142116489c8115199852e466263a8631d09cd9a4e2,0x72644604759e056254a5c25387325ba6b07286a252044782a54d03129cc2706b1941c115199504d4a614d59b61b9ad92,0x5ab307016869545325a50cdd12d59ad1b61b99a81b0905573090445dc141421164c94a211178550085dc946c7108cd5,
    0x1411d6b9a4e15a9549b61d59cc9042d6372a2521c065695c1411d6549a89083216ce2561aa1487118395d321c16b415c,0x402f589c098d6171caa3a45662c1cba25a94c705d0b4901625c9c532772547ca1a878b2487687381083216ae2561a81,0x85cae24c15a11013d692a50718b0a5d01ac2d2c732362cc5b025a1ae1cc16c98d10c1356791b49ad16c91416a672c0b3,0x9e16190645c15c1818ea70262e85cda25a94c705d0b4901705ca4532772547c994318edb931855199256b66732420f5,
    0x2d67a98d16c9711929044cab9340ac26b0b38968450855ae46665e26526d67545c474264a7306345ba6b26c0467418a4,0x2560811568870813568b210105674a90aac9083ba17338b625305684404f5a4a941c62c297406b0b4b018c5cac732105,0x46c06e2568531c52839b40720ecb040475a4a7446c0541c1543d247321411d6532772547ca1a874870814564b2887081,0x2839b40720ecb040475a4a7446c0541c18c5cac0550f491cc85047594c9dc951f26460475ae856241d1ab7309d06b86d,
    0x1568870813561811d6da295ab99589101056d91b999897a9d49b51959741d016d18e9911b09ac1083ba17338968531c5,0xcdc1813569aa78a5a20c11567426e9cc18c918d8c27366938ae86d66b1c4343cb418531ad0035cc9cb07ca1a87487081,0x81016082396083216085456c891a05094e9ae1cc18d1055983724c95c41543d2c035654b1b28115479c045cd4700362
  ]
]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
private lemma check_c1 : checkCase r1_c1 syms_c1 50 chunks_c1 = true := by
  decide +kernel

private lemma solve_c1 (L : LatinSquare 7) (hred : IsReducedWith (r1Table 1) L) :
    ∃ σ, IsTransversal L σ :=
  solve_case 1 r1_c1 syms_c1 50 chunks_c1
    (by decide) (by decide +kernel) check_c1 L hred

def r1_c2 : List Nat := [1,2,3,0,5,6,4]
def syms_c2 : List (List Nat × List Nat × List Nat) := [
  ([0,1,2,3,6,4,5], [0,1,2,3,5,6,4], [0,1,2,3,6,4,5]),
  ([0,1,2,3,5,6,4], [0,1,2,3,6,4,5], [0,1,2,3,5,6,4]),
  ([0,3,2,1,4,6,5], [1,0,3,2,5,4,6], [1,0,3,2,5,4,6]),
  ([0,3,2,1,5,4,6], [1,0,3,2,6,5,4], [1,0,3,2,6,5,4]),
  ([0,3,2,1,6,5,4], [1,0,3,2,4,6,5], [1,0,3,2,4,6,5]),
  ([1,0,3,2,4,6,5], [2,1,0,3,5,4,6], [2,1,0,3,5,4,6]),
  ([1,0,3,2,5,4,6], [2,1,0,3,6,5,4], [2,1,0,3,6,5,4]),
  ([1,0,3,2,6,5,4], [2,1,0,3,4,6,5], [2,1,0,3,4,6,5]),
  ([3,0,1,2,4,5,6], [1,2,3,0,4,5,6], [3,0,1,2,4,5,6]),
  ([3,0,1,2,6,4,5], [1,2,3,0,5,6,4], [3,0,1,2,6,4,5]),
  ([3,0,1,2,5,6,4], [1,2,3,0,6,4,5], [3,0,1,2,5,6,4]),
  ([2,1,0,3,4,6,5], [3,2,1,0,5,4,6], [3,2,1,0,5,4,6]),
  ([2,1,0,3,5,4,6], [3,2,1,0,6,5,4], [3,2,1,0,6,5,4]),
  ([2,1,0,3,6,5,4], [3,2,1,0,4,6,5], [3,2,1,0,4,6,5]),
  ([2,3,0,1,4,5,6], [2,3,0,1,4,5,6], [2,3,0,1,4,5,6]),
  ([2,3,0,1,6,4,5], [2,3,0,1,5,6,4], [2,3,0,1,6,4,5]),
  ([2,3,0,1,5,6,4], [2,3,0,1,6,4,5], [2,3,0,1,5,6,4]),
  ([1,2,3,0,4,5,6], [3,0,1,2,4,5,6], [1,2,3,0,4,5,6]),
  ([1,2,3,0,6,4,5], [3,0,1,2,5,6,4], [1,2,3,0,6,4,5]),
  ([1,2,3,0,5,6,4], [3,0,1,2,6,4,5], [1,2,3,0,5,6,4]),
  ([3,2,1,0,4,6,5], [0,3,2,1,5,4,6], [0,3,2,1,5,4,6]),
  ([3,2,1,0,5,4,6], [0,3,2,1,6,5,4], [0,3,2,1,6,5,4]),
  ([3,2,1,0,6,5,4], [0,3,2,1,4,6,5], [0,3,2,1,4,6,5])
]
def chunks_c2 : List Nat := List.flatten [
  [
    0x729d11b099015318f1ad1cc16c94c708435e902346724011735701434adc5895476b1487ca9a878873a93713072c7287,0xd99b919817a1749b61d51959d01711b098d1ac1084a73733281528cdc9326ea5290c3096d99b819917a1d49959751b61,0xb51b09911d01ac1cc90c8d6272e89e25d85b4822f511c72a8f25314c708b13590218cae405095e70046e71c58195621d,0x59ac521f268208059a84418251ed89ba1999791b41761951d59931b11d017095296e9cd1ac98c1654a35d91999941d59,
    0xa6a65a1d21c208059a2420c059ac521c208059aa4208159ac521f21c208059a84210659ac521f2a6a1c208059aa42081,0xb89999791749951d59d11b01ad1cc9084c6b7242630404e5c5c72a6f25314c706c09e901b846a402999a72d8968551f2,0xb6e26605e45d26346b06c4642740754732828ee21c95ad991ab062d06a5c0b41aa119d014f511c7326ea5292eac25d81,0x7326ea529b8a8c5b41d11b0990108477192b4632730422f511c72a6f25314c714c19a90506279c141d1a72e8960714e0,
    0xaa1c99a53835d91789751b49941911b01d09ad1cc1113c457232844ee21c99ad59173062b05c5c0ac172119b0239d124,0xb59761d29531709cd14e96f17910c5856d00c6276c9018c70c8ba2d0086bcacb11ac7c99a87082156ca9a99687083056,0x63c11b7626e86665e46d65d875474054a53c73a5b25cc6426504294b1ac54958108899dd00c6276c6b1165ba1999951,0xd1a72669d8ae86d6809aa66c4ead2a5322356a5999761791ba1b5906b982b1cc94a93c73a6305b1c4343cb401d3a2b2c,
    0xa9ea5d85b1c0ccd8ac7076b1487ca9a87887371399082056085156c8999846dd89791581d515499417099118c9cc1068,0x1a8549d19cd14f1ac9b115019319599918c70b306cb022e5c1c5aa183316589541b49b11ac1cc9142d0b72e894ca3c93,0x135d00ccc56cb33215d81b899917a1941751b61d11b01ad1cc9011d5c7246b56530552414e0d6c06899ab01a9cc2c532,0x4b547328681335c08ea1c7264760f46a5682ccca2c08bd44716a830c25ae8a3c93a54c5505625ea5d85b1c50cc5b408b,
    0x566b1487c870820166a10841966b1487ca9a870820166a90820566b1487c9a0820166a1c1474d9314f18c10b095972b,0x22771b053066a4142d0b7052a60dcba27326ea4f15a9561507ca9a996874870820166890830166b14870820166a9082,0xd19b09911959ac1cd1d410328cdb02c21aec615875d81991789d59b41751949d09919b11ac9cd18c718a744d05c446ac,0x761b06a8386cd911990acd042d5c3419a360d00ccd8ac01c5719010ecc9c7517077aa4ea6f267442dd89981791749b51,
    0x855b2a6a65a1c20c15aa872662a317656a407464078d8a4b09ac2043cac701626a9c7491a8911d19b01ad1b49561190,0x11973b2b98857626e46605e856a6d86c66446567405cc5425b453c73a7545505d2e31c322e8b4043b3292b1f266a1c2,0xb1a014af191504046e72c044a9e92bc8897606e86625e46d65d87546507426c464642328ce47325a95014f1ce96cb549,0xb337161dac521f2a6a1e21cea4d6420815821455b2271b1075d474073a75276456a66264463040a6669c7a295ab81b61,
    0x46c26d45d855c53263c734752740766462ab134188ae2d02c5d12c08e62c91ba94a802ecca4ac7099135b0218cae4081,0x8d14f152a08bc2c9331c2a4672c08435e90207571c66e425d99761789ba199191a086acc92c4f036e86645e26506465c,0x274464654a5305ba6b46c06d26e8454318f4148ce2d02a262ec085873923c95c818356acab42c57a2b619715416e9ac9,0x59ac521f21c208059a84210659ac521f2a6a1c208059aa4208159ac521f268208059a86177057666605e45d86547505c,
    0xb027a406e11a900aa62dc06ad0372d89ca9bc93a55c568541f2a6a65a1d21c208059a2420c059ac521c208059aa42081,0x6b44322a99c0cab3071e45c1ddc93c9baae50877646e05e25d46b2730752650634b466c464266686a98874072744b01,0x1f266a1c20855b2a6a65a1c20c15aa87265aa319666a4074643195324b09ac20cac2c703226a9c0cab3071e24d58476c,0xd89b91999581d51549941911b190c585691dc7405c273a5b453c54a833ac0a4b627a214199ad003a27648c700caf292b,
    0xba1b1604206e73499a22dd91b999817a1949d41751b61571d29b11919501cc94e96f170a589081973d003a276457421d,0x1cdc4e84c1c20815821455b226239d1654b4a9c454253a4621475cd91190a63d0281e36c08c6359015857246f2572098,0x44d5a724cab842d766a606566448059d864b6272a8f25315a96e14c719032bd0054cce40117357151dac521f2a6a1e2,0x76192d86e46c06b2830c35b666645ea5626307347405c454a6c26e07526565d86d46b89b1c5508cf406c19ab0152e0dc,
    0x242674a1c762ae1b09911d0104695a91caa3c94c56a531c440d7b401635c90046e71c344c9d7a9589749711529d09016,0xc30d6d89b91581529d01b097117a9d59b41ae16c9761951999cd18c7154233d0350dc34044d5a724c8308e59e25b473,0x1c208059aa4208159ac521f268208059a8430c35b646e26665ea5606507566d46b85b25d854a6c05c4404f5324d09cc1,0xc93854c56a551f2a6a65a1d21c208059a2420c059ac521c208059aa4208159ac521f21c208059a84210659ac521f2a6a,
    0x6f25315a94c7101a9ed0606c6b4021b9ab2b899b3055e25d4416b582cac9cd1013d4c723040a6669c01397172d89ca9b,0xa9cc9ad6036e46426c06d29e25d481af442cd12015c6393325598b16c0742e44f34631c62d513403354cb008d5c6c72a,0xca9a99687083056aa1c99ce8855b89b11d09d91999d59b419018c9cc16d174995308cb839020f531c08397171ea96054,0x762b8c41dda9789581751549d41d11529909991cc98c114387272569cc93c9b8ad86e66b1c4343cb4b07c99a87082156,
    0x5bc6326606e66d4a44407315647163455a9531d297116f18d14c10c558c71e2952a4240731564cc7181b1ad0067589c,0x6d1cc9019d62704433a5c7324f110d4f072669d8ae06d66b88055e85c54101539cb06c1e456a75065655254c74a5c253,0xcf414899ad002d4d6404652b9011a56a45728f24c76b1487ca9a878873a1347082056085156c891a8951d015299098c1,0x1a56a45728f20c2096d89999791761951901d19d41b49ae16c914a626716a6c45425ca414f5824cd1148ce272e045054,
    0x35ad019466a497255e225d89999951901d19d41b61cd1ac1b91b0a5295817a97496e171204455e90158476400d59c901,0xc2452a7aa0a0d59d010b4ae48a86757616d1ae1063b9073669c294a9ea66464640332764cc70c89aad231c62147741a0,0xb92b6252a7a97516e170a04295e9003a27640c30d6d99b89991581b51549d41d09919711ae16c97620e9d10b2c043354,0x820166a10841966b1487ca9a870820166a90820566b1487c9a0820166a1143416d99981589541d49d11919cc1ac9b01,
    0x8740ae119900aa62dcb626f25714c772a5a9507ca9a996874870820166890830166b14870820166a90820566b1487c87,0x6d18c9941d19b0991199a19aa21d008ae2ec00cb9a91dcab8958652b316506c4642634840b3a5c110b997346a6686a98,0xb89941991ad18c9cc1084ce97366a4682b988640a9c23702a660dcb626f25714c77aa581353835d91b81789d49b51cc1,0x66a1c20855b2a6a65a1c20c15aa87265888dd5c26305b473243530a5cd9a91a09ea2190263585c772ae2561119cadb01,
    0x80eaac04395671e24b43596546606327344563189c91a4f26e1771b61b11b99ac20c856670307551c0439aa71e45c1f2,0xca40589aa71d1dac521f2a6a1e21ce6420815821455b22533709640e6695c9d85bc6b86e46c66d0814c59ac033354b03,0xec26d06b48143475c5728f115999072e89cc8d154053273043131a9cd5a91a08e728916a95cab89e85ca63c5b1c070d,0x655c6c054253063c66064474642781b2400e76290072e464cd1099d44716aab89e85ca5b1c560c5b4099135d15233966,
    0x665055c53263c7347426466c46d26b08267511c0c1972716a5e25ca941c56819a404672a92e8830825b626e47506d265,0xc521f21c208059a84210659ac521f2a6a1c208059aa4208159ac521f268208059a8460cc59ea5625c269790976066475,0x95a172621b05506664142d0b72e89ca9bc96a53855c541f2a6a65a1d21c208059a2420c059ac521c208059aa4208159a,0xc1c5727510e53955a17715414f1ae18c1cc96c710b1aad008cdcac043b327002f589c7077aa956645b41acad19b11909
  ],
  [
    0x5727490ec475b02d825a17715414f1ae18c1cd16c714b0a6d010f2b1c72e44595ad19b11903ae25a14c201a9717016ac,0xa6a65a1c20c15aa872645c2627566d46506466c2740433a2a248d1cc9099d6072b8968530814ee11c0589aa7016acc1c,0xda9581d41b59951919d11529b010d53309152a627326304506669cba24f27717916e2ac700bba271c1f266a1c20855b2,0xa56255c7525d474054a5bc734530452d681c9598c9911b19b42b91981103a56d0406e6b4053a26b03c458ac7a21833d6,
    0x789771949d515416e1cc94f18c1ad1183b117022e6a1cd295095aad8302bca172d6a46ac1c22c59b4033354b0c750d76,0x842d6174058d6271dc90c63b6e45e86d06b863473275455c5d25bc931c58ca1b41a32a8d008d1d5c95a3ac41dba1991,0xa6a1e21cea4d84c1c20815821455b224eb1076e87546d05525406427326b46306645e25b8860ec45c08b9a8734a96ab6,0xb331c62c4ab472a94e41dd897a1d59d01b09b41711749931951999b915295715816e9ae1cd14c71418f2d231dac521f2,
    0xb41751ae16c702bc54b01434aec1840cd7b666e86647506d26567446c06b45b85d45e296054281560ce4932572060d5a,0x4257ac03189db05a1d455264454c7426c04214cce4582ba2ac91420c20a6d89999581971d59549911531d01b09b917a1,0xd5ab2839a96665e85b26b86d26507565d4c343587406cc83b24c95c404e5c6c4ea72900bd159002f58a4cc714189ed01,0x487c9a0820166a146e11d791589749b51501b09d111468d191ca9b853a6b06e8454318f4144c8bd014e5c24932572060,
    0x6874870820166890830166b14870820166a90820566b1487c870820166a10841966b1487ca9a870820166a90820566b1,0xd0606c6b4119b82d054c4c74199aa0d0086e6ac014b8b9015ac0e4013d4c7004e5c5c77272aae25314e95a1547ca9a99,0xb1ad040d5c74073544b0086e6acae25a14c76ea52a7321ac45dd99b81989b51b09d01d49959911cd18c16c9792101a9e,0xd01b11b4a7897510999a8b021742e4cc947382dd81999951d59b41d09901b11b8a7917490999a8b003728e4cd18c7181,
    0xd89791b4174995399ad59173062b05c5c0ac172119b05506664141d1a7020e5c5cba2581cac21dd91b81999941d59909,0x27304177051c4ea7a1531d29911709771ae16c705d132b0035e89cb07c99a87082156ca9a99687083056aa1c99a84c5d,0x5560b4aa5053a63273040b3265c91114439a901a3469c99aba1b59ad17a222dd91b99981589b51959541d49073b10b23,0xd1177646e66625e87525d455c5425cc7305b26b86d0656634423a0adc902d2a4ea08dd0371604214e73406509eb047a9,
    0x91ea9e829556ab46a665d85c25e45ba6b8734531c3226ab4019972b231dac521f2a6a1e21ce84d1c20815821455b2245,0x3a27641420c20a6d99b81589b517617115316c9ae1b09d01d49541919971992170b01b4acc714851ed034253ac0cd886,0x972532044d5a92e2a077626667546d27466c46e05e45c282363c247626e9ae14c95aa0c8d2ad052338b4cc704295e900,0x1966b1487ca9a870820166a90820566b1487c9a0820166a11432d6b8a7915a9549ae14c16e976105ad60b1c2819466a4,
    0xaa62dcb627326ea5714e15a9507ca9a996874870820166890830166b14870820166a90820566b1487c870820166a1084,0x6423a3a24b12b0e41dd91b81d19cc9ad1b09911999789d417519498c712a383d06a446b403274cb0089dc6c0ae119900,0x8bb30716a9e44ba2656b893a5585605ea5b1c40cdcb40631aab1c1ddca9d1076e26b07327606665e45d275465064274,0x7898ee445b029427a95615814e9ae1cc18d16c706b0a6b002e2d5cd03a55d529498d105d9907266b466c4640c30a5c5c,
    0xc6c41dd81b91999909d19b01b49ae14c15619418d1cc9d510b306cb03c0d8ac0a3370b0310dca40c2d4c7022ecc1c5aa,0x8a1a1677526506324342635c50b06b5a0715cab8ad45d85cc5b1c3a0e8ac787c99a87082156ca9a99687083056aa1c99,0xa9b8531c318d5240c8566733162355c7505d45cc830ae32494b00caf2900ba3464ac18d10e9816700a6669c0e9d1072d,0x2dc0d0ba1715c5625405cc74240395724daa128749571d09911b1950173108bb30903332a24ad18c108895e716aad8b3,
    0xca49918c76b1487ca9a87887399082056085156c89716a0db81999b61941749911b198c9ad16e118a62c735473086425,0x718c2b76256075665c55254c74064641b1e0a4b41cd1ac9b121468d192e893a9ea5b8840e959c7097510589aab01163,0x166a90820566b1487c9a0820166a1183316ba17a9589b09ac16e14e902953372d4b64732402f455c74971110b1aa926,0x732571507ca9a996874870820166890830166b14870820166a90820566b1487c870820166a10841966b1487ca9a87082,
    0x1ac6a40ca94671eaab89684dd035660ad06c46b2730634c429d1b417111ab0089dc6c1541999050b42dcba26ea5a94c7,0x89ba96a531ddc950652b076646566c46427467346305b25d4416a89ac022b8bb018ee0ac0ea131b01cea82c044a9e901,0x45e2ac59917625e46526465c27447566d46b2634ec0a60b31c441d3b417111ab0588666c15e06290051dc64151d0372e,0xb8b9011ac6a405cb82903544c6405eaa090342539c7aaae25a135c435d91981949919d01d59b51b09ac18d108b94671c,
    0xab3a931f266a1c20855b2a6a65a1c20c15aa87264dd1077626e06647566526d46307345b25c46c27406464112a7a4014,0x5cc642630823ac0dcd1200c59d9028cdc2495ab1a00cd5a916ab3a8308259e89b26b86344236079c95ab1a00cd5a916,0x25ca42d5e8ab881c9d81cd5277214e715571589731d09b1150706055eb06a8872491ab5a1a035ab36a8bd50966455c54,0xd0078d8a476237051db99b020ee81191eaad894c9b853a63c7326b1dac521f2a6a1e21cdc4e84c1cb1c20815821455b2,
    0xb819995a9949d59b51541931509d01b197117896e98d10c3096d025327a97098f16d14c70c8d15d007718a4cc719912a,0x275276656a55063c53254c7405c25e44304259ea54c5505625c453a63c5b1c3234574088d63d010b4ae41020c2166d91,0x8a4c93c5ba6b8732631dac521f2a6a1c208059a2420c059ac521c208059aa4208159ac521f21c208059a8430c55ae066,0x991581959549d410f214cb03c0caac0e2171b1ea830c559d896a5505ba6b8734531c508ccf407211db14c83105596a9d,
    0x46d8ea1c3226574088ba3d0066e52cc87ce9ac78c7082056c81083016ca94870820164b1c816870820166a140eae5901,0x25aa521c0c656ac082056d899917a9941919d11d595495815317096f16a14a94e11585a172c06e64563447401a87591d,0xb19b02360ce45aa0820567a9b61749711b09b995315415894e16f14a9a81687088ba3d0208159ea5605a2420c1596a9e,0x1aad0070e56401d3a291d89aa521c086e6acc8704395692a1e3d423656ad89cc9b853c6a0420c15aa8521c280eaec0b0,
    0x5627324f16a10c30d6d825aa731789ce96d1181396da9b89581b59549d41951d19531901999791b117096f1cd14c7119,0xaf401636391589a1c2088596aae25d85e453c5ba5cc5a24204b59589d45a8521c22358f414899ad0067552ccd1082056,0x7324f1c81d4b885d99751d01d49959911982b41b19b91151d03d00a62cec01598b933472a521c44457b415181ed06460,0x509b017316d14f1ce9d11d49b599510e1a16b03a44cac0f1b10b2468314cca47890c8995d0078d8a47624a1c81082056,
    0xba34647326e14f16a94a15a954150a0439569010a6ae402cc5a92d8f226a1c11ac6a4ce9ac70c30d6d99b919815a9541,0xd81d59d11c894870b0b0bb02328ce408e943916a8208159ea92a7205a1c504e5b606e46665e25d46527566406c674440,0xc645aa7629495416a9487021b9ab010a6ae4ce9c87011973b010e55a4a87083056c81083056791941919989b99b51b02,0x5416890812d65627496a1487019d54b011746a4cc90820565837aa5626a1d2b445d81b59d51d1a9999020660ea900563,
    0x901709b11b819995315896f14c7111c2bd052328f4015999933272a521c05a176401636391589a1c0465cec082216761,0x5b4672044c1e26d06467407565d4652419560ec073162b0095ac6cb127325a95096e995e40dd917a9d41b59949751d19,0x1e21cea4d8430425b666e06625e456a7546d66505cc6c46465405b253c73a742415847640568e891d895252872042081,0xc9ca5d263c5b4531c02f4564cc70f1162b0310d5a47a258570dd1215419992e895c9ca9b853a63c7326b1dac521f2a6a
  ],
  [
    0x4e98f16c7050d2bb002f456400ad63932ac897646e666256065c55254a7406c46d07565d46465c25ba634430c25ad095,0x456265c6d45507426c064653c63243ca521c52ad597497110c1096d89b99991581571b41d59949751729b11d01919509,0xa93c5ba6b8732631dac521f2a6a1c208059a2420c059ac521c208059aa4208159ac521f21c208059a866688b7606e666,0x162664cc9d9119314cd062c4ab418b942d044c5c7402b332b1ca830c559e894a5605ba6b8734531d5c8310559e8a5c94,
    0x1c20815b20420c05b2a521c2080592c7205a1c208059a8430c259e87505d25b46b86d46566c26447465405626606e6c6,0xa521c60656b40c51d67717096e14f16a94a15290ca1669003356a4791ba3a870c1b94d002e656400aba39321f3a6b1e3,0xd062ac0f452a082056ba1789571581729751b49b195094e16f14a9a8168700aba390208159ca5405a2420c1594a9c25a,0x487101b9ad321c16255aca87128541709911b19b49d591718d0b34085730464ba27726e14f1a81083056aa148714a81e,
    0x89dc93c5a866688b7666e266456055c7506d474a6c65426405c45d253a5bc7344387509c95b0c43aa9031a1aa47a26a9,0xb021617a45a268708221652a7a1b097114f16e97716890812d65a27916a14870c1d54d002b58e400d99a933442081596,0x82dd89b99791b51959d19709911054ce892609dcb505ba53c54a55241560cec05d132b2c042174664cd1ca94870b181d,0xc35b529625dc73a5b453c54a550818e85ac06b132b01cec42c0c435691c2402e65647a24a1c810820567724f1c81473,
    0x46d6754740857304647725496e14f16a94a1529581081973d016255ac0509abb050a17a4ba3c89a87070b1ab33a6b1c3,0x956b2a1c20c15b52720420c15b50722521c42a87b4032a5cb14a8208159ca92a7205a1c604e5b666625e46506465c26c,0x6accc90820565035a272a6a187509dd4295990210e0ea91e894aa625605aa521c406e6b40509abb33a721c2065cf4058,0xb510a9983b2c6403728e4085d0b933272a521d689a1c2065cf40822167a15816890812d65a27896a14870c1d54d01a34,
    0x3339023a3a247a25894a1c81082056c817ac40dd99989791d419597495714e96f1729d1190150902ac5c900ace524b81,0x425b646527566d45dc54a55074273a5b24314659d255c74a6426c65405bc732531c2a63c2c073b10b1c4402e6564085,0x549581086accd0318cab406509eb007aa86cd19b13141cd4d04072af4029ca3b331eb1dac521f2a6a1e21cea4dc4c1c3,0x5528066e52c031aa3b0094e6acb19346715b11055cc4936096255041434aec0f0d417299095316d14e98f1951b59761,
    0x6b1487c870820166a1181396d89999791951d59d1170914b990914a53c5ba63264c453066a4144cd191d8b30ad06e856,0x72a4e98f1cc16c7181ad4d0422e6b4019b94b00c6a8ecac76b1487ca9a870820166890830166b14870820166a9082056,0x7914e98f1cc16c7762ba20c1b16d0606b534019b94b00c6a8ec2a8735d9a762ba1b19b5295b4f293252a1b0d59d0a532,0x16ca94870820164b1c816870820166a11316ad4f1cc98c193252a0c1096981589959541b49911b19531d09d51d99729,
    0xc890812d6ca9487a87082056c81646b157a1589751446b1d7617915a1547ca94870822164a1ca9a87687082056c81083,0x98190a53272a6f14c7148ca3d04073ab4068d1ab3326e11a36d8b429e25685d4552404758eccd18c7ac7ca9487082056,0x487c87082056c81645995b61b815495a1789751019b94b0094e6acb19d03a8dd4295998190a73252a6e9d03a8dd42959,0x87547667429cc94ab3a5b46bd1036d85d45e85c294cb4a9bc734531c32265741818abd00a63cac8c7ac7a89083056aa1,
    0x2c5949d299197095314e96f1cc910dc8372c442363c249825895410509abb051505ae46605e85626c66446565505d26d,0x420c15aa8521d6a5c174a94c53a5bc732c17ac4247628c2b41ba1549581088ba3d0614c6b4031aa3b0074e8acb199aa,0x4e5b666625e456065455275064654c5c253a5bc73474a453a30a48c101999571d8ae86c46d68086bcac070b1ab2b1ea,0x24610d6a4d9a959060cd5b0094e6acb19045cd4901132ae4cc7ac76b1487ca9a8788737138106ccd5541589088ba3d06,
    0x4c98f198ad9ab1906568692564181d5ac5aa1609197114e98f16c70c8d15d0183356c044cab906814063453c5ba5c464,0xd49951b597615319097114e98f16c901674c73464058d8e4b02cc2541011b33b011ab5240ccab5d49541531d01709911,0x12bca4ac76b1487ca9a870820166890830166b14870820166a90820566b1487c870820166a10c1096d91ba19997a9589,0xd99ba17895a9b51761d495415094f18c1931cd1d01b196e971110335690438276495b991108b9ad01c2b8ac046ad4901,
    0x687082056c81083016ca94870820164b1c816870820166a1370715b1908d833916a93c5ba73263064c810acce4103516,0xa521ea1c20815b20531ac35ea5685bc53a5525d85c44508229e7a15a94f16e9731751561507ca94870822164a1ca9a87,0x26d86c66444111dca494275170ad020cc17291ea9bc53a54c810f55240468ea9334631eb1f2a521c20815b224204b5b2,0xca47aa4ea6f2531042b3393314c56e8b509cc9ba53c56a558640542410a5ce4044cea933251ce897626e466656875655,
    0xc23aac0468ab9231eb1ea2420c15aa8521f21c20815b2055d0876307327409585626d06e86c6833aa124044772903305,0x8c770916a9ccb3a5b44504e5b6a6e66646d86565d45e856255054c6405c26c47467525bc734531c32265740688d6b01,0xc10965aa4f1ce96c97320429739011a2ae4c5c42dd91ba1999789b59761d49951025c99b1506c474654264041115ce4,0x5d87546565525cc6447426c654053c6305b1c42356b40b0b19b02385724cea5a9088ba3d0182b5ac019b94b010acce4,
    0x5aa8521e2c19b7666e86645e27546d05d85525306326405c47426c642958c6495b044772914c830425b666e86625e46d,0x7a1b61d5195974901cd51b34064454255080d5a86cb1908d19c90239d1245aa7324f1ce98c16c7060ad6b2b1ea0420c1,0x70a94999adaa541589c2c2d5d41959709d11901989d995a9549ce98d14c7182a5cd2c64115e524532c6c41dd99b91989,0x90971118baa092c6b4076656a75455053273a631c199a16495a072ac4b01a1e8ac6f2532043b949010acce495a235d5a,
    0x6403728e4cc7ac76b1487ca9a878873a934195a235da9b997a1589d51cc14e9541749b61711b09d199019918cea15991,0xca4582d026ea52a00bd549050cb5b646e86665e265c7566d45d87405c46425ba63453c54a5605524157072c02539ab2c,0x16c0650f2b3468212bc64b02cc2581081b33d0162c5ac00bb949003aa8e4528ccd5714c98f1909711083c6c92c68031d,0x820166a90820566b1487c870820166a10c1096d91b999897a1d49751b619595717299115094e98f16cb0c632ad0298b,
    0xd732914a9c2430c2595c9ca93a63c7305b1c622b8b400bb949003aa8e4ac76b1487ca9a870820166890830166b1487,0x166a10c10965724e98f1cc16c972a00ab339003aa8e4528ccdd81589d498f1cd14c1572063172b240746c0ccd8acb11,0x711286b1d7617296f17914e95715a1507ca94870822164a1ca9a87687082056c81083016ca94870820164b1c81687082,0x17291dc9ba53c54a802f5524cd18c7ac7ca9487082056c890812d6ca9487a87082056c812c6b155614f15896e97717a1,
    0xbb94910999b6d86e655c56853a5bc5ca542402a5ce4b1100dce293324c77216546466c44474e0a498279170ad0205c,0x8dcb625a1789d930708abb003a3564cc11742d55a1789991b99b61068d1ab00333564d82b0100dce29332631c406acf4,0x709b1100d8f29231eb1ea2420c15aa8521f21c20815b206e50876e66607526565d455c5ca6446c07465425bc53a46215,0xca3915c93a5bc73274a802a5ce4ca1a1dd89991581959d51771549529901d196d14f1ce906bd1071e8ae66d840ace8ac,
    0x5b626e66645e85605dc6d865675455254a6c06427465c453c73a6305b1c422b5b40c1b94d003aa8e457070d712b1900d,0x9099997a1951711749b61d29d59d91cc95488f5d51d8a581529b01d19ce94c7058956b231c621d8b405615c915c83042,0x32bca4ac7a81083056aa1487a63435d91b999817a1589d49751b61959529709911b01d194c1ce9101396b81589b19501,0xd0404e5b666e46605e85d26d865674a6c65c46425bc63473053a55c56254040ca9724032363935441c2c6ac00eaa3900
  ],
  [
    0xd919995295814c9ce98c7108795d0521e8b45720c1096909b19b8ab62d027717a15295815497114f1ce98c16c7108ad6,0x4f205598371504054ccec04571672c1dac521f2a6a1e21cdc4e84c1c6a2546d66e85c46c240363ca4c6b115b1ad01d59,0xcc710e09dd01b838acd0701d332b030c35b646665d87526546d67305b46b86e0452266b405e560b232415a315cd1a932,0x4652b70504e5a665e256a65264463c5b853254c5ca5d46b06d86e47607565504157382c54b135b81d59d9199994a542,
    0xc521f21c208059a86ad0b15d45b86347326b06d86e484055cf406215eb03b9112c043b16713c94a64c5c25ea82385734,0x1330a9b2609cab30a3c94c56a531c640caf40153339151dac521f2a6a1c208059a2420c059ac521c208059aa4208159a,0x454a6b86c26e645054cf4154233d01b066ac054b83724c850d05b626e65e46d87565d25b86b4441ab45c951b09919d13,0x46605ca5e264654c56a531c4443d740d11acd014c59a40143739030425a646307347605ea5627526566d45d87465b25c,
    0x46d66545d87326305b46b84422e69c0d4a70724c6665ea5605c254a430825b666e47506d66c27446b87325b45d863c65,0xc20417b2a521c2088592872a6a1da1c20815b20420c05b2a521c2080592c7205a1c208059a8430c35b646e27507466c,0xa8632c0b5644b14c9ca5bc5e256a4234673475105d0a6b0094acecb07ca9487082056c890812d6ca9487a87082056c81,0xb81d91999941d590318d5b342644631f31c117469c68dc25d91b81999b595614c9ae1cc1d498d1909d19066615925083,
    0x8521f21c20815b206ac6076e45e26d85ca5bc6326b053854c56a5d4552404758ec911d09566645562d11909ae13838ad,0x225d99b819897915a9761d51b59941549531d299197096f1ae18d14c7101cabd0074e52cb11045d1a9331ea2420c15aa,0x3029150ae09d8ab8631c4072af4088d63d0510335eb999815a99497516e18d1ac1b61541919509d29d59d9278b732b9a,0x66446565cc5d45426b05b853c55074a75276656a5e2432265740298f2b10ce995e4a666446c66d4756652c5303ca415e,
    0x8abd00a63cac8c7063c15b1cc9e95116609d8b4a94c56a5505bc6b8634531f31ea0420c15aa8521c414d5ae46606d86c,0xb99d59d11529b0991902ccd192d8ab463b8856e46606d26c664465674a75476656a550542807718a4761789ae16c7181,0xd00a728ec1850557b6a6e46665e25605d45526507566c674454a64240b0e6a4046b1a91b86b26d88066656cb10675da9,0xa5525305bc6b86b39096646d86e66c453c6b25b85cc5d483a429ac0e0356b033728247890c8995d231c4072af4088d63,
    0xd062158f41a035ad0054cce44f29725476b1487ca9a878873a13476b182db89791b51b19709911054ce891d8b4a94c56,0xd0b92d89b87326b1c4055cf44c704695a923cb32a895ea7565c27307447626e656054a6c064663266483444d7415119c,0x285508ce41438729340ae0866458b4762c6a81dd91999789751949d59073950b2e06c674064442b3322472a5a950902a,0x256a5405ca7426b87305b1c5054cf41085abd01194ae40c2096d91d59b51949b199119997896d1cc9042d2b71ca96a54,
    0xc6a81dd917895a9d59751949501729911d09b19cc1ad1b8199912919ad2d8830825b646e07566d46526c66446665d85e,0x4c59a40143739019466a44f29725476b1487ca9a870820166890830166b14870820166a90820566b1487c870820166a1,0x726056a7426c46465405ca418f0564cc21432d6b99b61d59751cd1ac96e10547a870195e41c991b119198c715119cd01,0x66447406c66e2452338b4054c1d9003728e4cc7141533d131c15847648f21432d6d91b99789b61d59751ac96e1065790,
    0xa7526d87466406565d46b25b85c26c46e654a56242234af400dca3919aa0d7666605e456a5425ca5d25b86b46d875465,0x1c2080592c7205a1c208059a84eaa315d2ad86e27426c66b44308259d8ab85b1c4216af4055c239330a9d1077606645e,0x5a9507ca9487082056c890812d6ca9487a87082056c810c20417b2a521c2088592872a6a1da1c20815b20420c05b2a52,0x473b10375265673063240aa62dcad20e999072d89bc5d455c531c52839b40e10b5b1e243286b340b115cb002f551c72a,
    0x1418b372e4c2a4672c08d0e69002ee51c70908b1ac902226adc7aa58989ea0dd499598c9cc106bd1072d4ab89dc5585b,0xdca39011746a4cc7a89083056aa1487c87082056c81531a1dd81999949911d19d51b01b59771561cc96d14f1ae18c1,0x654a4088dce402347572c4a5480ace52c7097910c8d15d1a831b76a9dcae656054a5525b853c6306b46d8807718acb01,0x175474686754224daa90258152a01e95191d895c5bc6b8634531f31ea0420c15aa8521c6a1dc5526b05b853c63264074,
    0x7254a46ac46e65c25e44307553417031ad003728e4d594c598d78971102bc62900b0e6a402ccd191b8ad89dc95274ad1,0x7468670aa24d9119832ad063438b4b0105d0a690074cca47476b1487ca9a8788738121e8ad571b497616f1ae10f1aa0,0xd6371ca94056a42644d7405a1ac90078d524183316ba19997a9589951b59529909ad16e171118b950923c93055c73275,0xc521f21c208059a85c2a8d7666e86645e27526d06567446426c663c6b47305b853255c818c5cac08c15e9006a1d5c00a,
    0x4c711943572664460d5b405d0a690078d52401c37291d1dac521f2a6a1c208059a2420c059ac521c208059aa4208159a,0x26d47406c65425ca6446304566641cba26e11107a9725c9504308259e85b46b84442e65ccc28f19415717299115015a9,0x4870820164b1c816870820166a1183316ba252a5897a96e170a05d0a6901686b2401e3549051105b625e456a7567346b,0x855c541f2a521c20815b224204b5b2a521ea1c20815b204308105eca94870822164a1ca9a87687082056c81083016ca9,
    0x80aaec18ab037364852c29b470710a15ed03845cac7aa0a17ad8d1ac1042b337332414358dc142d0b72e89ca9bc96a53,0x33354b0d79096e666256855c6406345326b86c47467307526d06565d45a831b7326306626e656853c5525dc6b85b1c6,0x83056aa1487c87082056c814f182dd91ba1d59951999589571749d019098c1ad14e16f1cc90cdd02703a3445cb19b42,0x26b86305b1c1d53124d59070563b1dca1c1576c09e865055c5c45d25bc6b8634531c163456c060ceab01132ae4cc7a89,
    0x9158f1155065264045d13224b51ac18d11718c272c6a66ae8860830839b6a6e66645e85625506526d474454a6c06465c,0x65e45626546d66c474654a5c245ccc424ba2d4aac16e18c990105cc8590050dce45434f2772050d63b01132ae400ad63,0x8ab92324162655c7721013967497120c5d1191e8a50b4a95c54056a5bc6b8634531f31ea0420c15aa8521c60cc5b6a66,0xb01132ae400ad6390404e5b666e86645e256a55254074a6466506d66c26b45b85c440ccd5240754c4935441c23aac046,
    0x5715897097515294c16f1ae1a346555aa919b11b5ad99d2a502d4103388db008cdcac70900b9959231c3075534058d15,0x6e1cd1ac1ba14e9581085333d06062af4b5b1418f2d2c4403666a48c76b1487ca9a878873a9361307a142f5daab4a7a1,0xa4208159ac521f21c208059a842d0bb65c66664294c851316a472a6e14e9cc9ac1ba20c1956d06062af4a33855d4272a,0xa54cec02b872b1ca84d5175e8b50a4c94a55c5605ba6b8734531e31dac521f2a6a1c208059a2420c059ac521c208059a,
    0xaf47a2ae1019b9471d4416255ac144596ba1789971ad16e1751549531b09085333933242a3385cd4258218b12ad2d640,0x56c81083016ca94870820164b1c816870820166a178a82d571d19cc1d49b11b59b89d919419319995810991acd06062,0xa6d0414acf400dca372c1f2a521c20815b224204b5b2a521ea1c20815b204308101eca94870822164a1ca9a87687082,0x35c435d89b81d199099995a1d519418d14c9ae1cc106bc8472d643a84c6c0e2370b14a9cc5ba5d255c43446b2c7910cd,
    0x708abb01d03aacd1190955cc0d789771549729531909d116d14e9cc9085d1972b8968421633b4058956b231c036669c,0xc5394d019427ac00d5a372c1ea2420c15aa8521f21c20815b20682a3d5687626e06b873044073a9c792999b51941d59,0x6c700d7a270604e5b665607545b87326346625e46e86b0ad665040855cec91ad2a54685d7a2732cea529571589ae14c7,0x95a031762b2e8aac6077646e06666527565dc74a5c254c63073253a5626d45504152e0ec055730b2444031e5647a2ae2
  ],
  [
    0x5714c70a83a3b161ea0420c15aa8521e2370755c6b46d06447427545d25cc94ab3a83816a5c792101756d0089e364d9a,0x3846b408e82b7023ac0dcd2a559835d91ba1999789ad16e1751949b59911b09d1900e5639023740e4d427328c2cea529,0x98a6c9ae1026a8b7250b304604e5ae86625e45dc6546466c46d65526b25b85c254c402b58e41838a99350766734631c5,0x1f2a6a1e21ce84d1de14c55dc95074a6465c254c53a403568dcb1208b16690238476408437390206ccdc0c10967a2919,
    0x7aa1432d6d89b81999791b51971b19d01d59549709911531042d2b90031dca45aa7626e9ae1cd14c71888d5d231dac52,0x6ea5aa0c8956d062235740889abd050cb5ad87407565d45b87346b0460ac2dc063b9071c2b62a5c96055254c83305ca4,0x450cb5b646665e25525c454c64265c7566d46c6b40b32531c5843cac15c382902784a64b8301d9919027a1a24762ae2,0x1e31dac521f2a6a1c208059a2420c059ac521c208059aa4208159ac521f21c208059a845a25655c54064c5c26c474673,
    0xa8892666d86e47566c65b87346b1c6214af40f086ab00354ce40c8b1671ea9912ad7609d8a4c96a54055c5ba6b873453,0x8402ee51c711043956905a15264454c7406c65c25b473275440c6c6ac7621432d6d89581971751549531d017099110f4,0x8059a8440d45b666e45e256a6d27547406c65425ba732530408d5c5c0635a8724c66065655c40465cec031b1ab1d8ab,0xc890812d6ca9487a87082056c810c20407b2a521c2088592872a6a1da1c20815b20420c05b2a521c2080592c7205a1c2,
    0x4152e0e4ac18c9cd31ab0a1d06a9c23407211db0031dca40ae119900aa62dcb627326ea5714e15a9507ca9487082056,0x73056b8ad653a5585625ea5b1c1ac29ac00bb9471c1c4645cb405e16291dcb571037606e66645e26565d47526c474664,0x82056c8135099db627895a95494e16e98c90468ab73426c6640c10e559cd03a55d528d105d99072407466c4d6a9e469,0x732363c85b815a98c9ad14c1ce9045d1a700b3345c902b1a01478d90039d8a46e2b62532772547a89083056aa1487c87,
    0xd1037626e66605e46d86c47467546426565d26b05b8634c18f542c0445ab933a96a531c408dcf405a166b141c6445734,0x7516e20d6a607344c323455c7890ca135d01c8476c0429ab70518159e9816e1749b61b11b99ac219094b736a9e45625d,0x35e8a401197371b8ad894c9dc951ea0420c15aa8521f570857666e056a7526c664065653073a63240ba345c992b62ad2,0x446119a9c90a1950cc9360b3a96a630531c10a6adc50715119cd015067647320e558d8ca789711b09ad214acc472e6c0,
    0x11db352a0776a7566d86545d27446c26467306b45b86326606e65e4562430825a646567546d27466c46e65d85e26b85b,0x6e9ae1cd14c70708d5b011a2ae400d99a9231dac521f2a6a1e21ce04a1357654de443c0d8b405a166b01ca3a1cd59072,0xd054266740708d5b15ca4c810a5ce40468ab9060cc5ad6db8ae89ea96261d50765c9c25d455254c861296a4d8a5aa7a2,0xa4208159ac521f21c208059a8440d459e85d25c45425307327407546c66d06e46b89ba96a6566627664642177419115c,
    0x966464683956224972d025415320c4d5191e896a5ba6b8734531e31dac521f2a6a1c208059a2420c059ac521c208059a,0x7a15a9d59b51941931d01b195095714c16e9ae1cc9103ca97042d6a1c7497111033729266460cc59b8ae89ea96246ad1,0x815b204308101eca94870822164a1ca9a87687082056c81083016ca94870820164b1c816870820166a1103516d91b89,0x6e98d1cc9ac14c719115cd01a839ac74905a1acb010accdc050d6371cc95c541f2a521c20815b224204b5b2a521ea1c2,
    0xd41b59919b01d1105e42c90155e124054b839007a98a4ae27a95a16d1ad6225d99ba19897915a9d51d01919941b11b59,0x15670892b44342999cba26e97915a94c714b0a6d015439a47090531ac901426adc772549a0e6a5d99b919899518c1cc9,0x2420c15aa8521f21c20815b2051730b6d46b86c06e65ea5685b45d58897666627546d06566446c663073274045782864,0x952b0bc15771541709531b019119498c108e8e87266ad6b54746731c2646b2c0a83a3b0680d6ac08e11d913ab6a961ea,
    0x34ad17354ed0a64656640631c0855cec00e5639131c23057a400cd5a933a90ce996d654c5505dc7527468294bc24999,0x47565d255c7446c65405cc6426b86305b1c03568e40c10967a26c9ae1d4a81dd99ba1789771549711531d09b196e1ad1,0xa1db51949b19ac18d1901d09d59d9153154177178971210e4e89266c58507ac17111ab2e8830825b626e46665e86d065,0x6e1cd30b0363b0694a0ec0a52f0b0635c41cb1208b1669023847640843739063446a44eadaa587a81083056aa1487c62,
    0x2ae8ab45b84031e55cd4290208e82b9231c03568e44c7cea183316ba1999791749951571501731909d19d41b598c1ac9,0x56392308a8e8d6566627507665cc7446406c654255c40465cec662a35d99991b49959751571509731d11b1903566291e,0xc11562c70c2096d91b999897a1d419597496d1ae1b51731b09d1950157209c171b00b3266c91200b995901154ce400e,0x87646e06b896a5584054e72c1302abb0405ea9c98b0252b3b00a63c9cb5a91ab07c99a878b2487081216687371399307,
    0x25bc5d874a5c454c56a5e243b085b40ac0ced03302d74b4102c2b3b00b0e6ac90795a1012d67315094f10ee508734a9e,0x6e46625e856a7526d05d455854c74a5c25bc6b8734630531c3302d7404455e722cc8b7606e86647547326306b453855,0xc5585d26466546605e874a756764462256b48c70c8d62d01833aaccc7c8960eaa556174b9818c904397271cca3c68576,0x5a9d59b61941751549531d299197096f14e104559c72c46b1c2066af4019995b030425ae256a6d06c45cc5426b85b453,
    0xa7352c043cac9041475b646e066256a75654c74a5c45325bc5d26d46506466c2431744647a2562141516d91b819897a1,0x1567247320c50d6d81b919897a15a9d59b41951749531d29b099197116f1ae18c14c7148ca3d01533a24561050d1db00,0x54bb06342724043972736a93c9cc941f266a1e2c8604b5b6a6e86605e45626566326b05b85d26d475064474654a6c241,0x772916ab4a9bc830425ae26605e45686d46c66426565506b85b25d8752744b30860515b509d2558560a31c6642b2c1a0,
    0xad1031ad473545505cc6857646605e87326346527505d46465c26c46d66e26b8958531c53827340a9784b01c1d8ac044,0x541531d29919711b096f1ad14c78c7029cd4b01833aac019d62b331f2066688b6e85e46566d25d86c65c26444052bc64,0xb1110d0f29260c605159605586d046ae046c0654f0b2c246342724daa7325291021d6d91b819897a15a9d59b61951749,0x4f15615828c7148ca3d00a7352c029ca3b041475b646e25e87566d06525d474a6465c25bc6b853054c56a558405718ec,
    0x596ab4a941c31435a6056a6545585306b86d06e45e86c25c45d2a469bc94c74a756762462256b4181456daab42732529,0x87505525d86d46e0ab8531c074ccac18d41c70635c09c1a0a997256840875ad6a3ca465cc7426c1f266a1e21f6a8404b,0xb0408759cc8408759d86c45c25e49bcb4675464c656662730631c528673418895a73224508c5b50952560ab04508c596,0x9331f20440875a569e864c6c65c25bc8662545c75101e354b011aa71c14229674901e354b011aa71cd07c99a8719912a,
    0x959931d197098c16f110a77071d4a649e8c635c41cb11045c9c90508a59629d24074e52c029cd4b01833aacb09045c9c,0x6c66d27447565d86546608222e8f40cab30d016b0b2c011ba3b01833aaccc1ac714a19cd3226a1c622c69c1021d6d49,0x1f20430425a605e45685525d86547506d66425cc6c474663c7345305b24505cc9c14a73072e24604b59385626e85e455,0x1a9d0183276c762011d63b00ab466c1021d69317096f102a73172d08057332c060ceab00c5d89cd59d11b19045c9c933,
    0x5b2a820cf5b2a921c30425ae05e45cc6445b263c6626c66d47427565305526504686a0ecae25a1088d1dd022358f411a,0xae045073534142d0bd01a338ac0c109695ab196c9ad10c22d64c7cc7042d5c73266a1e21e3c8404b593ca4c941c20cd,0xd197297516c7141cd4d016b416c0c10966d2cc70c1972d010ae71cc891021d670a7a95495a1989d91d2a14bc14935093,0xca4c99a870c21165895614c1ac9b41ba1d59d81991949d29919b117097a9752021795b01a9e82c0c109695ada97a1d41
  ],
  [
    0x931c5073534019d62b01a338accc70c1972d3205a14cd5d246644aac198951b36a8408759eaad6b4a6c26465c1c10e5,0xcd4d02074af4019d15b05c1e85625505ca5d26b05b4430425ae05626d45585d26b85b45e87565ca6c274476a64666465,0xe5ca4042b9c73226a1c308459ea6506466646b053256075676274a852f4424562ba20c109658adaa7a17297516c7141,0xc40ae2f4182b19d016ae82c0c1096da97895817615497296d14e1cc1142d1972e86646504086acec070ae2b242ab1c1,
    0xc5c5495a2b829424c7141cd4d03074ab4068ce2b332410b571cc810c1096da97a15817495617294c9cc16d1062635725,0xb010acce4ac710d0f2d2c1f266a1e2c921c204859a1cdc4e04304259d8ae86b05b4430845b566d85d46c66b45b84509c,0xba1941999911cc1b9421dd91ba19997895a9951b59761549531d297114e16f10317627242f50b32631c622a8f4060ad6,0x51c7321a8749d297119096f18d1cc1d915315a95614c7181b1ad06c1e456a5d875455254c74a5c25bc5384511665cb59,
    0x539857010f551c7324f156101539cb0094acec0455337030425b507326305b44635851cda9d115299090445739010f5,0x751b61709911b01b8ad2a5a95496f1ad14e15320439729231c32358b4cc7c890c1096992959d51ae1b41b997a17496d2,0x58d15b03c16a6507566d45d85c46426c05bc6b253854c74a4058d724015c6391524046676c105496d919997a1941d59,0xac2185196d999895a9d41b51959531d29b019117094e16f1ac9ba15497617910c19aad00a63cac8c70c1cacd052328f4,
    0x85d275474054a5506d865653c5b85cc644732631c182b5acac7b07c99a878b2168751731b09911d015296e14f156158a,0x454c56a558531c406a7b4181b1ad2e85a15e26d66e86667647528266cc2cd2a5a9085d0bd330460865b6a6e66625e456,0x96da97915a1959529541761b51b9ad4a98a6c70630b5b1ccae65096e66627506d46566347327645e85bc5d274a6405c,0xaaccc7c81101456999d418c1951b594f156190950173174905e0acb34a96a8634273405d0a6b0094acec0c10969130c1,
    0x684232774058d15b10761d6e85bc5c45e276456a53854c74a4478aa24541761058d15b0460eaac03529c9266b5681833,0xb0112ace4ac710d0f2d2c1f266a1e21c304259e85cc6305b26b86d05d455854053c81c1d89c026a5a716aa56b4a75276,0x714ab6a73274480ccd524034ad19350931c508a5ae66645e855064c5c45d26d86567545bc538730632c182b5ac070aa3,0x11ea9c7319091022169317096f28c7015333b01162cdc18219678adaa762cc25415a15290c10967319098f16d1046754,
    0x52958ab029995416f18d1931949d59070aa3b2b1c085676c0445ab90308b5931c32358b4cc7c890c10966d2043d54701,0x1c3234574141c9cd01a328ec142296d99d51959749541d297116f18c99315095a9b61b01b897a1993102216da9709d11,0x458b372c1f266a1c60865ae85e4c162656c06b1a2b1cc860c65b566c254a74076a6546666e45e85c45d2962a4c9bca3,0xaa3b2b1c3065cb4732183196da9b999917a1589b61959d51d01529541749019d62b3326b4538410d6b1c9317116f28c7,
    0x74a7545d25e87305b4460c659e8958562b6a94a531c30845b6a6e86665e46d655854a7325305b85d29628606a734070,0x464c43330564cc9011d1d71304335681c7a2ae256101539cb0054ccec0457167030425b626e466656a6506d655864454,0x45b85cc5d4558542842d0d640354cc9131c5072734068ca3b0460eaac99ad5a060ceab331f2046a1d474054a5c25bc63,0x509901b11b497618f1ac16d173118b560916ab6474a41194ae41035a99030845b646e85e256a6d265074a6446c063c6b,
    0xa6c2db1dcc8310359386b241d2b09c999951d59070762b24c9bca31c5072734011d1db01a328ec0c1096ba1789951541,0x26a1c30845b6a5687567426c054a6b25305526446506665d45e26e46d8830425b6266656a6507565526446b053854074,0x589751b61d59541949731d115299018f16c90457327264ec24d19c556ab4a6c46b1c085676c0445ab90308b5931f31f2,0x474054a63c5305b24115cc9cb0b0c21167328f14c16e104579472c46b1c5072734088d63d01a328ec0c1096da9b997a1,
    0xd51b599319419896f1ae18c7188563d131c5072734068ca3b331f20430425b6a6e66625e45686505525d86d47565cc64,0x55ed030845ae66645e25686505d45525b86b46d875654a6426c074476a460d53347321707a15a9749561b01711509d29,0x5aab5ad99d29d49070762b1bca4c810f55240c40d69415495017098d1ac1b1110d0f2924c9bc4421e55cd2a5a9989101,0x90404b5a4c9424308b5a3c94c531d51c604b5961c20cd5b2a820cf5b2a921c4a1d45585c26c45405326b863040ba169c,
    0x86c015333502166654b11045cd49005718e4182196729d11daa78a88a901b09045cd49023708e4cc78f25314c70540f5,0x3965aad2a5077070812166873993471014569325010c1096da9901d09c82791761951b417296c9ae1070ae2735642d43,0x1a8b49571761d198c94c16f1ae1cd10c8d15706222adc043b32722c6a6521c0ace52c0c1b947321c3286b14787daa101,0x26d65586406c47467345326b0416ae11c8f27716c70cab067002a5cdca890c21167716e18f1ad3cca4c2b02981a99887,
    0xd547010e5c9ca8700bba27060830439ae866256065c7466c06446b45386307327546d65525d8430845ae866256065475,0x911b198c1cc9ad1043b32722c521f40c307551c00a97370604e5ab2ae866256062c52253c9585dc5b841c1d89cd4b0c1,0x4259dc5b1c30845ae85607525587345326b04662c45c7716e18f19898811412d6b819895a1d519595494f16e1771b61,0x156b89991581571901b114e1ac1b61959d194898b18c9cd1c811812d658a8c900a97372a1c1c23a9c0f11625351dd443,
    0x516d2a8b24f15095a948714b0a652e88504b594ab6a968ad8951ddc5b1de1c604b596242cc8b34033a62703ca0a5c142,0xd19909981529ae18d14c95a2143d11d256c3131aa4cc1043cac7121c323455c8b21421564b29725477611822568f2101,0xd741ab310d017509a44e2b628b21421564b2972ae25477490c10967716c71822561820c10e6da9b91b49d51b01a99c89,0xa921c404e5b32f4a94056a862c2b34043cac7040545ae46626b063473276065675474a6407266a26c654256a521c22c4,
    0x9729894f1581547daa1015167aad2a70710a0f5d0504b5a5c9524308b5a3c95c531c604b5961d41c20cd5b2a820cf5b2,0x66b85b45d86a2620652740754430425ac0ae46605d85e25b46b8414ee11cc870a1c1db331c1cd0b2c5a14c78f2181456,0x5aad2a507707081216687381181456989581182456b81791951989919b11881a99053d44532274075644c1e26466c46d,0xa891999425334630402e2d5cae28b26f17615714870c85665131c22e899c7911812d65871a306ab062d0b1cdaa101396,
    0xd19911999b89b01a9a05ab8452b4432acc1cb628b27716e1182196b035411820c10e6b99989b41b11919951d49d01c99,0x4870ec2169032b0b1c06b0a6503a843940e91a2506a4469452adaab625877716c7787182196d51541489c81cc98c1949,0x390b1c05ea147015a0adc15e8117014c5994562ba2d2a1a8549d01b199098f14c1ac9cd1a81c898991412d68b24f1549,0x5877610c2116d99c89881949b094b15014c98f199191a1a8951c89899909b19b49501cc14b14c98f1ad1a870e606ab03,
    0xa548c1cd10c20d6972549a1e88db19b49a81c9914a78452e4666e2c95c521c6710a644c70cac2c7010ec59452adaaae2,0x865ac692cb6665c664621c1b9852c06642bb0599846c0cd426901784a9414e7025138ae8b4a8cce856c0642746c20e6,0x1c37292a1c3c6055c0f11625351dd24304259dc5b1c40545ac66405426b46325206a272673076466655c7526d065446,0xc99cc9d92ae2971b51561142296b89ad1cc9d919995a9b61571501d29b199094e18c19518b1c99487118356d0621d8b4,
    0xcc70720ec901c1c554145296b91571b014e1ac9b619514818b18c1cd1c890c20d6b899995a9b19509d299018d14c1889,0xda9589d09529b01a8a0f42a852e6ad8ab45386326646468604b594ab4676a962d38ad843a468acc87108cead007718a4,0x5a5c9524308b5a3c95c531c604b5961d41c20cd5b2a820cf5b2a921c60c6594ab6a962a42aa292ca5c4387056c1812d6,0x333164050d635030845ad8ab45b84109eb1cd43855b02942d51c870a9c23b02373824cc78f25714c70620f5b1684504b
  ],
  [
    0x3071414569725410c1096d99b899917a9b51ae16c9761d29c81a99b0191971108bd289222b5265041832aec02ac63b02,0x4531c26459ac0b421db0274e82c08d8c671684214e7341052b3d0505cc9cb9a91ab07c99a878b24870812166873a9359,0x32bc9c90799a1412d6d899817916e1cd18c9951549531709771ac1b61d41170519b34a83a15c54a5cc74273a6b05b863,0xd917895a1d41b615495314e9cc9d297117719518c1ad10c10966c71540ceb0560e8acb811442b3d0510e6b400c6b5700,
    0x5e27505d465255c54a5cc7426b463053273a4217465c02ccd1702333a1c5a2b620c10966c705415eb0031ad5c1412d6,0x66656cd9a9190c1096b61b917497a1571589ce9ac16d14e152973100b8b59231c414acf400d8f272c1f225d53037646e,0xa941f266a1e2c9519c366695c94a5cc64274673a8035671c0c10966c97a1b919499815890819abd0510e6b405095eb00,0xb61d11d499411a8941911b19d0908e8e89231c2a740ec0b3161b168531c44352f4148d1ad018c5cac00dc9c915c9ccb3,
    0x65613405c1729003aa71c7724ead2a223ab5d41d89d11b199099999518c2581af2225d81b91999789751909b196e1ac9,0x7a25815621440c77ae66605687545506d86c464673063446223a9cd8a9490e05a9b0099d46c79170a6e2ac71190b5d05,0xae18c96d17895a14c70d1d44d0443567400d8f270035e89cb0900dc9c915c9ccb3a941f204304259c25b4833a2a1cd92,0x72e09c05cab073669dca4693ab4a830425b666e46626d85d45e87527446466345b24089dc5c942ac25810c1096d4a761,
    0x564d431888ead231c067552cc99a870c8d2ad221f3a8404b593ab4a941c414759e45c26c44035e8a4ac219888d71b881,0x73605e4430655b418889dd00aa666c0c2116d89b819995a1951931d11709771549b61b19ad14c16e17910c19aad00ce1,0x5742e456105095eb0066656c0509abb0304259e85b4a31c02ae71cc89128931709771d11d49b19b514c9ac16e118a62c,0x1c6223ab40589aab00363ca48c7c99a870c1096d91b817a1589b49d41971751909731ae14c16c91017aa7266b466c440,
    0x25606d855275065464c6b45b25c45dc5e8851a22f40c58b1d2c6a6644393a3401e855b01b8272cd0900e51d90308c593,0xd11b09b51549761791919731ae16c70ca946d062227741418b3d016255ac07052bb00aa666c00b5359130830425b646e,0xb0304259b4ac440363ca48c7c810c2116d81ba1999791589561d49941771d11709931b19b51ac91b0b999815a1971d41,0x5895614c1ac9b41ba1971981791749919731d09d99d51031762b2c44035e8a40c109658a6c718889dd05062cf40509ab,
    0xb07019d54b3204304259b441c1ca9cd41032b19b0408759dc9c2a4c81ce8524d41031ad4b2b1c02ae71cc89a870c2116,0xd51d07025c5ab366830425a645e865064c6325b45c25dc552560538ad86b040cac65c18d6a073627548583266cb9ad1a,0x1c50515a609625506b04308c5931c0c6b51c0354cc7352440875a5cab49e45d25cc64441d1d4246e2031563700cac65c,0x66446c66b481ab40dc752b610298b3b01aa0cec8c707215cb3266a1e21e5c8404b595ca4c941c20cd5b2a820cf5b2a92,
    0xb5d8ab86e06666426c66d4826459ac5a20c1956d050a66741021d67a1589541d49d297094e1cc16e918a7607364ae066,0xc99a871412d654a0298b3b01426aec05a970b05051596253855081aa0cec072b037354816a5c2c8c706a19cb3225c08e,0x7116e910a63572e6a606466b84304259e85ca5d46d873a6b45385b2c32a0d7406a833b01626aac8c706317290182e69c,0x5a646466c45ba5c274a7665d47527344387509c7a10ca835d030a5c7406a833b231c183569cc811021d6d92b51d29b09,
    0x47307549bab4a6c66425c1c1a8672c06317293226a1c30425ab85b246a9885cb424c21a3a4273669caa6064673a44087,0x25d45385527506c664274441ba30a4b6106a833b231c52b07340a0d4bd0383547400b972733a840875ae4950b6666063,0x6731c4c817740f10acd05c438b4d4907215cb320430845b506d85d45525306b25b85e256866064245c2645e85606b45b,0x524ac705d132b2c1f266a1e2c921c204859a1cea4d07306a95d4e346606429ca8408759e86445c25d4ae4ac69bab4a76,
    0x959751529731909d11ce98c14c7185711d019585ac0c1096d81589571d49529909731d114e1ce98c16c7108ad6d003ab,0x529731ce98c16d14c7181b1ad002ee8a41412d6b995a1531549b61959771d53d2ac9c22dd81b999917895a1d49571b61,0xadc0847a97240b4a93a823740dc5a108539cd0414acf400dcd47030425b52db24039d51cd2a0c1096d827895a1571761,0xce98c71702a3d01cc2b241888ea7366a56b51f22430425b626e06665e45d87546526d655c5425cc5b26b8730634423a0,
    0xcab70086bc9c947070b1a7266830425ac49cc5e46d25b25d855c414257ac0198b5b0046676c8f10adb8257273252ad01,0x6055e70085ad5c02159d723d4857646e05e256855c6d85d454a5cc6c274064453273a6306b44304259b1c085ad5c060,0xc6b84304259b1c037351c00d7a272c1f266a1e2c8510149e589561531709771b11b4902e88bb01706aacd2a9018ca4e9,0x26546d65d85e256055c54a7405cc64253873a6305b1c422b5b4ac70cd0a6d0414acf400dcd470304259689e25d895c9c,
    0x46546d675274a6425406305b273453a4075685cd827627325715a212959d9037928d2d51075710b030425b646e866675,0xcea101456d2a4e95a150710b0b5d1cc9dc1436c0a307324263585c01695971dcb4a94c53a560551f20430425ae26665e,0xae1b099011a8959b01d099110c437291e2a31c60d5334073544b028f522c08cc2b9023740e45a14c714bc14d00a7272c,0x383b241012d6d2a5090c2316cea5294c75871412d65470c10967a17496d2b91b610a8d0bb020e5c5c581168959d116c9,
    0x4d6971999901731b11d0908686b9005742e488a01199d5002a5cd414215673297274aa8ad0905682b9231f3a94a531c2,0x2e85a90195e09cb5a532999911972055833b2c040362ce48c7c99a87887083356caa0833d6caa487101456d2a501102,0x571589d81d527624e210d68672d66e86664406bcb4b11ac708195ed06222af40c1096d81b91d51ce94c1ae16d1729d09,0x9911087aad00a5ccac00d8b391bab4a802e5ca48c7c892a615d4c158ab5a5329999099725627a2101456791931949501,
    0x8c7c99a871012d650a053970924c95c414257ac01199db00362ce40c5096d997a1571711749b61ad14e1cc1d51959931,0xd8b39040885b605c25ba73474a5405624214ccf4b11ac9031a9c724c95c75240c5476c0c23164c71418f2d01626aac,0x9817896e1ac9b61959571729509931d01ce9d4975101d5a1b131d684214e734085333d06222af405511eb016255acb11,0x547b403151db0308c5931c5063cb48c7c811b0b99981791761d51b49959931501571d29709cc16e9ae10c2116d91b99,
    0x729509571b49ba1b02102af1901cd4a2499ad59031a9cb0405159e89405626c46e06d88066e8ac57293100cab392b1c5,0x21cab5d99931981d51959571016959b34a9bab31c6222af40509abb00362ce40c1096d89791581761951931d11ce96c9,0x35cc9cb07c89a870c2116d91ba1999789581d597514c9ac1b49531d09b119019725620c10966c708b946d00ae646c72a,0x8d19825a2762015d19b2b8402ecc9c72ad01cea00d794700362cdc00d5a370304259b4ab8402ee51c00d8b371cab3a80,
    0x9824c7019ba2b0508559d28142c7ac031a9cb0032ace4ac70c5332d01943cacb07c810c1096b59b89d51d997914c16c9,0xd299117098c1cd16e97515615310c20969117096e98c9cd1d29d895a1d59531549971b51b99791761119a86b041ab464,0x951d49761d29931709cd16e97915015715a1b81b594c9ae18c70c5394d00362cdc0c2096d99b919897a1581d49b59971,0x3471305615314c1589b81b591014569319495015714e1589981101af2d2b1c20657b41888abd01426aec0c2096d99989,
    0x772363c8578ad49b19d119019598c99920ca135d0508e73419115cd010e5c9c572732507c99a878b2487081216687399,0x98a4c9561d49d117091833549360c278532405dc84916a99c14b630ae093ab6a740754731c4645cb4042d5c70163589c,0x5ab976a6c46e05e256853a8443565c111770726483284d7415119cd0608d73414b1a2d0142675c572732507c894c4375,0x4259b45c240cea8640c4ca97246b568086e6ac7a25621412d6959549b61d51d1a00caf292b1c10ae71c058ba271dc88
  ],
  [
    0xcb4058d6271dc958488abd730a34660b6a96850d4b9760a62630b3a96a531c42c2d74043972715c9cc941f266a1e2c83,0x515b6aa645605cc88b6e89b88466e09cb5ad02919981118d51d01a346ac09e14c9005352e409c171933a96a531c4645,0x1a1b062e851c190959736a968551a177649e8ad841a346ac0558f072c441570724cea5a94c710b0b5d15c9cc941f2046,0x1c162e89c772561145296b89981791951919b11d09d59b61749ac16e1cd1185596b817919898c719a344b0680d6ac0ab,
    0x515b6a960430425b646e26605e87567425c45b26346526466c06b86d441a346ac05c435902746324014d59933a96a53,0x4e899c7511412d6547063435725c8404e595ca4c941dc1c408b59584604b5b6a9624308c5b3a96a531c504b5951d41c6,0x431025ae46626266a26d672a7526447466b86307347605ba5e856a521c65488f41950e1d2c0c5850cf40585665131c1,0x2c299416119a52e894ca5c951dea5b1dd1cbb9416b44182e69c0539a872e8b2a9ea5b8430825a626e4eb89ba5e876a56,
    0x1c631857405c435703b3045c09c18d503305c945a2b62932130ce9ac18d14c94a9581d8b14e0e29016a0d5c14ac23705,0x161433d010d6b144c7119a16d062a88f405a835714ca5cab8951de858362d7606567547468404e5b426c6d40b60a30aa,0xb62932470ae5989cc18d10c2096da9b81b51d09b19901a89899c81d59cd18c9991589143156b0acc98d198acaa5a9487,0x5329725477890c10967a96c7101516509d03b9289ab1a951d59101396502cc71ac611d017509a40ccc15701b1e0944e2,
    0x684d6c0720ecb2348109eb1c042b337014358dc572732507c99a878b24870812166873811015161013965079321412d6,0x26c46d06b8442abc1cb9a91995198a0ca835d026263741888ead056660b48c704297371dc8304259e45b25d8b44ad481,0xc9c572732507c891812d6daad4a5894e956202999ab1c2402e2d6400d8f29030425b645e856a55853273a7527405b45c,0x71dc85a2526407466c453873a6346b06e85b25e443c0d8b4173062d0668d834d410720ecb1d881ac68ac050ba37010e5,
    0x5aa709ce9168951909d19b01711cd14e9ae16c70e9816b032ae81c7a10ca835d050a62f40c2971d00363ca48c7058995,0x4c70630b5b15c9cc941f266a1e2c830425ae25e856a6d855273a6b05b45384035671cb1170900b8b5900363ca40c1096,0x8c1991b09919949d41d11cca18a62c7064252dc188b1a736a9684304259e85d46d85b26b442c2c2dcd429498c2cea5a9,0xe409cb8891e8b3a93056a55899ab096c6a666544182b5ac021ab3b2b1c4645cb405c0b590162e89c772363c85b99789,
    0xa96a531c18c2d6c043972715c9cc941f20430425b626e46667506d26546325b45c27446406c64177052409e14c901574,0x46b86c26446526304642565c086b197346a66b6a968430425b666626507527446465b26346b06c24037272408bb84733,0x72409d18c916a850515a669b8ad865453a55056876a746752731c1702d64058d6271dc830425ae45e26d05d85b473275,0x8c5b3a96a531c504b5951d41c31445ae87526d46b25b84085dc9c4c15618d19410a5233b01832aec00d8f272c040372,
    0x91199ac99a87083356ca9a99487198315d050cccb488705a13551d1e5c8404e595ca4c941dc1c408b58604b5b6a96243,0x19d5472a1c30825b6a6e46665e85625586d26447466b86327345ba4035e89c4c2b02d41c891812d658ad49b19d018c9,0x4b3a9ea5b841c1ca9c031b1a7352720420cf5b2a521c067551c0429737041085930a40b50722420cd5b2a521c60cd534,0x2e2d54019972503226a948c70f5214903d01aa40338557351dea5b1dd1c504b5850515951de44304259ea5b1e0b9176b,
    0x26406665626d455865c430845b646e26667426c654073a6b453252a6a062272640ae6454932b619515715a2159816d00,0x9a852d8968ae4b27053642626432acc14992532ad29718c70708d57030845b646e874273a6b253072652a6a06c654c62,0x564033855703c44a94d477a10c21169994c98894a9c81ce9d89a99ac1b09d1908e8c5901b838a40b50e1901ac2994099,0x8c70708d57050830429b646e65586c274654c6a052253073263464065c6d46b8842d6a1c89a0b3344532a96a662c3d08,
    0x65c6204035cc94b61b01ac94e103155c72a6c07718a4cc715a0669007a1564b92141396992532b61541971ad14e1cc9,0x7138ae8b2a86086592ab6aab8961de24304259ea5b1c508a5a5c6c26406a662266654c52a56272076a7464504e594c95,0x1968cb0833d6d99d49b51941ac1cd18c9991931d01899a89b195095714870531acb058ce42c0cd426901706aa40c89aa,0x81016081056183
  ]
]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
private lemma check_c2 : checkCase r1_c2 syms_c2 51 chunks_c2 = true := by
  decide +kernel

private lemma solve_c2 (L : LatinSquare 7) (hred : IsReducedWith (r1Table 2) L) :
    ∃ σ, IsTransversal L σ :=
  solve_case 2 r1_c2 syms_c2 51 chunks_c2
    (by decide) (by decide +kernel) check_c2 L hred

def r1_c3 : List Nat := [1,2,0,4,3,6,5]
def syms_c3 : List (List Nat × List Nat × List Nat) := [
  ([0,1,2,3,4,6,5], [0,1,2,3,4,6,5], [0,1,2,3,4,6,5]),
  ([0,1,2,4,3,5,6], [0,1,2,4,3,5,6], [0,1,2,4,3,5,6]),
  ([0,1,2,4,3,6,5], [0,1,2,4,3,6,5], [0,1,2,4,3,6,5]),
  ([0,1,2,5,6,3,4], [0,1,2,5,6,3,4], [0,1,2,5,6,3,4]),
  ([0,1,2,6,5,3,4], [0,1,2,5,6,4,3], [0,1,2,6,5,3,4]),
  ([0,1,2,5,6,4,3], [0,1,2,6,5,3,4], [0,1,2,5,6,4,3]),
  ([0,1,2,6,5,4,3], [0,1,2,6,5,4,3], [0,1,2,6,5,4,3]),
  ([0,2,1,3,4,5,6], [1,0,2,4,3,6,5], [1,0,2,4,3,6,5]),
  ([0,2,1,3,4,6,5], [1,0,2,4,3,5,6], [1,0,2,4,3,5,6]),
  ([0,2,1,4,3,5,6], [1,0,2,3,4,6,5], [1,0,2,3,4,6,5]),
  ([0,2,1,4,3,6,5], [1,0,2,3,4,5,6], [1,0,2,3,4,5,6]),
  ([0,2,1,5,6,3,4], [1,0,2,6,5,4,3], [1,0,2,6,5,4,3]),
  ([0,2,1,6,5,3,4], [1,0,2,6,5,3,4], [1,0,2,5,6,4,3]),
  ([0,2,1,5,6,4,3], [1,0,2,5,6,4,3], [1,0,2,6,5,3,4]),
  ([0,2,1,6,5,4,3], [1,0,2,5,6,3,4], [1,0,2,5,6,3,4]),
  ([1,0,2,3,4,5,6], [2,1,0,4,3,6,5], [2,1,0,4,3,6,5]),
  ([1,0,2,3,4,6,5], [2,1,0,4,3,5,6], [2,1,0,4,3,5,6]),
  ([1,0,2,4,3,5,6], [2,1,0,3,4,6,5], [2,1,0,3,4,6,5]),
  ([1,0,2,4,3,6,5], [2,1,0,3,4,5,6], [2,1,0,3,4,5,6]),
  ([1,0,2,5,6,3,4], [2,1,0,6,5,4,3], [2,1,0,6,5,4,3]),
  ([1,0,2,6,5,3,4], [2,1,0,6,5,3,4], [2,1,0,5,6,4,3]),
  ([1,0,2,5,6,4,3], [2,1,0,5,6,4,3], [2,1,0,6,5,3,4]),
  ([1,0,2,6,5,4,3], [2,1,0,5,6,3,4], [2,1,0,5,6,3,4]),
  ([2,0,1,3,4,5,6], [1,2,0,3,4,5,6], [2,0,1,3,4,5,6]),
  ([2,0,1,3,4,6,5], [1,2,0,3,4,6,5], [2,0,1,3,4,6,5]),
  ([2,0,1,4,3,5,6], [1,2,0,4,3,5,6], [2,0,1,4,3,5,6]),
  ([2,0,1,4,3,6,5], [1,2,0,4,3,6,5], [2,0,1,4,3,6,5]),
  ([2,0,1,5,6,3,4], [1,2,0,5,6,3,4], [2,0,1,5,6,3,4]),
  ([2,0,1,6,5,3,4], [1,2,0,5,6,4,3], [2,0,1,6,5,3,4]),
  ([2,0,1,5,6,4,3], [1,2,0,6,5,3,4], [2,0,1,5,6,4,3]),
  ([2,0,1,6,5,4,3], [1,2,0,6,5,4,3], [2,0,1,6,5,4,3]),
  ([1,2,0,3,4,5,6], [2,0,1,3,4,5,6], [1,2,0,3,4,5,6]),
  ([1,2,0,3,4,6,5], [2,0,1,3,4,6,5], [1,2,0,3,4,6,5]),
  ([1,2,0,4,3,5,6], [2,0,1,4,3,5,6], [1,2,0,4,3,5,6]),
  ([1,2,0,4,3,6,5], [2,0,1,4,3,6,5], [1,2,0,4,3,6,5]),
  ([1,2,0,5,6,3,4], [2,0,1,5,6,3,4], [1,2,0,5,6,3,4]),
  ([1,2,0,6,5,3,4], [2,0,1,5,6,4,3], [1,2,0,6,5,3,4]),
  ([1,2,0,5,6,4,3], [2,0,1,6,5,3,4], [1,2,0,5,6,4,3]),
  ([1,2,0,6,5,4,3], [2,0,1,6,5,4,3], [1,2,0,6,5,4,3]),
  ([2,1,0,3,4,5,6], [0,2,1,4,3,6,5], [0,2,1,4,3,6,5]),
  ([2,1,0,3,4,6,5], [0,2,1,4,3,5,6], [0,2,1,4,3,5,6]),
  ([2,1,0,4,3,5,6], [0,2,1,3,4,6,5], [0,2,1,3,4,6,5]),
  ([2,1,0,4,3,6,5], [0,2,1,3,4,5,6], [0,2,1,3,4,5,6]),
  ([2,1,0,5,6,3,4], [0,2,1,6,5,4,3], [0,2,1,6,5,4,3]),
  ([2,1,0,6,5,3,4], [0,2,1,6,5,3,4], [0,2,1,5,6,4,3]),
  ([2,1,0,5,6,4,3], [0,2,1,5,6,4,3], [0,2,1,6,5,3,4]),
  ([2,1,0,6,5,4,3], [0,2,1,5,6,3,4], [0,2,1,5,6,3,4])
]
def chunks_c3 : List Nat := List.flatten [
  [
    0xd5a599b1a235d9ab625a154792a6f25314c7ca1a874870820164b28870820d64aa0820164b28876873a93713072c7287,0xd768ad696674688b6e6b58968551e4a9bc94c531f2673888b6e8b56966450820ded9ab625a15477328ea529d1a22dba2,0xba1d51b5956158908dce0d340731c606c6b4b11ac7ca1a871820847b68ad696673888b6e6b58968551dcca3a94a6c688,0x6546407427606d86e6568552414f582c73252a4f18e96c71021117a605e46525d064a5c254c53a5bc634405a52dcd99,
    0x561053ba0b1cc94a93c63a5b1f31c1d446acb0151d235d9aba1589b595610557a0b13a63264a94cb394856625e47565d,0x8562421742f4d11d1d215d5ab61b995a154a05aba0b13a63264a94c8408345ed99ba1981791589949741911d09d51b59,0xd5956158908eae0d2c06b1c50746b4d11cc7c894e52359817917499517319095294f18e96c105676073666e87506d655,0x6c26e0758766568552414ee82c73252a4f18e96c71021117a605e46525d064a5c254c53a5bc634405662dcda1b99b51,
    0xd60b1cc94a93c63a5b1eb1c1b846acd01d1d215b9ada1589d59561056760b13a63264a94c93948d6625e46d65d065464,0x1ac2f4b1151d235b5ad61d995a154a05ad60b13a63264a94c8408345eda1b99981791589949741911b09b51d59561053,0x830160830164870830564aa887082056ce52159817917499517319095294f18e96c10557a073686e66d075655856242,0x5a9561519b9a2259aab62d1a6f25315595a14c7ca1a874870820164b28870820d64aa0820164b2887687371399083016,
    0x1ac6a4ac7ca1a871420857b68ad69cca3a96a55854675688966ab58ac69bc94c556568531f264408221eba2d5a7328ea,0x8e96d12e2c2dd81ba19a97097915315895619019496f18d14c71191aad1d04163456c060ceab331c622b8b4019ba2b01,0x5a95615094f18e96c7cc7021b93b30b0b556aa3a81d5461cba1b59561d49b11d19d810f18adba294a7895a9561731509,0xa7567426c664053a632462254dcd92712951060772b0119d524532ce222dba1989781b59751941911b01d19d91d4a732,
    0x45d1a9331f2273811b7606e86625e456a5d25cc7446406546d05585425b053c63a40c6569cd5ab19045d1a90ea98966,0x27446c66e05674897646e066a5e25687587466c46d65c05d46426505bc63453a54c552ab1c52338b4060ceab006758ac,0x781d59751941911d01b19b91b4a7325a95615094f18e96c7ac7058d15b008754eca342d55aa8ea06e51873687565586d,0x9a97895a1d61d19b01b597117419099516f18c14e953154a81ac6db92912751941060795b0115e524532ae2235da1989,
    0x4870820164b28870820d64aa0820164b28876873a93590830160830160830164870830564aa88708205659d225d81b91,0x688b6e6b58a4a9bc95c568546531f26450827deba2772d1a8ea529599561b1a235d9ab6292a6f25715a15194c7ca1a87,0x6d86e455c56854263453a5bc4605d51cd9ab1900dcd49331c306e8b4ac7ca1a871820847b689dcac6a3a94a56655874,0xcb162555687505526d8654c429ea34022b8bb0031e56400e95a91dc94a93c63a5b1d95a0b6627546505d264a7405c45e,
    0x5244e622dd81b99791741951709b11d199015294c98e998ad49070762b022f4164086b0b90231dc2408cce89168ad895,0x233ab4b1a2359917817499415719297115094e96f18c903589971687626e66d86c0746754731c406e4f4070b13b003ab,0x864265054a5525685dc5c45e263a5b06c611d7666e06c683b9422478ab625715a19499295096f18c14c7119195b26444,0x1de94857686e66645e05dc5c26406526c46d074675455863a5b453c54a562ab1c4233ab40c1d62d331f227206c77546d,
    0xd53d01a344ec00dcd49162e0b7667446c66d06e2968b5895c98ab196d0a605e45c08031dca400d99a91dc94a93c63a5b,0x8e96c14f152958ad1a22d9917817499415719297115094e96f18c902e89973665686e27587406c66d46b1c3234574101,0x6873713a13070830160830160830164870830564aa8870820567a5215da1b99981791771709911949b01b51d19d41561,0x4aa8870820561020517b224408145eca1a871020427b264408109eca1a874870820164b28870820d64aa0820164b2887,
    0x8125eb626f25714c7ca1a874870820164b28870820d64aa0820164b28876873a1347083016083016083016487083056,0x6f25714c705c156b0033569c92a5a9507ca1a870c209679dcb389584308125ed626f25714c7c9914205f79dcab895843,0xd0672a234022a73b027a8864772ae25611a8749701b11cd18c9ac1190ae17346ae6b60c0d152ec0ae621900aa1cdcb62,0x561c9d80dd51cc9110d4b702a7381cb626f25714c713115ab0421d59c9aa58932859d78a9920cab30d0568e83418c558,
    0x69c92a5a9507c89b8c615d91b99d49b51941909b01d19cc16c978171209d3a090439562411ea889234816b581c772ae2,0x31663415cc88d02770864772ce256194e685b19d11d9ab82702cc294202c58bb02d58864d626f25714c705c1aab0032e,0x73589bc95c531c4a466ac1087aa726a9626e4e037666e06626546d27507446c66306b45b25c05e4842b3a3419a360d05,0x941909d01b198d1ac16c971208cce890278d82410d59890477222405aba071dcb389586a7a036d46b24442e2dc0b1ae0,
    0x164b28870820d64aa0820164b28876873990830160830160830164870830564aa887082056d4c615d99b91781b49d51,0xb5a92a6f25715195a94c7c991420907a6a9dcb46ab896854a5564408121eba2d5a92a6f25715195a94c7ca1a87487082,0xd1a90239d824cc9142d0b70153561cba292a6f25a94e1571507ca1a871420907a6a9dcac6b3896854a5564408121eda2,0x6b605685e26c66e46d0ab8631c42ea19c0439aa71c1c4c456ac10b156926aacc5a17465c06346b06c46d685d1846c045,
    0x8c718b115d052c4cb402b3a2b010e6a9c10bca8720772355c5325bc4505e89c5a2b82ae1cc1060cea725064272b08775,0x917b605625387326b06e85e45d09bc95c6526404608245ed51941d19911b01b59b91771781549ae16d14f15a1d89cc1,0x70712919ab042c6aa49aa0e2a7571208d7a09334630460a1adcac9182b0b70152e61cda292a6f25a94e1571507c89182,0xb0c6b0b7606e25e45685d07547466c06d65bc6b453255c652644738631c62c457414b132d00ccd8ac0439567042f2a1c,
    0xc44c5d09cce1d915a1789b83b19909d01d5a02b394b010e559c10ba86705c15c5625385bc6b4730768462a0af40688d6,0x592a82080592ca21da1cea4d84c1c20c05820c05820c05921c20c1592aa21c20815a5cd116d26545d055c6306b45325b,0x5820c05921c20c1592aa21c208158408145ec891020517b286a1c408109ec991020427b286a1d21c2080592ca21c2083,0xb9ad627328ea5a95195714c7c991420437b286a1d21c2080592ca21c2083592a82080592ca21da1ce84d1c20c05820c0,
    0x74207282bb018c5cac00e95a902af085cb627328ea5714e15a9507ca1a871820907a6a9dcac6b3895854c5664408121e,0x47465b25c06c4c510e4f406c0d6b01d03aac00c79570172ac1c907199154d01705ca47724252f5d19b11b9ad82902ac2,0x507c89cc454db91d51b19d01d9978170acc94f1945562b52ae1cd10c8d1571e45c25b1c031e55c05cc8570635476e69e,0xc8570031dc9c907159194d017065647724262edb1ad9ab830ab18cb003666a4032665702ce885cd627328ea5714e15a9,
    0xaac00c77270172ac1c973445b81791951b496c1ad1016ae17158b3875081ac4cac046b1372c65c27447668510e6b405c,0x4aa887082056c5462dd81991941d51b49561ce1ac14c90cd53071b45e296aa3a8175681cb9ad19701b1306c0d6b01d03,0xa871820447b264508141eca1a874870820164b28870820d64aa0820164b2887687399083016083016083016487083056,0xd62ae2cc78b16874a2c87a873713a13072c70830160830160830164870830564aa8870820561820517b224608145eca1,
    0x6f1ad18c7019d62b00a664dcb620c2456b19b515598e94c95a9d99d0114631a92e2c1ab382c0352e2914c9bc40c5d89c,0xd81b99789559d19901949741d539930a03abb02ac89a408cd43902b8c0e45aac656859aad5a70ab19b8959954a5324e9,0x8a99099519820c2ba1d06a9887405ac25b1ac94ca3c5b1c086e4ecb624e2ac70c8d62d010f58a4cc70830168a93330ad,0x74a5315594898b10ab10e51c08232e0e40ae6219022ee8246aa5aa8e9083016d99b897915a9701d11d41749559b19489
  ],
  [
    0x749d51d19b11b59029993b00ad686c02558b9250b609c0444c53a4113c6892345bcdaaa6a931c4470af45620811d6791,0x66e8ac029d1352d8938ab1c30d15a6a56662252a54281943ca4023a7290059d8649438d16eb6b2932666a15599b89791,0xd415597016b1489531b19911d0b188762d02c252ec0ab226902706a645aa6e98f1887118a56d0068e964752021b93b00,0xcd4b00c6b8ac045d13922c5a1c20475921d58907719664956b46ae66c4407664645326f18e9083016d99b91981789949,
    0x4a4c9b263a430915a6aae454c56663c5ba531c547383401533392224309159eaac694c5665325bc63a40c6569cd5a029,0x66c04614c6a4d8b072ae0b00b8b8a45326f10297a272d8b38ab1e2c5a1d28b21c20805830e45ae4b40a605ea6545d05c,0xb5303916aa999a166aad69c2b4676256655294c93a5bc734631c066e8ac0319537358830915b4675455663a53256a6e,0x4567aab625324e16f18e9cc9ac78b16874870830168a932b0b5d99789741b51b8199194a55ab199010b422b90232e0e4,
    0xf152db9306bca0b344811744e4cc7193225d018c5cac7320c24567aa5315996f18e9cd14c7031ae2b0050dce45620c2,0x915a6a54c56665464263c5ba734531c050dce45620c24569aab625324e18f16e9cc9ac7881328cd5589901519d0bb12,0x24099d464951062a33b1ac94ca3c5b1c08754ecd624e2cc70c8ba2d010ee8a4ac7c870820160c3916cc9044d53724c83,0x6762462e50b40a87a1b02d08ae470208cd43902d5886408bd6091aa96aa3a43951d7666e45e05565d26d06c65c464074,
    0x59c0a4c65062252c45222cd48d16f3b826aa9aa4c70d1a26d158820805ae66605e45d26546d055654252c62264c6c474,0x752021d53b006758ac031b135358938b31c20c059d096a52262a652660ac0546410a6ae40157a192345badaca4c82080,0x914c9bc63a507a995e06c66e276666464074442ba0664b4194b0b422b9156c16b4a245aa6e98f1887119156d02646b34,0xc5325bc63a40a6669c59ab5ad190162e59011ac4e48b16870811d64875620811d6992b1a5596a94895a9d99d1101e951,
    0x9004ce964562ce10e9535d93073aa0b1ccb3893c55880c6b8ac046b1392b1e2c5a1d21c20805820ce5a224309159ea94,0x7627368ab8b31e2c5a1d28b21ea1cea4d8420805820ce5a2060a5676529d4e3a9ea8422e4f4191b03d00a738ac042ae6,0xb59b0951958a57292a4e96f1ad18c70c1d62d050664dcba22f415559a982b5ad41d197011932259014ee8245726f1181,0x27446405c25e45666c66d255c7566545d05bc6b4531c56889ac022d4bb05c8c0ec01ad61b003664e452a31d0b5d9a74a,
    0xcc70830168a995660dd99981791589951d41559b499097016c9ad105eaa07344457a10a4b1a15e81191dc830915b6066,0x929d11b19b4906b982b05508ce4702054b83905598864053ba091ac95ca3c5b1c406e4f4ba24e2ac7058d62b002f58a4,0x571d59d11701751b49b194898b190999194201aba1b05c9886c6aa52a8e90c2456d81991789599d599417515094a9889,0xaf509aca5c8204759e095c52262c662650b40546402a5ce408676192345bcdaaa4a931c267096c5a20811d6d81789599,
    0x914a9ba63c621c384656c0d1174b1e48406e4f40c1ba2d050744d4ba24e2ac70c34567029299818894a90708ab52345b,0x7467526d66546406c446560664d8198b1542339166c32acc245726f18e9083016952d1a5996b1489571b59b110c5991,0xd49571729911d01b095194c96f18e918195a736685073534181ae2d01a344ec0852e6922c5a1c20475921d68a077155d,0xba2ce2ac78b16874a2c870820160c391697272a6c98e90c245692a5715198f16e94c78890c2456b91989781b59751941,
    0x465274264454a63a53240cd531c59ad5ab41b19701103c6a9260830758b4070b13b05508ce4053d60915c9bc4505e89c,0x303b006ae86c00e953914a8c782b6e69d2b5674254656295ca4a93a5bc734631c306e8b41819537368830915b645e25d,0x951b41559d499097016c9cd105dca072c4467610a4d1a19d81191dc830915a40662a5495c5665bc734531c08ae2ec1aa,0x6f18e9cd14c7181ae2d020cd9a45a20c2456ba257272a4e16f18e9cc9ac78b16874870830168a999560db99981791589,
    0x95d7897299098e96d100e76273405465524157462cb1105dc149021742e4cc709e2259017855247720c245672a571519,0xa95c54663c5ba734531c20cd9a45a20c2456ba257292a4e18f16e9cc9ac7881c6a81dd4a55950a7296c98e998a793390,0x864053d6091ac95ca3c5b1c40754f4da24e2cc7058ba2b002ee8a4ac7c870820160c3916cc9060d53725c830915ac4a4,0x5d475274652262c642664650806b586c1aa621b1aa94aa3a420c059d45e294a56652262a464c4354702054d43906558,
    0x805a5c55662252c54284383aa4103c6a90215e8649838d16f36aa92a4c70a1a33b168820475ae05e256655c6d66c45c,0x758b4181b135368938b31c682c464a54662252a552404e5c6c10654b9260ad09c0428c63640a3a7092345badaca5c82,0x7a2b064c89640d4171915c9bc63a607a95566a54ac6b56744431a546452a6e98f18870e0c55b0308d9a4792101d53d03,0xad4d050738b4070b13b22c5a1c20475921d68820475ae06625667546d66505d25c05aa52254a7466446c2c54262f4068,
    0x91dcb3893c5688606b8b4070b13b2b1e2c5a1d21c20805820ce5a22430915b569ca95c5465325bc63a4506669cb9a181,0x7717916c94f100e4e573448210eae48ea72a00cb939168b38560ec3552546ac082706364d1105ea149021ac2e409ca70,0xca3a93c54a863284e4da2b62031ae2b2b1e2c5a1d28b21ea1cea4dc4c1c20805820ce5a204a9a8755254682766224952,0x235d99ba1d61909d11b19b4a58955a03274cb00a666ac73252a4f18e96c70c1aa6d052338b4021ab3b3304454bd6429c,
    0x582047594cd21d31eb1c20c05a2a756a037686e66645e05d26507546d85c46c27464159d12455958a4e98c992a532ae2,0x70ae2b01d056ac8ea72a9328891023d698a50ad49073a14b01c2c4ec034a5ab1baa4a9cca2c5a1c2047594ad21c2080,0x77405ac2cb146b41ec1f31c408f5b626e86645e05665d26506d45587445426c641d54624cc16d107072a735640ce952c,0x66e85627526d6558414ee82c92914204e7a3a5b253c52a5ac622462ac614d89b995a1549b61d5907415ab24c5c1c42b0,
    0x6898a918531352626445cc5d475276446888af40c632a51e0a50806ae86c5070820168f16c94e94b16a9889072b18536,0x1033d6d91789d499519297118f16e94c98896b14a9108ab350418ba94982742062b83b016ae82c0820168f16e94c94b1,0x5aba0b020c05b666e26645687545566d85d264c5c463253c62a5225ac5ba8336609c0252f251e0a50806ae86c507d07,0x26e85587566d1c30975b666e25e45687545566d86525ca6445bc63a5325a262c52a4422acd401d33252609d0818ae0ec,
    0x2338945a1559d49d99b890811d69297095316a94894e96f18c919182b70655c21c8b1011b33500b8c4d4068ce2516676,0x4870820160811d65334874c70830169097298f16c98a94894e9532144c5a901b9381c0b58c871ac4046bd14146313505,0x2650664760756805a566c06e518b344a3a5b05caa4ca225676116e895881b9382cd126e98c192a7328b16870811d652b,0x101cabd0067296c1162ed90a7328e96d14f152a14cc1392e8b5880a738accc7188ae2d2b1e2c5a1d28b21f06a995d45e,
    0xda159954a034a5ab13a63264a94c8615c5b666e86605e46525d06d47586447426c64056666455958a73252a4f18e96c7,0x9297095318c14e96f107570271565627587666e86d040a738acd11b19cc9145756b91981789b61951741b19711d09d59,0x35e0a4d42982ac718c15ad00d0d4ec6ea92a7320c25d653272a8ea6f24c78b16874870830168a9cd1a25991781949751,0x1c610d4f403195ab01d056ac8ea72a9320c25d653292a6ea8f24c78811023d6d11509b191023d6d1950903274c92c444,
    0x594cd21d31f31f21c208058408f5b666e06625e45685566d85d06545b27307527445426c64408f5ac4542746f609d0ab,0xac70833968ea72a9328891023d698a50ab4906bc14b01a344ec02cc5ab1baa4a9cca2c5a1c2047594ad21c2080582047,0x4f582c9290833968e96c94f14a96b188914ad1853666e25685527586d641b066ac9317070caa34d018a87ac51ab07d07,0xc5326225aa52c41832ad40252f251e0a50806b586c5070820168f16c94e94b16a988906ad1853686e65626d275655841
  ],
  [
    0x6898b102e31352445ca5e46e26526d444a88cec01d33252609d0818b50ec05ad60b020805ae26646d45d264c5c463a5b,0x46625667525586d65d45cc6445ba63c5325a262a52c41832ad40c632a51e0a50806b586c507b070c25d68e96f14c94a9,0x789599d49561b599519297118c94e98b14896a96f205e94270439d09c1062ea52609d0818b50ec05ad60b020805b686e,0x5a4c5c254a5ac52253c5ba63242a60cdc0ae708722a42074ad418531350622b8945a1d89b99559d61b470811d6da1b91,
    0x475a425cc63a5b262c52253c54a80d296a418d4e07055a321c6a9081cec500d4c4d4070ae251665587527686e2420c0,0x396b128e96c172a93288955e845da25620754e0b2c49ba63064a9cca2c5a1c2047594ad21c2080582047594cd21d31c2,0x1023d6b1950902a78c93444439d0a4b42982cc714c19ad00b0e4ec6ea92a7320c25d653272a8ea6f24c78b1687487083,0x611b04ca962c9aab1a5326f24c7043aa69011ac6a4ac78b16874a2c87a873713810820160833968811023d6b11509d19,
    0x47406c4546552414e8d2c0b0b0bb02ace82c5aa7328ea711a35da1599549d599417519098d1cc1d11701789b91b62135,0xa5bc632405a565c14e4e073666e86d27587446c640573324559050b33b010ea9a4cc11020887a645e26505d46425b073,0x252ad68ad881528cec6b29320820167036f29320811d65334874c7021b93b0066e8ac043ba292b1c20c05a2a4481c053,0x45a1db1c115e89cb07cc7021b93b060d35b666e466a5e26345ba5d47525567445426c642173864702cc106cc83725062,
    0x2764752b46ae66d854c55656853a63c62a521c21733347ab0820169a98f14e98894b101e2a552546407445465cc5d05e,0x5594c98f18896b1029ce2512aa6a968ae66d8815589ac035654b2278d16646505d464c5c074454663a53c622420c05a6,0x811d64e9487103b167a96c98e94f16b18894a9105c9952649d49c064c6504088dcecd115071844d6789d19d91d49531,0x65586c2546521c20805b645cc5e27407566445b052c62263c6505d4446295ac118c6ab1aaa6a931c32358b40c25d64c9,
    0xb61559016accb3466c4411746a4cc7188ae2d2b1e2c5a1d28b21e0cab36545ba63066a820475b666625e45d2ae856a6d,0xa622bb342c2c2c2ec8ea5aa108d53d01132ae41020487a645e256a5d06525cc6405425b453c63a40ba345cda1b99d51,0x18466a7368ae66d881d03aac909044cab92c0411746a4cc91020887a625e46545cc6c45465b253c552405ab32c902742,0x901782b24751019ba2b2b1c1815cec7320c25d67aa5328ea6f24c78b16874870830168a91a8951531d197118c14e96f1,
    0x7146809aa664b02cc2941021b93b0509b5b646e666a5e25685526d87567326345ba4089e35c941909d01b1151901aa74,0x949060573b24c830975a6a94c9baa3c931e204509b5b646e65e25687565d45526d840b1e46c9a9d099118c96e902278d,0x1c08754ec019d62b010f58a4cc7c870820160a6acd6e98d19aa78a509b1906509e901990764cc9060cab72b04086e4dc,0x86d65c06c25ba6b0634416a519c94301a97173445464068e96475105c172b1aca4c8208059c0dbca4c82047594cd21d3,
    0x8e98b148906609d52546406c45465cc5d05e45a1db1c119d89cd07ac7021d53b020ce5b666e466a5e256862252a55275,0xb99991589d599417515614f14a98898e9931701b115190ea18c92d28143396c7ab0811d6da1b999895a9b49d595614f1,0x45625d06545cc6406c454653c63252a5a262c405ac2d4031b1a53687565586d2c521e8b405662cb00b9952c083396da1,0x97593242047593a521c20805a6a63c6225aa5b253a52c409aa65479290173174295201aa74b2c4541c60935ae666a5e,
    0x66625e45d2b6856a756558742546521c20805a2242047594c7466426545bc63062c521c46295ac6aa9aa4c70c8ba2d03,0x585a5b018c5cac7320c25d67aa5328ea6f24c78b16874870833966b1889931519d0902675192545ba63066a820475ae,0x4c7070b13b0032ace4ac78b16874a2c87a873a934108201608339688119585dd0111e548926a9e45ba7344067589c749,0xd99a9017aa82477252a8ea1307819497517098c1cd1d01b1151958908ca1ed04216af4194a58d00b0e4ec57292a6f2,
    0x1c20c05a2a61c1d55d454a5bc53255c63a65242833a6c599088b33d0032ace4cc1142516ba1599951549b59d61d1ab11,0x971749701d096f1cc18d10ca9857260c30a6a5cb115190c236691e443306ab46aa92a4c7101b93d0306e8b400bba292b,0xcc1014d597168542556ad8814e89ac033a8cb018c6aac7036ea92a0811d652b487082016d99ba1589d51b595614b1889,0x28222b9b4015cccb1dcda1db1c035e89cb07cc7101b93d050d65b666e45e25d47527446c6421738649816b18899718d1,
    0xa52244342794991901d11519729781751082016b999817915a1549b61d599514e94b18898f1929701d1151919a14c936,0xb344541c20805a5c5d27547469aa62263a52c53254a4609d324d8b070762b020c05b626e656855c6d875665253a63c62,0x1d31c16358ac0820164c90811d64f14871036969718e98896b16c94f14a9105c9952405ca5e0a649d48088dcec05aba0,0x16529b199099916e98c18a94870e0c55d1aca5c820805a645bc63065c820475a525d45e2b56ad86e655c5686c254652,
    0x46525bc634531c1a344ec00bca59331eb1e2c5a1d28b21f42a877647407565d45ca5e26445b063a66044232af4889083,0x8e96c700bca59050945b686e45666545527566d87446c64177282477252a8e96d1102048795c5425665c05e264a6605d,0x7919299817499518c90c56165295998e94c757205e8add99ba1589949b51d61559055d18b2c6b42403a56a477252a4f1,0x7098e96c11020487b686e07566d855c64a7446c65c05425bc630531d664222ccf400bca590032ace4cc9362cc5b12701,
    0x516b9ad5ab6272a8ea6f25715a15194c78b16874870830168a9142516da1b81989791d59b61771d11b19901951549529,0x27344507389c562ba1b11b5a0f1a84b0342cc6c0ce0ac91e44306e8b4198aa1d2b1c4215cf405e15490163589c772142,0x5a15194c7881168561711509b19d01d599299519898c16e9cc9182716d99981589929d015197096e98c9171813725475,0x55dd8250a7499298d16e9791702cc9ac1101b93726244215cf406615a9018354dc972142516b9ad5ab6292a6ea8f2571,
    0x7036ea92a0811d652b4870820169818894b3562da208cc2bd1aaa4a931c40754f40c1d62d002f58a4cc7c87082016831,0x16accb1dcda1db1c039d89cd07ac7101d53d020ce5a5c6b06346606225ac46303a94562da1d11d5a053c2cb00af232c,0xb11519729781751082016981791951929701b115198f14e98890811d6949b51b8ab1ada1529599d595614f18e98b1487,0x26d46c69aa62263a52c53254a4509e324b8b0687a2b020c05b666e256855c7586d665253a63c52262a402b4754991901,
    0xd095194874c7058ba2b02080593242047593c521c262225ac52a55c7586d65d241686b2c05ad60b2c4541c20805a5c5d,0x9117296c14a98898e99817497910e0c55d03829cb46b29720820169916f18c19720811d694975178ab5ad61d995715a1,0xc1d6271e24321697405d19490162e89c772142516d9ab5ad6272a8ea6f25715a15194c78b1687487083396b51b01b99,0x65c92a6f25315a95594c78b16874a2c87a873713a13070820160833968816b580db5250a9299499917118c1ac96e9cd1,
    0x68d73466c441950ce402539a9250418c656c063172b1cc83d11b6e66c27465c4414ecc24b62ad1ce18c101199d700535,0x4f27317a96c701d3a291d1e2c5a1c20475921c20c05a2a6e8d117606e65e46d85565d27546b27385b0634c4195674026,0x46428119d8a405ac25714c8408f5ae25666d67527465424409ea64d92b120d686892606546327304323589c56292aae2,0x45ca54c552531c270ea24081cec71664260d9b41990acd017845640195a57356a0376066a5e47525ca6c474673463065,
    0xadc56272aae24f29319a98c70650f29251e224408f59ea5585cc64a5426b86347325b046a1bc7306326506b46c274664,0x66d86e26c66b451833b6b8ae2558566531c3886374162383d018a8cdc53215685dd92b1211666891e05d45b273044470,0x5e27565d06d25b47327446c66e45585665429caab893ca4c66a631c58427b40660d590094e4e414204e7b565d455256,0x5c1aab02a1e86c014b99724a9bc94c56a556531e2c5a1d28b21c20805840cf5b309ea5b45d05c294ca6064a4408f5b6
  ],
  [
    0xd254419435ac0754e0b011744dcb07063172b1cc95318d7626e66645e07586526c47465c25d46307346b86d040b162ec,0x8c1cc9025cd17344a544094e6ac1020487b646605e256a55254674275664a7385b46326b06d85d045650d2cb991630b1,0x4f1ae1b8159908d0f4d0094e4ec0454e67011744dcb078b16874870830168a9d4c09dd99b91781d61559749b41ae16d1,0x158f17356ab8958566531c415e4746f21023d67aad5aae24f1561599731929d115071023d67aab59561d19731929509,
    0x5b6066a5e25665527566505ca642417055a48d1cc9ac1b927520254f1b34440b8b8a4b62c5a12db41b91d81d09cd18c1,0x8359a9cd1d89791d417297496c114e68470199aa1c59ab81b5ad190660d59158ab880855cdc951025393b2c1e204509b,0x8a47478b16870811d6487c87082016103996d09046953923c8408f5a6ab56ab893c55856664c5ca744541c0d4c6ac54b,0xb19ce1ad14c914c433704631a9cb827297919a98c195190a5321023d656159950a92ace24f27317a96c705d13290078d,
    0xb585c9aa532781729a7409db82b59941d4b56292ace24f27317a96c71990acd01784564105996d89599561d59b49d11,0x99175c94175105e115b0098d4ec046b137341e2c5a1d21c20805820ce5a224c17276b0634650642843466a4118a56703,0xaa6a833a50b402e899b231c11a3a9c1023d6d81b919897a9599561731929509b19b49d59ce1ac18d16c94f10195a5700,0xc4065695c1884e57364ac49d4417a2a2cd1a22dd81b99791589d61b41559749951909b11cd14e1ac9108b9371bc94c9c,
    0x915c9bc931e2c5a1d28b21ea1ce84d1c20805820ce5a204408f5ae26605ea5665586d66527505cc64a5427386b05b253,0xb89d61b59751949cc1ae181dc55d815295999099a99517497917021560cc92e2450666b40558339231c5214cf4043566,0xb1d01b10cec02c39ab016ae81c9aa52a9070c85a5d0170656405c17291dc8414199ed919a9781599709901529d19b11,0x54951904276691b4c22c6b240889ab70263585c5aac9c22db997815895599498d16c9711ae1b09b51cc1d61d19d9215c,
    0xcab89585b0450945ac69bcad87566525d455c531c628477400a7a57166541e2c5a1c20475921c20c05a2a4408121e951,0x29e95c5995078891ac2d5d01b0909d3a092b893c5585dc42645d2c08e11d90222ccdc58986bc15951cd18c909897171d,0x6a635c74acc9045ce272c242343d2400ad1d7162450d45b46b526b86c46d653c55865c5d45b24505e89cb8914a0f4d00,0x6ad8b386b1c60656b48c7148533d01116ae45726f24c78b16874a2c870820161849d69297117aa982d0108666c91b080,
    0x46e066a5667586d65d265464254a746762734451565ae066a5e45665d265454a6c65c064246529624d89d11056ae0935,0x5a54551c4215cf405c17291dc8408121ed919817895a9519929701d09b11b99b61d59751949ac1ce110506679e45c06c,0x70029e95c5995078b16874870830168a9a60cd5b61ad1ce16c91107a970447561c8c39aa5891020487a4a96a541c5094,0x6526c66d4756762740821746648c1cd105ac2571dcab89585b2450945b569bcad86c66e455c6b0531c6284774042ae6,
    0x6a5c1cd9a772ae2b595616c9142516d5a6f2b61b99571b11ac14c70a90f4b0238476400a77470222ccdc5891850617ae,0x7567647325b04505e89cb8114a0f4d0029e95c042d2b7166541e205ca88d6e066a5e46546425ca6c474075273463041,0x1e2c5a1c20475921f21c20805860e75a6a9e05ca5d45b27304117389cb0108d0f490223395c00a77471624266cd6c6b4,0xc5587385b44508139ed61b59ac98c1949751571d196f1cd14c71a8313b062c2b241817627362462847740429ab716654,
    0xc63073442330adc7aa92a0631aa92b2a524098d4ecd0908e11d90222ccdc589143516949d19d51b59ac98c109898d71d,0x736046284774042ae67002a5cdc5995078b168748708201608339688914204e7b666e06647586d66c45c05d455c5385b,0x6f24e1571d61d99cd208666c73404238476400a99d70222ccdc58914204e7ad6b5855c7467345385bc46099b1c181762,0x4854ce824ba2ce1ac714199ad231c1a14cec00c573915c9bc931e2c5a1d28b21ea1ce0420805820ce5a204508139eb5a,
    0x94974179170a054a339003738a4da2cc1ae1333a159a995190952959ada2cd11020487ad664a5c06c254656a75076674,0x7344037389cda2b0a8caae20c1d6271e243445d340560ec90142ccdc54777298aa1db899a9599d51901529d19b11b59,0x6f25715994c707211db010a6adc5078b16870811d64870830168a91824d69a97915891020487a4a96a541c3561d5c45b,0xc3415a3a0d02705c64772ae25a1559b1e215d919897a9d59d01711741929951b49b19ad1cc9050ce572308507389cba2,
    0x2c57aa70192994209d131b3426c4421742e4ae25a2141ce2d050b4674cc7042cec7262e857466c46e67506d2654c46a9,0x4508139eba28f25715994c706a0f4b010a6adc50788918389698a772ae25a15494f20457a271eaac2a4a802f58a49aa,0x4e7a3c95c531c606c4f4046ae291688508139ed9a8f24e1571589ba1b59b11ac7042b1e729833565cab89686d255663,0x926a94a566ae8b386b1c60656b4068533b014c5d248c1050973715c9bc931e2c5a1d28b21c208058508139e972549142,
    0x656a6c454664a40d2b464d09d5ab4270118386a9368b34742a877625e47566d05d26546427446c65c0422ecc24116a58,0x45e256a6d47566c054664a5c45b06327346b8403ab89cd090560ec90098d6a4050b337250551c1815cec7721020487ae,0x5994c707211db002b395c0429ab7141e2c5a1d21c20c05a2a460935a6a5e45624408121e92a5a95071020487b686e666,0x22dd91b99b51b01d19d419499118c1cc900bd62726a9dc5e25ca5b4ab896855642d0bb6327304507389cba1ad26f2571,
    0xc568b56ae6450a33b4141993d01c22aecd626455a2d02ae1b11b42d5ab9a18195ad030a6a7401a98db231c10a579c8d6,0xc7465c064a6c46d66b0531c1a83d2c00ab337010a6adc5078812d58359a9d91789729d0915631891dc5526b87305b453,0x8058508139e57214204e7a5cab896855253ca31c10a579ca60cd59725a1ae1b415598c914204e79eab50a3cae856655,0x4731c10b3b1cc58955772ce25a1d495596c114204e7b689bc95c566531c1c8476c00a7a57141e2c5a1c20475921f21c2,
    0x88914204e7ae69dc6d07566545524508139e6f27415714c7022ccdb016b416c5a214204e7ae69bc93855c56276875674,0x6c914204e7a6aad09bcb6856655c6c66405ca744756730531c1c8476c0427667002b395c5078b1687487082016083396,0x8b21ea1cea4d84c1c20805820ce5a204508139e57214204e79dcb3896855253c9b1c109eb1cc589557725a1ce1d41559,0x7919419898d16c108c7a87166b60c0d296acba2ce2ac70cc1aad0032e4dc92a10204879cca3a94a55c566531e2c5a1d2,
    0x5921c20c05a2a46a2d65466c25b4730744409ab4649518ca191625715c9cc840ae2e418336290414e6a4982da282b395,0x4ce7621742a4aa3444c14c5565ca5dc5e064263a5b1c21742e4cc71015abd0065696c00c5739168ab8931e2c5a1c2047,0xcec71668606c6b4ac70314e5b2e893b08d7626e66605e47505dc74664263a5b05ca6c46d255654c820f58640a52f0925,0xc5e463a7325b1c046bd2c070b13b050dd5a5054c5525ca5dc5e063a5b445c5c09cd5ab51b19085d199022ecc24cc1081,
    0xb56cc1081d2b7168ab8931e226c38275e0ac26d6a3073275045c5c0ac00e762924a86a25054c7466446c26d65525ca5d,0x55264a54c7465c26345ba73075441c2b8ac0754e0b01a1c59cb11b59ac718152bd00a54cec14631390507389cba20c4,0x8ea5295715994c78b16874a2c870820161043d6d5253274179197198191272a6c98e9cc114204e7b626605e456665c5d,0xb41ad18c108195e72c6966b5645d084ec0d4c29b2e8b385b1c3d02a6c7810cc156d03306ab400cd53724a8408121e732,
    0x6545dc5525c254c6c67447326b8631f5640c5a96c011774b0029e9641020887b646626545dc5527425c454c41cac624,0x8ab8931e2c5a1d21c20c05a2a4408221ed89ba1991599941771549d11709531b19b51ac1ce11020887b686e46625666d,0x46e66605e25d46526d05cc6c454655c75642d03a6c0ae708b342403939640868e99234730403354dc92a6e9081766716,0x8931e20464e99650b60664ed66b06c47464338456408195e71665e2430559b4021573b05644cac1462e292e88408f5b6
  ],
  [
    0x782b41b19ad1cc1161c83714ca5c40855cec1610f2b0507389cba214204e7b66a5c95654c6c640354ce40817667168ab,0xb940ec0708ea7344756731c50539b40314e5b368830ed5ab04206b99c5a2ce24c78b16870811d6487c870820160ae85d,0x82016083396889182716b9a589081cecd01a344ec1709897815997519417316e9ac18d1929509571b19b49068d13b01,0x641c2c4ecac7cc71015abd0065696c1852e293688508139eb9a772559531d1900e4e5902066adc5a2ce24c78b1687487,
    0x792952d41b11d19972645981791599b89b42952d59d11b19b0e615791941989b81b5292a8d16e91857117166ac674475,0xe4ae1cd1d620297a2b1b1c5214cf408b1ac9003666a45aa8ea4c78b16874a2c87a873a1347082016083396881d540cd,0xcb6455654c746423ac0e40b46689358b306b84408121ed99b89981791b59749951571909d0151973100bca592c482d0d,0x72d8b567388086e4dc8b322db99791ce1d81589771d19d51b61559532063172901983aa4947128393b26a9e94236e69d,
    0x1e2c5a1c20475921c20c05a2a4408321ed81b91789599771549531b19d11701133a8891b46b24032acdc9098c103195a,0xb00af2864cd1ac71290d6d00393964029ce272d8830d85a609ea5c05b463a7304267511c09897171dcab895854c56653,0xd19d81949d51559589b99b0a05c17291dc94c810f58a4cc9142516d89599911d01509b19b92731751571d59949021b93,0xce4029d1372d88512159d26405c4418c5ca40a3a3190281dc5c972ae25615315994c78891435967917019116e98c19a9,
    0xc2b465d59d929aad027816e9cc98c70c8aa6d2543175e094ca6a64065c6345ba4115c59cb91b19cc1ac70e9116d00354,0x8b21c208058508139ed81991971751549d119015317090ab330905d0a6246c1ccb0ae8c893569666e26c6433509a47aa,0x9aa62e855d9a772b81559531b1990102c67293386b46d880c5d8ac0445ab9003a56a46c1088766716aa3a931e2c5a1d2,0xc87b646e66c07467325b45c25e054c5625565dc6b86d475840c656ac02c599b244631c19435a49470c8566d04c0d4ec,
    0xcd16c9034655724263040a6669cd62b59ae2021d53703c1625dc6d45c27446b85b073275855654c410a6ae4b19901102,0xb59b91b0205e425902728c64772ae25615315994c78b16874870830168a9142516d89b91b01711781599771549531d19,0xb11519571949991d59d099010cc1aa9003a56a47aa8e96c7108cabd0066e8accd1ac700c573900a7389cb6265682dd1a,0x791771951531b199018c96e9709043d62934480af2864cc1a98875d825329a97719519018c9142516d81b99589751731,
    0x8339e9a97819098d16e9711749d19d51d89b59b91b020a3a3193304287561c972ae25615315994c7881aa1c1db819a9,0xa55c7565d265464c5ba730631c322a9b4021b93b0d0f455626e66c440754c64751019ba2b011ab8a4ac700c57392d885,0x475921f21c208058508139ed91b81989599571d59509b19d01711cc96c17499519310cc1aa903b8c0a47aa14204e7a6,0xc0d2a2e4772532043ba293346b1c4c43ab400e4e5900c6b89cd620c3b56ac1099b8471dcb3895854c566531e2c5a1c2,
    0x1c20805820ce5a224508139eb81599549b59771711531b099019519897a96c18e90468ea73647467324ad43966a9ba63,0xd621050547b606e26d66527546c47466405c2422f4164084ce99021ac664ac209898d71dcb3895854c566531e2c5a1d2,0x19d62b010ab9a4cc199d445d819a9791771b11531d199019518c96e9709043ba293346b1c4c43ab400b5a5900c6b89c,0xce400d993916aa3a931e2c5a1d28b21ea1ce0420805820ce5a2045a1dc7446c66406545526325ba5c254c5664222ccf4,
    0xa2525d055c7445465cc6406c26e66645e27306b85d43437386b46e8b669dcad255654c6c6423589a46c7068533b00315,0x45c732571b591824d6ba1791589d99ad1ce1d51034559b244632803ab89c6c2d029470605abb04a0e4ec10b1aa926a85,0xb01116ae45a2ae24c78b16870811d64870830168a91020487b686e25666c45427466406347307545d05e45b2ab884af0,0x70857626e666a6c47467546d254c5565c05dc5e4642650634430d859ea63a5b1c2870aec085d0b9331c1a14cec031ae2,
    0xb2a0f435dc94c810ee8a400d8f272d46c66b1c58435ac0454e690518b8a4ba21a8b49559531b19711083d619242740ee,0xa9ce0b0312d5b31c0c6c4ec0445ab9011ab8a45a2ae24c7889c85665d525329a9771791911cc18c96e9702941021b93,0x46d66c4a4c95ca509c0b31c086e4ec15c08e91d24066e8acac7159116b0518c4e4ba214204e7a4c74054655c828750ec,0x742d52532972050b33b010ac7a414204e7b6666a5e456275055654c7425c064465c6305ba4035cc9cb19b5214204e7b5,
    0x27545cc74254655c6c06d6650662644b386b1db1c1a14cec00b5a59003a54e45aa8ea4c78b16874a2c87082016c8474d,0x519571b11b59ac1ce10c60557a625e45dc65475255654c7465c2422f5824902b11b41b9ada2cd11020487b666e85e45d,0x484a8666c10ab8371dc94c9c1c16159ac130353b042c55a410b1aa926a8408121ed99ba1991789741949d51731901d09,0x5a2ae24c78b16874870830168a91020487b569465626e65e4c645d81cda2ae2043d62715c83362d768ad0ab863064265,
    0x709b11b41559531d1910e0ea90039d8a49aa31a1ad7aa902b41b99b128e9cc16c7068533b00c6b8ac00e4e5901116ae4,0x94106509eb01832aecb59b11045d1a9331c066e8acac704356690518b8a4ba289e22dd89b99791771d51949cc18d1901,0x2e4cc1d4a058aa6b0142ccec021b93b28d11763a5b25eaa6495cac46d65d45cc850b38641a88d16e9751d01519731909,0x864b99b52742b0110dcc2926a9ba730631c1c1396c00d533901116ae4046ae29168ab8931e20460935b44766962c50b4,
    0x7b626e66d46c074675054c55665c6646429d27345b05c4803a54e47aa14204e7b645e275265c5565c464254c746407aa,0x9115318c96e9709741b19b51559151d03b0547382c14204e7a5295ca4c850b42e4cc7019ba2b2b1c10d59a4ba214204e,0x4deaa88f235d05e46d65c26c0443730a49aa6e9cc18c7058aa6b0086e4ec00ab3390508139ed999a9791589d49971d01,0x8139e571519731b030c3b56ac7068533b00a738ac00b5a59168b38931e2c5a1c20475921f21c208059a131b54ca5c5d,
    0x26d05566527545dc54c7466b45b05c4410f58a49037aa8ea00d7a272c2411746a4cc71a10eab011539a41852e2936885,0xce5a224508139eb91989599549d59b41771901531d09b198e9ac96c17a9712951021d53b010b3b2414204e7ae666456,0x7b665ea6507545cc5d274054655c6d663a6b05b1c1a14cec029ce2b010d59a400e4e59168b38931e2c5a1d21c2080582,0x54aac7019d62b331c6843aac0445ab90614b8a4da21689495599018d1ac1b11709531d1910e42b90035e8a49aa14204e,
    0xac16c700ace590508139eb999917a9589571b49d59d11b015196c98e9909941751732182ae190508139e772b91531599,0x405820435820415820805820ce5a20744cd16d07566b26306427404099d4649539aad133457a9d01d5994199190a8e9,0x2
  ]
]

set_option maxRecDepth 200000 in
set_option maxHeartbeats 10000000 in
private lemma check_c3 : checkCase r1_c3 syms_c3 51 chunks_c3 = true := by
  decide +kernel

private lemma solve_c3 (L : LatinSquare 7) (hred : IsReducedWith (r1Table 3) L) :
    ∃ σ, IsTransversal L σ :=
  solve_case 3 r1_c3 syms_c3 51 chunks_c3
    (by decide) (by decide +kernel) check_c3 L hred

end OMA.LS7

-- Step LatinSquare.oddOrderLeq9LatinSquareTransversal.R1.H1.R1.H1
-- Credit: @tkaiman
theorem OMA.solution : OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1.H1 := by
  intro L
  obtain ⟨k, M, hred, hiso⟩ := OMA.LS7.normalize_to_4 L
  apply OMA.LS7.hasTransversal_of_isotopic hiso
  fin_cases k
  · exact OMA.LS7.solve_c0 M hred
  · exact OMA.LS7.solve_c1 M hred
  · exact OMA.LS7.solve_c2 M hred
  · exact OMA.LS7.solve_c3 M hred
