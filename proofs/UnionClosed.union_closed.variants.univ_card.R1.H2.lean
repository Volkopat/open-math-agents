import OMAReductions.R_UnionClosed_union_closed_variants_univ_card_R1
import Mathlib

/-!
Proof of the four-element minimum case on the twelve-coordinate universe
(Vuckovic and Zivkovic 2017, Table I, rows 7, 8, 12, 16, 26, 27, 28, 29, 30, 31, 32)
using kernel-verified reflective Farkas LP duality branch-and-bound certificates.
-/

namespace H2Proof
open Finset UnionClosed
open scoped Classical

-- ============================================================================
-- Section 1: Binary-tree integer vector (VTree) and lookup tree (CTree)
-- ============================================================================

inductive VTree : ℕ → Type
  | leaf : ℤ → VTree 0
  | node {d : ℕ} : VTree d → VTree d → VTree (d + 1)

def VTree.ofFun : (d : ℕ) → (ℕ → ℤ) → VTree d
  | 0, f => .leaf (f 0)
  | d + 1, f => .node (VTree.ofFun d (fun i => f (2 * i))) (VTree.ofFun d (fun i => f (2 * i + 1)))

def VTree.scale : {d : ℕ} → ℤ → VTree d → VTree d
  | 0, s, .leaf x => .leaf (s * x)
  | _ + 1, s, .node l r => .node (l.scale s) (r.scale s)

def VTree.addAt : {d : ℕ} → VTree d → ℕ → ℤ → VTree d
  | 0, .leaf x, _, δ => .leaf (x + δ)
  | _ + 1, .node l r, i, δ =>
    if i % 2 = 0 then .node (l.addAt (i / 2) δ) r
    else .node l (r.addAt (i / 2) δ)

def VTree.addList {d : ℕ} (t : VTree d) (xs : List ℕ) (δ : ℤ) : VTree d :=
  xs.foldl (fun acc a => acc.addAt a δ) t

def VTree.dot : {d : ℕ} → VTree d → (ℕ → ℤ) → ℤ
  | 0, .leaf x, v => x * v 0
  | _ + 1, .node l r, v => l.dot (fun i => v (2 * i)) + r.dot (fun i => v (2 * i + 1))

def VTree.negSum : {d : ℕ} → VTree d → ℤ
  | 0, .leaf x => if x < 0 then x else 0
  | _ + 1, .node l r => l.negSum + r.negSum

lemma sum_range_two_mul (n : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ Finset.range (2 * n), f i =
      (∑ i ∈ Finset.range n, f (2 * i)) + (∑ i ∈ Finset.range n, f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ, Finset.sum_range_succ]
    ring

lemma VTree.dot_ofFun (d : ℕ) (f v : ℕ → ℤ) :
    (VTree.ofFun d f).dot v = ∑ i ∈ Finset.range (2 ^ d), f i * v i := by
  induction d generalizing f v with
  | zero => simp [VTree.ofFun, VTree.dot]
  | succ d ih =>
    simp only [VTree.ofFun, VTree.dot, ih]
    rw [pow_succ', sum_range_two_mul]

lemma VTree.dot_scale {d : ℕ} (s : ℤ) (t : VTree d) (v : ℕ → ℤ) :
    (t.scale s).dot v = s * t.dot v := by
  induction t generalizing v with
  | leaf x => simp [VTree.scale, VTree.dot]; ring
  | node l r ihl ihr => simp [VTree.scale, VTree.dot, ihl, ihr]; ring

lemma VTree.dot_addAt {d : ℕ} (t : VTree d) (i : ℕ) (hi : i < 2 ^ d) (δ : ℤ) (v : ℕ → ℤ) :
    (t.addAt i δ).dot v = t.dot v + δ * v i := by
  induction t generalizing i v with
  | leaf x =>
    have h0 : i = 0 := by omega
    subst h0; simp [VTree.addAt, VTree.dot]; ring
  | @node d l r ihl ihr =>
    simp only [VTree.addAt]
    split_ifs with h
    · have hlt : i / 2 < 2 ^ d := by rw [pow_succ'] at hi; omega
      have heq : 2 * (i / 2) = i := by omega
      simp only [VTree.dot, ihl (i / 2) hlt (fun j => v (2 * j)), heq]
      ring
    · have hlt : i / 2 < 2 ^ d := by rw [pow_succ'] at hi; omega
      have heq : 2 * (i / 2) + 1 = i := by omega
      simp only [VTree.dot, ihr (i / 2) hlt (fun j => v (2 * j + 1)), heq]
      ring

lemma VTree.dot_addList {d : ℕ} (t : VTree d) (xs : List ℕ) (hxs : ∀ a ∈ xs, a < 2 ^ d)
    (δ : ℤ) (v : ℕ → ℤ) :
    (t.addList xs δ).dot v = t.dot v + δ * (xs.map v).sum := by
  induction xs generalizing t with
  | nil => simp [VTree.addList]
  | cons a tl ih =>
    simp only [VTree.addList, List.foldl_cons, List.map_cons, List.sum_cons]
    have ha : a < 2 ^ d := hxs a (List.mem_cons_self ..)
    have htl : ∀ x ∈ tl, x < 2 ^ d := fun x hx => hxs x (List.mem_cons_of_mem _ hx)
    change ((t.addAt a δ).addList tl δ).dot v = _
    rw [ih (t.addAt a δ) htl, VTree.dot_addAt t a ha δ v]
    ring

lemma VTree.negSum_le_dot {d : ℕ} (t : VTree d) (v : ℕ → ℤ) (hbit : ∀ i, v i = 0 ∨ v i = 1) :
    t.negSum ≤ t.dot v := by
  induction t generalizing v with
  | leaf x =>
    simp only [VTree.negSum, VTree.dot]
    rcases hbit 0 with h | h <;> rw [h] <;> split_ifs <;> omega
  | node l r ihl ihr =>
    simp only [VTree.negSum, VTree.dot]
    exact add_le_add (ihl _ (fun i => hbit _)) (ihr _ (fun i => hbit _))

inductive CTree (α : Type) : ℕ → Type
  | leaf : Option α → CTree α 0
  | node {d : ℕ} : CTree α d → CTree α d → CTree α (d + 1)

def CTree.empty {α : Type} : (d : ℕ) → CTree α d
  | 0 => .leaf none
  | d + 1 => .node (CTree.empty d) (CTree.empty d)

def CTree.get? {α : Type} : {d : ℕ} → CTree α d → ℕ → Option α
  | 0, .leaf x, _ => x
  | _ + 1, .node l r, i => if i % 2 = 0 then l.get? (i / 2) else r.get? (i / 2)

def CTree.set {α : Type} : {d : ℕ} → CTree α d → ℕ → α → CTree α d
  | 0, .leaf _, _, x => .leaf (some x)
  | _ + 1, .node l r, i, x =>
    if i % 2 = 0 then .node (l.set (i / 2) x) r
    else .node l (r.set (i / 2) x)

def CTree.ofListAux {α : Type} {d : ℕ} : List α → ℕ → CTree α d → CTree α d
  | [], _, acc => acc
  | x :: xs, idx, acc => CTree.ofListAux xs (idx + 1) (acc.set idx x)

def CTree.ofList {α : Type} (d : ℕ) (xs : List α) : CTree α d :=
  CTree.ofListAux xs 0 (CTree.empty d)

lemma CTree.empty_get? {α : Type} (d i : ℕ) : (CTree.empty (α := α) d).get? i = none := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih => simp [CTree.empty, CTree.get?, ih]

lemma CTree.set_preserves {α : Type} {d : ℕ} (P : α → Prop) (t : CTree α d) (i : ℕ) (x : α)
    (ht : ∀ j y, t.get? j = some y → P y) (hx : P x) :
    ∀ j y, (t.set i x).get? j = some y → P y := by
  induction t generalizing i with
  | leaf o =>
    intro j y h; simp only [CTree.set, CTree.get?, Option.some.injEq] at h; subst h; exact hx
  | node l r ihl ihr =>
    intro j y h
    simp only [CTree.set] at h
    split_ifs at h with hi
    · simp only [CTree.get?] at h
      split_ifs at h with hj
      · exact ihl (i / 2) (fun k z hz => ht (2 * k) z (by simp [CTree.get?, hz])) (j / 2) y h
      · exact ht j y (by simp [CTree.get?, hj, h])
    · simp only [CTree.get?] at h
      split_ifs at h with hj
      · exact ht j y (by simp [CTree.get?, hj, h])
      · exact ihr (i / 2) (fun k z hz => ht (2 * k + 1) z (by
          simp only [CTree.get?, show ¬ (2 * k + 1) % 2 = 0 by omega, ↓reduceIte,
            show (2 * k + 1) / 2 = k by omega, hz])) (j / 2) y h

lemma CTree.ofListAux_preserves {α : Type} {d : ℕ} (P : α → Prop) (xs : List α) (idx : ℕ)
    (acc : CTree α d) (hacc : ∀ j y, acc.get? j = some y → P y) (hxs : ∀ x ∈ xs, P x) :
    ∀ j y, (CTree.ofListAux xs idx acc).get? j = some y → P y := by
  induction xs generalizing idx acc with
  | nil => exact hacc
  | cons x tl ih =>
    exact ih (idx + 1) (acc.set idx x)
      (CTree.set_preserves P acc idx x hacc (hxs x (List.mem_cons_self ..)))
      (fun z hz => hxs z (List.mem_cons_of_mem _ hz))

lemma CTree.ofList_preserves {α : Type} (d : ℕ) (P : α → Prop) (xs : List α) (hxs : ∀ x ∈ xs, P x) :
    ∀ j y, (CTree.ofList d xs).get? j = some y → P y :=
  CTree.ofListAux_preserves P xs 0 (CTree.empty d)
    (fun j y h => by rw [CTree.empty_get?] at h; cases h) hxs

-- ============================================================================
-- Section 2: Reflective Farkas LP Branch-and-Bound Verifier
-- ============================================================================

inductive Term where
  | j (m a b : ℕ)
  | f (m a g : ℕ)
  | z (m a : ℕ)
  | o (m a : ℕ)
  | c (m idx : ℕ)

def decodeTerm (p : ℕ) : Term :=
  let m := (p >>> 17) + 1
  let tag := (p >>> 14) &&& 7
  if tag = 0 then .j m (p &&& 127) ((p >>> 7) &&& 127)
  else if tag = 1 then .f m (p &&& 127) ((p >>> 7) &&& 127)
  else if tag = 2 then .z m (p &&& 127)
  else if tag = 3 then .o m (p &&& 127)
  else .c m (p &&& 16383)

inductive BnbTree where
  | lf (sc : ℕ) (ts : List ℕ)
  | br (var : ℕ) (lo hi : BnbTree)

def popcount : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, m => (if m % 2 = 1 then 1 else 0) + popcount n (m / 2)

def isSmall (r k a : ℕ) : Bool :=
  !(k == 0 && a == 0) && popcount r a + k < 4

def isFixed (r k : ℕ) (FiMasks : List ℕ) (a : ℕ) : Bool :=
  if k == 0 then FiMasks.contains a else a == 2 ^ r - 1

def checkLeafLoop (r k : ℕ) (genMasks FiMasks : List ℕ) {cd : ℕ} (fmap : CTree (List ℕ × ℤ) cd)
    (zeros ones : List ℕ) : VTree r → ℤ → List Term → Bool
  | t, B, [] => decide (B < t.negSum)
  | t, B, .j m a b :: rest =>
    if a < 2 ^ r && b < 2 ^ r then
      let mz : ℤ := m
      checkLeafLoop r k genMasks FiMasks fmap zeros ones
        (((t.addAt a mz).addAt b mz).addAt (a ||| b) (-mz)) (B + mz) rest
    else false
  | t, B, .f m a g :: rest =>
    if a < 2 ^ r && genMasks.contains g then
      let mz : ℤ := m
      checkLeafLoop r k genMasks FiMasks fmap zeros ones
        ((t.addAt a mz).addAt (a ||| g) (-mz)) B rest
    else false
  | t, B, .z m a :: rest =>
    if a < 2 ^ r && (isSmall r k a || zeros.contains a) then
      checkLeafLoop r k genMasks FiMasks fmap zeros ones (t.addAt a (m : ℤ)) B rest
    else false
  | t, B, .o m a :: rest =>
    if a < 2 ^ r && (isFixed r k FiMasks a || ones.contains a) then
      let mz : ℤ := m
      checkLeafLoop r k genMasks FiMasks fmap zeros ones (t.addAt a (-mz)) (B - mz) rest
    else false
  | t, B, .c m idx :: rest =>
    match fmap.get? idx with
    | none => false
    | some (xs, rhs) =>
      let mz : ℤ := m
      checkLeafLoop r k genMasks FiMasks fmap zeros ones (t.addList xs mz) (B + mz * rhs) rest

def checkLeaf (r k : ℕ) (objTree : VTree r) (target : ℤ) (genMasks FiMasks : List ℕ)
    {cd : ℕ} (fmap : CTree (List ℕ × ℤ) cd) (zeros ones : List ℕ) (sc : ℕ) (ts : List ℕ) : Bool :=
  checkLeafLoop r k genMasks FiMasks fmap zeros ones (objTree.scale (sc : ℤ)) ((sc : ℤ) * (target - 1)) (ts.map decodeTerm)

def checkTree (r k : ℕ) (objTree : VTree r) (target : ℤ) (genMasks FiMasks : List ℕ)
    {cd : ℕ} (fmap : CTree (List ℕ × ℤ) cd) : List ℕ → List ℕ → BnbTree → Bool
  | zeros, ones, .lf sc ts => checkLeaf r k objTree target genMasks FiMasks fmap zeros ones sc ts
  | zeros, ones, .br v lo hi =>
    checkTree r k objTree target genMasks FiMasks fmap (v :: zeros) ones lo &&
    checkTree r k objTree target genMasks FiMasks fmap zeros (v :: ones) hi

lemma lor_lt_two_pow {r a b : ℕ} (ha : a < 2 ^ r) (hb : b < 2 ^ r) : (a ||| b) < 2 ^ r := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Nat.testBit_or, Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hi)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hi))]
  rfl

lemma checkLeafLoop_sound {r k cd : ℕ} {genMasks FiMasks : List ℕ} {fmap : CTree (List ℕ × ℤ) cd}
    {zeros ones : List ℕ} {v : ℕ → ℤ}
    (hbit : ∀ i, v i = 0 ∨ v i = 1)
    (hjoin : ∀ a < 2 ^ r, ∀ b < 2 ^ r, v a + v b - v (a ||| b) ≤ 1)
    (hforce : ∀ a < 2 ^ r, ∀ g ∈ genMasks, g < 2 ^ r ∧ v a - v (a ||| g) ≤ 0)
    (hsmall : ∀ a < 2 ^ r, isSmall r k a = true → v a ≤ 0)
    (hfixed : ∀ a < 2 ^ r, isFixed r k FiMasks a = true → -v a ≤ -1)
    (hzeros : ∀ a ∈ zeros, v a ≤ 0)
    (hones : ∀ a ∈ ones, -v a ≤ -1)
    (hfmap : ∀ idx p, fmap.get? idx = some p → (∀ a ∈ p.1, a < 2 ^ r) ∧ (p.1.map v).sum ≤ p.2)
    (t : VTree r) (B : ℤ) (ts : List Term)
    (htB : t.dot v ≤ B)
    (hchk : checkLeafLoop r k genMasks FiMasks fmap zeros ones t B ts = true) : False := by
  induction ts generalizing t B with
  | nil =>
    simp only [checkLeafLoop, decide_eq_true_eq] at hchk
    have hns := VTree.negSum_le_dot t v hbit
    omega
  | cons tm rest ih =>
    cases tm with
    | j m a b =>
      simp only [checkLeafLoop] at hchk
      split_ifs at hchk with hab
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hab
      have hu : (a ||| b) < 2 ^ r := lor_lt_two_pow hab.1 hab.2
      have hj : v a + v b - v (a ||| b) ≤ 1 := hjoin a hab.1 b hab.2
      have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
      have hdot : (((t.addAt a (m : ℤ)).addAt b (m : ℤ)).addAt (a ||| b) (-(m : ℤ))).dot v ≤ B + (m : ℤ) := by
        rw [VTree.dot_addAt _ _ hu, VTree.dot_addAt _ _ hab.2, VTree.dot_addAt _ _ hab.1]
        nlinarith
      exact ih _ _ hdot hchk
    | f m a g =>
      simp only [checkLeafLoop] at hchk
      split_ifs at hchk with hag
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_eq_mem] at hag
      have ⟨hg, hf⟩ := hforce a hag.1 g hag.2
      have hu : (a ||| g) < 2 ^ r := lor_lt_two_pow hag.1 hg
      have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
      have hdot : ((t.addAt a (m : ℤ)).addAt (a ||| g) (-(m : ℤ))).dot v ≤ B := by
        rw [VTree.dot_addAt _ _ hu, VTree.dot_addAt _ _ hag.1]
        nlinarith
      exact ih _ _ hdot hchk
    | z m a =>
      simp only [checkLeafLoop] at hchk
      split_ifs at hchk with haz
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.contains_eq_mem] at haz
      have hva : v a ≤ 0 := haz.2.elim (hsmall a haz.1) (hzeros a)
      have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
      have hdot : (t.addAt a (m : ℤ)).dot v ≤ B := by
        rw [VTree.dot_addAt _ _ haz.1]; nlinarith
      exact ih _ _ hdot hchk
    | o m a =>
      simp only [checkLeafLoop] at hchk
      split_ifs at hchk with hao
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.contains_eq_mem] at hao
      have hva : -v a ≤ -1 := hao.2.elim (hfixed a hao.1) (hones a)
      have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
      have hdot : (t.addAt a (-(m : ℤ))).dot v ≤ B - (m : ℤ) := by
        rw [VTree.dot_addAt _ _ hao.1]; nlinarith
      exact ih _ _ hdot hchk
    | c m idx =>
      simp only [checkLeafLoop] at hchk
      cases hget : fmap.get? idx with
      | none => rw [hget] at hchk; cases hchk
      | some p =>
        rw [hget] at hchk
        have ⟨hxs, hle⟩ := hfmap idx p hget
        have hm : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
        have hdot : (t.addList p.1 (m : ℤ)).dot v ≤ B + (m : ℤ) * p.2 := by
          rw [VTree.dot_addList _ _ hxs]; nlinarith
        exact ih _ _ hdot hchk

lemma checkTree_sound {r k cd : ℕ} {objTree : VTree r} {target : ℤ} {genMasks FiMasks : List ℕ}
    {fmap : CTree (List ℕ × ℤ) cd} {v : ℕ → ℤ}
    (hbit : ∀ i, v i = 0 ∨ v i = 1)
    (hjoin : ∀ a < 2 ^ r, ∀ b < 2 ^ r, v a + v b - v (a ||| b) ≤ 1)
    (hforce : ∀ a < 2 ^ r, ∀ g ∈ genMasks, g < 2 ^ r ∧ v a - v (a ||| g) ≤ 0)
    (hsmall : ∀ a < 2 ^ r, isSmall r k a = true → v a ≤ 0)
    (hfixed : ∀ a < 2 ^ r, isFixed r k FiMasks a = true → -v a ≤ -1)
    (hfmap : ∀ idx p, fmap.get? idx = some p → (∀ a ∈ p.1, a < 2 ^ r) ∧ (p.1.map v).sum ≤ p.2)
    (zeros ones : List ℕ) (tree : BnbTree)
    (hzeros : ∀ a ∈ zeros, v a ≤ 0) (hones : ∀ a ∈ ones, -v a ≤ -1)
    (hchk : checkTree r k objTree target genMasks FiMasks fmap zeros ones tree = true) :
    target ≤ objTree.dot v := by
  induction tree generalizing zeros ones with
  | lf sc ts =>
    by_contra! hbad
    have hle : objTree.dot v ≤ target - 1 := by omega
    have hm : (0 : ℤ) ≤ (sc : ℤ) := Int.natCast_nonneg sc
    have htB : (objTree.scale (sc : ℤ)).dot v ≤ (sc : ℤ) * (target - 1) := by
      rw [VTree.dot_scale]; nlinarith
    exact checkLeafLoop_sound hbit hjoin hforce hsmall hfixed hzeros hones hfmap _ _ (ts.map decodeTerm) htB hchk
  | br var lo hi ihlo ihhi =>
    simp only [checkTree, Bool.and_eq_true] at hchk
    rcases hbit var with hv0 | hv1
    · exact ihlo (var :: zeros) ones
        (fun a ha => by rcases List.mem_cons.mp ha with rfl | h; omega; exact hzeros a h)
        hones hchk.1
    · exact ihhi zeros (var :: ones) hzeros
        (fun a ha => by rcases List.mem_cons.mp ha with rfl | h; omega; exact hones a h)
        hchk.2

-- ============================================================================
-- Section 3: Bitmasks, decode, Patterns, and Forbidden-Cut Certificates
-- ============================================================================

def decode {b : ℕ} (e : Fin b ↪ Fin 12) (m : ℕ) : Finset (Fin 12) :=
  (univ.filter (fun i : Fin b => m.testBit i.val)).map e

lemma decode_zero {b : ℕ} (e : Fin b ↪ Fin 12) : decode e 0 = ∅ := by
  ext x; simp [decode]

lemma decode_all_ones {b : ℕ} (e : Fin b ↪ Fin 12) : decode e (2 ^ b - 1) = univ.map e := by
  ext x
  simp only [decode, mem_map, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, _, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, by rw [Nat.testBit_two_pow_sub_one]; exact decide_eq_true i.isLt, rfl⟩

lemma decode_or {b : ℕ} (e : Fin b ↪ Fin 12) (m₁ m₂ : ℕ) :
    decode e (m₁ ||| m₂) = decode e m₁ ∪ decode e m₂ := by
  ext x
  simp only [decode, mem_union, mem_map, mem_filter, mem_univ, true_and, Nat.testBit_or, Bool.or_eq_true]
  constructor
  · rintro ⟨i, h | h, rfl⟩
    · exact Or.inl ⟨i, h, rfl⟩
    · exact Or.inr ⟨i, h, rfl⟩
  · rintro (⟨i, h, rfl⟩ | ⟨i, h, rfl⟩)
    · exact ⟨i, Or.inl h, rfl⟩
    · exact ⟨i, Or.inr h, rfl⟩

lemma popcount_eq_card (b m : ℕ) :
    popcount b m = ((univ : Finset (Fin b)).filter (fun i => m.testBit i.val)).card := by
  induction b generalizing m with
  | zero => simp [popcount]
  | succ b ih =>
    rw [popcount, ih (m / 2), Fin.univ_succ, filter_cons]
    let embS : Fin b ↪ Fin (b + 1) := ⟨Fin.succ, Fin.succ_injective _⟩
    have hstep : (univ.map embS).filter (fun i : Fin (b + 1) => m.testBit i.val) =
        (univ.filter (fun i : Fin b => (m / 2).testBit i.val)).map embS := by
      ext i
      simp only [mem_filter, mem_map, mem_univ, true_and, embS, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨j, rfl⟩, h⟩
        refine ⟨j, ?_, rfl⟩
        rw [Nat.testBit_div_two]
        simpa [Nat.testBit_succ] using h
      · rintro ⟨j, h, rfl⟩
        refine ⟨⟨j, rfl⟩, ?_⟩
        rw [Nat.testBit_div_two] at h
        simpa [Nat.testBit_succ] using h
    have h0 : m.testBit 0 = decide (m % 2 = 1) := Nat.testBit_zero m
    by_cases hm : m % 2 = 1
    · have ht : m.testBit (0 : Fin (b + 1)).val = true := by simpa [h0] using hm
      rw [if_pos ht, card_cons, hstep, card_map, if_pos hm]
      omega
    · have hf : ¬ m.testBit (0 : Fin (b + 1)).val = true := by simp [h0, hm]
      rw [if_neg hf, hstep, card_map, if_neg hm, zero_add]

lemma decode_card {b : ℕ} (e : Fin b ↪ Fin 12) (m : ℕ) :
    (decode e m).card = popcount b m := by
  rw [decode, card_map, popcount_eq_card]

lemma decode_inj {b : ℕ} (e : Fin b ↪ Fin 12) {m₁ m₂ : ℕ} (h₁ : m₁ < 2 ^ b) (h₂ : m₂ < 2 ^ b)
    (heq : decode e m₁ = decode e m₂) : m₁ = m₂ := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < b
  · have hmem : e ⟨i, hi⟩ ∈ decode e m₁ ↔ e ⟨i, hi⟩ ∈ decode e m₂ := by rw [heq]
    simp only [decode, mem_map, mem_filter, mem_univ, true_and] at hmem
    have hl : (∃ j : Fin b, m₁.testBit j.val = true ∧ e j = e ⟨i, hi⟩) ↔ m₁.testBit i = true := by
      constructor
      · rintro ⟨j, hj, he⟩; cases e.injective he; exact hj
      · intro h; exact ⟨⟨i, hi⟩, h, rfl⟩
    have hr : (∃ j : Fin b, m₂.testBit j.val = true ∧ e j = e ⟨i, hi⟩) ↔ m₂.testBit i = true := by
      constructor
      · rintro ⟨j, hj, he⟩; cases e.injective he; exact hj
      · intro h; exact ⟨⟨i, hi⟩, h, rfl⟩
    rw [hl, hr] at hmem
    cases h1 : m₁.testBit i <;> cases h2 : m₂.testBit i <;> simp_all
  · have hle : b ≤ i := by omega
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h₁ (Nat.pow_le_pow_right (by omega) hle)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le h₂ (Nat.pow_le_pow_right (by omega) hle))]

lemma decode_subset_of_or {b : ℕ} (e : Fin b ↪ Fin 12) {m₁ m₂ : ℕ} (h : (m₁ ||| m₂) = m₂) :
    decode e m₁ ⊆ decode e m₂ := by
  rw [← h, decode_or]; exact subset_union_left

lemma decode_subset_of_and {b : ℕ} (e : Fin b ↪ Fin 12) {m₁ m₂ : ℕ} (h : (m₁ &&& m₂) = m₂) :
    decode e m₂ ⊆ decode e m₁ := by
  intro x hx
  simp only [decode, mem_map, mem_filter, mem_univ, true_and] at hx ⊢
  obtain ⟨i, hi, rfl⟩ := hx
  refine ⟨i, ?_, rfl⟩
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at hi
  exact hi.1

-- Pattern table for the 11 rows of H2!
def patR : ℕ → ℕ
  | 7 => 6
  | 8 => 7
  | 12 => 6
  | 16 => 5
  | 26 => 6
  | 27 => 6
  | 28 => 5
  | 29 => 6
  | 30 => 5
  | 31 => 6
  | 32 => 4
  | _ => 0

def patGens : ℕ → List ℕ
  | 7 => [15, 23, 27, 39, 43, 51]
  | 8 => [15, 23, 39, 71]
  | 12 => [15, 23, 39]
  | 16 => [15, 23, 27]
  | 26 => [15, 23, 47]
  | 27 => [15, 31, 47]
  | 28 => [15, 23]
  | 29 => [31, 47]
  | 30 => [15, 31]
  | 31 => [15, 51]
  | 32 => [15]
  | _ => []

def HasPattern (F : Finset (Finset (Fin 12))) (pr : ℕ) : Prop :=
  ∃ e : Fin (patR pr) ↪ Fin 12, ∀ g ∈ patGens pr, decode e g ∈ F

def nodupNat : List ℕ → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupNat xs

lemma nodupNat_sound {xs : List ℕ} (h : nodupNat xs = true) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x tl ih =>
    simp only [nodupNat, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    exact List.nodup_cons.mpr ⟨h.1, ih h.2⟩

def Kmask (r k : ℕ) : ℕ := ((1 <<< k) - 1) <<< r

lemma testBit_one_shl (p t : ℕ) : (1 <<< p).testBit t = decide (p = t) := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

def mapMaskAux : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | p :: ps, i, g => (if g.testBit i then 1 <<< p else 0) ||| mapMaskAux ps (i + 1) g

def mapMask (phi : List ℕ) (g : ℕ) : ℕ := mapMaskAux phi 0 g

lemma testBit_mapMaskAux (ps : List ℕ) (i g t : ℕ) :
    (mapMaskAux ps i g).testBit t = true ↔
      ∃ j : Fin ps.length, g.testBit (i + j.val) = true ∧ ps[j] = t := by
  induction ps generalizing i with
  | nil => simp [mapMaskAux]
  | cons p tl ih =>
    simp only [mapMaskAux, Nat.testBit_or, Bool.or_eq_true, ih (i + 1)]
    constructor
    · rintro (h | ⟨j, hj, hp⟩)
      · split_ifs at h with hg
        · rw [testBit_one_shl, decide_eq_true_eq] at h
          exact ⟨⟨0, by simp⟩, by simpa using hg, by simpa using h⟩
        · simp at h
      · exact ⟨⟨j.val + 1, by simp [j.isLt]⟩, by rwa [show i + (j.val + 1) = (i + 1) + j.val by omega], by simpa using hp⟩
    · rintro ⟨⟨idx, hidx⟩, hg, hp⟩
      cases idx with
      | zero =>
        left
        simp only [Nat.add_zero] at hg
        change p = t at hp
        rw [if_pos hg, testBit_one_shl, decide_eq_true_eq]
        exact hp
      | succ j =>
        right
        refine ⟨⟨j, Nat.lt_of_succ_lt_succ hidx⟩, ?_, ?_⟩
        · rwa [show (i + 1) + j = i + (j + 1) by omega]
        · simpa using hp

lemma decode_comp_emb {m n : ℕ} (e_ext : Fin n ↪ Fin 12) (phi : List ℕ)
    (hlen : phi.length = m) (hnd : phi.Nodup) (hlt : ∀ x ∈ phi, x < n) :
    ∃ e' : Fin m ↪ Fin 12, ∀ g' : ℕ, decode e' g' = decode e_ext (mapMask phi g') := by
  let f : Fin m → Fin n := fun i => ⟨phi[i.val]'(hlen ▸ i.isLt), hlt _ (List.getElem_mem _)⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    have hval : phi[a.val]'(hlen ▸ a.isLt) = phi[b.val]'(hlen ▸ b.isLt) := congrArg Fin.val hab
    have hidx := (List.Nodup.getElem_inj_iff hnd).mp hval
    exact Fin.ext hidx
  refine ⟨⟨fun i => e_ext (f i), e_ext.injective.comp hf_inj⟩, ?_⟩
  intro g'
  ext x
  simp only [decode, mem_map, mem_filter, mem_univ, true_and, mapMask, testBit_mapMaskAux, Nat.zero_add]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨f i, ⟨⟨i.val, hlen ▸ i.isLt⟩, hi, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨j, hj, hpy⟩, rfl⟩
    refine ⟨⟨j.val, hlen ▸ j.isLt⟩, hj, ?_⟩
    exact congrArg e_ext (Fin.ext hpy)

-- Extension of e : Fin r ↪ Fin 12 with disjoint K : Finset (Fin 12) to Fin (r + K.card) ↪ Fin 12
lemma extEmb {r : ℕ} (e : Fin r ↪ Fin 12) (K : Finset (Fin 12))
    (hdisj : Disjoint (univ.map e) K) :
    ∃ e_ext : Fin (r + K.card) ↪ Fin 12,
      (∀ a < 2 ^ r, decode e_ext a = decode e a) ∧
      (∀ a < 2 ^ r, decode e_ext (Kmask r K.card ||| a) = K ∪ decode e a) := by
  let eK : Fin K.card ≃ ↥K := (Fintype.equivFinOfCardEq (Fintype.card_coe K)).symm
  let f : Fin (r + K.card) → Fin 12 := fun i =>
    if h : i.val < r then e ⟨i.val, h⟩ else (eK ⟨i.val - r, by omega⟩).val
  have hf_inj : Function.Injective f := by
    intro x y hxy
    simp only [f] at hxy
    split_ifs at hxy with hx hy hy
    · have hv : x.val = y.val := congrArg (Fin.val : Fin r → ℕ) (e.injective hxy)
      exact Fin.ext hv
    · exfalso
      have h1 : e ⟨x.val, hx⟩ ∈ univ.map e := mem_map.mpr ⟨_, mem_univ _, rfl⟩
      have h2 : e ⟨x.val, hx⟩ ∈ K := hxy ▸ (eK _).property
      exact Finset.disjoint_left.mp hdisj h1 h2
    · exfalso
      have h1 : e ⟨y.val, hy⟩ ∈ univ.map e := mem_map.mpr ⟨_, mem_univ _, rfl⟩
      have h2 : e ⟨y.val, hy⟩ ∈ K := hxy.symm ▸ (eK _).property
      exact Finset.disjoint_left.mp hdisj h1 h2
    · have hv : x.val - r = y.val - r := congrArg Fin.val (eK.injective (Subtype.ext hxy))
      exact Fin.ext (by omega)
  let e_ext : Fin (r + K.card) ↪ Fin 12 := ⟨f, hf_inj⟩
  have hlow : ∀ a < 2 ^ r, decode e_ext a = decode e a := by
    intro a ha
    ext x
    simp only [decode, mem_map, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hlt : i.val < r := by
        by_contra hge
        have hle : r ≤ i.val := by omega
        have := Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hle))
        rw [this] at hi; cases hi
      refine ⟨⟨i.val, hlt⟩, hi, ?_⟩
      change e ⟨i.val, hlt⟩ = f i
      simp only [f, dif_pos hlt]
    · rintro ⟨i, hi, rfl⟩
      refine ⟨⟨i.val, by omega⟩, hi, ?_⟩
      change f ⟨i.val, by omega⟩ = e i
      simp only [f, dif_pos i.isLt]
  have hK : decode e_ext (Kmask r K.card) = K := by
    ext x
    simp only [decode, mem_map, mem_filter, mem_univ, true_and, Kmask, Nat.testBit_shiftLeft]
    constructor
    · rintro ⟨i, hi, rfl⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
      have hge : ¬ i.val < r := by omega
      change f i ∈ K
      simp only [f, dif_neg hge]
      exact (eK _).property
    · intro hx
      let j : Fin K.card := eK.symm ⟨x, hx⟩
      refine ⟨⟨r + j.val, by omega⟩, ?_, ?_⟩
      · simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.add_sub_cancel_left]
        refine ⟨Nat.le_add_right r j.val, ?_⟩
        rw [show 1 <<< K.card = 2 ^ K.card by simp [Nat.shiftLeft_eq], Nat.testBit_two_pow_sub_one]
        exact decide_eq_true j.isLt
      · change f ⟨r + j.val, by omega⟩ = x
        simp only [f, dif_neg (show ¬ (r + j.val < r) by omega)]
        have hj : (⟨r + j.val - r, by omega⟩ : Fin K.card) = j := Fin.ext (by dsimp; omega)
        rw [hj]; exact congrArg Subtype.val (eK.apply_symm_apply ⟨x, hx⟩)
  refine ⟨e_ext, hlow, fun a ha => ?_⟩
  rw [decode_or, hK, hlow a ha]

-- Helper: sum of {0,1}-valued function over a Nodup list
lemma all_one_of_sum_gt {xs : List ℕ} {v : ℕ → ℤ} (hbit : ∀ i, v i = 0 ∨ v i = 1)
    (hgt : (xs.length : ℤ) - 1 < (xs.map v).sum) : ∀ a ∈ xs, v a = 1 := by
  induction xs with
  | nil => intro a ha; cases ha
  | cons x tl ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons] at hgt
    have htl_le : (tl.map v).sum ≤ (tl.length : ℤ) := by
      clear ih hgt
      induction tl with
      | nil => simp
      | cons y ys ihy =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rcases hbit y with h | h <;> omega
    have hx : v x = 1 := by rcases hbit x with h | h <;> omega
    have hgt' : (tl.length : ℤ) - 1 < (tl.map v).sum := by omega
    intro a ha
    rcases List.mem_cons.mp ha with rfl | h
    · exact hx
    · exact ih hgt' a h

lemma two_ones_of_sum_ge_two {xs : List ℕ} {v : ℕ → ℤ} (hnd : xs.Nodup)
    (hbit : ∀ i, v i = 0 ∨ v i = 1) (hge : 2 ≤ (xs.map v).sum) :
    ∃ a ∈ xs, ∃ b ∈ xs, a < b ∧ v a = 1 ∧ v b = 1 := by
  induction xs with
  | nil => simp at hge
  | cons x tl ih =>
    simp only [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons] at hge
    rcases hbit x with hx | hx
    · rw [hx, zero_add] at hge
      obtain ⟨a, ha, b, hb, hab, hva, hvb⟩ := ih hnd.2 hge
      exact ⟨a, List.mem_cons_of_mem _ ha, b, List.mem_cons_of_mem _ hb, hab, hva, hvb⟩
    · rw [hx] at hge
      have hex : ∃ y ∈ tl, v y = 1 := by
        by_contra! hall
        have hzero : (tl.map v).sum = 0 := by
          apply List.sum_eq_zero
          intro z hz
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
          rcases hbit y with h | h
          · exact h
          · exact absurd h (hall y hy)
        omega
      obtain ⟨y, hy, hvy⟩ := hex
      have hne : x ≠ y := fun heq => hnd.1 (heq ▸ hy)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact ⟨x, List.mem_cons_self .., y, List.mem_cons_of_mem _ hy, hlt, hx, hvy⟩
      · exact ⟨y, List.mem_cons_of_mem _ hy, x, List.mem_cons_self .., hgt, hvy, hx⟩

lemma filter_ones_length {xs : List ℕ} {v : ℕ → ℤ} (hbit : ∀ i, v i = 0 ∨ v i = 1) :
    ((xs.filter (fun a => decide (v a = 1))).length : ℤ) = (xs.map v).sum := by
  induction xs with
  | nil => simp
  | cons x tl ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    rcases hbit x with hx | hx
    · simp [hx, ih]
    · simp [hx, ih]; omega

-- Forbidden cut certificate type
inductive FCutCert where
  | d (xs : List ℕ) (pr : ℕ) (phi : List ℕ)
  | q (xs : List ℕ) (pws : List (ℕ × ℕ × ℕ × List ℕ))
  | t (xs : List ℕ) (t3 : ℕ) (inF : List ℕ) (pr : ℕ)
  | v (xs : List ℕ) (f5 : ℕ) (inF : List ℕ)

def FCutCert.toPair : FCutCert → List ℕ × ℤ
  | .d xs _ _ => (xs, (xs.length : ℤ) - 1)
  | .q xs _ => (xs, 1)
  | .t xs _ inF pr => (xs, (if pr == 12 then 2 else 3) - (inF.length : ℤ))
  | .v xs _ inF => (xs, 2 - (inF.length : ℤ))

def checkDirect (r k : ℕ) (FiMasks allowedPrs : List ℕ) (xs : List ℕ) (pr : ℕ) (phi : List ℕ) : Bool :=
  allowedPrs.contains pr &&
  nodupNat xs &&
  xs.all (· < 2 ^ r) &&
  phi.length == patR pr &&
  nodupNat phi &&
  phi.all (· < r + k) &&
  let km := Kmask r k
  (patGens pr).all fun g =>
    let m := mapMask phi g
    FiMasks.contains m ||
    xs.any (fun a => FiMasks.any (fun b => ((km ||| a) ||| b) == m)) ||
    xs.any (fun a => xs.any (fun a2 => ((km ||| a) ||| a2) == m))

def checkFCut (r k : ℕ) (FiMasks allowedPrs : List ℕ) : FCutCert → Bool
  | .d xs pr phi => checkDirect r k FiMasks allowedPrs xs pr phi
  | .q xs pws =>
    nodupNat xs && xs.all (· < 2 ^ r) &&
    xs.all fun a => xs.all fun b =>
      !(a < b) || pws.any fun (a', b', pr, phi) =>
        a' == a && b' == b && checkDirect r k FiMasks allowedPrs [a, b] pr phi
  | .t xs t3 inF pr =>
    (pr == 12 || pr == 8) && allowedPrs.contains pr &&
    nodupNat xs && xs.all (· < 2 ^ r) && nodupNat inF &&
    t3 < 2 ^ (r + k) && popcount (r + k) t3 == 3 &&
    let km := Kmask r k
    inF.all (fun y => FiMasks.contains y && y < 2 ^ (r + k) && popcount (r + k) y == 4 && (y &&& t3) == t3) &&
    xs.all (fun a => let x := km ||| a; popcount (r + k) x == 4 && (x &&& t3) == t3 && !inF.contains x)
  | .v xs f5 inF =>
    allowedPrs.contains 16 &&
    nodupNat xs && xs.all (· < 2 ^ r) && nodupNat inF &&
    f5 < 2 ^ (r + k) && popcount (r + k) f5 == 5 &&
    let km := Kmask r k
    inF.all (fun y => FiMasks.contains y && y < 2 ^ (r + k) && popcount (r + k) y == 4 && (y ||| f5) == f5) &&
    xs.all (fun a => let x := km ||| a; popcount (r + k) x == 4 && (x ||| f5) == f5 && !inF.contains x)

lemma checkDirect_sound {r k : ℕ} {F : Finset (Finset (Fin 12))}
    (closed : IsUnionClosed F)
    {e : Fin r ↪ Fin 12} {K : Finset (Fin 12)} (hk : K.card = k)
    {e_ext : Fin (r + k) ↪ Fin 12}
    (hlow : ∀ a < 2 ^ r, decode e_ext a = decode e a)
    (hhi : ∀ a < 2 ^ r, decode e_ext (Kmask r k ||| a) = K ∪ decode e a)
    {FiMasks allowedPrs : List ℕ}
    (hFi : ∀ b ∈ FiMasks, b < 2 ^ r ∧ decode e b ∈ F)
    (hNoPrev : ∀ pr ∈ allowedPrs, ¬ HasPattern F pr)
    {v : ℕ → ℤ} (hv : ∀ a < 2 ^ r, v a = if K ∪ decode e a ∈ F then 1 else 0)
    (hbit : ∀ i, v i = 0 ∨ v i = 1)
    {xs : List ℕ} {pr : ℕ} {phi : List ℕ}
    (hchk : checkDirect r k FiMasks allowedPrs xs pr phi = true) :
    (∀ a ∈ xs, a < 2 ^ r) ∧ (xs.map v).sum ≤ (xs.length : ℤ) - 1 := by
  simp only [checkDirect, Bool.and_eq_true, List.contains_eq_mem, List.all_eq_true,
    decide_eq_true_eq, beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨hpr, hnd_xs⟩, hxs_lt⟩, hphi_len⟩, hnd_phi⟩, hphi_lt⟩, hgens⟩ := hchk
  refine ⟨hxs_lt, ?_⟩
  by_contra! hgt
  have hall1 : ∀ a ∈ xs, v a = 1 := all_one_of_sum_gt hbit hgt
  have hmemF : ∀ a ∈ xs, K ∪ decode e a ∈ F := by
    intro a ha
    have h1 := hall1 a ha
    rw [hv a (hxs_lt a ha)] at h1
    split_ifs at h1 with h
    · exact h
    · omega
  obtain ⟨e', he'⟩ := decode_comp_emb e_ext phi hphi_len (nodupNat_sound hnd_phi) hphi_lt
  apply hNoPrev pr hpr
  refine ⟨e', fun g hg => ?_⟩
  rw [he' g]
  have hm := hgens g hg
  simp only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hm
  rcases hm with (h1 | ⟨a, ha, b, hb, hEq⟩) | ⟨a, ha, a2, ha2, hEq⟩
  · have ⟨hblt, hbF⟩ := hFi _ h1
    rw [hlow _ hblt]; exact hbF
  · rw [← hEq, decode_or, hhi a (hxs_lt a ha), hlow b (hFi b hb).1]
    exact closed _ (hmemF a ha) _ (hFi b hb).2
  · rw [← hEq, Nat.or_assoc, ← Nat.or_assoc (Kmask r k) a, show (Kmask r k ||| a) ||| a2 = (Kmask r k ||| a) ||| (Kmask r k ||| a2) by
      apply Nat.eq_of_testBit_eq; intro i; simp [Nat.testBit_or]; cases (Kmask r k).testBit i <;> cases a.testBit i <;> cases a2.testBit i <;> rfl]
    rw [decode_or, hhi a (hxs_lt a ha), hhi a2 (hxs_lt a2 ha2)]
    exact closed _ (hmemF a ha) _ (hmemF a2 ha2)

-- Helper: 3 or 4 distinct 4-sets containing a 3-set T gives HasPattern F 12 or HasPattern F 8
lemma hasPattern_shareTriple {F : Finset (Finset (Fin 12))} {T : Finset (Fin 12)} (hT : T.card = 3)
    {pr : ℕ} (hpr : pr = 12 ∨ pr = 8)
    {S : Finset (Finset (Fin 12))} (hSF : S ⊆ F)
    (hS4 : ∀ A ∈ S, A.card = 4 ∧ T ⊆ A)
    (hScard : (if pr = 12 then 3 else 4) ≤ S.card) : HasPattern F pr := by
  let ext := S.image (fun A => A \ T)
  have h1 : ∀ A ∈ S, ∃ x, A \ T = {x} ∧ x ∉ T ∧ A = insert x T := by
    intro A hA
    have ⟨hA4, hTA⟩ := hS4 A hA
    have hc : (A \ T).card = 1 := by rw [card_sdiff_of_subset hTA, hA4, hT]
    obtain ⟨x, hx⟩ := card_eq_one.mp hc
    have hxmem : x ∈ A \ T := hx ▸ mem_singleton_self x
    have hxA : x ∈ A := (mem_sdiff.mp hxmem).1
    have hxT : x ∉ T := (mem_sdiff.mp hxmem).2
    have hEq : A = insert x T := by
      ext y; constructor
      · intro hy
        by_cases hyT : y ∈ T
        · exact mem_insert_of_mem hyT
        · have : y ∈ A \ T := mem_sdiff.mpr ⟨hy, hyT⟩
          rw [hx, mem_singleton] at this; exact mem_insert.mpr (Or.inl this)
      · intro hy
        rcases mem_insert.mp hy with rfl | hyT
        · exact hxA
        · exact hTA hyT
    exact ⟨x, hx, hxT, hEq⟩
  let pick (A : Finset (Fin 12)) : Fin 12 := if h : (A \ T).Nonempty then h.choose else 0
  have hpick : ∀ A ∈ S, pick A ∉ T ∧ A = insert (pick A) T := by
    intro A hA
    obtain ⟨x, hx, hxT, hEq⟩ := h1 A hA
    have hne : (A \ T).Nonempty := ⟨x, hx ▸ mem_singleton_self x⟩
    have hch : pick A = x := by
      simp only [pick, dif_pos hne]
      exact mem_singleton.mp (hx ▸ hne.choose_spec)
    rw [hch]; exact ⟨hxT, hEq⟩
  have hinj : Set.InjOn pick (S : Set (Finset (Fin 12))) := by
    intro A hA B hB hAB
    rw [(hpick A hA).2, (hpick B hB).2, hAB]
  let X := S.image pick
  have hXcard : (if pr = 12 then 3 else 4) ≤ X.card := by
    rw [card_image_of_injOn hinj]; exact hScard
  have hXdisj : Disjoint T X := by
    rw [Finset.disjoint_right]
    intro x hx
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hx
    exact (hpick A hA).1
  have hXmem : ∀ x ∈ X, insert x T ∈ F := by
    intro x hx
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hx
    rw [← (hpick A hA).2]; exact hSF hA
  let eTeq : Fin 3 ≃ ↥T := (Fintype.equivFinOfCardEq (show Fintype.card ↥T = 3 by rw [Fintype.card_coe]; exact hT)).symm
  let eT : Fin 3 ↪ Fin 12 := ⟨fun i => (eTeq i).val, fun a b h => eTeq.injective (Subtype.ext h)⟩
  have heT : univ.map eT = T := by
    ext x; simp only [mem_map, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact (eTeq i).property
    · intro hx; exact ⟨eTeq.symm ⟨x, hx⟩, congrArg Subtype.val (eTeq.apply_symm_apply ⟨x, hx⟩)⟩
  rcases hpr with rfl | rfl
  · simp only [↓reduceIte] at hXcard
    obtain ⟨X3, hX3sub, hX3card⟩ := exists_subset_card_eq hXcard
    let eX3 : Fin 3 ≃ ↥X3 := (Fintype.equivFinOfCardEq (show Fintype.card ↥X3 = 3 by rw [Fintype.card_coe]; exact hX3card)).symm
    let f : Fin 6 → Fin 12 := fun i =>
      if h : i.val < 3 then eT ⟨i.val, h⟩ else (eX3 ⟨i.val - 3, by omega⟩).val
    have hf_inj : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      split_ifs at hab with ha hb hb
      · have hv : a.val = b.val := congrArg (Fin.val : Fin 3 → ℕ) (eT.injective hab)
        exact Fin.ext hv
      · exfalso
        have h1 : eT ⟨a.val, ha⟩ ∈ T := heT ▸ mem_map.mpr ⟨_, mem_univ _, rfl⟩
        have h2 : eT ⟨a.val, ha⟩ ∈ X := hX3sub (hab ▸ (eX3 _).property)
        exact Finset.disjoint_left.mp hXdisj h1 h2
      · exfalso
        have h1 : eT ⟨b.val, hb⟩ ∈ T := heT ▸ mem_map.mpr ⟨_, mem_univ _, rfl⟩
        have h2 : eT ⟨b.val, hb⟩ ∈ X := hX3sub (hab.symm ▸ (eX3 _).property)
        exact Finset.disjoint_left.mp hXdisj h1 h2
      · have hv : a.val - 3 = b.val - 3 := congrArg Fin.val (eX3.injective (Subtype.ext hab))
        exact Fin.ext (by omega)
    let emb : Fin 6 ↪ Fin 12 := ⟨f, hf_inj⟩
    have hdec : ∀ j : Fin 3, decode emb (7 ||| (1 <<< (3 + j.val))) = insert (eX3 j).val T := by
      intro j
      ext x
      simp only [decode, mem_map, mem_filter, mem_univ, true_and, mem_insert,
        Nat.testBit_or, Bool.or_eq_true, testBit_one_shl, decide_eq_true_eq]
      constructor
      · rintro ⟨i, hi | hi, rfl⟩
        · right
          have hlt : i.val < 3 := by
            by_contra hge
            have := Nat.testBit_lt_two_pow (lt_of_lt_of_le (show 7 < 2 ^ 3 by decide) (Nat.pow_le_pow_right (by omega) (by omega : 3 ≤ i.val)))
            rw [this] at hi; cases hi
          change f i ∈ T
          simp only [f, dif_pos hlt]
          exact heT ▸ mem_map.mpr ⟨⟨i.val, hlt⟩, mem_univ _, rfl⟩
        · left
          have hge : ¬ i.val < 3 := by omega
          change f i = (eX3 j).val
          simp only [f, dif_neg hge]
          have hj : (⟨i.val - 3, by omega⟩ : Fin 3) = j := Fin.ext (by dsimp; omega)
          rw [hj]
      · rintro (rfl | hxT)
        · refine ⟨⟨3 + j.val, by omega⟩, Or.inr rfl, ?_⟩
          change f ⟨3 + j.val, by omega⟩ = (eX3 j).val
          simp only [f, dif_neg (show ¬ (3 + j.val < 3) by omega)]
          have hj : (⟨3 + j.val - 3, by omega⟩ : Fin 3) = j := Fin.ext (by dsimp; omega)
          rw [hj]
        · rw [← heT, mem_map] at hxT
          obtain ⟨i, _, rfl⟩ := hxT
          refine ⟨⟨i.val, by omega⟩, Or.inl ?_, ?_⟩
          · change (7 : ℕ).testBit i.val = true; fin_cases i <;> rfl
          · change f ⟨i.val, by omega⟩ = eT i; simp only [f, dif_pos i.isLt]
    dsimp only [HasPattern, patR, patGens]
    refine ⟨emb, fun g hg => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · rw [show (15 : ℕ) = 7 ||| (1 <<< (3 + (0 : Fin 3).val)) by rfl, hdec]
      exact hXmem _ (hX3sub (eX3 0).property)
    · rw [show (23 : ℕ) = 7 ||| (1 <<< (3 + (1 : Fin 3).val)) by rfl, hdec]
      exact hXmem _ (hX3sub (eX3 1).property)
    · rw [show (39 : ℕ) = 7 ||| (1 <<< (3 + (2 : Fin 3).val)) by rfl, hdec]
      exact hXmem _ (hX3sub (eX3 2).property)
  · simp only [show (8 : ℕ) ≠ 12 by decide, ↓reduceIte] at hXcard
    obtain ⟨X4, hX4sub, hX4card⟩ := exists_subset_card_eq hXcard
    let eX4 : Fin 4 ≃ ↥X4 := (Fintype.equivFinOfCardEq (show Fintype.card ↥X4 = 4 by rw [Fintype.card_coe]; exact hX4card)).symm
    let f : Fin 7 → Fin 12 := fun i =>
      if h : i.val < 3 then eT ⟨i.val, h⟩ else (eX4 ⟨i.val - 3, by omega⟩).val
    have hf_inj : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      split_ifs at hab with ha hb hb
      · have hv : a.val = b.val := congrArg (Fin.val : Fin 3 → ℕ) (eT.injective hab)
        exact Fin.ext hv
      · exfalso
        have h1 : eT ⟨a.val, ha⟩ ∈ T := heT ▸ mem_map.mpr ⟨_, mem_univ _, rfl⟩
        have h2 : eT ⟨a.val, ha⟩ ∈ X := hX4sub (hab ▸ (eX4 _).property)
        exact Finset.disjoint_left.mp hXdisj h1 h2
      · exfalso
        have h1 : eT ⟨b.val, hb⟩ ∈ T := heT ▸ mem_map.mpr ⟨_, mem_univ _, rfl⟩
        have h2 : eT ⟨b.val, hb⟩ ∈ X := hX4sub (hab.symm ▸ (eX4 _).property)
        exact Finset.disjoint_left.mp hXdisj h1 h2
      · have hv : a.val - 3 = b.val - 3 := congrArg Fin.val (eX4.injective (Subtype.ext hab))
        exact Fin.ext (by omega)
    let emb : Fin 7 ↪ Fin 12 := ⟨f, hf_inj⟩
    have hdec : ∀ j : Fin 4, decode emb (7 ||| (1 <<< (3 + j.val))) = insert (eX4 j).val T := by
      intro j
      ext x
      simp only [decode, mem_map, mem_filter, mem_univ, true_and, mem_insert,
        Nat.testBit_or, Bool.or_eq_true, testBit_one_shl, decide_eq_true_eq]
      constructor
      · rintro ⟨i, hi | hi, rfl⟩
        · right
          have hlt : i.val < 3 := by
            by_contra hge
            have := Nat.testBit_lt_two_pow (lt_of_lt_of_le (show 7 < 2 ^ 3 by decide) (Nat.pow_le_pow_right (by omega) (by omega : 3 ≤ i.val)))
            rw [this] at hi; cases hi
          change f i ∈ T
          simp only [f, dif_pos hlt]
          exact heT ▸ mem_map.mpr ⟨⟨i.val, hlt⟩, mem_univ _, rfl⟩
        · left
          have hge : ¬ i.val < 3 := by omega
          change f i = (eX4 j).val
          simp only [f, dif_neg hge]
          have hj : (⟨i.val - 3, by omega⟩ : Fin 4) = j := Fin.ext (by dsimp; omega)
          rw [hj]
      · rintro (rfl | hxT)
        · refine ⟨⟨3 + j.val, by omega⟩, Or.inr rfl, ?_⟩
          change f ⟨3 + j.val, by omega⟩ = (eX4 j).val
          simp only [f, dif_neg (show ¬ (3 + j.val < 3) by omega)]
          have hj : (⟨3 + j.val - 3, by omega⟩ : Fin 4) = j := Fin.ext (by dsimp; omega)
          rw [hj]
        · rw [← heT, mem_map] at hxT
          obtain ⟨i, _, rfl⟩ := hxT
          refine ⟨⟨i.val, by omega⟩, Or.inl ?_, ?_⟩
          · change (7 : ℕ).testBit i.val = true; fin_cases i <;> rfl
          · change f ⟨i.val, by omega⟩ = eT i; simp only [f, dif_pos i.isLt]
    dsimp only [HasPattern, patR, patGens]
    refine ⟨emb, fun g hg => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · rw [show (15 : ℕ) = 7 ||| (1 <<< (3 + (0 : Fin 4).val)) by rfl, hdec]
      exact hXmem _ (hX4sub (eX4 0).property)
    · rw [show (23 : ℕ) = 7 ||| (1 <<< (3 + (1 : Fin 4).val)) by rfl, hdec]
      exact hXmem _ (hX4sub (eX4 1).property)
    · rw [show (39 : ℕ) = 7 ||| (1 <<< (3 + (2 : Fin 4).val)) by rfl, hdec]
      exact hXmem _ (hX4sub (eX4 2).property)
    · rw [show (71 : ℕ) = 7 ||| (1 <<< (3 + (3 : Fin 4).val)) by rfl, hdec]
      exact hXmem _ (hX4sub (eX4 3).property)

-- Helper: 3 distinct 4-subsets of a 5-set U gives HasPattern F 16!
lemma hasPattern_inFive {F : Finset (Finset (Fin 12))} {U : Finset (Fin 12)} (hU : U.card = 5)
    {S : Finset (Finset (Fin 12))} (hSF : S ⊆ F)
    (hS4 : ∀ A ∈ S, A.card = 4 ∧ A ⊆ U) (hScard : 3 ≤ S.card) : HasPattern F 16 := by
  let pick (A : Finset (Fin 12)) : Fin 12 := if h : (U \ A).Nonempty then h.choose else 0
  have hpick : ∀ A ∈ S, pick A ∈ U ∧ A = U.erase (pick A) := by
    intro A hA
    have ⟨hA4, hAU⟩ := hS4 A hA
    have hc : (U \ A).card = 1 := by rw [card_sdiff_of_subset hAU, hU, hA4]
    obtain ⟨x, hx⟩ := card_eq_one.mp hc
    have hne : (U \ A).Nonempty := ⟨x, hx ▸ mem_singleton_self x⟩
    have hch : pick A = x := by simp only [pick, dif_pos hne]; exact mem_singleton.mp (hx ▸ hne.choose_spec)
    have hxU : x ∈ U := (mem_sdiff.mp (hx ▸ mem_singleton_self x)).1
    have hxA : x ∉ A := (mem_sdiff.mp (hx ▸ mem_singleton_self x)).2
    have hEq : A = U.erase x := by
      ext y; simp only [mem_erase]
      constructor
      · intro hy; exact ⟨fun h => hxA (h ▸ hy), hAU hy⟩
      · rintro ⟨hne, hyU⟩
        by_contra hyA
        have : y ∈ U \ A := mem_sdiff.mpr ⟨hyU, hyA⟩
        rw [hx, mem_singleton] at this; exact hne this
    rw [hch]; exact ⟨hxU, hEq⟩
  have hinj : Set.InjOn pick (S : Set (Finset (Fin 12))) := by
    intro A hA B hB hAB; rw [(hpick A hA).2, (hpick B hB).2, hAB]
  let X := S.image pick
  have hXsub : X ⊆ U := by
    intro x hx; obtain ⟨A, hA, rfl⟩ := mem_image.mp hx; exact (hpick A hA).1
  have hXcard : 3 ≤ X.card := by rw [card_image_of_injOn hinj]; exact hScard
  obtain ⟨X3, hX3sub, hX3card⟩ := exists_subset_card_eq hXcard
  have hX3U : X3 ⊆ U := hX3sub.trans hXsub
  have hRcard : (U \ X3).card = 2 := by rw [card_sdiff_of_subset hX3U, hU, hX3card]
  let eR : Fin 2 ≃ ↥(U \ X3) := (Fintype.equivFinOfCardEq (show Fintype.card ↥(U \ X3) = 2 by rw [Fintype.card_coe]; exact hRcard)).symm
  let eX : Fin 3 ≃ ↥X3 := (Fintype.equivFinOfCardEq (show Fintype.card ↥X3 = 3 by rw [Fintype.card_coe]; exact hX3card)).symm
  let f : Fin 5 → Fin 12 := fun i =>
    if h : i.val < 2 then (eR ⟨i.val, h⟩).val else (eX ⟨i.val - 2, by omega⟩).val
  have hf_inj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    split_ifs at hab with ha hb hb
    · have hv : a.val = b.val := congrArg (Fin.val : Fin 2 → ℕ) (eR.injective (Subtype.ext hab))
      exact Fin.ext hv
    · exfalso; exact (mem_sdiff.mp (eR _).property).2 (hab ▸ (eX _).property)
    · exfalso; exact (mem_sdiff.mp (eR _).property).2 (hab.symm ▸ (eX _).property)
    · have hv : a.val - 2 = b.val - 2 := congrArg Fin.val (eX.injective (Subtype.ext hab))
      exact Fin.ext (by omega)
  let emb : Fin 5 ↪ Fin 12 := ⟨f, hf_inj⟩
  have hsurj : univ.map emb = U := by
    ext x
    simp only [mem_map, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      change f i ∈ U
      simp only [f]; split_ifs
      · exact (mem_sdiff.mp (eR _).property).1
      · exact hX3U (eX _).property
    · intro hxU
      by_cases hxX : x ∈ X3
      · let j : Fin 3 := eX.symm ⟨x, hxX⟩
        refine ⟨⟨2 + j.val, by omega⟩, ?_⟩
        change f ⟨2 + j.val, by omega⟩ = x
        simp only [f, dif_neg (show ¬ (2 + j.val < 2) by omega)]
        have hj : (⟨2 + j.val - 2, by omega⟩ : Fin 3) = j := Fin.ext (by dsimp; omega)
        rw [hj]; exact congrArg Subtype.val (eX.apply_symm_apply ⟨x, hxX⟩)
      · let j : Fin 2 := eR.symm ⟨x, mem_sdiff.mpr ⟨hxU, hxX⟩⟩
        refine ⟨⟨j.val, by omega⟩, ?_⟩
        change f ⟨j.val, by omega⟩ = x
        simp only [f, dif_pos j.isLt]
        exact congrArg Subtype.val (eR.apply_symm_apply ⟨x, mem_sdiff.mpr ⟨hxU, hxX⟩⟩)
  have hf_ge : ∀ j : Fin 3, emb ⟨2 + j.val, by omega⟩ = (eX j).val := by
    intro j
    change f ⟨2 + j.val, by omega⟩ = (eX j).val
    simp only [f, dif_neg (show ¬ (2 + j.val < 2) by omega)]
    have hj : (⟨2 + j.val - 2, by omega⟩ : Fin 3) = j := Fin.ext (by dsimp; omega)
    rw [hj]
  have hErase : ∀ j : Fin 3, decode emb (31 ^^^ (1 <<< (2 + j.val))) = U.erase (eX j).val := by
    intro j
    ext x
    simp only [decode, mem_map, mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hne : i.val ≠ 2 + j.val := by
        intro h; rw [h, Nat.testBit_xor, testBit_one_shl] at hi
        have h31 : (31 : ℕ).testBit (2 + j.val) = true := by fin_cases j <;> decide
        simp [h31] at hi
      refine ⟨?_, hsurj ▸ mem_map.mpr ⟨i, mem_univ _, rfl⟩⟩
      intro heq
      have hi' : i = ⟨2 + j.val, by omega⟩ := emb.injective (by rw [heq, hf_ge j])
      exact hne (congrArg Fin.val hi')
    · rintro ⟨hne, hxU⟩
      rw [← hsurj, mem_map] at hxU
      obtain ⟨i, _, rfl⟩ := hxU
      refine ⟨i, ?_, rfl⟩
      have hne_i : i.val ≠ 2 + j.val := by
        intro h; apply hne
        have hi' : i = ⟨2 + j.val, by omega⟩ := Fin.ext h
        rw [hi', hf_ge j]
      rw [Nat.testBit_xor, testBit_one_shl]
      have h31 : (31 : ℕ).testBit i.val = true := by fin_cases i <;> decide
      simp [h31, show (2 + j.val = i.val) ↔ False by simp [hne_i.symm]]
  have hErMem : ∀ j : Fin 3, U.erase (eX j).val ∈ F := by
    intro j
    have hxX : (eX j).val ∈ X := hX3sub (eX j).property
    obtain ⟨A, hA, hAp⟩ := mem_image.mp hxX
    rw [← hAp, ← (hpick A hA).2]; exact hSF hA
  dsimp only [HasPattern, patR, patGens]
  refine ⟨emb, fun g hg => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · rw [show (15 : ℕ) = 31 ^^^ (1 <<< (2 + (2 : Fin 3).val)) by rfl, hErase]
    exact hErMem 2
  · rw [show (23 : ℕ) = 31 ^^^ (1 <<< (2 + (1 : Fin 3).val)) by rfl, hErase]
    exact hErMem 1
  · rw [show (27 : ℕ) = 31 ^^^ (1 <<< (2 + (0 : Fin 3).val)) by rfl, hErase]
    exact hErMem 0

lemma checkFCut_sound {r k : ℕ} {F : Finset (Finset (Fin 12))}
    (closed : IsUnionClosed F)
    {e : Fin r ↪ Fin 12} {K : Finset (Fin 12)} (hk : K.card = k)
    {e_ext : Fin (r + k) ↪ Fin 12}
    (hlow : ∀ a < 2 ^ r, decode e_ext a = decode e a)
    (hhi : ∀ a < 2 ^ r, decode e_ext (Kmask r k ||| a) = K ∪ decode e a)
    {FiMasks allowedPrs : List ℕ}
    (hFi : ∀ b ∈ FiMasks, b < 2 ^ r ∧ decode e b ∈ F)
    (hNoPrev : ∀ pr ∈ allowedPrs, ¬ HasPattern F pr)
    {v : ℕ → ℤ} (hv : ∀ a < 2 ^ r, v a = if K ∪ decode e a ∈ F then 1 else 0)
    (hbit : ∀ i, v i = 0 ∨ v i = 1)
    (fc : FCutCert)
    (hchk : checkFCut r k FiMasks allowedPrs fc = true) :
    (∀ a ∈ fc.toPair.1, a < 2 ^ r) ∧ (fc.toPair.1.map v).sum ≤ fc.toPair.2 := by
  cases fc with
  | d xs pr phi =>
    exact checkDirect_sound closed hk hlow hhi hFi hNoPrev hv hbit hchk
  | q xs pws =>
    simp only [checkFCut, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not, List.any_eq_true, beq_iff_eq] at hchk
    obtain ⟨⟨hnd, hlt⟩, hpairs⟩ := hchk
    simp only [FCutCert.toPair]
    refine ⟨hlt, ?_⟩
    by_contra! hgt
    obtain ⟨a, ha, b, hb, hab, hva, hvb⟩ := two_ones_of_sum_ge_two (nodupNat_sound hnd) hbit (by omega)
    rcases hpairs a ha b hb with hnot | ⟨⟨a', b', pr, phi⟩, _, hpw⟩
    · exact hnot hab
    · dsimp only at hpw
      obtain ⟨⟨ha', hb'⟩, hdir⟩ := hpw
      have ⟨_, hle⟩ := checkDirect_sound closed hk hlow hhi hFi hNoPrev hv hbit hdir
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at hle
      omega
  | t xs t3 inF pr =>
    simp only [checkFCut, Bool.and_eq_true, Bool.or_eq_true, List.contains_eq_mem, List.all_eq_true,
      decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hchk
    obtain ⟨⟨⟨⟨⟨⟨⟨hpr, hpr_mem⟩, hnd_xs⟩, hlt_xs⟩, hnd_inF⟩, ht3_lt⟩, ht3_c⟩, ⟨hinF, hxs⟩⟩ := hchk
    simp only [FCutCert.toPair]
    refine ⟨hlt_xs, ?_⟩
    by_contra! hgt
    let xs1 := xs.filter (fun a => decide (v a = 1))
    have hxs1_len : (xs1.length : ℤ) = (xs.map v).sum := filter_ones_length hbit
    have hxs1_nd : xs1.Nodup := (nodupNat_sound hnd_xs).filter _
    let ms1 := xs1.map (fun a => Kmask r k ||| a)
    have hKmask_lt : ∀ a < 2 ^ r, Kmask r k ||| a < 2 ^ (r + k) := by
      intro a ha
      apply lor_lt_two_pow
      · simp only [Kmask, Nat.shiftLeft_eq, one_mul]
        have : (2 ^ k - 1) * 2 ^ r < 2 ^ k * 2 ^ r := Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (Nat.two_pow_pos k) (by omega)) (Nat.two_pow_pos r)
        rw [pow_add, Nat.mul_comm (2 ^ r)]; exact this
      · exact lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (Nat.le_add_right r k))
    have hms1_inj : ∀ a < 2 ^ r, ∀ b < 2 ^ r, (Kmask r k ||| a) = (Kmask r k ||| b) → a = b := by
      intro a ha b hb heq
      apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < r
      · have h := congrArg (fun n => n.testBit i) heq
        simp only [Nat.testBit_or, Kmask, Nat.testBit_shiftLeft, show ¬ (r ≤ i) by omega, decide_false, Bool.false_and, Bool.false_or] at h
        exact h
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega : r ≤ i))),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega : r ≤ i)))]
    have hms1_nd : ms1.Nodup := by
      rw [List.nodup_map_iff_inj_on hxs1_nd]
      intro a ha b hb heq
      exact hms1_inj a (hlt_xs a (List.mem_of_mem_filter ha)) b (hlt_xs b (List.mem_of_mem_filter hb)) heq
    let allM := inF ++ ms1
    have hallM_nd : allM.Nodup := by
      rw [List.nodup_append]
      refine ⟨nodupNat_sound hnd_inF, hms1_nd, ?_⟩
      intro y hy z hz heq
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      have hxa := (hxs a (List.mem_of_mem_filter ha)).2
      exact hxa (heq ▸ hy)
    let S := allM.toFinset.image (decode e_ext)
    have hallM_lt : ∀ m ∈ allM, m < 2 ^ (r + k) := by
      intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · exact (hinF m hm).1.1.2
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
        exact hKmask_lt a (hlt_xs a (List.mem_of_mem_filter ha))
    have hScard : S.card = allM.length := by
      rw [card_image_of_injOn, List.toFinset_card_of_nodup hallM_nd]
      intro m₁ hm₁ m₂ hm₂ heq
      exact decode_inj e_ext (hallM_lt m₁ (List.mem_toFinset.mp hm₁)) (hallM_lt m₂ (List.mem_toFinset.mp hm₂)) heq
    have hSF : S ⊆ F := by
      intro A hA
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hA
      rcases List.mem_append.mp (List.mem_toFinset.mp hm) with hm | hm
      · have hFi_m := hFi m (hinF m hm).1.1.1
        rw [hlow m hFi_m.1]; exact hFi_m.2
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
        have ha_xs : a ∈ xs := List.mem_of_mem_filter ha
        have hv1 : v a = 1 := of_decide_eq_true (List.mem_filter.mp ha).2
        rw [hhi a (hlt_xs a ha_xs)]
        rw [hv a (hlt_xs a ha_xs)] at hv1
        split_ifs at hv1 with h; exact h; omega
    have hS4 : ∀ A ∈ S, A.card = 4 ∧ decode e_ext t3 ⊆ A := by
      intro A hA
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hA
      rcases List.mem_append.mp (List.mem_toFinset.mp hm) with hm | hm
      · have h := hinF m hm
        exact ⟨by rw [decode_card, h.1.2], decode_subset_of_and e_ext h.2⟩
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
        have h := hxs a (List.mem_of_mem_filter ha)
        exact ⟨by rw [decode_card, h.1.1], decode_subset_of_and e_ext h.1.2⟩
    have hScard_ge : (if pr = 12 then 3 else 4) ≤ S.card := by
      rw [hScard, List.length_append, List.length_map]
      rcases hpr with rfl | rfl <;> simp at hgt ⊢ <;> omega
    exact hNoPrev pr hpr_mem (hasPattern_shareTriple (by rw [decode_card, ht3_c]) hpr hSF hS4 hScard_ge)
  | v xs f5 inF =>
    simp only [checkFCut, Bool.and_eq_true, List.contains_eq_mem, List.all_eq_true,
      decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hchk
    obtain ⟨⟨⟨⟨⟨⟨h16, hnd_xs⟩, hlt_xs⟩, hnd_inF⟩, hf5_lt⟩, hf5_c⟩, ⟨hinF, hxs⟩⟩ := hchk
    simp only [FCutCert.toPair]
    refine ⟨hlt_xs, ?_⟩
    by_contra! hgt
    let xs1 := xs.filter (fun a => decide (v a = 1))
    have hxs1_len : (xs1.length : ℤ) = (xs.map v).sum := filter_ones_length hbit
    have hxs1_nd : xs1.Nodup := (nodupNat_sound hnd_xs).filter _
    let ms1 := xs1.map (fun a => Kmask r k ||| a)
    have hKmask_lt : ∀ a < 2 ^ r, Kmask r k ||| a < 2 ^ (r + k) := by
      intro a ha
      apply lor_lt_two_pow
      · simp only [Kmask, Nat.shiftLeft_eq, one_mul]
        have : (2 ^ k - 1) * 2 ^ r < 2 ^ k * 2 ^ r := Nat.mul_lt_mul_of_pos_right (Nat.sub_lt (Nat.two_pow_pos k) (by omega)) (Nat.two_pow_pos r)
        rw [pow_add, Nat.mul_comm (2 ^ r)]; exact this
      · exact lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (Nat.le_add_right r k))
    have hms1_inj : ∀ a < 2 ^ r, ∀ b < 2 ^ r, (Kmask r k ||| a) = (Kmask r k ||| b) → a = b := by
      intro a ha b hb heq
      apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < r
      · have h := congrArg (fun n => n.testBit i) heq
        simp only [Nat.testBit_or, Kmask, Nat.testBit_shiftLeft, show ¬ (r ≤ i) by omega, decide_false, Bool.false_and, Bool.false_or] at h
        exact h
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega : r ≤ i))),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by omega : r ≤ i)))]
    have hms1_nd : ms1.Nodup := by
      rw [List.nodup_map_iff_inj_on hxs1_nd]
      intro a ha b hb heq
      exact hms1_inj a (hlt_xs a (List.mem_of_mem_filter ha)) b (hlt_xs b (List.mem_of_mem_filter hb)) heq
    let allM := inF ++ ms1
    have hallM_nd : allM.Nodup := by
      rw [List.nodup_append]
      refine ⟨nodupNat_sound hnd_inF, hms1_nd, ?_⟩
      intro y hy z hz heq
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
      exact (hxs a (List.mem_of_mem_filter ha)).2 (heq ▸ hy)
    let S := allM.toFinset.image (decode e_ext)
    have hallM_lt : ∀ m ∈ allM, m < 2 ^ (r + k) := by
      intro m hm
      rcases List.mem_append.mp hm with hm | hm
      · exact (hinF m hm).1.1.2
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
        exact hKmask_lt a (hlt_xs a (List.mem_of_mem_filter ha))
    have hScard : S.card = allM.length := by
      rw [card_image_of_injOn, List.toFinset_card_of_nodup hallM_nd]
      intro m₁ hm₁ m₂ hm₂ heq
      exact decode_inj e_ext (hallM_lt m₁ (List.mem_toFinset.mp hm₁)) (hallM_lt m₂ (List.mem_toFinset.mp hm₂)) heq
    have hSF : S ⊆ F := by
      intro A hA
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hA
      rcases List.mem_append.mp (List.mem_toFinset.mp hm) with hm | hm
      · have hFi_m := hFi m (hinF m hm).1.1.1
        rw [hlow m hFi_m.1]; exact hFi_m.2
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
        have ha_xs : a ∈ xs := List.mem_of_mem_filter ha
        have hv1 : v a = 1 := of_decide_eq_true (List.mem_filter.mp ha).2
        rw [hhi a (hlt_xs a ha_xs)]
        rw [hv a (hlt_xs a ha_xs)] at hv1
        split_ifs at hv1 with h; exact h; omega
    have hS4 : ∀ A ∈ S, A.card = 4 ∧ A ⊆ decode e_ext f5 := by
      intro A hA
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hA
      rcases List.mem_append.mp (List.mem_toFinset.mp hm) with hm | hm
      · have h := hinF m hm
        exact ⟨by rw [decode_card, h.1.2], decode_subset_of_or e_ext h.2⟩
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
        have h := hxs a (List.mem_of_mem_filter ha)
        exact ⟨by rw [decode_card, h.1.1], decode_subset_of_or e_ext h.1.2⟩
    have hScard_ge : 3 ≤ S.card := by
      rw [hScard, List.length_append, List.length_map]
      omega
    exact hNoPrev 16 h16 (hasPattern_inFive (by rw [decode_card, hf5_c]) hSF hS4 hScard_ge)

-- ============================================================================
-- Section 4: Generalized Weighted Fiber Assembly
-- ============================================================================

def maskWeight (r : ℕ) (w : Fin r → ℕ) (m : ℕ) : ℕ :=
  ∑ i : Fin r, if m.testBit i.val then w i else 0

def maskWeightFast : List ℕ → ℕ → ℕ
  | [], _ => 0
  | w0 :: ws, m => (if m % 2 = 1 then w0 else 0) + maskWeightFast ws (m / 2)

lemma maskWeight_eq_fast (ws : List ℕ) (m : ℕ) :
    maskWeight ws.length (fun i => ws[i]) m = maskWeightFast ws m := by
  induction ws generalizing m with
  | nil => simp [maskWeight, maskWeightFast]
  | cons w0 tl ih =>
    simp only [List.length_cons, maskWeight, maskWeightFast]
    rw [Fin.sum_univ_succ]
    have h0 : m.testBit 0 = decide (m % 2 = 1) := Nat.testBit_zero m
    have hhead : (if m.testBit (0 : Fin (tl.length + 1)).val = true then (w0 :: tl)[(0 : Fin (tl.length + 1))] else 0) =
        if m % 2 = 1 then w0 else 0 := by
      change (if m.testBit 0 = true then w0 else 0) = _
      rw [h0]; by_cases hm : m % 2 = 1 <;> simp [hm]
    rw [hhead, ← ih (m / 2), maskWeight]
    congr 1
    apply sum_congr rfl
    intro i _
    have hbit : m.testBit (i.succ).val = (m / 2).testBit i.val := by
      rw [Fin.val_succ, Nat.testBit_succ, Nat.testBit_div_two]
    rw [hbit]
    simp [List.getElem_cons_succ]

def encodeBits : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | r + 1, P => (if P 0 then 1 else 0) + 2 * encodeBits r (fun i => P (i + 1))

lemma encodeBits_lt (r : ℕ) (P : ℕ → Bool) : encodeBits r P < 2 ^ r := by
  induction r generalizing P with
  | zero => simp [encodeBits]
  | succ r ih =>
    simp only [encodeBits, pow_succ']
    have h := ih (fun i => P (i + 1))
    cases P 0 <;> simp <;> omega

lemma testBit_encodeBits (r : ℕ) (P : ℕ → Bool) (i : ℕ) :
    (encodeBits r P).testBit i = (decide (i < r) && P i) := by
  induction r generalizing P i with
  | zero => simp [encodeBits]
  | succ r ih =>
    cases i with
    | zero =>
      simp only [encodeBits, Nat.testBit_zero]
      cases P 0 <;> simp
    | succ j =>
      simp only [encodeBits, Nat.testBit_succ]
      have hdiv : ((if P 0 then 1 else 0) + 2 * encodeBits r (fun i => P (i + 1))) / 2 =
          encodeBits r (fun i => P (i + 1)) := by cases P 0 <;> simp <;> omega
      rw [hdiv, ih]
      simp [Nat.succ_lt_succ_iff]

lemma exists_mask_of_subset {r : ℕ} (e : Fin r ↪ Fin 12) (X : Finset (Fin 12)) :
    ∃ m < 2 ^ r, decode e m = X ∩ univ.map e := by
  let P (i : ℕ) : Bool := if h : i < r then decide (e ⟨i, h⟩ ∈ X) else false
  refine ⟨encodeBits r P, encodeBits_lt r P, ?_⟩
  ext x
  simp only [decode, mem_map, mem_filter, mem_univ, true_and, mem_inter, testBit_encodeBits,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨i, ⟨hi, hPi⟩, rfl⟩
    simp only [P, dif_pos i.isLt, decide_eq_true_eq] at hPi
    exact ⟨hPi, i, rfl⟩
  · rintro ⟨hxX, i, rfl⟩
    refine ⟨i, ⟨i.isLt, ?_⟩, rfl⟩
    simp [P, i.isLt, hxX]

lemma maskWeight_eq_sum {r : ℕ} (e : Fin r ↪ Fin 12) (w : Fin r → ℕ) (d : ℕ) (m : ℕ) :
    ∑ x ∈ decode e m, (if hx : ∃ i : Fin r, e i = x then w hx.choose else d) = maskWeight r w m := by
  rw [decode, sum_map, maskWeight, ← sum_filter]
  apply sum_congr rfl
  intro i _
  have hex : ∃ j : Fin r, e j = e i := ⟨i, rfl⟩
  rw [dif_pos hex]
  have hch : hex.choose = i := e.injective hex.choose_spec
  rw [hch]

lemma weight_from_fibers {r : ℕ} (hr : r < 12) (F : Finset (Finset (Fin 12))) (e : Fin r ↪ Fin 12)
    (full : univ ∈ F)
    (w : Fin r → ℕ) (d t : ℕ) (pd : 0 < d)
    (balance : (∑ i : Fin r, w i) + d * (12 - r) = 2 * t)
    (c : ℤ) (pc : 0 ≤ c)
    (bound : ∀ K ⊆ univ \ (univ.map e),
      (∃ a < 2 ^ r, K ∪ decode e a ∈ F) →
      (if K = univ \ (univ.map e) then c else 0) - (if K = ∅ then c else 0) ≤
        ∑ a ∈ Finset.range (2 ^ r),
          ((maskWeight r w a : ℤ) + (d : ℤ) * (K.card : ℤ) - (t : ℤ)) *
            (if K ∪ decode e a ∈ F then (1 : ℤ) else 0)) :
    ∃ W : Fin 12 → ℕ, 0 < ∑ i, W i ∧ F.card * (∑ i, W i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, W i) := by
  let B := (univ : Finset (Fin r)).map e
  let W : Fin 12 → ℕ := fun x => if hx : ∃ i : Fin r, e i = x then w hx.choose else d
  have hsumW : ∑ x : Fin 12, W x = 2 * t := by
    have hsplit : (univ : Finset (Fin 12)) = B ∪ (univ \ B) := by ext x; simp
    have hdisj : Disjoint B (univ \ B) := disjoint_sdiff
    rw [hsplit, sum_union hdisj]
    have hB : ∑ x ∈ B, W x = ∑ i : Fin r, w i := by
      rw [sum_map]
      apply sum_congr rfl
      intro i _
      have hex : ∃ j : Fin r, e j = e i := ⟨i, rfl⟩
      simp only [W, dif_pos hex]
      rw [e.injective hex.choose_spec]
    have hO : ∑ x ∈ univ \ B, W x = d * (12 - r) := by
      have hconst : ∀ x ∈ univ \ B, W x = d := by
        intro x hx
        have hnot : ¬ ∃ i : Fin r, e i = x := by
          rintro ⟨i, rfl⟩; exact (mem_sdiff.mp hx).2 (mem_map.mpr ⟨i, mem_univ _, rfl⟩)
        simp [W, hnot]
      rw [sum_congr rfl hconst, sum_const, smul_eq_mul, card_sdiff_of_subset (subset_univ _),
          card_univ, Fintype.card_fin, card_map, card_univ, Fintype.card_fin, Nat.mul_comm]
    rw [hB, hO, balance]
  have hpos : 0 < ∑ x : Fin 12, W x := by
    rw [hsumW]
    have : 0 < d * (12 - r) := Nat.mul_pos pd (by omega)
    omega
  refine ⟨W, hpos, ?_⟩
  -- Prove 0 ≤ ∑ X ∈ F, ((∑ i ∈ X, W i : ℤ) - t)
  suffices htot : (0 : ℤ) ≤ ∑ X ∈ F, ((∑ i ∈ X, W i : ℕ) - (t : ℤ)) by
    rw [hsumW]
    have h1 : (0 : ℤ) ≤ (∑ X ∈ F, ((∑ i ∈ X, W i : ℕ) : ℤ)) - (F.card : ℤ) * (t : ℤ) := by
      simpa [sum_sub_distrib, sum_const, nsmul_eq_mul] using htot
    have h2 : (F.card : ℤ) * (2 * (t : ℤ)) ≤ 2 * (∑ X ∈ F, ((∑ i ∈ X, W i : ℕ) : ℤ)) := by linarith
    have hcast : ((F.card * (2 * t) : ℕ) : ℤ) ≤ ((2 * ∑ X ∈ F, ∑ i ∈ X, W i : ℕ) : ℤ) := by
      simpa [Nat.cast_sum, Nat.cast_mul] using h2
    exact_mod_cast hcast
  -- Partition F by K = X \ B ∈ powerset (univ \ B)
  have hmaps : ∀ X ∈ F, X \ B ∈ (univ \ B).powerset := fun X _ =>
    mem_powerset.mpr (sdiff_subset_sdiff (subset_univ X) (Subset.refl B))
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hoff : (0 : ℤ) = ∑ K ∈ (univ \ B).powerset,
      ((if K = univ \ B then c else 0) - (if K = ∅ then c else 0)) := by
    have h1 : univ \ B ∈ (univ \ B).powerset := mem_powerset.mpr (Subset.refl _)
    have h2 : ∅ ∈ (univ \ B).powerset := mem_powerset.mpr (empty_subset _)
    simp [sum_sub_distrib, h1, h2]
  rw [hoff]
  apply sum_le_sum
  intro K hK
  have hKsub : K ⊆ univ \ B := mem_powerset.mp hK
  have hKdisj : Disjoint K B := disjoint_sdiff_self_left.mono_left hKsub
  -- Rewrite fiber sum over Finset.range (2^r) via decode e!
  have hfib : ∑ X ∈ F.filter (fun X => X \ B = K), (((∑ i ∈ X, W i : ℕ) : ℤ) - (t : ℤ)) =
      ∑ a ∈ Finset.range (2 ^ r),
        ((maskWeight r w a : ℤ) + (d : ℤ) * (K.card : ℤ) - (t : ℤ)) *
          (if K ∪ decode e a ∈ F then (1 : ℤ) else 0) := by
    let phi (a : ℕ) : Finset (Fin 12) := K ∪ decode e a
    have hphi_sdiff : ∀ a, phi a \ B = K := by
      intro a
      have hdecB : decode e a ⊆ B := by
        intro x hx; obtain ⟨i, _, rfl⟩ := mem_map.mp hx; exact mem_map.mpr ⟨i, mem_univ _, rfl⟩
      ext x; simp only [phi, mem_sdiff, mem_union]
      constructor
      · rintro ⟨hxK | hxD, hxB⟩
        · exact hxK
        · exact absurd (hdecB hxD) hxB
      · intro hxK; exact ⟨Or.inl hxK, Finset.disjoint_left.mp hKdisj hxK⟩
    have hphi_inter : ∀ a, phi a ∩ B = decode e a := by
      intro a
      have hdecB : decode e a ⊆ B := by
        intro x hx; obtain ⟨i, _, rfl⟩ := mem_map.mp hx; exact mem_map.mpr ⟨i, mem_univ _, rfl⟩
      ext x; simp only [phi, mem_inter, mem_union]
      constructor
      · rintro ⟨hxK | hxD, hxB⟩
        · exact absurd hxB (Finset.disjoint_left.mp hKdisj hxK)
        · exact hxD
      · intro hxD; exact ⟨Or.inr hxD, hdecB hxD⟩
    have hWphi : ∀ a, ∑ i ∈ phi a, W i = maskWeight r w a + d * K.card := by
      intro a
      have hdisj_a : Disjoint K (decode e a) := by
        have hdecB : decode e a ⊆ B := by
          intro x hx; obtain ⟨i, _, rfl⟩ := mem_map.mp hx; exact mem_map.mpr ⟨i, mem_univ _, rfl⟩
        exact hKdisj.mono_right hdecB
      rw [sum_union hdisj_a, maskWeight_eq_sum e w d a]
      have hKW : ∑ i ∈ K, W i = d * K.card := by
        have hc : ∀ x ∈ K, W x = d := by
          intro x hx
          have hnot : ¬ ∃ i : Fin r, e i = x := by
            rintro ⟨i, rfl⟩; exact Finset.disjoint_left.mp hKdisj hx (mem_map.mpr ⟨i, mem_univ _, rfl⟩)
          simp [W, hnot]
        rw [sum_congr rfl hc, sum_const, smul_eq_mul, Nat.mul_comm]
      rw [hKW, Nat.add_comm]
    -- Bijection between (Finset.range (2^r)).filter (phi · ∈ F) and F.filter (· \ B = K)
    rw [show (∑ a ∈ Finset.range (2 ^ r),
        ((maskWeight r w a : ℤ) + (d : ℤ) * (K.card : ℤ) - (t : ℤ)) *
          (if phi a ∈ F then (1 : ℤ) else 0)) =
      ∑ a ∈ (Finset.range (2 ^ r)).filter (fun a => phi a ∈ F),
        ((maskWeight r w a : ℤ) + (d : ℤ) * (K.card : ℤ) - (t : ℤ)) by
      rw [sum_filter]; apply sum_congr rfl; intro a _; split_ifs <;> ring]
    symm
    apply Finset.sum_bij (fun a _ => phi a)
    · intro a ha
      rw [mem_filter] at ha ⊢
      exact ⟨ha.2, hphi_sdiff a⟩
    · intro a₁ ha₁ a₂ ha₂ heq
      have h1 : decode e a₁ = decode e a₂ := by
        rw [← hphi_inter a₁, ← hphi_inter a₂, heq]
      exact decode_inj e (mem_range.mp (mem_filter.mp ha₁).1) (mem_range.mp (mem_filter.mp ha₂).1) h1
    · intro X hX
      rw [mem_filter] at hX
      obtain ⟨m, hm_lt, hm_eq⟩ := exists_mask_of_subset e X
      have hphi_m : phi m = X := by
        simp only [phi, hm_eq, ← hX.2]
        ext x; simp only [mem_union, mem_inter, mem_sdiff]
        by_cases hx : x ∈ B <;> simp [B, hx]
      exact ⟨m, mem_filter.mpr ⟨mem_range.mpr hm_lt, hphi_m.symm ▸ hX.1⟩, hphi_m⟩
    · intro a _
      rw [hWphi a]; push_cast; rfl
  rw [hfib]
  by_cases hne : ∃ a < 2 ^ r, K ∪ decode e a ∈ F
  · exact bound K hKsub hne
  · push_neg at hne
    have hK_ne_top : K ≠ univ \ B := by
      intro htop
      have hfull : K ∪ decode e (2 ^ r - 1) = univ := by
        rw [htop, decode_all_ones]; ext x; simp [B]
      exact hne (2 ^ r - 1) (Nat.sub_lt (Nat.two_pow_pos r) (by omega)) (hfull ▸ full)
    have hsum0 : ∑ a ∈ Finset.range (2 ^ r),
        ((maskWeight r w a : ℤ) + (d : ℤ) * (K.card : ℤ) - (t : ℤ)) *
          (if K ∪ decode e a ∈ F then (1 : ℤ) else 0) = 0 := by
      apply sum_eq_zero; intro a ha
      rw [if_neg (hne a (mem_range.mp ha)), mul_zero]
    rw [hsum0, if_neg hK_ne_top]; split_ifs <;> omega

-- Master layer verification lemma: turns two `decide +kernel` checks into the fiber lower bound!
def checkLayer {r cd : ℕ} (k : ℕ) (objTree : VTree r) (target : ℤ)
    (genMasks FiMasks allowedPrs : List ℕ) (fcuts : List FCutCert) (tree : BnbTree) : Bool :=
  fcuts.all (checkFCut r k FiMasks allowedPrs) &&
  checkTree r k objTree target genMasks FiMasks (CTree.ofList cd (fcuts.map FCutCert.toPair)) [] [] tree

lemma checkLayer_sound {cd : ℕ} (k : ℕ) {F : Finset (Finset (Fin 12))}
    (closed : IsUnionClosed F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    {ws : List ℕ}
    {e : Fin ws.length ↪ Fin 12} {K : Finset (Fin 12)}
    (hKsub : K ⊆ univ \ (univ.map e)) (hk : K.card = k)
    (hne : ∃ a < 2 ^ ws.length, K ∪ decode e a ∈ F)
    {d t : ℕ} {target : ℤ}
    {genMasks FiMasks allowedPrs : List ℕ}
    (hGens : ∀ g ∈ genMasks, g < 2 ^ ws.length ∧ decode e g ∈ F)
    (hFi : ∀ b ∈ FiMasks, b < 2 ^ ws.length ∧ decode e b ∈ F)
    (hTopMem : 2 ^ ws.length - 1 ∈ FiMasks)
    (hNoPrev : ∀ pr ∈ allowedPrs, ¬ HasPattern F pr)
    (fcuts : List FCutCert) (tree : BnbTree)
    (hchk : checkLayer (cd := cd) k
      (VTree.ofFun ws.length (fun a => (maskWeightFast ws a : ℤ) + (d : ℤ) * (k : ℤ) - (t : ℤ)))
      target genMasks FiMasks allowedPrs fcuts tree = true) :
    target ≤ ∑ a ∈ Finset.range (2 ^ ws.length),
      ((maskWeight ws.length (fun i => ws[i.val]'i.isLt) a : ℤ) + (d : ℤ) * (K.card : ℤ) - (t : ℤ)) *
        (if K ∪ decode e a ∈ F then (1 : ℤ) else 0) := by
  subst hk
  have hmw : ∀ a, maskWeight ws.length (fun i => ws[i.val]'i.isLt) a = maskWeightFast ws a :=
    fun a => maskWeight_eq_fast ws a
  simp_rw [hmw]
  simp only [checkLayer, Bool.and_eq_true, List.all_eq_true] at hchk
  obtain ⟨hfc_all, htree_ok⟩ := hchk
  have hdisj : Disjoint (univ.map e) K := disjoint_sdiff_self_right.mono_right hKsub
  obtain ⟨e_ext, hlow, hhi⟩ := extEmb e K hdisj
  let v : ℕ → ℤ := fun a => if K ∪ decode e a ∈ F then 1 else 0
  have hbit : ∀ i, v i = 0 ∨ v i = 1 := fun i => by simp only [v]; split_ifs <;> simp
  have hjoin : ∀ a < 2 ^ ws.length, ∀ b < 2 ^ ws.length, v a + v b - v (a ||| b) ≤ 1 := by
    intro a _ b _
    simp only [v]
    split_ifs with ha hb hab hab hab hab
    · omega
    · exfalso; apply hab
      have hEq : K ∪ decode e (a ||| b) = (K ∪ decode e a) ∪ (K ∪ decode e b) := by
        rw [decode_or]; ext x; simp; tauto
      rw [hEq]; exact closed _ ha _ hb
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have hforce : ∀ a < 2 ^ ws.length, ∀ g ∈ genMasks, g < 2 ^ ws.length ∧ v a - v (a ||| g) ≤ 0 := by
    intro a _ g hg
    obtain ⟨hglt, hgF⟩ := hGens g hg
    refine ⟨hglt, ?_⟩
    simp only [v]
    split_ifs with ha hag hag
    · omega
    · exfalso; apply hag
      have hEq : K ∪ decode e (a ||| g) = (K ∪ decode e a) ∪ decode e g := by
        rw [decode_or, union_assoc]
      rw [hEq]; exact closed _ ha _ hgF
    · omega
    · omega
  have hsmall : ∀ a < 2 ^ ws.length, isSmall ws.length K.card a = true → v a ≤ 0 := by
    intro a ha hsm
    simp only [isSmall, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      beq_eq_false_iff_ne, decide_eq_true_eq] at hsm
    obtain ⟨hn0, hcard_lt⟩ := hsm
    simp only [v]
    split_ifs with hmem
    · exfalso
      have hdisj_a : Disjoint K (decode e a) := by
        have hdecB : decode e a ⊆ univ.map e := by
          intro x hx; obtain ⟨i, _, rfl⟩ := mem_map.mp hx; exact mem_map.mpr ⟨i, mem_univ _, rfl⟩
        exact hdisj.symm.mono_right hdecB
      have hcard_eq : (K ∪ decode e a).card = K.card + popcount ws.length a := by
        rw [card_union_of_disjoint hdisj_a, decode_card]
      have hne_set : (K ∪ decode e a).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        rw [union_eq_empty] at hemp
        rcases hn0 with hK0 | ha0
        · exact hK0 (by rw [hemp.1, card_empty])
        · have : decode e a = decode e 0 := by rw [hemp.2, decode_zero]
          exact ha0 (decode_inj e ha (Nat.two_pow_pos ws.length) this)
      have hge4 := minSize _ hmem hne_set
      omega
    · omega
  have hfixed : ∀ a < 2 ^ ws.length, isFixed ws.length K.card FiMasks a = true → -v a ≤ -1 := by
    intro a _ hfx
    simp only [isFixed] at hfx
    by_cases hK0 : K.card = 0
    · simp only [hK0, beq_self_eq_true, ↓reduceIte, List.contains_eq_mem, decide_eq_true_eq] at hfx
      have hKe : K = ∅ := card_eq_zero.mp hK0
      have hmem : K ∪ decode e a ∈ F := by rw [hKe, empty_union]; exact (hFi a hfx).2
      simp [v, hmem]
    · simp only [beq_iff_eq, hK0, ↓reduceIte] at hfx
      subst hfx
      obtain ⟨a0, ha0lt, ha0F⟩ := hne
      have htopF : decode e (2 ^ ws.length - 1) ∈ F := (hFi _ hTopMem).2
      have hEq : K ∪ decode e (2 ^ ws.length - 1) = (K ∪ decode e a0) ∪ decode e (2 ^ ws.length - 1) := by
        rw [union_assoc]
        congr 1
        rw [decode_all_ones]
        have hsub : decode e a0 ⊆ univ.map e := by
          intro x hx; obtain ⟨i, _, rfl⟩ := mem_map.mp hx; exact mem_map.mpr ⟨i, mem_univ _, rfl⟩
        exact (union_eq_right.mpr hsub).symm
      have hmem : K ∪ decode e (2 ^ ws.length - 1) ∈ F := hEq ▸ closed _ ha0F _ htopF
      simp [v, hmem]
  have hfmap : ∀ idx p, (CTree.ofList cd (fcuts.map FCutCert.toPair)).get? idx = some p →
      (∀ a ∈ p.1, a < 2 ^ ws.length) ∧ (p.1.map v).sum ≤ p.2 := by
    apply CTree.ofList_preserves
    intro p hp
    obtain ⟨fc, hfc_mem, rfl⟩ := List.mem_map.mp hp
    exact checkFCut_sound closed rfl hlow hhi hFi hNoPrev (fun a _ => rfl) hbit fc (hfc_all fc hfc_mem)
  have hres := checkTree_sound hbit hjoin hforce hsmall hfixed hfmap [] [] tree
    (by intro _ h; cases h) (by intro _ h; cases h) htree_ok
  rw [VTree.dot_ofFun] at hres
  exact hres

-- Closure checker: verifies FiMasks is generated from 0 and patGens by union-closure!
def checkClosureAux (r : ℕ) (gens : List ℕ) : List ℕ → List ℕ → Bool
  | _, [] => true
  | seen, b :: rest =>
    (b < 2 ^ r) &&
    (b == 0 || gens.contains b ||
      seen.any (fun x => seen.any (fun y => (x ||| y) == b))) &&
    checkClosureAux r gens (b :: seen) rest

lemma checkClosureAux_sound {r : ℕ} {F : Finset (Finset (Fin 12))}
    (closed : IsUnionClosed F) (empty : ∅ ∈ F)
    {e : Fin r ↪ Fin 12} {gens : List ℕ}
    (hGens : ∀ g ∈ gens, decode e g ∈ F)
    (seen rest : List ℕ)
    (hseen : ∀ x ∈ seen, x < 2 ^ r ∧ decode e x ∈ F)
    (hchk : checkClosureAux r gens seen rest = true) :
    ∀ b ∈ rest, b < 2 ^ r ∧ decode e b ∈ F := by
  induction rest generalizing seen with
  | nil => intro b hb; cases hb
  | cons b tl ih =>
    simp only [checkClosureAux, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      beq_iff_eq, List.contains_eq_mem, List.any_eq_true] at hchk
    obtain ⟨⟨hlt, hgen⟩, hrest⟩ := hchk
    have hbF : decode e b ∈ F := by
      rcases hgen with (rfl | hgm) | ⟨x, hx, y, hy, rfl⟩
      · rw [decode_zero]; exact empty
      · exact hGens b hgm
      · rw [decode_or]; exact closed _ (hseen x hx).2 _ (hseen y hy).2
    have hseen' : ∀ x ∈ b :: seen, x < 2 ^ r ∧ decode e x ∈ F := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hlt, hbF⟩
      · exact hseen x hx
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨hlt, hbF⟩
    · exact ih (b :: seen) hseen' hrest z hz

lemma hasPattern_32_of_exists_four {F : Finset (Finset (Fin 12))}
    (h4 : ∃ S ∈ F, S.card = 4) : HasPattern F 32 := by
  obtain ⟨S, hSF, hScard⟩ := h4
  let eSeq : Fin 4 ≃ ↥S := (Fintype.equivFinOfCardEq (show Fintype.card ↥S = 4 by rw [Fintype.card_coe]; exact hScard)).symm
  let e : Fin 4 ↪ Fin 12 := ⟨fun i => (eSeq i).val, fun a b h => eSeq.injective (Subtype.ext h)⟩
  have hdec : decode e 15 = S := by
    rw [show (15 : ℕ) = 2 ^ 4 - 1 by rfl, decode_all_ones]
    ext x; simp only [mem_map, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact (eSeq i).property
    · intro hx; exact ⟨eSeq.symm ⟨x, hx⟩, congrArg Subtype.val (eSeq.apply_symm_apply ⟨x, hx⟩)⟩
  dsimp only [HasPattern, patR, patGens]
  refine ⟨e, fun g hg => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  subst hg; rw [hdec]; exact hSF

-- Helper for K.card bounds
lemma K_card_le {r : ℕ} (e : Fin r ↪ Fin 12) {K : Finset (Fin 12)}
    (hKsub : K ⊆ univ \ (univ.map e)) : K.card ≤ 12 - r := by
  have hcap : (univ \ (univ.map e)).card = 12 - r := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, card_map, card_univ, Fintype.card_fin]
  exact (card_le_card hKsub).trans_eq hcap

lemma K_eq_top_iff {r : ℕ} (e : Fin r ↪ Fin 12) {K : Finset (Fin 12)}
    (hKsub : K ⊆ univ \ (univ.map e)) : K = univ \ (univ.map e) ↔ K.card = 12 - r := by
  have hcap : (univ \ (univ.map e)).card = 12 - r := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, card_map, card_univ, Fintype.card_fin]
  constructor
  · intro h; rw [h, hcap]
  · intro h; exact eq_of_subset_of_card_le hKsub (by omega)

-- Compact 1-multiplier Term constructors (saves ~50 KiB on certificate data!)
abbrev j1 (a b : ℕ) : Term := Term.j 1 a b
abbrev f1 (a g : ℕ) : Term := Term.f 1 a g
abbrev z1 (a : ℕ) : Term := Term.z 1 a
abbrev o1 (a : ℕ) : Term := Term.o 1 a
abbrev c1 (idx : ℕ) : Term := Term.c 1 idx


open Term BnbTree FCutCert

-- ==================== Row 7 (r=6) ====================
private def r7_ws : List ℕ := [5,5,4,4,4,4]
private def r7_fi : List ℕ := [0,15,23,27,31,39,43,47,51,55,59,63]
private def r7_prev : List ℕ := []
private def r7_k0_fc : List FCutCert := []
private def r7_k0_tr : BnbTree := lf 1 [1343489,1343490,688131,1474564,819205,819206,163847,1474568,819209,819210,163851,950284,294925,294926,180239,1474576,819217,819218,163859,950292,294933,294934,180247,950296,294937,294938,180251,426012,704543,1474592,819233,819234,163875,950308,294949,294950,180263,950312,294953,294954,180267,426028,704559,950320,294961,294962,180275,426036,704567,426040,704571,1228863]
private lemma r7_k0_ok : checkLayer (r := 6) (cd := 1) 0 (VTree.ofFun 6 (fun a => (maskWeightFast r7_ws a : ℤ) + (1 : ℤ) * (0 : ℤ) - (16 : ℤ))) (0 : ℤ) (patGens 7) r7_fi r7_prev r7_k0_fc r7_k0_tr = true := by decide +kernel
private def r7_k1_fc : List FCutCert := []
private def r7_k1_tr : BnbTree := lf 1 [21383,19851,149389,18318,19342,18323,149397,150422,150937,152986,280476,19363,150437,152486,149417,149418,280492,19377,22961,150962,281524,282040,1867776,1212417,1212418,557059,1343492,688133,688134,1343496,688137,688138,819212,1343504,688145,688146,819220,819224,1343520,688161,688162,819236,819240,819248,1359935]
private lemma r7_k1_ok : checkLayer (r := 6) (cd := 1) 1 (VTree.ofFun 6 (fun a => (maskWeightFast r7_ws a : ℤ) + (1 : ℤ) * (1 : ℤ) - (16 : ℤ))) (0 : ℤ) (patGens 7) r7_fi r7_prev r7_k1_fc r7_k1_tr = true := by decide +kernel
private def r7_k2_fc : List FCutCert := []
private def r7_k2_tr : BnbTree := br 12 (br 20 (br 5 (br 6 (lf 1 [280451,19331,19337,281993,22921,19850,18317,21393,154001,150418,284050,19349,21398,673688,18330,19873,22945,19362,415138,18340,19364,414628,18341,673704,19882,281520,22961,19378,150968,4874,268298,5646,134673,5273,5665,137761,1736704,1081345,1081346,1212420,557061,557062,1212424,688140,1212432,688148,1212448,1491007]) (lf 2 [808323,22915,935814,936838,1985926,938886,1987974,1988998,937354,808337,415122,150945,282018,809378,21929,658438,134406,660486,136454,268294,137478,6662,400390,138502,133769,135689,530441,6281,137226,135821,137230,266769,660498,136982,397848,135960,136729,397468,135710,136737,137761,6308,6697,3571712,2260993,2260994,2523140,1212421,11714566,2523144,1474572,2523152,1474580,2523168,3063871])) (lf 3 [1199491,152963,1460101,1461125,3034501,1463173,3036549,3037573,939401,152970,150929,940433,1068449,416161,1854882,789509,1053701,399365,268421,137733,662533,1051654,661510,792585,1053194,399882,133261,6157,268558,267793,266770,660498,267538,267794,267413,267286,135320,266777,267034,266780,266908,5406720,3440641,3440642,3833860,16171013,3833864,2261004,3833872,2261012,3833888,4636735])) (lf 1 [280451,19843,152965,18310,283526,19849,150929,21905,21906,416146,935828,412564,940436,546200,415137,542628,21412,18342,19888,267269,5126,264713,6665,2570,268298,6666,6157,2574,136209,3348,4244,266516,4756,5268,5396,6292,138260,7444,5653,5654,6424,6169,135452,1736704,1081345,1081346,1212420,1212424,688140,1212432,3981332,1212448,1491007])) (lf 1 [150915,153987,281477,416134,150921,285065,152970,411532,937356,939404,19348,414612,415128,154017,414628,19880,21928,21930,138245,6662,268298,133260,264460,3212,135308,266508,4748,5260,137228,6284,6412,6157,6670,267281,135698,4244,5653,5142,4888,5784,5658,135452,1736704,1081345,1081346,1212420,1212424,3981324,1212432,1212448,1491007])
private lemma r7_k2_ok : checkLayer (r := 6) (cd := 1) 2 (VTree.ofFun 6 (fun a => (maskWeightFast r7_ws a : ℤ) + (1 : ℤ) * (2 : ℤ) - (16 : ℤ))) (0 : ℤ) (patGens 7) r7_fi r7_prev r7_k2_fc r7_k2_tr = true := by decide +kernel
private def r7_k3_fc : List FCutCert := []
private def r7_k3_tr : BnbTree := br 4 (br 8 (br 16 (br 1 (lf 1 [542594,281474,150403,22915,19845,152453,283526,284041,19850,152970,281484,414609,413074,411540,18332,1066912,416161,543652,544168,282032,19896,6661,3078,1289,137228,5652,397592,1605632,950273,1081348,1081352,1081360,1622079]) (lf 1 [2901889,543617,544129,545665,546177,2906497,1068431,1070479,1070003,1070515,769,1281,3073,2562,5634,7170,2307,398341,5126,137222,2185,264713,268298,264460,135436,266769,4372,4118,135320,135704,135193,4124,4385,6689,1605632,7913473,1081348,1081352,1081360,1622079])) (lf 1 [18305,545665,673666,21891,18310,283535,1066896,543632,544144,1069968,1070480,547216,542624,415136,18338,769,2049,1154,2050,2051,4227,398341,3078,7174,133641,6153,399370,133260,264460,5648,135697,6673,135698,135444,5140,266392,4632,4380,1605632,1081348,1081352,4767760,1622079])) (lf 1 [543617,283521,152450,547202,542600,1067912,544136,1069960,546184,1071496,807824,150432,642,1027,2051,4355,3077,137221,398342,4104,397833,399370,133260,264460,4112,136209,4626,135316,266516,135320,5656,4124,7220,1605632,1081348,4505608,1622079])) (lf 4 [2772353,284034,2513282,2508676,2509700,4607364,2511748,4609412,4610436,2119048,2119056,152987,2117024,661505,399873,514,393858,398850,394243,395267,397315,1841284,269316,1051653,136197,7173,1971206,6150,1050760,264456,268936,1970697,264714,1579018,788620,1575180,1052816,136848,399120,1839380,136212,790680,397848,1052697,266266,266268,4380,6717440,19709956,6733887])
private lemma r7_k3_ok : checkLayer (r := 6) (cd := 1) 3 (VTree.ofFun 6 (fun a => (maskWeightFast r7_ws a : ℤ) + (1 : ℤ) * (3 : ℤ) - (16 : ℤ))) (0 : ℤ) (patGens 7) r7_fi r7_prev r7_k3_fc r7_k3_tr = true := by decide +kernel
private def r7_k4_fc : List FCutCert := []
private def r7_k4_tr : BnbTree := br 0 (lf 1 [413057,283521,18306,674690,152963,542596,281988,21894,674696,19337,152969,152970,283532,807824,150929,152978,283540,415128,149408,413088,154016,283556,411560,416176,131845,1029,2184,1546,4368,2578,135457,4641,1474560,1753151]) (lf 10 [33965952,7752576,7753088,7754624,7755136,33970560,12995983,12998031,12997555,12998067,3539457,2491137,1181185,1444097,5114882,1314306,1053186,1184770,1836035,528387,1028,3802372,1181828,1183876,4356,3150853,4200453,1181702,4460552,1183880,2365704,1181705,1577481,792585,1312780,2492556,1181710,1183758,1183888,3674384,2232850,5116948,3805210,83804160,18268223])
private lemma r7_k4_ok : checkLayer (r := 6) (cd := 1) 4 (VTree.ofFun 6 (fun a => (maskWeightFast r7_ws a : ℤ) + (1 : ℤ) * (4 : ℤ) - (16 : ℤ))) (0 : ℤ) (patGens 7) r7_fi r7_prev r7_k4_fc r7_k4_tr = true := by decide +kernel
private def r7_k5_fc : List FCutCert := []
private def r7_k5_tr : BnbTree := lf 1 [411520,805760,675201,19842,545666,21379,806276,21381,22917,153990,150408,546184,152969,150410,280460,152976,547216,152465,152978,283540,284056,542624,154016,150945,150946,280484,280488,281520,1884223]
private lemma r7_k5_ok : checkLayer (r := 6) (cd := 1) 5 (VTree.ofFun 6 (fun a => (maskWeightFast r7_ws a : ℤ) + (1 : ℤ) * (5 : ℤ) - (16 : ℤ))) (0 : ℤ) (patGens 7) r7_fi r7_prev r7_k5_fc r7_k5_tr = true := by decide +kernel
private def r7_k6_fc : List FCutCert := []
private def r7_k6_tr : BnbTree := lf 1 [673664,412544,412545,19841,544130,150916,414596,21381,21382,19336,545672,21897,19338,149388,673680,21393,21394,149396,150936,673696,19361,18338,150436,150952,150448,2015295]
private lemma r7_k6_ok : checkLayer (r := 6) (cd := 1) 6 (VTree.ofFun 6 (fun a => (maskWeightFast r7_ws a : ℤ) + (1 : ℤ) * (6 : ℤ) - (16 : ℤ))) (0 : ℤ) (patGens 7) r7_fi r7_prev r7_k6_fc r7_k6_tr = true := by decide +kernel
private lemma solve_row7 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hpat : HasPattern F 7) (hprev : ∀ pr ∈ r7_prev, ¬ HasPattern F pr) :
    ∃ W : Fin 12 → ℕ, 0 < ∑ i, W i ∧ F.card * (∑ i, W i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, W i) := by
  dsimp only [HasPattern, patR] at hpat
  obtain ⟨e0, he⟩ := hpat
  let e : Fin r7_ws.length ↪ Fin 12 := e0
  have he' : ∀ g ∈ patGens 7, decode e g ∈ F := he
  have hGens : ∀ g ∈ patGens 7, g < 2 ^ r7_ws.length ∧ decode e g ∈ F := by
    intro g hg
    refine ⟨?_, he' g hg⟩
    have hall : (patGens 7).all (· < 2 ^ r7_ws.length) = true := by decide
    simp only [List.all_eq_true, decide_eq_true_eq] at hall
    exact hall g hg
  have hFi : ∀ b ∈ r7_fi, b < 2 ^ r7_ws.length ∧ decode e b ∈ F :=
    checkClosureAux_sound closed empty he' [] r7_fi (fun _ h => by cases h) (by decide)
  have hTop : 2 ^ r7_ws.length - 1 ∈ r7_fi := by decide
  apply weight_from_fibers (r := r7_ws.length) (by decide) F e full (fun i => r7_ws[i.val]'i.isLt) 1 16 (by decide) (by decide) (0 : ℤ) (by decide)
  intro K hKsub hne
  have hkle : K.card ≤ 6 := K_card_le e hKsub
  have htop_iff : K = univ \ univ.map e ↔ K.card = 6 := K_eq_top_iff e hKsub
  have hlo_iff : K = ∅ ↔ K.card = 0 := card_eq_zero.symm
  have hoff : (if K = univ \ univ.map e then (0 : ℤ) else 0) - (if K = ∅ then (0 : ℤ) else 0) =
      (if K.card = 6 then (0 : ℤ) else 0) - (if K.card = 0 then (0 : ℤ) else 0) := by
    simp only [htop_iff, hlo_iff]
  rw [hoff]
  match hk : K.card with
  | 0 =>
    have h := checkLayer_sound (cd := 1) 0 closed minSize (ws := r7_ws) hKsub hk hne hGens hFi hTop hprev r7_k0_fc r7_k0_tr r7_k0_ok
    simpa [hk] using h
  | 1 =>
    have h := checkLayer_sound (cd := 1) 1 closed minSize (ws := r7_ws) hKsub hk hne hGens hFi hTop hprev r7_k1_fc r7_k1_tr r7_k1_ok
    simpa [hk] using h
  | 2 =>
    have h := checkLayer_sound (cd := 1) 2 closed minSize (ws := r7_ws) hKsub hk hne hGens hFi hTop hprev r7_k2_fc r7_k2_tr r7_k2_ok
    simpa [hk] using h
  | 3 =>
    have h := checkLayer_sound (cd := 1) 3 closed minSize (ws := r7_ws) hKsub hk hne hGens hFi hTop hprev r7_k3_fc r7_k3_tr r7_k3_ok
    simpa [hk] using h
  | 4 =>
    have h := checkLayer_sound (cd := 1) 4 closed minSize (ws := r7_ws) hKsub hk hne hGens hFi hTop hprev r7_k4_fc r7_k4_tr r7_k4_ok
    simpa [hk] using h
  | 5 =>
    have h := checkLayer_sound (cd := 1) 5 closed minSize (ws := r7_ws) hKsub hk hne hGens hFi hTop hprev r7_k5_fc r7_k5_tr r7_k5_ok
    simpa [hk] using h
  | 6 =>
    have h := checkLayer_sound (cd := 1) 6 closed minSize (ws := r7_ws) hKsub hk hne hGens hFi hTop hprev r7_k6_fc r7_k6_tr r7_k6_ok
    simpa [hk] using h
  | _ + 7 => omega

-- ==================== Row 8 (r=7) ====================
private def r8_ws : List ℕ := [8,8,8,6,6,6,6]
private def r8_fi : List ℕ := [0,15,23,31,39,47,55,63,71,79,87,95,103,111,119,127]
private def r8_prev : List ℕ := [7]
private def r8_k0_fc : List FCutCert := []
private def r8_k0_tr : BnbTree := lf 2 [144667,136861,146462,138411,138542,138419,145589,146486,144057,404666,10044,142012,142140,13116,141771,142925,13134,144729,670298,407772,144739,670825,670060,5406721,5406722,3309571,5406724,3309573,3309574,1212423,5931016,3833865,3833866,1736715,3833868,1736717,1736718,180239,5931024,3833873,3833874,1736723,3833876,1736725,1736726,180247,4358168,2261017,2261018,2261020,1753119,5931040,3833889,3833890,1736739,3833892,1736741,1736742,180263,4358184,2261033,2261034,2261036,1753135,4358192,2261041,2261042,2261044,1753143,2785336,3326015,5931072,3833921,3833922,1736771,3833924,1736773,1736774,180295,4358216,2261065,2261066,2261068,1753167,4358224,2261073,2261074,2261076,1753175,2785368,3326047,4358240,2261089,2261090,2261092,1753191,2785384,3326063,2785392,3326071,4898943]
private lemma r8_k0_ok : checkLayer (r := 7) (cd := 1) 0 (VTree.ofFun 7 (fun a => (maskWeightFast r8_ws a : ℤ) + (2 : ℤ) * (0 : ℤ) - (29 : ℤ))) (0 : ℤ) (patGens 8) r8_fi r8_prev r8_k0_fc r8_k0_tr = true := by decide +kernel
private def r8_k1_fc : List FCutCert := []
private def r8_k1_t0 : BnbTree := br 44 (br 56 (br 88 (br 104 (br 112 (lf 1 [281479,543627,280461,21389,545678,542611,280469,152469,411542,938911,280483,19363,150437,283557,412582,680881,149426,549810,542644,150467,287683,543685,281542,152518,281545,414665,149450,152522,804812,804817,411604,21463,18396,807905,804834,18410,18412,19441,19442,19444,13453,4886,6307,146484,7481,15420,272970,799314,11609,3440640,2392065,2392066,1343491,2392068,1343493,1343494,2654216,1605641,1605642,1605644,2654224,1605649,1605650,1605652,1867800,819225,819226,819228,2654240,1605665,1605666,1605668,1867816,819241,819242,819244,1867824,1081400,2654272,1605697,1605698,1605700,1867848,1867856,1081432,1867872,1081448,1081456,2670719]) (lf 1 [281479,280462,18323,542613,280470,411555,280485,149414,283558,542641,150449,804786,805812,18361,18362,18364,287683,280521,411594,149452,152524,805841,542674,150482,804820,18393,18394,18396,807905,542690,152546,804836,18409,1854448,538635,538637,145422,407571,145430,14371,145445,145475,538693,538694,407625,276554,276556,14442,14444,15473,15474,15476,3440640,2392065,2392066,1343491,2392068,1343493,1343494,2654216,1605641,1605642,1605644,2654224,1605649,1605650,1605652,1867800,819225,819226,819228,2654240,1605665,1605666,1605668,1867816,819241,819242,819244,1867824,1081400,2654272,1605697,1605698,1605700,1867848,1867856,1081432,1867872,1081448,6602864,2670719])) (lf 2 [674695,1198987,673677,150414,673685,411555,676771,1197989,411558,1723313,1198002,412594,1722292,149433,149434,149436,680902,1723337,411594,1199050,1722316,411601,150481,674770,1199060,149466,1201121,1330146,19428,938980,3819496,2247664,406541,930830,1192979,406549,1192982,668710,1193027,1193029,408646,930897,930898,406612,143961,144476,143969,144737,12898,144610,145640,145768,146024,146540,6979584,4882433,4882434,2785283,4882436,2785285,2785286,5406728,3309577,3309578,3309580,5406736,3309585,3309586,3309588,3833880,1736729,1736730,1736732,5406752,3309601,3309602,3309604,3833896,1736745,1736746,1736748,3833904,2261048,5406784,3309633,3309634,3309636,3833928,3833936,2261080,3833952,13287528,5423231])) (lf 1 [287623,150411,152459,280461,152461,545678,542611,149397,281493,283557,542641,150449,805810,804788,18361,18362,18364,542665,545738,411596,21452,676817,281554,674772,1853400,414689,414690,21476,1066984,1068016,11275,535574,535587,142373,535590,535619,535621,142406,277574,9545,11849,9802,11468,11601,10834,275026,274648,274776,275032,13528,13656,13912,14552,14680,14936,3440640,2392065,2392066,1343491,2392068,1343493,1343494,2654216,1605641,1605642,1605644,2654224,1605649,1605650,1605652,1867800,819225,819226,819228,2654240,1605665,1605666,1605668,1867816,819241,819242,819244,1867824,1081400,2654272,1605697,1605698,1605700,1867848,1867856,6602840,1867872,2670719])) (lf 2 [680839,1198987,936845,673678,674707,1197987,411557,411558,676774,1461169,674738,943028,3819448,804809,542666,673740,281553,1460178,150482,1592276,2246616,412641,807905,1332194,1198052,2246632,149481,2247664,138253,400398,400403,1186837,1186838,670757,137777,137778,664754,138420,1188280,1188536,1188664,927032,665144,927928,142520,142904,144696,144952,140858,141500,9545,10833,145626,12641,143969,143970,146034,6979584,4882433,4882434,2785283,4882436,2785285,2785286,5406728,3309577,3309578,3309580,5406736,3309585,3309586,3309588,3833880,1736729,1736730,1736732,5406752,3309601,3309602,3309604,3833896,1736745,1736746,1736748,3833904,13287480,5406784,3309633,3309634,3309636,3833928,3833936,3833952,5423231])) (lf 3 [1074055,542603,411533,674701,1854350,1067925,1066902,680854,287647,1723299,1461157,19366,1069990,3426220,5786540,5792684,2253748,680899,1854405,21446,674759,1460170,1067978,1853388,673748,3033048,280540,938977,2249700,3427312,1192971,273421,145933,1848339,665109,7203,267813,267814,137766,2365612,2234668,138412,269612,2630828,2631852,2631980,1845804,273580,273708,2634028,276652,276780,144433,6706,144946,1188664,1585336,275768,13881,275644,1064003,275014,14918,10518528,7372801,7372802,4227075,7372804,4227077,4227078,8159240,5013513,5013514,5013516,8159248,5013521,5013522,5013524,5799960,2654233,2654234,2654236,8159264,5013537,5013538,5013540,5799976,2654249,2654250,33341484,5799984,8159296,5013569,5013570,5013572,5800008,5800016,5800032,8175743])
private def r8_k1_t1 : BnbTree := br 25 (br 26 (br 28 (br 41 (br 42 (r8_k1_t0) (lf 2 [673671,936843,1198989,942990,674707,942998,943011,676773,412582,680870,2246570,3820458,3826602,1723314,674755,418757,281542,156614,412617,411594,674762,673740,19410,2246616,149466,412641,1723362,414692,1461232,140555,140558,406547,1186837,144662,136483,406565,136746,1448106,1710634,138410,533290,1189034,927274,1714346,141610,1714730,142506,142890,143530,12842,144554,145578,145706,145962,670762,141612,405676,669740,144433,139704,405688,144952,139706,144444,668741,1061458,6979584,4882433,4882434,2785283,4882436,2785285,2785286,5406728,3309577,3309578,3309580,5406736,3309585,3309586,3309588,3833880,1736729,1736730,1736732,5406752,3309601,3309602,3309604,3833896,1736745,22200362,3833904,5406784,3309633,3309634,3309636,3833928,3833936,3833952,5423231])) (lf 2 [680839,673675,418699,1198989,418702,281491,414611,935829,156565,281494,156566,1074083,412581,676773,1199014,2246569,3820457,3826601,1598385,935875,935877,1723337,674767,1723345,1198040,281569,1070049,281570,1068016,150513,269326,275470,267411,537622,6435,660777,136745,1317161,1448489,138793,139689,1451305,1713705,1714473,1714729,11305,142633,142889,1062953,145705,145961,671273,136746,137770,142506,146474,408619,797740,274732,12849,144562,405816,1061432,144696,144953,144442,143941,140614,930886,143713,143970,6979584,4882433,4882434,2785283,4882436,2785285,2785286,5406728,3309577,3309578,3309580,5406736,3309585,3309586,3309588,3833880,1736729,1736730,1736732,5406752,3309601,3309602,3309604,3833896,23511081,3833904,5406784,3309633,3309634,3309636,3833928,3833936,3833952,5423231])) (lf 2 [680839,149387,411533,418701,1205134,1201043,938901,674710,2246556,3822492,3826588,545699,21413,287654,935849,1197994,549809,811956,1201093,545734,149449,1460172,1201103,412626,1723348,1591268,804840,2247664,924683,140813,134677,134678,141590,1053340,791324,136348,268444,792860,1451164,1451292,142492,142620,1716380,1716508,1192988,144540,144668,145564,145692,535587,136489,136745,142890,927916,403756,137777,142385,145969,797746,533300,1188280,142393,142394,141628,144970,670801,12882,13394,6979584,4882433,4882434,2785283,4882436,2785285,2785286,5406728,3309577,3309578,3309580,5406736,3309585,3309586,3309588,3833880,1736729,1736730,22200348,5406752,3309601,3309602,3309604,3833896,3833904,5406784,3309633,3309634,3309636,3833928,3833936,3833952,5423231])) (lf 2 [676743,673675,25483,545678,680851,674709,938902,2246554,3822490,3826586,418725,1467305,1197994,673708,287663,1199026,156594,414659,680899,1201093,1329098,673740,1461204,411618,1199074,1066984,149482,2247664,9483,145675,134669,662541,144397,136462,275470,134419,137491,404501,134422,1448090,1448474,138394,138778,1188634,1451162,140826,142490,142874,1716378,1716762,406554,144538,144922,145562,145946,670746,660124,665756,1190179,137766,141606,666662,136489,928812,142641,140472,140856,927928,140858,140874,141906,6979584,4882433,4882434,2785283,4882436,2785285,2785286,5406728,3309577,3309578,3309580,5406736,3309585,3309586,3309588,3833880,1736729,22200346,5406752,3309601,3309602,3309604,3833896,3833904,5406784,3309633,3309634,3309636,3833928,3833936,3833952,5423231])) (lf 2 [680839,673675,414603,1201037,25486,150419,414611,156563,412565,938902,2246553,3822489,3826585,676771,674725,411561,680873,943020,943026,18371,938949,674758,21446,1722313,149452,1199057,414673,1070049,1984488,2247664,928782,15374,139667,134293,137365,141845,140054,134425,135577,1447193,398873,1186329,1451545,1452313,403993,142617,536729,1716505,1716761,144665,144921,145561,145689,145945,277529,134682,1184538,399644,8988,533788,146460,144547,273445,11429,136489,136745,137521,141617,928305,404532,795064,1058104,143032,139961,11322,11450,142396,144476,6979584,4882433,4882434,2785283,4882436,2785285,2785286,5406728,3309577,3309578,3309580,5406736,3309585,3309586,3309588,3833880,22462489,5406752,3309601,3309602,3309604,3833896,3833904,5406784,3309633,3309634,3309636,3833928,3833936,3833952,5423231])
private def r8_k1_tr : BnbTree := r8_k1_t1
private lemma r8_k1_ok : checkLayer (r := 7) (cd := 1) 1 (VTree.ofFun 7 (fun a => (maskWeightFast r8_ws a : ℤ) + (2 : ℤ) * (1 : ℤ) - (29 : ℤ))) (0 : ℤ) (patGens 8) r8_fi r8_prev r8_k1_fc r8_k1_tr = true := by decide +kernel
private def r8_k2_fc : List FCutCert := [d [3,5,6,17,18,20] 7 [7,8,0,1,2,4],d [3,9,10,17,18,24] 7 [7,8,0,1,3,4],d [3,9,10,33,34,40] 7 [7,8,0,1,3,5],d [3,9,10,65,66,72] 7 [7,8,0,1,3,6],d [3,17,18,33,34,48] 7 [7,8,0,1,4,5],d [5,9,12,33,36,40] 7 [7,8,0,2,3,5],d [5,9,12,65,68,72] 7 [7,8,0,2,3,6],d [5,33,36,65,68,96] 7 [7,8,0,2,5,6],d [9,17,24,33,40,48] 7 [7,8,0,3,4,5],d [9,17,24,65,72,80] 7 [7,8,0,3,4,6],d [9,33,40,65,72,96] 7 [7,8,0,3,5,6],d [17,33,48,65,80,96] 7 [7,8,0,4,5,6],d [6,10,12,66,68,72] 7 [7,8,1,2,3,6],d [6,18,20,34,36,48] 7 [7,8,1,2,4,5],d [6,18,20,66,68,80] 7 [7,8,1,2,4,6],d [6,34,36,66,68,96] 7 [7,8,1,2,5,6],d [10,18,24,34,40,48] 7 [7,8,1,3,4,5],d [10,18,24,66,72,80] 7 [7,8,1,3,4,6],d [10,34,40,66,72,96] 7 [7,8,1,3,5,6],d [18,34,48,66,80,96] 7 [7,8,1,4,5,6],d [12,20,24,36,40,48] 7 [7,8,2,3,4,5],d [12,20,24,68,72,80] 7 [7,8,2,3,4,6],d [12,36,40,68,72,96] 7 [7,8,2,3,5,6],d [20,36,48,68,80,96] 7 [7,8,2,4,5,6],d [24,40,48,72,80,96] 7 [7,8,3,4,5,6]]
private def r8_k2_t0 : BnbTree := br 34 (br 36 (br 65 (br 66 (lf 1 [149379,280453,543621,21382,942982,21383,25485,287630,21395,283541,280470,152473,411546,411548,283555,280485,280486,150441,542634,543660,280497,150449,543666,542644,281539,411588,545732,280517,281542,283591,543689,543690,543692,149457,281553,150482,283602,545748,150497,283617,542690,542692,804840,805872,793603,11269,142347,15371,139789,134291,11289,3610,273449,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,1343506,1343508,1605656,2392096,1343521,1343522,1343524,1605672,1605680,2392128,1343553,1343554,1605704,1605712,1605728,2932863]) (lf 1 [805763,152451,1067909,1066886,19335,21387,281485,280462,150415,545679,152469,283542,1460119,545690,676767,150435,283557,281510,542634,411570,19378,149432,5785538,1330114,3560386,549826,2116559,2118607,2116583,143627,274707,8725,532761,532764,9507,532777,532780,532785,532788,532792,271554,271938,272578,272962,11330,274626,406082,144450,14402,277058,15426,142403,13379,141508,11332,12484,13380,13636,407620,142405,13381,11334,144454,141641,141898,12874,14410,10572,14412,12498,13138,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,1343506,1343508,1605656,2392096,1343521,1343522,1343524,1605672,1605680,2392128,1343553,18268226,1605704,1605712,1605728,2932863])) (lf 3 [3427203,1460101,1856389,3427206,280455,281483,545675,674701,1067918,1069971,542613,1066902,3032983,1856407,1856409,2904991,1066915,1066917,1067942,1197993,1591217,17582017,4213697,10900417,1860545,6573007,6575055,6573031,10379,272525,405653,1843354,1843356,532777,1843370,1843372,139825,1843378,1843380,2629816,1058113,1058369,403777,1059393,273473,1061185,406081,275521,800065,538177,276545,665154,534722,406082,1193026,276546,1062979,271684,272708,273476,536772,274756,930884,276548,277572,1059909,666694,276550,928073,799305,272586,274769,667860,9732096,6586369,6586370,6586372,7372808,4227081,4227082,4227084,7372816,4227089,4227090,4227092,5013528,7372832,4227105,4227106,4227108,5013544,5013552,7372864,53657665,5013576,5013584,5013600,8962175])) (lf 2 [1722243,412547,1729413,673670,1467270,149383,674702,1461135,674707,156565,411548,11683748,2771876,1201060,7234468,4344751,4350895,2247617,549826,2508740,150468,412613,2640839,149452,1066964,3164119,4344807,407557,532747,8587,668173,397845,659990,1184281,1184282,135708,398108,662563,660644,660772,137380,664356,1189028,1189156,140836,1190052,1190180,1453092,667812,406820,145444,146468,531493,10789,142374,268841,14377,138282,139690,399660,139948,405804,930865,139442,406066,401716,274612,12472,145473,665154,145474,276547,668770,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,2785298,2785300,3309592,4882464,2785313,2785314,36093988,3309608,3309616,4882496,3309640,3309648,3309664,5947519])) (lf 2 [1197955,936835,1067909,1854342,156551,418710,2770839,11683746,2771874,1201058,7234466,4344751,4350895,1722305,935874,1067970,549827,2771908,287685,1199050,1198034,1591255,18392,4344807,1061893,265478,8331,536843,659981,4366,532750,659731,531477,8853,136470,1184025,135450,397722,4634,1184028,660642,529954,662050,663714,664354,1189026,1189410,1190050,1190434,1453090,144418,145442,408098,146466,145443,661668,8356,144420,669732,11301,537125,531494,13350,407593,399530,274602,12842,536876,8626,536754,406066,138292,139956,143544,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,2785298,2785300,3309592,4882464,2785313,36093986,3309608,3309616,4882496,3309640,3309648,3309664,5947519])
private def r8_k2_t1 : BnbTree := br 96 (br 18 (br 20 (br 33 (r8_k2_t0) (lf 12 [14044035,14043013,14050182,1461127,4606862,6179727,1066899,4605846,7751575,7365535,70666145,17189793,7754657,43934625,26626991,26633135,17188801,2509762,4606915,10898372,4613061,10898375,7097289,11945943,26627047,1446027,3020939,1190029,3289229,1192083,2110483,922773,401941,3027093,1446041,3019033,3019417,7737498,7737500,660769,4593185,4593953,4594209,400929,4596001,4596257,533665,7742753,7743009,1452193,7743777,7744033,9317409,799777,3029537,1457185,2233506,2496034,2497058,1448994,141474,1453090,1455138,1456162,4600867,1971492,1972516,1973284,4596516,1455140,4601892,1448997,4601894,1454377,2765353,4862506,401708,4596017,926258,405812,5648696,4597954,39223296,26640385,26640386,26640388,29786120,17203209,17203210,17203212,29786128,17203217,17203218,17203220,20348952,29786144,215138337,20348968,20348976,29786176,20349000,20349008,20349024,36094079])) (lf 1 [280451,545667,673669,287621,280454,18311,938895,5785492,543636,1332116,3564436,2118559,2122655,25505,804770,280483,18340,1205156,156588,943023,804801,804804,156613,149446,545743,2118615,149476,3203,142342,274950,14342,268555,264717,137742,10766,134419,4243,265492,266388,266516,529556,529684,5652,533652,533780,272532,272660,11284,536724,536852,799764,14356,273429,145430,15382,137753,8601,8857,135836,135964,8988,270881,272929,14370,11301,10790,8748,10412,137521,8369,140849,8372,794936,141633,271938,10434,145475,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,1343506,17743892,1605656,2392096,1605672,1605680,2392128,1605704,1605712,1605728,2932863])) (lf 2 [673667,938883,418691,2246534,152455,1725327,11683730,1198994,2773906,7234450,4346783,4350879,2384801,1197986,680869,680870,549802,156591,1984450,673732,1987524,680902,152522,4346839,3164135,928773,1193989,135435,403723,657933,665870,658578,658962,659858,659986,1184914,136466,1185298,1189010,1189394,665746,666130,142354,1192082,143634,1192466,1717266,400403,145427,137364,138260,664212,142356,405780,662549,142358,143638,146454,135449,139417,659994,137370,141466,137500,143644,267553,663970,140578,399524,663844,138289,663730,141874,925876,141876,664897,145489,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,35569682,3309592,4882464,3309608,3309616,4882496,3309640,3309648,3309664,5947519])) (br 18 (lf 2 [1197955,674691,412549,938885,152455,2770836,1984417,674721,2771874,1067940,673702,281513,1199020,1853367,673720,673729,1205185,2509762,1984452,150468,412617,1199050,674764,1198033,411604,4343776,4344800,2778080,143363,660613,667654,406534,931846,667659,667661,667662,667667,667669,667670,1191961,1191962,1191964,662563,660772,6308,137508,138276,142372,667685,12585,143402,143914,139825,143409,536881,399922,401586,405684,144436,142401,142402,405571,144451,142404,669765,668742,143433,406089,143436,143564,404050,143442,406098,143444,405720,143704,146530,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,2785298,3309592,4882464,3309608,3309616,4882496,3309640,3309648,20889696,5947519]) (lf 5 [545667,2515843,1725317,3164038,549767,29378450,3165074,7099282,18244498,11031455,11035551,2508705,414625,4474786,152486,2377665,4474818,18372,11031511,11028448,7103456,1838339,538883,1849349,1847307,1847309,526606,1191950,1839250,1839634,529682,3151378,3155090,3156498,2501650,14954514,1192082,143890,1192978,1848339,1843348,3155220,1846548,1847317,1182998,529686,3158041,2502684,538908,1849635,399524,1847333,1585190,3152169,1188266,536618,1317425,1194289,531508,404532,536628,1190712,274744,2111800,538689,538947,2242884,1849413,1849670,536652,2505036,1845585,1193041,1192530,1323608,1847649,143970,539746,2031623,2555919,16285696,11042817,11042818,11042820,12353544,7110665,7110666,7110668,12353552,7110673,86687762,8421400,12353568,8421416,8421424,12353600,8421448,8421456,48283744,14991487]))
private def r8_k2_t2 : BnbTree := br 72 (br 80 (r8_k2_t1) (br 96 (br 18 (lf 2 [935811,674693,938885,1461126,149383,1463188,411541,935831,1197980,1199009,149410,152482,1336226,2508708,935857,411570,1198004,1460152,2770881,1205186,1332164,1201097,938954,545740,4343760,4346832,2778064,1198049,18408,1193987,407557,665606,665611,665613,665614,665619,3220,265492,661780,142357,658710,138265,532761,141337,10394,272414,532769,664097,10529,8610,141346,11298,274978,665635,141348,665637,665638,1189929,1189930,1189932,141361,144450,535619,274756,144452,665669,666694,141386,141388,272588,12625,12881,406609,668242,13394,146514,667988,406612,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,2785298,3309592,4882464,3309608,3309616,4882496,3309640,21282896,3309664,5947519]) (lf 2 [149379,1205123,935814,807814,152455,11683730,1198994,2773906,7234450,4346783,4350879,411553,21410,2384802,1984420,149414,1853377,2377666,673731,1198020,21444,411590,4084687,4346839,152545,149474,667907,665605,666629,669701,657675,665613,657678,659602,659986,1185298,138258,926866,1189394,4859922,403602,142354,668178,136467,141331,146451,659604,796692,665876,666645,662550,1190169,929946,145818,141340,928028,664097,140578,665635,665637,406054,1189929,927786,1190193,141362,403634,404018,141364,928052,665912,664897,13377,143684,669765,140614,141385,145489,1586260,327694,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,34390034,3309592,4882464,3309608,3309616,4882496,3309640,9617488,3309664,5947519])) (lf 1 [542597,21383,673682,543634,1329044,18326,807839,1329057,805794,674724,414628,149426,149428,149431,411576,411585,156609,287682,804804,2115536,2118608,1336272,2115552,1336288,1062915,274437,14341,404486,538630,274443,276493,272398,142355,15379,274453,144406,401689,10265,10778,405658,274460,143644,268834,7202,274467,6308,272421,274470,141353,10793,12329,12585,534570,532652,268593,7217,8504,272962,275523,271684,11332,272453,276550,538697,10314,14410,10572,407628,3027024,12496,12624,12880,272721,143953,12882,13410,13412,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,1605656,2392096,1605672,1605680,2392128,1605704,10010704,7520352,2932863]))) (br 80 (br 96 (br 18 (lf 2 [411523,936835,936837,1987462,156550,156551,673675,938900,676759,935833,411546,545690,1197980,1984417,1985442,674724,1991588,673703,1199018,1199020,1729463,1066936,1985473,676801,1467332,674759,2770888,4344776,4346824,545745,676820,412644,543728,664579,928773,144389,668685,664590,664595,3348,659604,140308,533780,664597,664598,140313,660642,664611,664613,664614,401705,1188913,1188914,1188916,8504,402616,534722,667842,406082,145474,666691,665924,143684,145476,664645,668742,141640,143560,143688,143944,141641,404041,143562,276554,667980,145484,146508,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,2785298,3309592,4882464,3309608,3309616,4882496,20889672,3309648,3309664,5947519]) (lf 1 [1066883,542597,414598,156550,21383,1069967,5785490,543634,1332114,3564434,2118559,2122655,149410,1332162,287683,1329096,2118600,2118615,271365,15365,271366,273675,273421,264462,527890,266386,398482,529938,268818,270866,4727826,533650,402962,537106,269331,3220,136468,400404,144404,145428,271381,274710,265497,4377,4506,6426,528670,9249,797985,8994,9250,10658,9251,11299,9252,1191204,271397,271398,11561,270890,402481,11569,402482,140596,271420,271422,271681,403777,272961,11585,535876,273477,144454,10440,10824,14920,12620,275537,14417,14418,12628,536794,276570,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,20234258,1605656,2392096,1605672,1605680,2392128,11452488,1605712,1605728,2932863])) (lf 2 [935811,149383,1984402,1198996,673689,2771873,1329058,1201058,1984420,149417,1199018,804780,1723311,1198008,1199041,943041,1461186,156612,2770888,4344776,4346824,4344800,2778080,405507,668675,926725,928773,146437,2241542,667659,664589,404494,145422,664082,664595,1455124,667669,664598,405529,1191962,140316,927004,5666,664611,660644,664613,669734,138281,138284,1188913,139826,402994,407090,1188148,403009,664643,665796,668740,667717,664646,141512,4075592,143560,143688,1190473,142410,145484,1454157,143441,143442,405714,406610,143713,146017,668258,407652,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,3309592,4882464,3309608,3309616,4882496,21413960,3309648,14860384,5947519])) (lf 1 [280453,18311,18318,673682,543634,1069972,283545,545690,542620,1329057,150434,21410,414628,19370,18354,804792,549825,1329096,2116552,2118600,1330128,2118608,1332192,10243,273411,13315,407555,664581,272390,668678,272395,271373,141326,141331,15379,134292,272405,271382,929314,271395,270500,270628,9252,271397,271398,139561,272937,403626,9516,403500,402481,9521,271410,10290,270516,139572,271938,11330,273475,1190980,14404,273477,142406,14406,1845320,10440,141896,405704,536904,271689,143945,141644,665677,12496,275664,406864,14160,275026,143452,14428,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,1605656,2392096,1605672,1605680,2392128,11452488,8306768,2932863]))
private def r8_k2_t3 : BnbTree := br 72 (br 80 (br 96 (br 18 (lf 2 [673667,149381,1198981,1467270,149383,673683,1197972,673686,149409,1074081,1722274,1201060,287652,18342,1205161,542636,4343728,2773936,4350896,2771905,1725378,2508740,149447,935889,1198034,542676,1329112,1198049,1198050,411623,1448963,138245,407557,661510,661515,661517,661518,658580,658708,661525,4633,137241,14361,137242,145434,137244,268444,530716,267553,668193,144417,406050,144418,146466,661539,144420,669988,669733,537638,793130,399532,14380,926000,663984,139824,664240,664368,1189040,1189168,1189424,141488,273457,535090,275508,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,2785298,3309592,4882464,3309608,21676080,4882496,3309640,3309648,3309664,5947519]) (lf 2 [938883,1205123,542597,676741,1853318,152455,1205135,11683730,1198994,2773906,7234450,4346783,4350879,1984417,2384802,156579,1598372,673703,2246594,152515,676815,4346839,411618,1198052,1722343,661509,10757,661515,661517,661518,920082,658578,658962,1184914,136466,1185298,2627602,661650,662034,1581202,664338,1189010,402962,538770,665875,399380,534676,142356,669717,1717270,137241,137497,141594,929946,137244,137500,664097,401699,667940,669733,660774,139690,139824,664240,1189168,665136,534704,141616,1583536,145457,146481,1712690,1059378,404530,928820,1056952,539448,143555,327693,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,35569682,3309592,4882464,3309608,9617456,4882496,3309640,3309648,3309664,5947519])) (lf 1 [18309,280454,18311,280466,543634,1329044,287647,542625,545698,673700,2115504,1332144,2122672,805825,418753,1330114,1329092,25542,542674,804823,149464,2115552,1336288,275459,669699,268293,538629,274438,276486,268299,268301,276494,10386,10770,11282,269331,138261,11285,274454,266521,6169,12313,528922,6172,399516,267553,274721,140834,14370,268323,274469,268326,538665,6186,12330,538668,270768,271024,533808,2633776,12848,12337,140466,12338,12850,15410,140468,12468,143668,143928,144454,12361,274636,272977,11345,11348,12504,13412,14696,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,1605656,2392096,1605672,10797104,2392128,1605704,1605712,6471776,2932863])) (lf 1 [411526,18311,673682,543634,542612,1066913,149410,545698,287650,811940,2115504,1332144,2122672,1329089,156610,287684,2115536,1336272,1460192,21472,280546,149476,272387,669699,268293,13317,538629,268294,142342,268299,268301,272398,268307,136468,271508,14356,272405,272406,141337,272921,6170,268826,10394,399516,14492,143649,12450,141347,13347,270628,10404,272421,269350,6185,403497,139818,10410,6188,403756,8624,271152,9392,533808,534064,534576,141488,10544,11440,15409,401970,9394,139572,139576,139704,11330,13378,11332,13380,273477,144468,275041,13409,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,1605656,2392096,1605672,9617456,2392128,1605704,5554256,2932863])) (lf 5 [2508677,542599,804754,3165074,3557268,2508698,5392289,3167138,1591204,11028400,7099312,11035568,3171268,7096264,11029448,11031496,7097296,7099360,1841155,531459,3156995,1844229,403461,537605,14341,5776390,1841163,1185805,536589,1841166,2896914,1844243,136468,3155092,1844245,1054742,665622,2494745,533529,538138,3158300,529953,533537,273953,529954,533538,1844259,1184932,661796,3285284,1841189,1850406,1840425,530474,276522,530476,1188908,532784,1843632,1843888,1844016,6038576,3811120,1323824,531505,1057329,1321265,2368050,1843380,534708,536628,3155512,1844545,3161153,1845442,797250,146498,141636,534856,928328,1190474,538705,799826,1192152,1847905,1195108,16285696,11042817,11042818,11042820,12353544,7110665,7110666,7110668,12353552,7110673,8421400,12353568,8421416,50642992,12353600,45793352,14991487])
private def r8_k2_t4 : BnbTree := br 12 (br 17 (br 48 (r8_k2_t2) (r8_k2_t3)) (br 72 (br 96 (lf 6 [1332099,3819397,942981,676743,35276689,3820433,8541073,21914513,13259679,13263775,7882657,5530530,2249635,6185892,542631,8538049,2642882,2249667,1725380,2778052,2249669,13259735,673761,12470247,1320067,1323139,2234374,400390,1980422,2242571,1443981,661517,2238478,2231569,658961,2232593,660625,3806481,3806737,268817,1318417,2236689,3810577,3810833,927761,666641,3027217,3813905,4600849,669713,408081,670737,2231826,2233490,402578,275474,145426,2239507,2104340,1844372,2238612,1841173,275477,2238486,661785,793113,139545,1059353,667929,661530,665626,665628,2236708,2236965,2238502,667817,1188400,2237232,3811633,139826,403506,2239538,2500788,2632248,798914,2031616,589828,19562496,13271041,13271042,13271044,14843912,8552457,8552458,8552460,14843920,107528209,10125336,14843936,10125352,14843968,10125384,10125408,18006143]) (lf 3960 [2551859075,2551866245,43148166,43140999,475681671,23356917649,2595113873,5709386641,14533157777,8823657375,8823661471,2530232226,1557025699,3179038628,562189222,1557022658,4152248260,8823657431,8823654368,5709390816,129636358,129640454,2292332550,1557016587,1557018765,1557016590,64752913,2595098129,518919313,2595099921,3208517137,518920465,1557012753,1557013009,2595104017,2595104273,518925329,12820295697,2595107345,518927377,194515730,1981686930,518928530,1492126867,64760851,943590548,713562260,518921236,1427251476,1462637717,94250133,1557016598,155595033,2530228378,1981687965,1232607778,518921250,518928418,2530225188,1557016613,821704742,613298473,1037965617,843323953,1037972530,518926388,613296312,1981692088,259404866,1557018819,1557017669,1557016646,518926409,518926546,2076063954,518925396,2076063956,1557016929,518929505,259404898,2119368704,5709430795,908263443,12976029696,8823668737,8823668738,8823668740,9861758984,5709398025,5709398026,5709398028,9861758992,82571345937,6747488280,9861759008,6747488296,9861759040,6747488328,36044718176,11937955967])) (lf 1 [18307,545667,25477,280454,18311,283533,5785489,543633,1332113,3564433,2118559,2122655,280481,542633,1070017,156609,156610,1329096,2118600,2118615,152544,271363,406533,276485,15365,271366,272390,273547,273422,527633,266513,529681,529937,1447953,138769,8721,3810321,533777,665617,272657,12305,275473,277777,265746,7186,795666,3219,7187,9235,135316,6292,269332,537748,265365,271382,6169,268443,137372,664609,140450,666786,271395,9252,10276,1058980,271397,271398,1057073,9777,10545,404530,11442,533556,140856,274499,141508,535748,274628,271429,271430,10824,12616,14792,277192,272969,143564,272462,12370,11476,405849,537177,407641,667738,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,21151761,1605656,2392096,1605672,2392128,12369992,2932863]))) (br 48 (lf 1 [281477,152454,19335,542604,1330060,3560332,5792652,545681,543636,418711,674724,283556,2116527,549812,938945,19394,281540,283588,549828,281542,2116559,2118607,807888,543712,400387,271363,10243,13315,272389,274437,272902,274438,15366,267531,264460,265356,266380,4620,267020,530572,530700,7180,270604,270988,10252,534668,534796,536716,536844,12812,800780,274957,10254,141838,4625,267793,144401,139666,9234,271506,12306,12818,271379,135316,266516,12308,5653,140309,275478,140825,135322,139418,9370,397596,9500,270625,11297,9250,273442,271395,9765,142373,8361,401705,140842,140588,140600,13379,11337,3178496,2129921,2129922,2129924,2392072,1343497,1343498,17874956,2392080,1605656,2392096,1605672,1605680,2392128,2932863]) (lf 2 [545667,152455,1197964,2771852,7230348,11690892,1198996,1467284,283556,2384804,4344751,2771888,4350896,1205188,4344783,4346831,936912,150484,283616,662531,664579,12291,132613,141829,405509,1192965,661510,1452038,661515,658572,658700,135436,398604,13506572,663692,663820,141324,1190028,141580,666380,1192204,929805,661518,2235921,140305,141841,140818,1715218,143890,145426,146450,662547,402965,141333,669718,396569,139932,927004,398625,661025,1186337,143905,138274,1449506,140322,402978,661539,669733,667686,136489,137257,141353,141865,144425,140588,144428,139440,663984,1189040,141872,1453360,139825,140337,668209,1188402,405557,1712316,1974588,402108,664380,1713212,928060,1192124,6455296,4358145,4358146,4358148,4882440,2785289,2785290,42123276,4882448,3309592,4882464,3309608,25083952,4882496,5947519]))
private def r8_k2_t5 : BnbTree := br 9 (br 10 (r8_k2_t4) (br 48 (br 80 (lf 2 [414595,942979,1198982,938886,152455,1197962,2771850,7230346,11690890,418706,156563,156566,680865,2771874,418727,4344751,1463234,156611,1985476,674758,4344783,4346831,938962,938967,2247648,667651,1055749,797701,143365,657546,1051146,659850,659978,1185930,137482,1186314,663690,140298,665098,1190026,1190410,142346,1192074,1192458,144394,1718282,6411,537611,264332,265356,660620,138252,664716,143628,668685,269326,11278,146446,659985,401937,140305,13329,659602,398098,663698,143634,402451,136340,139924,140308,9364,667924,664597,401686,791833,136730,401562,402970,790684,271644,267550,271649,663844,402724,664613,140582,140329,663724,140332,401842,271538,141636,404549,6455296,4358145,4358146,4358148,4882440,2785289,36225034,4882448,3309592,4882464,3309608,3309616,4882496,3309648,5947519]) (lf 4 [1463171,414597,414599,2508682,5655434,14570378,23487370,2511761,2509714,3036050,8801199,2249665,1070018,2515906,2118596,8801231,8803279,5655504,8803280,2238467,667907,1451013,2501637,400390,533510,1456134,1443978,264714,1051402,1446026,135946,924682,795402,20326410,1190026,665994,2501130,1454602,1061898,1062410,408586,1452043,1445004,400396,1585164,1452045,1184014,143630,1448209,1456147,1446164,1452308,2108692,402453,930837,267542,400409,400665,1053210,927258,1447196,923932,4074785,927266,403490,1190050,1451043,403492,3943716,1452069,1189926,2500649,533674,2500652,2501937,2501940,925880,1451329,144705,407617,667715,668739,1454404,1452101,537670,405704,403529,928073,275785,929994,403532,930392,3027034,930010,1060958,1900556,13008896,8814593,8814594,8814596,9863176,5668873,79347722,9863184,6717464,9863200,6717480,6717488,9863232,45531216,11976831])) (lf 5 [2249606,545671,3164042,7097226,18240394,29385610,3165074,3302290,1074068,6579106,676772,418727,11029423,7097264,11035568,3171266,11029455,11031503,2509776,1185795,534531,3814403,3808261,1846277,928006,1847302,1837194,1444618,2494602,1839626,13375498,3152010,3152394,1843338,1843722,2762762,3156106,3156490,1192074,3158538,3815434,539658,1841163,1837196,1840268,530444,2496780,1841165,1841166,530705,1844241,536593,1847315,401684,535572,2109716,1324308,538644,1845269,272406,530457,663833,927001,668953,265754,1974810,664730,403740,1191964,930076,1843489,2499617,1847331,2106660,1583396,1841189,1841190,531753,533545,3154986,537643,2108716,536620,275756,532784,1843632,1843888,1844016,3155504,1191088,1847728,2503856,536760,5120186,3023418,2368698,1192122,1846334,458765,16285696,11042817,11042818,11042820,12353544,7110665,101761034,12353552,8421400,12353568,8421416,51953712,12353600,14991487]))) (br 48 (br 80 (br 96 (lf 2 [674691,152451,1201029,1461126,680838,152455,1197961,2771849,7230345,11690889,676753,1729425,21396,680853,938903,1991585,805796,152485,680871,4344751,2771905,1723330,418755,4344783,4346831,4346839,403587,667779,137349,665733,657673,657929,659721,659977,137353,661769,1186313,7433,664841,1190153,1190409,142345,535817,142857,1192201,1192457,144393,1718281,657930,269322,402954,797706,144394,661643,660748,399628,138252,139532,404492,144396,146444,140301,402573,662542,139665,659602,4626,8722,405650,406546,267411,271379,270612,140052,402580,664598,135449,923161,1188378,921884,140444,664098,664611,664228,140580,271397,11301,664614,533033,140585,402986,139564,8504,140856,406598,6455296,4358145,4358146,4358148,4882440,35307529,4882448,3309592,4882464,3309608,3309616,4882496,3309648,3309664,5947519]) (lf 8 [1854339,5137283,2116486,936839,5130121,11422601,29250441,47080329,11422625,1332131,3691428,17714095,1199041,9194434,805830,17714127,17716175,17714144,11428832,1321989,7091206,1707273,1577353,3019273,1579273,5118473,924681,3023241,2368009,140297,927881,48115721,5124617,659978,928778,929802,6304906,1181835,1710219,2230412,397580,533644,3026957,795662,2109454,4591889,3028113,136338,929810,13330,9974930,3026963,3679380,7615636,3026965,3026966,1970457,927001,1975833,3289114,926876,4075548,1316002,924706,1584162,3683492,3029029,3026982,3414313,1709610,3290282,2234540,929836,929841,1454131,3024440,1979576,931908,3027013,2106438,4073674,5125330,5125332,1978584,930136,3027297,932962,276587,2635885,2162691,7929862,26116096,17727489,17727490,17727492,19824648,167034889,19824656,13533208,19824672,13533224,13533232,19824704,13533264,98353248,24035455])) (lf 2 [1069957,21382,549766,156551,1197961,2771849,7230345,11690889,1198993,1463185,1201042,4344751,676801,287681,1987522,4344783,4346831,2771920,4346832,667651,932995,1452038,657929,1182985,659721,659977,1186057,1186313,401929,10102793,403721,1190409,1061129,799241,144393,670985,802313,395786,1715338,664715,140428,1325068,667661,666638,134674,5266,399506,138258,12306,146450,667795,661652,665748,9365,536597,9238,535574,922137,136345,400411,929820,2763937,1977506,665635,928932,665637,665638,796201,1189930,9388,1060012,927032,144450,141379,406595,797892,144452,275525,276549,664646,666440,143562,272460,143568,12624,143952,669392,403793,142418,12888,13404,458755,1114118,6455296,4358145,4358146,4358148,4882440,45006857,4882448,3309592,4882464,3309608,3309616,4882496,21413968,5947519])) (lf 12 [3171203,5524357,1461127,7751561,17189769,43930505,70673289,543633,16540561,4215713,12870561,676770,4219811,414628,2118565,26626991,17189808,26633136,4481985,26627023,26629071,543696,4593667,4597763,1325059,4593669,3682309,9968646,3942406,2230537,133513,3017353,4591881,4593161,52041737,7739657,4595977,10888201,1452041,1976841,1454089,7745801,7746057,9582601,6438409,3017226,1969290,4597898,5646858,1454090,4593675,1445004,1445132,4592908,4595852,3025036,1453068,4597773,3020814,1454094,4596882,3027090,6960146,4337683,9313428,4595860,1457173,3676182,793622,4072985,4596890,1452058,3808412,3814428,1449122,3810466,4599970,1456162,276515,1451044,5383332,1452068,8006692,794789,1456165,792614,3682342,2237737,3030313,2244137,1447978,1452074,1447980,662700,663724,1450160,4596144,4596400,4596528,5383472,3551280,7742001,7742516,12460345,9314873,3548729,7743801,1190969,39223296,26640385,26640386,26640388,29786120,250789897,29786128,20348952,29786144,20348968,125747248,29786176,36094079]))
private def r8_k2_t6 : BnbTree := br 72 (br 96 (br 12 (br 18 (lf 2 [1197955,936835,156551,674701,1460116,150420,1197980,680863,2771873,1860514,418723,1201060,287652,2770856,4344744,4350888,418737,1205170,1205172,1198017,936897,673730,943042,2247620,1199049,673740,411607,1722328,150500,936944,267269,1055749,668165,658694,1446918,660491,664846,660499,659732,136212,660501,660502,4377,266777,136217,406553,267290,5914,139555,661668,267301,275493,668710,139432,663976,139816,664232,664360,1190056,1190184,1190440,143656,663849,402985,139818,667818,146474,139436,402732,407596,531502,13370,405857,143970,145506,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,2785298,3309592,4882464,21807144,3309616,4882496,3309640,3309648,3309664,5947519]) (lf 2 [942979,149381,935814,156551,156555,680845,680846,11683730,1198994,2773906,7234450,4346783,4350879,414625,2773922,680868,1991591,2770856,4350888,673730,149450,4346839,398339,665859,396805,1448965,798982,275462,395531,134290,658962,659858,659986,8393746,792082,1189010,140562,1190418,667154,1192082,406034,13074,145426,933010,660499,134292,659604,928788,668692,660501,660502,398617,142361,1189402,136481,663841,145441,146465,664868,144420,145444,660517,660518,137384,137768,139560,664232,664360,1190056,403752,404264,399657,669737,399530,274732,404529,663986,531764,275508,139832,2760890,926010,2499130,668218,145466,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,39895058,3309592,4882464,21545000,3309616,4882496,3309640,3309648,3309664,5947519])) (lf 2 [2249605,1198982,414598,418694,156551,1197964,2771852,7230348,11690892,545684,1860500,2116513,1729442,2773924,4350887,4344751,805828,418756,4344783,4346831,936932,3296231,402563,9475,143491,405763,799747,133387,398347,657676,658572,659724,6689804,1185932,663820,664716,1190028,665868,142348,146444,660493,666638,529554,923154,13330,660499,135956,660501,668694,136217,136729,1185306,136220,139420,664348,533025,145442,136227,407587,662053,399910,137512,139432,663976,140584,140840,403752,666152,533801,141866,931882,2236588,1974572,140588,666668,927282,664248,929976,667972,143956,6455296,4358145,4358146,4358148,4882440,2785289,2785290,35045388,4882448,2785297,3309592,4882464,10141736,3309616,4882496,3309640,3309648,3309664,5947519])) (lf 6 [150406,674695,3819404,4606860,1722260,2771860,1984410,3822497,5917602,2509732,8538024,13257640,13263784,6965185,8539074,4212676,3826628,3427273,1461194,2640847,5392344,13257696,8545248,6960131,6960133,1971206,2240518,2241542,2242571,2233357,2240526,4067858,667666,3552274,2233363,3813652,2233365,2233366,1446169,2241049,1716250,3813404,2234657,2234913,141858,668706,2233379,661796,141476,668708,2235429,136230,1973286,661672,661800,662056,2497320,2237224,1976488,666152,16920616,667689,3029033,3020970,665770,3811628,668724,929976,1451585,2240579,271556,2240581,2238026,667729,667732,1978580,670817,1457380,19562496,13271041,13271042,13271044,14843912,8552457,8552458,14843920,8552465,10125336,14843936,66502696,10125360,14843968,10125384,10125392,47104096,18006143])) (br 96 (lf 1 [19335,542604,674700,150418,150420,542620,150433,545697,1067938,1205156,1329064,2116520,2122664,156593,1330113,19394,549826,1329096,2116552,283604,21463,150497,21473,412644,543728,666627,275459,267269,269317,275461,267270,668678,267275,7181,9229,15373,271374,4626,529938,270866,267283,5140,5396,795668,267285,271382,5145,267545,9753,5146,406554,270625,12833,137762,271395,271397,269350,8488,271016,271144,1057832,9384,9768,403624,798248,5417,403753,9259,271409,139826,271410,271668,14402,271427,143556,274756,14404,10440,10568,140873,143689,141898,11340,3178496,2129921,2129922,2129924,2392072,1343497,1343498,2392080,1343505,1605656,2392096,10272808,1605680,2392128,7258184,1605712,1605728,2932863]) (lf 3 [411523,281479,1329036,2771852,1461140,18330,1197980,414625,4213666,1332132,4212648,6572968,6579112,811969,19394,943042,4082628,4212680,6573000,6573024,4219872,666627,2111491,1053701,1057797,1059845,922630,1057798,1192966,1057803,1060877,929806,14350,267282,8722,1844754,1717266,1053715,1840276,668692,1053717,1053718,267289,271385,1058073,1708186,271388,143644,1053985,271393,276513,1060899,5412,1057060,271396,1061028,1057829,1057830,268840,270632,1057192,1057448,1057832,1059368,532650,1845420,1057073,664881,795698,140466,274482,274994,270644,664628,274484,2629816,666694,277574,272712,1585481,1454674,667860,9732096,6586369,6586370,6586372,7372808,4227081,4227082,7372816,4227089,5013528,7372832,24559656,5013552,7372864,16564296,5013584,10010720,8962175]))
private def r8_k2_t7 : BnbTree := br 17 (br 48 (r8_k2_t6) (br 72 (br 12 (lf 1 [18309,18311,280461,1067922,1336212,411543,280473,549786,542620,25503,545700,1329064,2116520,2122664,1330096,2122672,1329089,549826,19401,281546,804824,1332192,662531,276483,922629,1055750,268299,267278,134290,13331,145427,268309,137238,15382,531489,9505,274977,146721,270882,402978,404002,267299,662692,267301,6182,144422,3151912,6440,8488,271016,271144,402600,9768,403624,403752,530473,399402,10794,137260,269484,143405,406573,145453,270768,8752,10416,10544,275632,268593,143921,12466,532788,795192,536888,405690,9532,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,1605656,2392096,12369960,8962096,2392128,1605704,1605712,2932863]) (lf 2 [680835,156551,1197964,2771852,7230348,11690892,1205138,1198996,1467284,680865,418722,1201060,1467300,4344751,2771888,4350896,156612,4344783,4346831,661507,662531,137221,924677,928773,1448966,667654,660491,265356,658700,8263692,137484,664204,664332,1190028,665868,142092,142348,143372,1192076,1192204,660493,660494,926226,9746,11282,143890,660499,668181,661526,3353,265753,273433,274458,398620,271644,1711137,144417,662562,1190434,145442,662563,399397,146469,661542,5117992,403752,142504,1187369,9770,536618,139436,795948,139440,663984,143920,275760,1188401,927282,1193012,667702,139832,1456185,405562,2236604,2761020,1189052,144444,6455296,4358145,4358146,4358148,4882440,2785289,2785290,37273612,4882448,2785297,3309592,4882464,5685288,22331440,4882496,3309640,3309648,5947519])) (br 12 (lf 1 [18307,18311,280462,543634,1197972,18329,414625,21410,1329064,2116520,2122664,1330096,2122672,674754,549828,1329096,2116552,543700,1332192,138243,144387,407555,267269,400389,140293,1053702,275467,137229,13325,266770,268434,271379,5140,271381,267286,397593,265754,5146,9754,140316,267553,268833,7201,11810,539682,269347,9252,271652,274596,15396,269349,269350,2889768,270760,271016,9512,9257,12585,274985,140842,9388,273452,12460,661550,8368,140848,139569,401970,14386,141492,794808,8504,533560,12856,271422,9537,143681,140482,9412,12612,11334,143430,11337,272721,11346,12498,12632,14436,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,1605656,2392096,10272808,6340656,2392128,4505672,1605712,2932863]) (lf 6 [676743,3819404,8539020,21910412,35283852,2515858,3820436,4613012,3036068,13257647,8539056,13263792,3826628,13257679,13259727,1199060,5526496,2905060,4594691,2237443,1448965,5385221,924678,405766,668678,4601862,2233355,2230540,2231436,6033676,1446924,27793420,9053196,2237580,2237708,2240652,1585420,2233357,2234382,8722,1189394,2107922,2234387,2234389,1184790,926742,664601,669209,664602,3024410,664604,1451164,1451292,662561,2235937,664609,4597281,799266,1457186,2235427,799012,1842213,276517,2234406,9181224,2236840,3811624,1056297,2637353,661546,2235946,664618,663852,1451052,3025068,3679278,2237104,2237232,665776,272944,667952,3810353,3810866,3416244,276532,664632,1454264,4989116,7741756,8135740,4522006,19562496,13271041,13271042,13271044,14843912,8552457,8552458,124174348,14843920,8552465,10125336,14843936,17481768,65847344,14843968,29147208,10125392,18006143])))) (lf 4 [411525,2515845,414599,287627,1984396,1729420,1074061,23480209,2509713,5657489,14574481,8803231,8807327,5661601,21410,1856420,5654440,8807336,2246600,8803287,1449091,271363,2634755,1446917,3020806,1454086,1056907,919692,669708,275469,1447950,1446417,26612753,267793,1448209,8465,402577,2499857,2500113,1977617,405009,1445394,7314,1319058,2501650,3219,1323027,396436,922772,1450132,926740,1451156,1454101,1446934,1314073,399641,398362,536730,924828,2366626,2500770,408610,1454115,2104484,929957,407589,1446950,1448744,401704,795048,1450664,533288,402600,406056,1447209,925866,798892,1194028,401584,532912,795440,2499121,407602,400436,928820,406580,407604,3023160,1843513,3023417,2892857,2500921,2501177,536633,2502969,1978937,13008896,8814593,8814594,8814596,9863176,5668873,5668874,9863184,80658449,6717464,9863200,46055464,9863232,6717520,11976831])
private def r8_k2_t8 : BnbTree := br 9 (br 10 (r8_k2_t7) (br 96 (lf 2 [150403,1201027,805766,1336198,150407,1197962,2771850,7230346,11690890,25495,2646945,2771874,1985444,4344751,2253744,1991607,2509762,19396,21447,4344783,4346831,661763,661509,664581,668677,657802,396042,134666,6165514,660618,399882,138250,663690,401930,1190026,142346,667146,1192458,144394,1456138,146442,2244106,403723,142347,395404,922892,923788,140556,660493,665870,2233617,659986,925842,140050,665106,136212,398484,1971476,660501,144406,136217,926745,1192090,926748,8737,139427,405795,668709,667942,139432,663976,139816,664232,402216,140328,141736,1190440,666792,401578,926890,402986,928812,145452,142382,139824,140593,139570,140466,664884,1450552,140350,6455296,4358145,4358146,4358148,4882440,2785289,39239690,4882448,3309592,4882464,10141736,4882496,3309648,3309664,5947519]) (lf 1 [543622,418694,25479,542602,1330058,3560330,5792650,283553,150434,1067940,152484,2116527,19393,150466,936900,2116559,2118607,2116576,1336288,267267,272643,275459,271365,274437,275461,133514,3210,1577994,138378,270474,139786,272522,272906,142858,4468746,276490,274443,264460,398604,273420,12300,274445,6158,141582,791825,402705,266386,405522,12818,12307,1324308,274453,267286,406809,5146,9242,140442,12314,529692,539937,274467,267301,274470,6696,270760,271016,141864,12328,269353,143401,141482,537900,15406,271152,931120,14128,12337,406833,536754,144436,144692,401592,276801,9540,11337,145481,536908,275032,14436,14441,1114130,3178496,2129921,2129922,2129924,2392072,1343497,20365322,2392080,1605656,2392096,3719208,2392128,1605712,11452512,2932863]))) (br 96 (br 48 (lf 4 [3036035,4612997,2509702,418695,2508681,5655433,14570377,23487369,5661601,1985442,1991586,1461155,943012,1461157,1205158,412583,8801199,1074097,5655489,2511815,8801231,8803279,543716,6966247,1454211,1711110,140294,1444105,2492937,14554121,923913,2497033,1450249,4334601,1451529,403593,1456137,1445386,1188362,404490,143882,1980426,1446923,4592780,923916,924685,408589,1446926,1446161,1446417,2502929,3544210,402578,1451027,402452,1451156,930836,1455125,1446934,398361,663961,8857,140825,799257,2499738,922780,930845,1450276,402084,929956,138278,399656,663976,401960,1450792,402600,402728,1976488,1452328,2501160,667048,3809833,1975593,665129,928041,1713322,668202,400428,1974572,3025965,401713,795313,13008896,8814593,8814594,8814596,9863176,73056265,9863184,6717464,9863200,24559656,6717488,9863232,6717520,6717536,11976831]) (lf 2 [281475,676739,680835,156549,156551,1197961,2771849,7230345,11690889,2778001,805778,1074081,1336226,414628,156580,4344751,2771888,4350896,4344783,4346831,662533,660486,1448966,657929,5116937,660745,8394761,665097,10505,1190409,142345,405769,408585,3594,2235530,664587,1447052,669709,661518,527890,1189010,661523,1447060,139412,142356,661653,661526,658713,8473,274713,142362,144410,406556,667810,144418,669731,663716,665765,668710,2365480,137512,137768,139816,664232,664360,1059112,1451049,1189161,402985,406698,139436,928812,664621,663984,139824,140336,139825,143537,668850,145458,139444,403636,143540,1188024,274744,143928,2629945,1974841,930361,327682,1245189,6455296,4358145,4358146,4358148,4882440,40943625,4882448,3309592,4882464,10272808,18530352,4882496,3309648,3309664,5947519])) (lf 2 [412547,674693,156551,1197961,2771849,7230345,11690889,1461154,1201058,1199012,4344751,1592258,674755,281540,943044,4344783,4346831,4344800,2778080,667651,931843,660485,661509,9222,667654,1324038,657801,1840137,662153,270985,271881,403721,1190409,142345,10104841,146441,1457673,530442,142346,1848458,660491,264332,265356,9484,927884,142348,145548,669709,529422,12302,659857,664081,798737,1578130,1061906,136212,2503700,660501,660502,136217,529689,1193114,660636,406684,144420,799908,661541,5158,535590,8488,664360,141480,3551272,665897,12330,406698,1193132,139568,139824,533808,1192241,1193138,405684,668852,271928,1193144,13752,271546,664770,276677,12873,403018,275032,668257,2818058,327702,6455296,4358145,4358146,4358148,4882440,41730057,4882448,3309592,4882464,11059240,4882496,3309648,23773280,5947519]))
private def r8_k2_t9 : BnbTree := br 33 (br 10 (br 12 (br 18 (lf 2 [935811,149383,935828,1198996,411545,1197978,1201060,2770856,4344744,4350888,2771888,1205188,2770888,4343760,4346832,2778064,2773984,660483,408579,140293,1981445,140294,1981446,666635,665613,670734,660499,136212,139540,668693,136214,403478,659993,1184028,137762,663714,139810,141346,668707,529572,12452,5157,399397,10277,660518,140840,7743528,143528,143656,138281,272425,138282,927786,403756,667948,6705,1057073,399922,664114,273460,401592,664248,664897,141633,408641,403650,670786,15938,669763,141380,143556,142406,405574,403017,141385,403785,141386,141898,141388,143692,143568,666193,144468,145492,274648,1195108,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,2785298,3309592,4882464,2785313,19972136,4882496,20627536,5947519]) (lf 3 [935814,280455,411534,17581970,1854354,4215698,10904466,6575007,6579103,1856418,156578,4212648,6579112,152514,1860546,4212680,6575063,2905056,676834,1053699,1058819,1061891,3423237,1053702,530438,269318,140550,268555,662539,534541,407565,526606,1051794,1053074,397842,17175570,1840274,1057298,1844754,1058834,273426,1585298,1055763,269332,3022100,670996,1053717,396566,538902,267289,277785,1319450,10524,1718300,402724,14628,3030308,1053733,1058854,1057192,271144,4466728,143528,1450538,275498,927020,799788,2238768,534833,1059889,13361,1452594,1850676,4071610,402618,8923194,665659,13377,9540,1058885,664646,1326153,275024,407120,273489,276561,1063249,273492,275032,1061474,2031635,9732096,6586369,6586370,6586372,7372808,4227081,4227082,4227084,7372816,4227089,61915154,5013528,7372832,4227105,34652200,7372864,17612880,8962175])) (lf 1 [25479,542604,1330060,3560332,5792652,543636,21396,21410,287650,414628,2116527,1199024,418756,2116559,2118607,1330128,2118608,676832,152548,272387,11267,275459,146435,267269,271365,273925,141318,800774,272395,2233356,267532,6156,268428,8972,9228,3942412,534668,273548,277644,264717,3598,140814,134674,661010,273938,267283,141588,277525,267286,540185,5146,10266,275482,143516,268834,142370,142882,267299,272421,274982,6312,139688,665640,1453608,143016,12584,402985,13353,141354,401580,1319212,9260,9388,10544,10800,10289,536114,141620,794808,9283,272453,146502,403529,404042,11850,145232,11350,274648,405852,851990,3178496,2129921,2129922,2129924,2392072,1343497,1343498,20103180,2392080,1343505,1605656,2392096,1343521,6340648,2392128,9879632,2932863])) (lf 6 [3564422,676743,3819402,8539018,21910410,35283850,3820434,3036050,152482,2773924,3302308,13257647,5393328,156610,1725380,13257679,13259727,8539088,13259728,1725408,1463266,1840131,4996099,2238469,668677,1718277,1981445,666630,2504710,657802,3804682,10490890,661514,3020938,1972746,3416202,2237962,23472138,3813514,2241034,668682,1444107,267275,273419,2233612,661772,5385484,2233357,2234382,1446931,8535316,2239509,136214,927766,931862,3810585,2232730,1451162,1448990,2234660,2243621,2238502,663720,2236840,664104,402088,8661032,14036264,661545,3024937,4596266,2237610,3811498,1060010,661548,3026220,665649,665906,665652,928052,2236600,1454648,1846337,1190212,1713221,2240838,1058891,665676,665932,1455568,3814484,8323090,19562496,13271041,13271042,13271044,14843912,8552457,127582218,14843920,8552465,10125336,14843936,8552481,42647592,14843968,58114128,18006143])) (lf 12 [1461125,1461127,7751562,3820426,9325452,4606866,673685,3032985,70666145,17189793,7754657,43934625,26626991,26633135,8013761,7758785,9062344,26626000,17195984,26627047,4596739,6958083,2240515,2102277,5514373,4597765,4594694,4597766,4599814,1446922,1452042,2238602,4597771,4592908,1447948,1452044,4597773,4593678,9311378,3029138,2633747,1848339,4591764,10884244,1457300,3812373,4592662,4591129,7748634,3018908,27923489,4592929,4593953,1448993,46934049,7743777,5779745,4600353,14038305,3292705,6431778,3155490,7353378,4594723,17185956,2364453,2107557,4593702,1448232,1581352,4596520,12855336,1454632,42219688,6437416,15344169,7743532,3023536,4860464,1193648,795185,1450673,4859185,274737,795186,533682,1452084,6172852,1189441,3030082,12336322,4597827,1452105,2763338,3156172,2107469,1454416,1454672,1455201,3423331,39223296,26640385,26640386,26640388,29786120,17203209,29786128,17203217,20348952,29786144,252624929,89964584,29786176,126664784,36094079])
private def r8_k2_t10 : BnbTree := br 48 (br 72 (br 80 (br 18 (lf 2 [1197955,412547,674693,676741,414598,152455,2773908,2770840,4346776,4350872,2508705,2515874,149412,156583,943018,1205164,412594,1205172,418743,935873,1205185,673730,150466,676809,935882,1201100,1199057,1070034,1199060,1330160,398467,658437,396294,1186822,666635,660621,134158,404494,658451,138261,404501,136470,401686,135320,135448,659864,135704,660120,660248,139544,663960,1712664,664216,664344,402584,1192088,1192216,1192472,659993,401945,667162,406554,399516,140572,144412,146460,661668,663844,667186,139448,144449,144450,144452,145476,14418,144473,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,2785298,22724632,4882464,3309608,3309616,4882496,3309640,3309648,3309664,5947519]) (lf 2 [938883,1205123,680837,1197958,287622,152455,676747,11683730,1198994,2773906,7234450,4346783,4350879,673698,1991586,680868,1197994,418732,2770882,1066951,676809,545738,1201100,1070031,4346839,1453061,533766,659597,135694,398862,395794,6425618,658578,658962,659602,1184914,662034,663954,139794,402194,144402,669714,146450,669715,661652,663700,145428,407828,658453,1192982,135320,659864,135704,660120,660248,137496,139416,139800,664216,141592,1192088,1192216,397849,922138,137370,399898,925850,2236954,1190042,1192474,137372,144412,928033,142380,139442,140082,402610,401592,1190456,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,34783250,11190296,4882464,3309608,3309616,4882496,3309640,3309648,3309664,5947519])) (lf 4 [411523,411527,1460109,5524370,2904983,5654424,8803224,8807320,2377634,2640802,2511780,1722281,1329068,18369,2515905,5523394,21442,5526468,2511817,2511818,5655504,8803280,3557352,1055747,1320963,1453059,400389,3025925,407557,408581,4598790,1452043,1448974,4626,1444883,1445012,530580,796948,404500,1978516,1453077,1444886,397464,397592,1446296,397848,1446552,1446680,1450392,926488,12986392,2369688,405656,406040,930329,1839642,403482,14362,2494620,1976865,405793,404516,665641,1054250,1321002,403505,1321265,402994,1977394,2501684,270520,272446,1451585,930113,10564,1452101,403526,406092,405840,406096,10577,405844,1849433,931934,13008896,8814593,8814594,8814596,9863176,5668873,5668874,5668876,9863184,5668881,45400088,9863200,6717480,6717488,9863232,6717512,30720080,6717536,11976831])) (lf 2 [935811,149383,1198994,1594260,2770840,4346776,4350872,1067937,1201058,418722,2770852,2249665,287681,811970,2771908,2770888,4346824,3298256,936944,658435,404483,662533,664581,666629,658438,666630,668678,664587,666637,666638,659602,136722,137746,140306,140307,406547,136468,8340,403732,145428,658453,662550,659864,660120,660248,136728,137368,137496,663960,664216,664344,1713176,140440,667800,1192216,930328,144920,399641,664857,922778,137754,402460,143516,408604,402721,10785,145441,664738,142882,141865,661034,140330,926769,402482,665908,140344,665154,534722,141890,145474,143560,143945,406604,535121,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,21676056,4882464,3309608,3309616,4882496,10666056,3309664,5947519])) (br 72 (lf 2 [280451,149383,542603,1198996,2770840,4346776,4350872,1460129,21409,2778018,1069988,156585,287658,1197996,2771888,4350896,2770881,1205186,938954,1070028,2771920,149474,1198056,1055747,669699,658437,661509,666629,1973254,145414,11275,661517,137230,142350,146446,658578,658962,266386,269330,142354,145426,268307,269331,663828,140564,408724,662549,661526,659864,660120,5511192,137368,137752,663960,139800,664216,664344,141464,536728,930072,403993,534682,403994,12826,403740,660769,660644,5412,663844,141350,407590,144425,1189040,141872,664113,141361,8754,1061426,273460,536756,1319480,272568,665912,9786,144452,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,21413912,4882464,3309608,14073904,4882496,3309640,3309664,5947519]) (lf 1 [18307,18311,280461,543634,1329048,2118552,2122648,280481,545697,680866,411556,411564,1330096,2122672,25538,414660,418756,1329096,2118600,1330128,21473,268291,271363,144387,1057797,9222,141318,535558,13318,268299,6158,140302,265362,7186,140434,269331,268436,268564,10388,405780,277525,265238,266648,266904,267032,5656,2365464,270744,271128,9752,6169,9241,8730,9242,277658,528668,274977,267428,403620,136489,271402,8368,8752,665264,12592,141617,143922,533812,1188024,794936,140344,272952,274626,13380,275525,12488,272713,407628,144724,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,9224216,2392096,1605672,6602800,2392128,4898888,1605728,2932863]))
private def r8_k2_t11 : BnbTree := br 48 (br 80 (lf 2 [18307,804742,149383,1067922,1594258,19348,2770840,4346776,4350872,1201057,1467297,943010,1067940,2770856,4350888,418738,943028,1199041,1205185,2770888,1199057,150482,676818,938964,152548,936944,660483,1317891,660485,662533,406533,146437,402438,406534,277510,658443,668685,662542,666643,658580,1051924,659732,660501,267286,273430,135448,659864,135704,660120,660248,6558744,137368,139416,139544,402200,141848,929944,143896,398361,5274,1058076,12572,267294,661026,661668,139556,9508,145444,664232,140840,273448,143528,143656,799017,143913,1188394,408748,145457,402994,145458,141620,1712440,663992,1450552,1189048,403001,406082,142406,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,21544984,4882464,16171048,3309616,4882496,3309648,3309664,5947519]) (lf 1 [411526,18311,543634,807828,1329048,2118552,2122648,545700,418724,1329064,2122664,412594,549825,807876,1329096,1330128,2118608,789507,144387,267269,269317,140293,14341,535558,272395,269325,3086,136206,529554,6290,272403,134420,143636,265237,272406,4248,4632,266904,1184792,5400,8344,270744,271000,140056,9752,796696,274712,537113,10266,141850,398363,397596,15388,267553,9761,666657,268834,270498,9378,273443,5412,275494,8360,9768,534572,401969,14386,8500,10292,8376,1057080,9784,13378,13382,9801,272713,534730,12496,143570,277844,538715,146785,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,10272792,2392096,4636712,1605680,2392128,5029968,1605728,2932863])) (br 18 (br 20 (lf 2 [411523,411526,1198982,149383,2770840,4346776,4350872,1201057,943009,1074082,549796,2770856,4350888,2771888,4350896,1205186,2770888,2771920,660483,924675,661509,1455109,399366,661515,134157,399373,661518,658451,660501,658454,135320,135704,660120,660248,267288,137496,664344,141848,142104,396825,668185,136346,925850,659740,144417,661026,12834,661539,660644,137508,532772,140324,664232,928296,143656,137769,403498,669738,407596,139440,663984,796209,274737,140338,402610,927924,401592,532792,664897,141633,142402,664772,402756,928068,145476,146500,274764,142417,1192152,145506,277860,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,2785298,2785300,14204952,4882464,7913512,9093168,4882496,3309664,5947519]) (lf 6 [1074053,3032966,673671,35276692,3820436,8541076,21914516,13259679,13263775,3822500,4613028,8538024,13263784,5785540,2646980,1329096,1198028,13259735,3822564,2233347,2234371,2235395,5514245,141317,2237446,1456134,2231307,2230797,920078,1193998,2233363,17959956,4067604,2232980,4592660,1447060,14030868,2236692,664596,2762388,1976468,3027092,1455380,1981716,2231317,1182742,922646,2232728,660760,663704,2236824,664856,3816088,660505,3025433,666138,3027994,7999644,1970460,3807516,3811612,3813660,927773,1194013,407585,2241570,2233382,2237096,2237224,665128,272040,1714344,667816,2233897,1713706,407594,670762,1452076,663856,3024176,3550257,145457,7741620,5382452,3810484,665652,1715254,3811388,2500669,19562496,13271041,13271042,13271044,14843912,8552457,8552458,8552460,14843920,8552465,8552466,124698644,24821784,14843936,33865768,10141744,14843968,10125408,18006143])) (lf 1 [18307,152451,18310,25478,25479,280459,5785490,543634,1332114,3564434,2118559,2122655,1336226,21412,152486,1329064,2122664,287682,1329096,2118615,670723,265221,662533,265222,143622,144390,267277,140302,13326,1838098,265362,266770,1446930,398482,530450,399506,270482,402578,534034,927762,536722,273427,136212,1059092,267285,267286,660504,6680,271000,9368,538648,5145,6425,921754,659994,10266,10394,406042,401692,10268,267553,275491,8484,268325,5158,8360,270760,271144,9512,535080,12840,15657,136746,274732,402736,666416,10289,10290,403634,404530,13363,270644,10292,794808,1319482,403771,145468,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,19447826,3063832,2392096,7782440,573488,2392128,1605728,2932863]))
private def r8_k2_t12 : BnbTree := br 10 (br 12 (br 17 (br 40 (r8_k2_t10) (r8_k2_t11)) (br 40 (lf 4 [411523,2515843,3557253,1591174,411527,1467275,1460109,1467278,5268367,23480209,2509713,5657489,14574481,8803231,8807327,3032993,2511777,2508713,5657537,6050760,2642895,8803287,1451139,926853,2235398,533510,15862801,1445137,1970705,1709329,1447441,661777,1450257,1450513,2499857,1453073,2503185,3552273,407569,146961,397842,2500114,2502802,661651,669715,2493588,921876,1450260,408596,1448981,1444886,397592,1446296,397848,1446552,1446680,399384,1710232,401688,401944,1450776,1452056,2502936,145816,408216,3543321,1710361,1450265,3547673,2500889,2501145,931866,660764,401692,1194012,928797,403490,2500772,928940,1450416,1977776,2502320,403508,1977396,404533,139960,1188537,4073531,13008896,8814593,8814594,8814596,9863176,5668873,5668874,5668876,9863184,79085585,26394648,9863200,6717480,9863232,6717536,11976831]) (lf 2 [18307,1205123,1066885,152455,287627,156557,11683729,1198993,2773905,7234449,4346783,4350879,938913,1729441,943012,2770856,4350888,18369,1984456,4346839,527363,143491,1061893,2235398,273419,407565,658446,2231313,3345,921105,921873,659985,8786961,140305,665873,666129,929041,1192465,145425,2235538,140306,145426,664595,136212,2235540,144404,273429,275477,661526,135448,3413016,145432,1712665,405785,1194521,9370,403482,404506,141340,142365,402594,405666,408610,660515,142372,405668,145444,660517,660518,139432,140840,143656,664105,405801,1188010,1189932,663984,664240,533680,140592,11952,139825,927281,1190066,145459,1189940,1056952,664376,927032,2761017,403769,404025,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,39108625,4374552,4882464,19709992,4882496,3309664,5947519]))) (br 80 (lf 3 [2642821,1463174,283527,1853324,4213644,10900364,17589132,1991569,1205138,1854356,2249620,1074069,1069974,674724,2646951,6572975,5006256,1205172,1463236,1860548,6573007,6575055,152535,1053699,1055747,1057795,666117,1059334,668678,1055755,10095628,1051788,1445132,1052812,1053452,1841420,1056908,1058060,1845388,1059084,273420,1847436,405772,274956,2635788,1061901,1051662,791057,137745,270865,534801,1053202,136210,530578,401554,277522,1051667,659608,4376,1053080,1053336,1056920,270616,1057176,1057560,1323288,669336,668697,273562,2232476,3019036,1446940,1840412,1057052,1451164,275612,1454622,140834,666658,139428,1057060,1057448,271528,271656,10536,271401,1453097,1450284,271660,1189425,270900,273592,271929,1056956,3417150,9732096,6586369,6586370,6586372,7372808,4227081,4227082,59424780,7372816,16826392,7372832,7372864,5013584,5013600,8962175]) (lf 1 [418693,545670,25479,542604,1330060,3560332,5792652,152465,543636,2116527,1067952,676802,545732,2116559,2118607,1330128,2118608,271363,272387,273411,530949,404486,272395,264332,1313804,527628,267404,267532,399628,400396,270476,270604,3680268,141452,405644,12556,407564,275469,275470,272913,278033,266770,929298,265235,276501,277014,4248,266648,4888,6424,8472,270744,276120,145688,269849,9753,10265,659612,136476,794780,12572,136734,402977,1322530,271012,9252,403492,9253,141349,141350,8488,534824,141864,142888,274216,142889,272428,402608,536113,141365,272568,13377,272454,15945,537162,12496,274768,15453,720917,3178496,2129921,2129922,2129924,2392072,1343497,1343498,21282828,2392080,2801688,2392096,2392128,10010704,1605728,2932863]))) (br 80 (br 48 (lf 1 [150403,414595,281478,549766,21383,542602,1330058,3560330,5792650,1332113,1074066,1336212,680866,2116527,418738,412610,545730,2116559,2118607,1594327,272643,136197,271365,10757,273413,10502,3673098,265738,266378,266762,137354,530954,270858,271498,141834,536714,12554,537098,800778,265227,4236,268428,11276,405772,146444,265229,275470,135698,266515,271381,4374,139542,4248,266648,4632,266904,271000,9368,1062680,266777,144409,135706,398362,398490,136730,925850,795162,664602,9370,144412,402721,142625,10530,273702,8744,534696,11304,9257,534058,9516,142380,10802,270776,271160,10808,270522,3178496,2129921,2129922,2129924,2392072,1343497,19447818,2392080,5554200,2392096,1605680,2392128,1605712,1605728,2932863]) (lf 2 [21379,549763,287622,156551,1197962,2771850,7230346,11690890,674705,412562,1991572,680854,1069985,418722,1467300,680870,4344751,2771888,4350896,4344783,4346831,661507,664579,661509,1448965,792582,928006,1705482,657546,3148810,659978,8525834,1055242,664074,928266,268299,273419,7436,797964,661517,658446,1717262,1056017,8465,662547,401684,146452,658453,399384,137368,663960,140440,141848,929944,8473,143641,802073,1057818,926874,1189402,930330,137244,924956,660769,8481,667937,669731,404516,660517,139560,1188137,8362,139818,12714,139564,931884,664240,664368,1189168,666416,798512,143536,143664,143920,141617,666673,1190066,8500,11318,2629818,1712698,1319994,2293776,6455296,4358145,4358146,4358148,4882440,2785289,41074698,4882448,6864920,4882464,24690736,4882496,3309648,3309664,5947519])) (lf 8 [3040131,5133190,942983,5130122,11422602,29250442,47080330,3429265,5264274,5131156,2511764,549794,17714095,943041,5264322,2511812,17714127,17716175,11422672,17716176,2773986,3017731,3020803,3017733,3024901,3025925,4069382,15207434,3018890,4854794,1711626,3023370,3024010,35530762,2503178,930826,5519370,5126282,932874,3027979,3020044,141324,8006924,3023885,3017742,3025169,535569,4074769,1192211,1718547,2233620,1191188,3023893,1711126,1194006,1970584,3019416,923800,3023512,1583128,1454616,5123353,7213210,922138,6165530,5124250,537626,2234652,2759708,929057,1975074,4728994,3811874,927779,10366244,3024934,1188264,926248,5122089,1974442,1450538,926890,5121324,6168752,4074801,2762802,5123124,927798,1974456,404024,5121594,1324099,276547,1976644,930116,927814,272584,666184,930889,930384,6094865,26116096,17727489,17727490,17727492,19824648,11436041,170704906,19824656,29933592,19824672,19824704,78037072,13533280,24035455]))
private def r8_k2_t13 : BnbTree := br 80 (br 48 (br 40 (lf 4 [4606851,1330053,1987461,1074053,2253702,414599,2508681,5655433,14570377,23487369,2118545,3433361,2515858,4088724,1467286,3429271,1074081,8801199,3560385,807879,8801231,8803279,2380753,152532,6050775,1444870,662534,15076361,1446153,1446537,399497,2496777,2497033,1450249,402057,927241,405641,2503177,3553289,408585,396426,1446410,1450506,1978506,920587,406539,1445004,1447052,661644,1190156,404492,404493,930829,1186830,142350,1450130,1452562,1446035,921748,401556,399509,926357,397848,1446680,398616,1447576,401816,1450776,3023896,403736,405784,1455768,4067609,398873,4071705,4071961,402457,1978649,922138,1451546,1979420,408732,927009,10401,665889,1453091,402468,402596,1453092,926121,402474,1453098,1975468,666161,1451320,1975355,666685,13008896,8814593,8814594,8814596,9863176,75415561,9863184,22986776,9863200,6717480,6717488,9863232,6717520,6717536,11976831]) (lf 1 [543619,25475,25478,25479,542601,1330057,3560329,5792649,1201041,1205140,25493,1074081,943010,287651,545700,2116527,287665,19378,25522,418740,156609,2116559,2118607,1068007,6275,142339,269317,141445,404485,662534,142342,3935241,1971209,5385,6665,269833,139529,8713,795657,537097,800777,265354,924810,136203,8331,265356,267404,400396,13324,7181,140301,269326,4625,135314,266770,668690,10387,143507,8340,135701,265238,2757656,271128,9240,9496,10776,1578009,5401,5657,9241,402713,534041,536857,136218,271514,406684,15388,270498,270501,267302,533672,1057065,534825,404009,9258,141482,402604,8369,274610,270776,664120,271032,401977,9274,3178496,2129921,2129922,2129924,2392072,19841033,2392080,6340632,2392096,6471720,1605680,2392128,1605712,1605728,2932863])) (lf 252 [165041027,165045125,32918407,165037961,363219849,924734345,1486250889,132008850,16409490,98984851,247620500,40264610,322855844,561400751,363219888,561406896,561400783,561402831,28186627,103689219,132003845,16389126,98965510,98966534,82457606,421923849,98962697,98962953,28184969,40243721,70653193,1153177609,9312777,98968073,40251913,32912393,61225481,32902154,14030858,73275530,98968714,94251146,68687883,30158987,82448652,58594444,188619916,32910348,98965517,98965518,155589778,9314450,115487764,98965525,98962454,18747672,98964248,65935384,98967960,264118809,32908313,32908825,132002073,124662297,98968602,32905244,32906396,32908322,65938594,70658210,2633890,70653987,94252069,4601893,106307881,94249130,32908332,132001964,32907440,98968240,98968368,115484208,65940784,32911664,58597681,32914737,165028018,61218996,94255156,198058296,231089209,165029177,16393785,165030201,165030457,32914493,363266056,49479696,825655296,561414145,561414146,561414148,627474440,5095997449,627474448,820953112,627474464,3184967728,627474496,429293648,429293664,759611519])) (br 10 (lf 2 [1201029,19335,25479,1197961,2771849,7230345,11690889,1067921,807825,1725332,19361,4344751,1987521,1074114,676804,4344783,4346831,2771920,4346832,658435,1447939,137221,668677,2239494,133641,659977,923913,662025,1448969,140297,140553,11675657,1192201,144393,931337,669705,659595,396428,2239628,399373,144397,664590,2763922,669715,136340,399508,665621,658454,659864,660248,137496,140568,927768,668184,145048,397593,1191066,659612,138268,146460,8481,664865,141345,140450,1977506,141348,1715364,665637,403752,928936,1715624,402985,404009,1189930,1188908,664240,141616,403761,141873,665651,404532,1188409,402626,665794,144450,405699,145475,667844,665670,141896,665161,406097,144468,720905,6455296,4358145,4358146,4358148,4882440,41336841,2785290,4882448,3063832,4882464,4882496,22462544,3309664,5947519]) (lf 3 [2380675,2249605,1467270,287623,1853321,4213641,10900361,17589129,1854353,152466,1069972,2771879,6572975,1725377,807874,1070019,283589,6573007,6575055,4213712,6575056,272387,661509,272389,1054726,665606,3015945,1051145,3017737,1052937,1053321,268425,662153,271625,11675657,1454345,275465,1838090,1054218,1841674,664074,664714,1451530,4204554,6171786,1847434,1847818,2231307,1849355,2238476,1846540,1057933,1051662,268307,661779,1840276,1052821,1059862,267544,267800,1447193,3416601,1839258,1446426,271898,1061915,1052828,668700,663714,271650,1846818,1058851,271652,272420,1846436,1058854,664360,1452584,2633128,273580,2632880,272433,1059121,272434,665778,665400,1846584,272445,665669,272454,669770,275534,665937,274769,277588,589825,1638409,3342353,9732096,6586369,6586370,6586372,7372808,58114057,25608202,7372816,10010648,7372832,7372864,36094032,5013600,8962175]))
private def r8_k2_t14 : BnbTree := br 48 (br 10 (br 20 (lf 1 [412547,542597,19335,1329048,2118552,2122648,1067937,152481,283554,1329064,2122664,150452,549828,1329096,1330128,2116576,1336288,535555,400389,1055750,134155,10251,267277,265230,267283,265237,271382,266648,1184280,135832,1971224,5272,6424,8344,8472,270744,271000,10776,538649,274458,143898,529692,533666,271906,14372,10277,267302,8488,141608,10792,12456,401705,268588,9260,10412,405809,14385,12338,270516,139448,139576,664120,533820,10428,274620,926782,140865,275009,272962,271430,272721,12641,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,1343506,1343508,10666008,2392096,5816360,1605680,2392128,1622088,2408544,2932863]) (lf 1 [411525,18311,5785492,543636,1332116,3564436,2118559,2122655,545700,1329064,2122664,549828,1329096,2118615,1332192,143363,800771,265221,141829,660486,272390,265227,267275,266765,273422,267283,1575956,265492,266388,2233364,1975316,271636,667668,536724,271381,266774,266648,266904,922648,5400,10392,536856,5145,7705,273945,9242,11802,921884,268444,530716,139548,929313,8738,143906,267302,12840,533033,9258,273962,137388,271020,664622,401588,8500,794808,532792,271160,795708,271548,140604,403644,402494,271938,141379,12355,141897,146764,539218,15700,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,1343506,18923540,3457048,2392096,7520296,1605680,2392128,4636744,835680,2932863])) (lf 1 [21383,542602,1330058,3560330,5792650,543636,545698,19364,19367,2116527,543666,412596,549826,2116559,2118607,1199056,19410,2116576,1336288,136195,272387,406531,1055749,1055750,264714,3804170,265354,267274,5258,268426,270474,139786,534026,403594,10762,929802,536714,277515,277517,267278,274451,9236,143636,265237,274454,4248,2626584,270744,403224,10392,536600,800024,136473,397466,398362,2499610,140442,537114,5148,402716,535841,14369,274467,1191204,267301,271398,8360,271016,404777,664106,9260,404524,143665,12340,794808,270904,271546,274502,272978,12370,12628,720914,3178496,2129921,2129922,2129924,2392072,1343497,20234250,1343500,2392080,1343505,1343506,8044568,2392096,4374568,1605680,2392128,2277448,6209632,2932863])) (br 10 (br 20 (lf 1 [18310,543622,18311,280459,1329048,2118552,2122648,545698,1329064,2122664,1330096,2122672,281537,418753,25538,936900,1329096,1332192,265219,269315,271363,662533,271365,269318,273421,268302,274451,265237,265238,659608,4376,4632,267032,791576,5528,8472,8728,406040,137497,9241,143385,137754,270490,266396,137500,136481,136354,268834,268323,267428,267556,404516,268325,8488,270760,8744,271016,9384,532780,8368,8496,8752,271152,533808,534833,15922,139576,533561,402494,405833,534732,536788,12898,1638424,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,1343506,1343508,10272792,2392096,5685288,6209584,2392128,3457096,2015328,2932863]) (lf 1 [411525,18311,5785492,543636,1332116,3564436,2118559,2122655,545700,1329064,2122664,549828,1329096,2118615,1332192,1063939,136197,5637,137221,1055750,265227,270861,271374,268307,1707028,265364,265492,3413012,6420,270612,533524,10388,404756,12308,12564,6165,140309,137238,12310,136216,9240,533784,930840,5145,9241,5146,11802,1052828,399644,141468,403740,141857,797730,273954,14370,276515,267556,271396,274469,271398,8488,9256,11305,143913,144937,143914,405804,270768,271024,270897,140337,402612,1319100,794940,795708,10556,402494,274502,10825,536780,141905,1638424,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,1343506,18399252,4243480,2392096,8175656,1753136,2392128,5554248,2408544,2932863])) (lf 1 [281475,19335,542602,1330058,3560330,5792650,19348,287636,545698,2116527,1330096,2122672,549826,2116559,2118607,543698,281556,1332192,527363,12291,265221,267269,271365,136198,531462,145414,1707018,266378,4618,1579018,270858,2630666,533642,534666,798730,405642,12299,145419,268301,265230,268307,6420,668948,267285,274454,4248,266648,5656,1447960,271000,140696,398617,9241,135322,398874,664602,534042,143898,140315,9244,402716,9249,402721,9252,1058084,274469,137254,11302,535849,271152,10800,12464,402737,12593,270770,12338,533812,794808,795192,401594,8762,798778,12628,275042,720914,1638424,3178496,2129921,2129922,2129924,2392072,1343497,20889610,1343500,2392080,1343505,1343506,6078488,2392096,1753128,8568880,2392128,5423176,5161056,2932863]))
private def r8_k2_t15 : BnbTree := br 72 (br 10 (br 20 (lf 2 [1197957,936837,150407,2770840,4346776,4350872,1201057,2770856,2771888,1984450,1205188,673737,2771920,4343776,4344800,2778080,1444867,667651,1313798,268294,405510,667659,134157,408589,668686,667667,396309,145429,403478,143382,135448,659864,660120,660248,136344,136728,663960,140568,2895896,922905,141593,1194010,6171,536603,1184028,535582,136481,927265,141857,398498,661026,535588,799780,145444,932900,139944,143656,136745,143401,6449,662065,272689,268850,401970,143410,13364,1712312,141633,666177,141890,408642,140484,664900,12357,277573,670790,140617,142412,142417,143441,667985,275026,537185,538209,143970,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,2785298,2785300,19316760,4882464,4882496,3309640,16040032,5947519]) (lf 2 [411525,156551,673677,11683732,1198996,2773908,7234452,4346783,4350879,149412,1201060,2508712,156610,680899,1460164,1198028,4346839,4343776,2778080,2231299,660485,137221,665605,400390,404486,1193990,661515,141326,144398,145934,667667,1182996,1184916,922900,399508,139540,1189012,926996,142356,666772,10366996,658453,669718,135320,660248,137752,139544,534552,1192088,930072,7223832,668185,408089,1454107,921756,139420,403998,144417,1195553,268322,15394,2244130,667683,668709,137258,1188140,141488,12336,141873,409137,662066,141362,535602,139572,401592,664248,1980993,404034,667718,143946,12368,928849,1195602,144482,144484,1245207,6455296,4358145,4358146,4358148,4882440,2785289,2785290,2785292,4882448,2785297,2785298,40026132,11583512,4882464,4882496,3309640,19841120,5947519])) (lf 2 [150407,1197962,2771850,7230346,11690890,936852,1461154,1201058,4344751,1199024,543682,1205186,4344783,4346831,2116560,4344800,2778080,267523,792579,929795,665605,1457157,2243590,264586,1575434,2624522,923786,1186314,141322,667146,9973770,930314,265227,267275,658445,6158,533774,274451,13588,662549,10262,536598,135704,4861976,4470040,1717656,139545,929817,1183898,136218,270874,1189018,665114,1191964,791582,1455393,670755,661796,799012,800036,660517,10534,536614,137384,403624,143528,1195305,661034,9770,408876,139568,664368,405682,12595,139448,664248,2241857,145473,9794,141506,666691,928836,408644,802116,272970,143562,144716,403793,535122,145492,143713,407651,144484,669798,6455296,4358145,4358146,4358148,4882440,2785289,39763978,2785292,4882448,2785297,2785298,12107800,4882464,4882496,3309640,24035424,5947519])) (br 40 (br 10 (br 20 (lf 1 [543621,411526,18311,1329048,2118552,2122648,21409,414626,1329060,1330096,549825,1329096,2118600,1330128,2116576,1336288,265219,531459,12291,10245,143365,13317,271366,142342,273419,274445,265230,271379,265237,265238,4248,4376,266648,266904,135960,8344,270744,8728,271000,926744,143512,274712,533017,528538,538652,271390,10529,142369,14369,267426,268834,14374,140329,137386,139818,9258,6188,137516,139436,13488,268593,139572,139448,664635,9793,271554,670786,272708,277574,140873,10314,406090,10444,12364,141905,146769,12370,12372,144468,929880,143713,12897,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,1343506,1343508,9748504,2392096,1605672,2392128,5292104,4112480,2932863]) (lf 1 [149381,21383,280461,5785492,543636,1332116,3564436,2118559,2122655,542625,18340,414628,542636,549828,1329096,2118600,2118615,1332192,1061891,268805,402437,1061894,277515,264718,265235,2231316,5396,269588,2237460,9876,141332,2633748,405652,265237,268310,6680,8344,406552,275864,539161,9242,403994,528540,4380,399516,794780,270620,274716,11809,11810,1063458,274467,143397,14885,273446,7209,9257,273961,400426,271024,14385,533554,8372,143672,146497,271938,275010,13378,14402,275523,272454,2371656,12872,538697,539210,141644,272977,147025,278098,1454172,12897,720919,3178496,2129921,2129922,2129924,2392072,1343497,1343498,1343500,2392080,1343505,1343506,20234260,2539544,2392096,1605672,2392128,8306760,7913568,2932863])) (lf 1 [19335,542602,1330058,3560330,5792650,19348,281494,19362,545698,2116527,1199024,150466,549826,2116559,2118607,1067984,2116576,1336288,268291,271363,276483,274437,668677,134150,271366,11270,274438,2493450,265354,4618,7178,1188874,403594,2764810,536714,269323,271373,3086,135438,140307,12307,266516,9236,664852,265237,4248,266648,266904,6680,8344,270744,143896,1586456,145176,137497,1053210,1451034,140826,143898,536604,267553,797985,9252,271398,6441,404777,143530,533804,9265,402737,12466,14386,401716,270520,405569,274753,534852,671044,275525,272454,143432,12488,143689,276553,275788,12880,12369,537940,536662,3178496,2129921,2129922,2129924,2392072,1343497,18792458,1343500,2392080,1343505,1343506,5423128,2392096,1605672,2392128,3719240,7913568,2932863])) (r8_k2_t14))
private def r8_k2_t16 : BnbTree := br 9 (br 17 (br 12 (br 18 (r8_k2_t15) (lf 8 [942983,5130122,2118538,1598346,47073170,5131154,11424658,29254546,17716127,17720223,2511778,2511782,7620520,1460138,2515906,1467332,7620552,1984458,17716183,17713120,11428832,1448963,4600835,3028995,3017733,3026949,1980421,932869,3017734,922886,1455110,3554310,3026955,3026957,3026958,27659282,3543186,1450514,4596882,5121554,3025042,1452562,29241362,3554834,3017747,924692,9320724,932884,3030037,3030038,3019416,923928,926232,3023512,928024,19279896,1454616,7223576,924697,1977369,1980441,7737498,9310746,11411610,4071962,5126428,3026979,1971492,406566,4073769,929833,405546,929836,4075820,5126449,3021362,928946,408627,929844,932916,3551800,3030083,3024196,3027014,405833,929873,932177,3554388,5124312,6697051,406626,1114128,1114129,7667731,4653080,26116096,17727489,17727490,17727492,19824648,11436041,11436044,19824656,11436049,172539922,68337688,19824672,19824704,107266144,24035455])) (lf 3960 [518933383,2595112844,5709384588,14533153676,23356924812,1651395474,424561556,2595115940,8823655343,1102859184,2306755506,2306755508,3827846082,2595120068,8823655375,8823657423,1102859216,778456020,8823655392,5709390816,1557016579,3114155011,1401297925,1557016581,1712732165,1557016582,3114152966,518926346,5190333962,1557016587,8823639052,1557007500,2076052748,1557008652,1557009548,518920332,1037966348,1557013132,1557013772,518925324,19360264204,1037973772,155589645,1401306125,1557015566,518921234,2595104274,943599634,1557007379,1268650772,1557016597,1557016598,518918296,1557008792,1557009048,1557012888,518924568,7629844504,2595106968,8460318232,3633198872,518921753,518925337,518919706,518918300,4152234268,4671283356,2076061980,518925342,4671288865,288241702,1037975081,2595109930,2076059820,518926385,882258481,674642993,288234034,518922552,363215937,674643521,1362373186,194521670,1362376774,518927433,2076065353,1037975114,518927953,613298258,1462645330,259403860,518926680,259405924,2011234324,2011234325,1102905366,3633250328,12976029696,8823668737,8823668738,8823668740,9861758984,5709398025,86774824972,9861758992,5709398033,39317585944,9861759008,9861759040,51709788256,11937955967])) (lf 2 [149383,411530,411532,11683729,1198993,2773905,7234449,4346783,4350879,149409,1201057,2508712,1205185,2770888,4346839,4343776,2778080,928771,1192963,1320965,275461,408581,2231302,664714,141450,12426,1063946,667659,271500,143372,1061004,407692,667661,667662,2886673,658705,134673,659729,267537,662033,1186833,12202001,664082,1587346,277650,666643,924820,1192212,408724,658453,658454,660248,399384,137496,139544,664344,140824,141464,2633752,6699160,1708313,6425,139545,1188377,666137,407578,923804,141341,2240542,5409,143906,667683,398500,2242724,136229,408613,529705,12329,15402,137260,137388,669740,139568,532912,801970,140596,143412,930360,271937,1981634,13379,664900,667717,12361,143434,538828,665937,408786,408788,539733,1114123,458776,6455296,4358145,4358146,4358148,4882440,2785289,4882448,41205777,16695320,4882464,4882496,27967584,5947519])) (lf 1 [287619,25479,542601,1330057,3560329,5792649,150417,283537,287633,281492,19361,545697,2116527,150448,543665,936897,25537,2116559,2118607,2116576,1336288,141315,405507,272517,668805,662534,277510,1707017,266505,266761,530697,270601,272649,141833,11273,5124105,536841,406025,539913,1326090,265227,266508,270604,271500,141580,265229,265230,266513,266770,398482,7186,12306,143506,274451,12308,274580,406676,274453,274454,4632,267032,5272,8472,270744,10776,1847320,1979544,397849,529945,270617,795161,537754,536604,268833,11298,12834,274467,274469,406698,15530,140468,10434,406724,276549,274502,12362,408778,12364,408780,12369,146516,538328,407651,13414,196618,1376280,3178496,2129921,2129922,2129924,2392072,21938185,2392080,8044568,2392096,2392128,14991456,2932863])
private def r8_k2_tr : BnbTree := br 24 (br 40 (r8_k2_t5) (br 80 (r8_k2_t8) (br 9 (br 17 (r8_k2_t9) (lf 9 [2246531,1066887,2246541,52971409,5786513,12866449,32924561,19944351,19948447,5788577,12863400,19948456,1856449,5792705,12863432,19944407,8541152,2249697,3412995,9219,1714179,2634755,3412997,1454085,5387269,661510,9714694,1706506,2888202,6826122,1059850,2106379,1189899,3410060,531596,2761868,1058828,4597900,1062925,3423246,3411217,3412625,56235025,35923985,1059857,1062929,4068882,8658066,1709075,1583123,1578260,4593684,3418260,1062932,3423253,3413014,2238618,5777564,1843745,5773474,3420322,3420706,3418147,9837732,1055782,2238502,3416488,3416744,1057960,1058088,1058344,17967144,4202793,1451561,398890,401962,3025066,1054764,3417392,1055794,4597938,2238515,10496180,5777976,8528185,10363449,2369081,8136761,5777721,3418182,1058121,534089,1061200,4600152,2243684,5046283,29392896,19955713,19955714,19955716,22315016,12877833,22315024,202424337,15237144,22315040,115130408,22315072,71090256,27050111])) (lf 1980 [259416967,1297500041,2854636425,7266521993,11678409609,1297501073,1297503121,1297503137,4411771823,1557023664,1037984705,4411771855,4411773903,2854636496,4411773904,2162578400,691950561,230556803,1600268291,497298435,778445957,778450949,778451973,778441734,1557019654,778438921,778439177,778441225,8621790217,1297488393,800070921,8200792073,345909769,778440202,778441866,1297488906,1009132555,1009129740,1297491212,259402764,288240780,778451981,778449934,259405841,1535382674,540552338,778446867,259396628,518919316,1297493140,86382613,691940501,778441750,259396633,1037971993,1297493146,518919324,317071777,28713505,605427874,518924450,1268657314,461254818,172890147,259401763,345912483,691935396,605429924,778445092,778446885,778446886,778445608,518924072,3604359208,237775144,1816538280,1528176937,1903043113,893789225,1297491497,144058921,800075049,1297492010,1297492012,1557014960,259401778,28718130,518922808,237777978,518923458,28715586,461255747,144060612,259404868,778451013,259404104,749616203,259404368,1153316560,778447441,1059597394,43136083,1037971801,1211039754,6487965696,4411785217,4411785218,4411785220,4930830344,43282513929,4930830352,3373695000,4930830368,15500492840,4930830400,24164352080,5968937087])))) (br 96 (br 9 (r8_k2_t12) (r8_k2_t13)) (r8_k2_t16))
set_option maxRecDepth 8192 in
private lemma r8_k2_ok : checkLayer (r := 7) (cd := 5) 2 (VTree.ofFun 7 (fun a => (maskWeightFast r8_ws a : ℤ) + (2 : ℤ) * (2 : ℤ) - (29 : ℤ))) (0 : ℤ) (patGens 8) r8_fi r8_prev r8_k2_fc r8_k2_tr = true := by decide +kernel
private def r8_k3_fc : List FCutCert := []
private def r8_k3_t0 : BnbTree := br 24 (br 40 (br 48 (br 72 (br 80 (lf 1 [542595,150403,811909,149382,1074057,25483,418700,25485,25486,411537,804754,150418,18323,281492,283540,18325,21398,283546,283548,18337,543649,283553,152482,811938,19363,1066916,21413,21414,280490,281516,281521,149426,25522,280500,542648,1070017,150466,807874,18371,1067972,19397,19398,281545,281546,281548,412623,280529,280532,1329120,280545,281570,280548,1199079,149480,543728,535558,264330,267402,272650,133260,275468,265364,2916352,1867777,1867778,1867780,2129928,2129936,1343512,2129952,1343528,1343536,2129984,1343560,1343568,3195007]) (lf 1 [411523,281478,280457,150409,21385,1069962,21388,18321,412561,1066898,1069972,18326,283545,283548,152481,549793,412578,545698,149412,280497,280498,280500,411576,1066945,411586,549826,807876,156612,152521,283594,21452,2377680,2380752,1598416,1329120,21476,149480,272387,272389,407557,403462,272393,10251,395404,10252,272524,10253,10254,10259,10261,272410,142369,10275,272420,10532,273444,10277,10278,272425,272426,272428,10296,10307,10309,10310,14409,141388,274640,274768,143954,275540,2916352,1867777,1867778,1867780,2129928,2129936,1343512,2129952,1343528,1343536,2129984,1343560,11583568,3195007])) (lf 2 [150403,414595,676741,1330057,1722250,412554,152459,938892,152462,936849,935826,412562,935828,545690,673692,1332127,1460129,414625,149410,1985442,1199012,943012,674729,674732,1198008,2247617,412610,1729474,2249668,3295176,4869064,4871112,412624,2249680,2509792,926723,926725,926726,143366,406534,3337,666121,1181836,142349,664594,140307,664596,402708,140309,140310,664601,142369,140323,140325,140326,664618,664625,664626,664628,140355,140357,140358,667848,668232,145480,665929,145482,669772,668753,667992,5931008,3833857,3833858,3833860,4358152,4358160,2785304,4358176,2785320,2785328,4358208,23248968,6471807])) (lf 1 [280451,412549,412553,411530,412556,549777,804754,281492,680852,280476,549791,1066913,280482,545698,18339,152484,156580,287657,287658,2377648,1594288,2384816,149441,811969,1066946,149444,150468,1332168,1329104,280532,1332192,149480,399363,268293,268294,407558,133385,268297,265354,6282,14346,6155,395404,6412,6157,6158,6163,6165,6166,268314,11298,141476,275492,6181,6182,268332,8624,8752,8880,9008,271536,271664,271920,10416,272688,11312,143536,143920,143665,11314,12850,142388,12596,401976,12472,2916352,1867777,1867778,1867780,2129928,2129936,1343512,2129952,1343528,11583536,2129984,3195007])) (lf 2 [676742,936841,1205129,2247562,1722252,156556,150418,1201042,1461140,418714,680860,1199009,943009,674722,152482,676772,3295144,4869032,4875176,2778032,418740,149441,1729473,2249666,1460164,674756,2771912,674761,2509776,805856,543716,1184771,405507,922629,668677,922630,138251,142348,144397,144398,134417,1184017,529681,5649,667666,136211,660500,136213,136214,660505,143395,928804,407588,136229,136230,661800,139688,139944,140072,664872,665128,141352,665768,665896,666152,667816,669737,12842,530604,12337,143412,139448,667960,5931008,3833857,3833858,3833860,4358152,4358160,2785304,4358176,23248936,4358208,6471807])) (lf 1 [156547,18309,152453,418694,673673,152457,25481,150417,549777,1069970,543636,414612,1591192,2380696,2384792,21409,414628,1329064,287657,287660,1336240,935873,25537,543682,411588,152516,1332168,21449,21450,281552,938960,1332192,396291,7171,396293,265222,528522,4618,268426,3083,135436,401676,276492,11277,3086,135697,5395,3093,3094,266392,266520,4504,4760,4888,268824,8600,8856,8984,140568,272536,10520,272920,274584,274712,274968,14360,266521,270874,144412,14364,11298,136484,273458,140472,141624,275532,2916352,1867777,1867778,1867780,2129928,2129936,11583512,2129952,2129984,3195007])
private def r8_k3_t1 : BnbTree := br 4 (br 8 (br 16 (br 32 (br 64 (r8_k3_t0) (lf 4 [804739,412550,805769,21385,1856394,2639756,3164049,2508690,3034004,5657496,4212641,280482,4213666,3560356,3951528,18352,2378672,26625984,6704064,16667584,3564480,9849807,9851855,9849831,1451011,1060867,1452037,1454085,406533,664582,1320966,797702,401673,401929,2504713,1188362,1323146,401419,1312908,405516,401421,401422,8722,1451154,275474,401427,1446932,401429,401430,1450009,1450010,1450012,270625,401443,271396,535588,401445,401446,8488,1450025,1318954,10282,1452076,1450288,1451312,1450033,1451058,8244,1319988,1974456,401720,1451585,928065,927938,406082,405571,403652,1454404,537668,405573,403526,406608,406610,1323092,12500,930392,11960320,7766017,7766018,7766020,8814600,8814608,8814624,59162688,13025407])) (lf 4 [149379,1067910,3164041,936841,18314,2378644,5654424,26625952,6704032,3560352,16671648,9849775,9855919,1329088,6704064,549824,2909121,542658,4605892,4737992,4999120,9849831,529411,1580035,929795,1972229,1454085,1971206,274438,266505,2099722,1447946,663690,397323,919692,264460,2494604,534540,399373,397326,921873,2503697,1446034,2363922,140306,267283,12307,397333,405526,1445913,528922,798746,790556,536604,401824,402080,402208,1451168,1451296,9760,1452192,1452320,1452576,404512,398625,1977378,929954,12834,398371,1450276,405541,6182,269350,530984,1323560,1456169,931882,1450284,1320496,794929,536881,794802,533554,799028,405688,11960320,7766017,7766018,7766020,8814600,8814608,59162656,13025407])) (lf 2 [673667,935818,13256592,1723280,3298192,8283024,4871071,4875167,935840,3302304,1725348,2246568,4343744,1729473,2770888,3822543,4871127,935904,927747,134149,923653,138245,141317,1182726,400390,662025,532745,667657,14345,399370,667658,141323,395404,268428,403468,800780,133133,137230,135568,135824,135952,660624,661008,139664,139920,140048,664720,664848,140816,667920,668176,144400,396561,143377,930833,658578,921746,397842,138259,397588,401684,665748,403732,134165,142358,137496,667800,145434,663836,401953,666145,1188386,404514,401960,665642,401584,402992,270641,404530,141624,5931008,3833857,3833858,3833860,4358152,29540368,6471807])) (br 16 (lf 2 [1722248,3296136,8278920,13263752,674706,936852,412576,3826592,1725348,4869039,2771888,3296192,943040,680897,4869071,4871119,1856464,2378720,412647,398339,400387,664579,658437,926725,134150,138246,1190918,133512,133768,133896,135560,135816,135944,530568,661768,268808,139656,139912,140040,665736,274440,667784,667912,143880,145416,657673,135433,397833,398857,139529,134282,926218,931850,136203,658700,660748,665868,134157,136206,532753,1586193,136722,402450,4372,267284,660628,664088,140568,406040,5145,270617,663708,925985,402721,665633,139426,664738,665122,10274,401960,666152,9265,271412,401592,5931008,3833857,3833858,3833860,29933576,4358160,6471807]) (lf 4 [3557256,6704008,16667528,26633096,3558288,6706064,16671632,3560352,4613024,9849775,1987520,3564480,9849807,9851855,9851863,929795,2503683,2496517,926725,920582,2504710,395272,396040,398088,402056,1452552,1454600,920841,1970697,1447177,395402,921738,793098,1452042,536714,395275,395276,919692,1970444,923916,397325,395278,397712,1447056,1447440,401808,402192,1451152,798864,1454352,3552528,1451281,1451537,2494994,1446930,139794,145554,401427,1445012,396564,1057044,1326100,401429,397976,4599832,1970332,270625,139809,797729,2499618,1450152,2498856,794800,1450544,1451057,402482,535604,2499128,2112577,408642,1452369,11960320,7766017,7766018,7766020,50249736,32817168,13025407]))) (lf 1 [13387652,805764,2511748,6710148,1592207,4084623,6579087,1592231,2378671,1592263,4084679,2378703,2380751,2378727,515,396291,136195,529540,5380,399492,138372,139268,8324,271492,10372,403716,273412,797956,274692,144644,15620,269317,406533,134150,5126,402438,2440,8968,1058824,141448,406152,135177,530441,10249,14345,4618,268810,536586,6155,133260,136460,139404,274444,12813,10766,4496,4752,4880,267792,8592,139920,140560,274576,13328,528401,139793,267282,271378,276498,265364,265492,274452,14357,4118,532760,270492,795169,143905,1059874,268580,270628,142372,270504,141864,9520,271920,13104,402481,139832,10306,2916352,1867777,1867778,27049988,3195007])
private def r8_k3_tr : BnbTree := br 1 (br 2 (r8_k3_t1) (lf 1 [13387650,805762,2511746,6710146,1592207,4084623,6579087,1592231,2378671,1592263,4084679,2378703,2380751,2378727,642,263298,1538,133250,265346,267778,925186,270850,1319938,271490,535042,11266,929794,406530,276482,407682,267267,404483,531460,663556,272388,11524,1029,529413,265478,405510,268808,402184,272520,272648,274568,669705,135306,135690,137354,139402,12810,395275,268300,8460,274444,13580,139277,133134,4496,4752,4880,267408,8592,271888,13328,397585,267537,266770,267282,270482,270355,795924,143636,8213,4118,8856,1061144,12824,135195,266524,401440,401952,403488,141728,532769,141345,8738,10786,140580,141348,401584,401968,8241,270898,277058,537162,2916352,1867777,30064642,3195007])) (br 2 (lf 5 [67389313,4475777,12997505,33973121,8407951,20861839,33317775,8407975,12340143,8408007,20861895,12340175,12342223,12340199,525057,1838337,1840385,1840641,530433,1841409,7741441,1844481,2762753,3156481,1846529,5257217,7092737,1184771,3156995,1182724,1056900,3683460,3422212,1580037,2761733,527366,3158022,1841672,533256,1845384,4206728,1849480,145928,3148297,1847817,538633,1313930,659466,2234506,1187978,526347,1183884,271500,2107532,1847308,537613,526350,1183760,528784,529040,529168,1840272,1844752,1847312,537616,1184273,529681,3809553,1840146,3810322,528403,1183892,1187860,529429,528406,1712792,1847576,1325208,397849,659483,3149980,2236576,1451168,2238496,534944,3154082,1845282,534690,3940516,532904,1845544,537256,13482,1843248,5775920,140337,1450168,1848386,13000,14974976,149078017,9732098,16302207]) (lf 8 [107890561,7228289,20861825,54420353,13519759,33444751,53371791,13519783,19811247,13519815,33444807,19811279,19813327,19811303,34341121,1966593,3017985,3021825,928001,4336129,929793,3027457,3027969,1979649,2897409,918146,790018,1184898,3020290,923650,2630786,4072962,8005634,16385027,6428675,8788995,5123075,4075523,275459,3017860,4069636,927876,5122308,5116933,3020805,3148806,537606,3291142,137736,926216,1968393,3279369,3805449,1708554,2496650,2759178,926474,927882,8396811,1843339,5122059,1718283,135436,1316876,399500,5120140,1845260,927885,919566,1576976,922000,922256,922384,4464656,3024144,3027216,930832,3023121,3023889,3026961,3020050,4075666,925715,1187860,1057812,271508,3026964,921621,926742,6688792,1315352,2105500,1183901,7873952,141984,925985,1974817,4860193,5120546,6038564,5120296,926120,926249,665641,926384,2236467,24018944,235847681,41205762,26132607]))
private lemma r8_k3_ok : checkLayer (r := 7) (cd := 1) 3 (VTree.ofFun 7 (fun a => (maskWeightFast r8_ws a : ℤ) + (2 : ℤ) * (3 : ℤ) - (29 : ℤ))) (0 : ℤ) (patGens 8) r8_fi r8_prev r8_k3_fc r8_k3_tr = true := by decide +kernel
private def r8_k4_fc : List FCutCert := []
private def r8_k4_tr : BnbTree := br 0 (br 1 (br 2 (lf 2 [1205123,2246532,3429256,414601,1723274,1729420,1984400,1461136,545681,674706,1467284,2249624,152473,152474,152476,543648,2249632,811936,1729441,1729442,1467300,1854376,156585,156586,156588,19375,2247600,150449,149426,3558336,674753,943041,1722306,543684,149448,1985480,150473,152524,1984464,152528,149458,2642903,673752,2246624,149473,149474,152548,673767,1592295,673768,674800,132228,662532,393989,133637,135685,139269,133126,267270,6662,6664,141832,657673,141449,1057297,140562,5406720,3309569,3309570,6996095]) (lf 4 [61228930,4606850,12473218,31351682,7752591,18764687,29778831,7752615,10898351,7752647,18764743,10898383,10900431,10898407,1442434,3015682,394370,1538,395394,265346,396802,397442,398466,398850,3020802,6274,401922,4334594,402562,2500098,5384194,403586,1453058,1585282,406018,401411,1976323,395524,3545348,1580036,799748,401413,405509,263430,397318,1184774,274694,2492424,6152,268424,1456136,2313,1446153,1323017,3016842,2361866,659978,1974284,1323020,2760720,2241808,1839250,925842,398612,537620,1970456,2367640,925976,1581592,8217,397338,3548448,2500896,404000,1056801,2498852,140324,3287336,1319472,401460,12609,1192010,10911744,6717441,132825090,14073983])) (lf 10 [153241473,11684737,31347585,78537601,19549071,47076239,74605455,19549095,27413423,19549127,47076295,27413455,27415503,27413479,3801857,1180929,1182209,2886657,9047297,1183233,8786177,1184257,4854785,1185025,1185281,3414273,9050625,3808257,1188097,7742465,6038785,8005121,6432769,1190145,9054721,3812353,4206849,1192449,3814401,6436865,1181826,133634,2624514,1184258,2495618,1185922,4727810,2500738,5122179,1192067,1180804,3544196,4069380,7743492,2493445,2236421,1454085,132102,919558,1187846,4983048,7348232,6693384,3409929,135689,2496521,270601,926345,5116042,2498698,5113996,3805324,7999504,4198800,2498576,2499601,2101266,1709074,3543060,1446932,2240532,925976,2236952,7745561,2892064,2499744,139426,3153955,6168740,3285288,2498608,3810352,6431920,27426816,373211137,35307647])) (lf 2 [30558080,2247552,6181760,15623040,3820431,9327503,14836623,3820455,5393327,3820487,9327559,5393359,5395407,5393383,132353,133377,135681,267777,137473,139777,1587201,132610,135170,135298,135682,137346,139266,139394,139778,141826,666626,143490,658435,402435,132228,659460,136452,662532,926724,141444,133125,927749,133126,929798,137736,1581064,141576,143624,276616,145672,670216,1316873,12297,1444362,133260,133388,4108,790668,528400,1450000,140560,798736,1188881,144401,922642,144402,144404,1188376,143896,143385,135194,135196,140448,1189408,401697,9249,925858,926754,1976356,401576,665640,139305,1450288,8249,49463296,6996095])
private lemma r8_k4_ok : checkLayer (r := 7) (cd := 1) 4 (VTree.ofFun 7 (fun a => (maskWeightFast r8_ws a : ℤ) + (2 : ℤ) * (4 : ℤ) - (29 : ℤ))) (0 : ℤ) (patGens 8) r8_fi r8_prev r8_k4_fc r8_k4_tr = true := by decide +kernel
private def r8_k5_fc : List FCutCert := []
private def r8_k5_tr : BnbTree := lf 1 [1329024,936832,1336193,1332098,287619,1330052,287621,281478,1594248,549769,545674,549772,1591184,545681,549778,542612,1336215,807832,21407,411552,1067936,281505,156577,549794,549796,811944,543663,804784,18360,1592256,543681,545730,543684,674759,804808,804816,1853399,1594327,18392,804832,18408,19440,3719295]
private lemma r8_k5_ok : checkLayer (r := 7) (cd := 1) 5 (VTree.ofFun 7 (fun a => (maskWeightFast r8_ws a : ℤ) + (2 : ℤ) * (5 : ℤ) - (29 : ℤ))) (0 : ℤ) (patGens 8) r8_fi r8_prev r8_k5_fc r8_k5_tr = true := by decide +kernel
private lemma solve_row8 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hpat : HasPattern F 8) (hprev : ∀ pr ∈ r8_prev, ¬ HasPattern F pr) :
    ∃ W : Fin 12 → ℕ, 0 < ∑ i, W i ∧ F.card * (∑ i, W i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, W i) := by
  dsimp only [HasPattern, patR] at hpat
  obtain ⟨e0, he⟩ := hpat
  let e : Fin r8_ws.length ↪ Fin 12 := e0
  have he' : ∀ g ∈ patGens 8, decode e g ∈ F := he
  have hGens : ∀ g ∈ patGens 8, g < 2 ^ r8_ws.length ∧ decode e g ∈ F := by
    intro g hg
    refine ⟨?_, he' g hg⟩
    have hall : (patGens 8).all (· < 2 ^ r8_ws.length) = true := by decide
    simp only [List.all_eq_true, decide_eq_true_eq] at hall
    exact hall g hg
  have hFi : ∀ b ∈ r8_fi, b < 2 ^ r8_ws.length ∧ decode e b ∈ F :=
    checkClosureAux_sound closed empty he' [] r8_fi (fun _ h => by cases h) (by decide)
  have hTop : 2 ^ r8_ws.length - 1 ∈ r8_fi := by decide
  apply weight_from_fibers (r := r8_ws.length) (by decide) F e full (fun i => r8_ws[i.val]'i.isLt) 2 29 (by decide) (by decide) (0 : ℤ) (by decide)
  intro K hKsub hne
  have hkle : K.card ≤ 5 := K_card_le e hKsub
  have htop_iff : K = univ \ univ.map e ↔ K.card = 5 := K_eq_top_iff e hKsub
  have hlo_iff : K = ∅ ↔ K.card = 0 := card_eq_zero.symm
  have hoff : (if K = univ \ univ.map e then (0 : ℤ) else 0) - (if K = ∅ then (0 : ℤ) else 0) =
      (if K.card = 5 then (0 : ℤ) else 0) - (if K.card = 0 then (0 : ℤ) else 0) := by
    simp only [htop_iff, hlo_iff]
  rw [hoff]
  match hk : K.card with
  | 0 =>
    have h := checkLayer_sound (cd := 1) 0 closed minSize (ws := r8_ws) hKsub hk hne hGens hFi hTop hprev r8_k0_fc r8_k0_tr r8_k0_ok
    simpa [hk] using h
  | 1 =>
    have h := checkLayer_sound (cd := 1) 1 closed minSize (ws := r8_ws) hKsub hk hne hGens hFi hTop hprev r8_k1_fc r8_k1_tr r8_k1_ok
    simpa [hk] using h
  | 2 =>
    have h := checkLayer_sound (cd := 5) 2 closed minSize (ws := r8_ws) hKsub hk hne hGens hFi hTop hprev r8_k2_fc r8_k2_tr r8_k2_ok
    simpa [hk] using h
  | 3 =>
    have h := checkLayer_sound (cd := 1) 3 closed minSize (ws := r8_ws) hKsub hk hne hGens hFi hTop hprev r8_k3_fc r8_k3_tr r8_k3_ok
    simpa [hk] using h
  | 4 =>
    have h := checkLayer_sound (cd := 1) 4 closed minSize (ws := r8_ws) hKsub hk hne hGens hFi hTop hprev r8_k4_fc r8_k4_tr r8_k4_ok
    simpa [hk] using h
  | 5 =>
    have h := checkLayer_sound (cd := 1) 5 closed minSize (ws := r8_ws) hKsub hk hne hGens hFi hTop hprev r8_k5_fc r8_k5_tr r8_k5_ok
    simpa [hk] using h
  | _ + 6 => omega

-- ==================== Row 12 (r=6) ====================
private def r12_ws : List ℕ := [10,10,10,8,8,8]
private def r12_fi : List ℕ := [0,15,23,31,39,47,55,63]
private def r12_prev : List ℕ := [7,8]
private def r12_k0_fc : List FCutCert := []
private def r12_k0_tr : BnbTree := lf 1 [2916353,2916354,1605635,2916356,1605637,1605638,294919,3178504,1867785,1867786,557067,1867788,557069,557070,573455,3178512,1867793,1867794,557075,1867796,557077,557078,573463,2129944,819225,819226,819228,1622047,3178528,1867809,1867810,557091,1867812,557093,557094,573479,2129960,819241,819242,819244,1622063,2129968,819249,819250,819252,1622071,1081400,2670655]
private lemma r12_k0_ok : checkLayer (r := 6) (cd := 1) 0 (VTree.ofFun 6 (fun a => (maskWeightFast r12_ws a : ℤ) + (2 : ℤ) * (0 : ℤ) - (33 : ℤ))) (0 : ℤ) (patGens 12) r12_fi r12_prev r12_k0_fc r12_k0_tr = true := by decide +kernel
private def r12_k1_fc : List FCutCert := [d [7] 8 [0,1,2,5,6,3,4]]
private def r12_k1_tr : BnbTree := lf 1 [280459,18317,152461,280462,281491,281494,542617,542618,542620,283555,19365,152485,18342,152486,542633,542634,149420,543665,412594,543668,269333,269356,7218,3964928,2654209,2654210,1343491,2654212,1343493,1343494,65536,2916360,1605641,1605642,1605644,2916368,1605649,1605650,1605652,1867800,2916384,1605665,1605666,1605668,1867816,1867824,2932799]
private lemma r12_k1_ok : checkLayer (r := 6) (cd := 1) 1 (VTree.ofFun 6 (fun a => (maskWeightFast r12_ws a : ℤ) + (2 : ℤ) * (1 : ℤ) - (33 : ℤ))) (0 : ℤ) (patGens 12) r12_fi r12_prev r12_k1_fc r12_k1_tr = true := by decide +kernel
private def r12_k2_fc : List FCutCert := [t [3,6,10,18,34] 194 [] 8,t [3,5,9,17,33] 193 [] 8,t [5,6,12,20,36] 196 [] 8,t [9,10,12,24,40] 200 [] 8,t [17,18,20,24,48] 208 [] 8,t [33,34,36,40,48] 224 [] 8,d [9,17,24,33,40,48] 7 [6,7,0,3,4,5]]
private def r12_k2_tr : BnbTree := br 9 (br 10 (br 12 (br 17 (br 24 (br 33 (br 40 (lf 2 [1066883,1069955,412549,1069957,1591174,152461,152462,412559,1723282,149395,2770836,152469,673690,935842,149411,1984420,149413,149417,3296176,674740,529925,527878,133387,658578,135958,5660,398498,1186850,660772,661809,7503872,4882433,4882434,4882436,5406728,2785289,2785290,2785292,5406736,2785297,3309592,5406752,2785313,3309608,6471743]) (lf 1 [411523,412549,542598,19334,281490,935828,19348,280473,280474,280476,1069986,412580,2115496,1592240,529411,529413,267270,5131,5133,5134,528914,267282,5139,136212,5141,5142,136738,5155,137508,5157,5158,137384,268840,269353,6314,138282,6444,3702784,2392065,2392066,2392068,2654216,1343497,1343498,1343500,2654224,1343505,1605656,2654240,1343521,4636712,3194943])) (lf 2 [1853315,935813,150405,1985414,543631,2377618,804756,149397,18326,4343713,4344737,2249633,268419,131845,660613,135307,135309,137230,266386,135315,1708180,4372,6166,659609,659610,659612,4641,660769,661025,661793,7201,136227,269349,137254,268456,662580,2686981,7503872,4882433,4882434,4882436,5406728,2785289,2785290,2785292,5406736,2785297,3309592,5406752,19054625,6471743])) (lf 2 [149379,935813,673670,149390,2247570,938900,4343704,1463201,935844,676772,3295144,3296176,658435,1186819,1182725,1444870,134155,134157,396434,134163,921876,661652,134165,134166,1183896,921880,135576,397848,135832,135960,136472,661016,4633,5401,266778,267418,661788,662050,267561,7503872,4882433,4882434,4882436,5406728,2785289,2785290,2785292,5406736,2785297,10666008,5406752,6471743])) (lf 2 [1725315,2115461,18310,414598,4343697,2247569,4346769,2770849,149410,1197992,396291,773,137222,1186822,133259,133261,137230,658705,658961,1708305,2757137,398481,660753,661009,136210,134291,135444,134165,135446,135577,135833,136354,137254,661672,924328,662066,2555908,7503872,4882433,4882434,4882436,5406728,2785289,2785290,2785292,5406736,19841041,5406752,6471743])) (lf 4 [150403,1592197,1594246,4605836,8801164,8803212,1463186,2640788,152481,2642852,5655472,1461172,1707011,2495491,398347,5638284,3541260,1970316,1970444,1447052,1447180,1448076,1448204,2497548,1973516,399373,399374,398354,396307,398357,398358,1183896,2494744,398104,1447449,1446938,921884,397980,1970333,398371,2949122,15106048,9863169,9863170,9863172,10911752,5668873,5668874,44351500,10911760,10911776,13025343])) (lf 2 [1592195,543622,1201030,2246538,4344714,4346762,2380690,1854370,414626,414628,138243,1707013,136197,138245,919690,133514,1968650,396426,658954,659594,135562,1446410,922634,660618,136714,2234378,661642,662026,137227,921740,662540,924940,136205,137230,1709329,661780,136213,137238,921752,398872,136217,659994,922654,136229,137254,327680,7503872,4882433,4882434,4882436,5406728,2785289,22069258,5406736,5406752,6471743])) (br 48 (lf 1 [281475,152453,19334,807814,1066889,2116489,2118537,412561,807826,19350,281505,805794,773,395529,2441,789001,134409,397577,922121,4745,267529,6281,268553,268809,400393,6283,6285,7182,4625,135316,136724,5141,135704,4505,136857,5274,136348,5660,5158,720897,1376259,3702784,2392065,2392066,2392068,2654216,11714569,2654224,2654240,1605680,3194943]) (lf 1 [1066889,2116489,2118537,1067921,1069985,2116528,3203,792579,7299,661509,269445,530438,400390,133385,2441,657929,134409,1052937,4489,791049,3282953,268553,3211,3213,6158,7186,793746,400532,7317,6166,6170,137244,7324,7330,269476,6181,6182,268841,268330,268459,268332,1376259,65540,65541,65542,3702784,2392065,2392066,2392068,2654216,13156361,2654224,2654240,8306736,3194943]))
private lemma r12_k2_ok : checkLayer (r := 6) (cd := 3) 2 (VTree.ofFun 6 (fun a => (maskWeightFast r12_ws a : ℤ) + (2 : ℤ) * (2 : ℤ) - (33 : ℤ))) (0 : ℤ) (patGens 12) r12_fi r12_prev r12_k2_fc r12_k2_tr = true := by decide +kernel
private def r12_k3_fc : List FCutCert := [t [1,2,4,8,16,32] 448 [] 8]
private def r12_k3_t0 : BnbTree := br 4 (br 8 (br 16 (br 32 (br 24 (lf 1 [804739,674693,807814,411529,281481,936842,150412,543633,414609,283538,673684,414625,804772,1329064,18348,1330096,19380,1157,1289,790796,2578,3602,397458,4244,6292,3353,4642,5282,7204,7210,7218,3440640,2129921,2129922,2129924,2392072,2392080,1343512,2392096,3457087]) (lf 6 [3426185,152457,4999050,5919628,2247569,1725329,6179730,3560340,14829464,2642849,2249634,3429284,8538024,8539056,674738,5377027,5377029,5377030,525577,656905,921097,661001,1181834,134156,657681,657937,396436,396564,1448980,4198552,4591896,3412504,660760,268440,268824,134425,662569,268849,21135360,13271041,13271042,13271044,14843912,14843920,37142552,14843936,21151807])) (lf 2 [542595,674693,2115465,1985418,1330060,1985428,1329048,4868000,4869024,2773920,135171,791555,135173,661509,135174,1447942,6153,135690,397580,268300,791057,1315857,133650,1970322,1184024,4632,135193,135194,135196,136481,136738,137378,136356,662564,137512,137768,6979584,4358145,4358146,4358148,4882440,4882448,9355296,6996031])) (br 9 (lf 1 [280451,411526,411530,152458,152460,2377616,1330064,2380688,935840,1332128,804776,2051,268291,2053,661509,2054,136198,1546,137226,657548,5264,5392,5648,3601,136209,528530,266770,6674,3220,3348,528660,6292,7188,266392,266520,528920,7201,4642,7218,3440640,2129921,2129922,2129924,2392072,1081353,4636688,3457087]) (lf 1 [1329033,2378633,2380681,1330064,2380688,1332128,791555,398341,268293,2054,658438,1289,1545,2361353,788745,920073,920714,265356,530444,5264,5648,2321,2577,790801,3090,266392,4376,922137,5401,135194,266267,268315,4124,135197,4385,4641,6433,269345,6705,3440640,2129921,2129922,2129924,2392072,9879561,4243472,3457087]))) (br 24 (lf 1 [674691,283526,1329032,2378632,2380680,543636,2247584,19361,283553,545700,1027,1029,660485,1030,268294,2361352,6280,6408,6664,659721,266761,264330,661514,919820,5388,2321,2577,135441,136209,267284,3353,4124,4385,4641,269345,6185,6188,3440640,2129921,2129922,2129924,7127048,3833880,3457087]) (br 9 (br 10 (br 12 (lf 1 [1329032,2378632,2380680,1330064,938896,805792,1332128,412592,1027,658435,1029,527365,4101,1030,265222,269318,6408,2321,2577,3345,3601,135441,266769,2578,3218,4242,528914,4244,660500,659608,659736,5656,4385,5284,6312,6698,3440640,2129921,2129922,2129924,4374536,1081353,1081354,1081356,2015256,3457087]) (lf 1 [1329032,2378632,2380680,543632,1594256,674708,674720,1332128,1027,2051,527363,1029,3077,4613,5125,269317,791558,919692,1050892,396300,2577,6292,6420,790680,790808,791064,5657,6682,135324,4380,5276,5404,4642,3440640,2129921,2129922,2129924,4112392,1081353,1081354,1490956,2539544,3457087])) (lf 1 [1329032,2378632,2380680,936848,1069968,281490,1332128,1199024,1027,2051,527363,1029,2053,134149,269317,790534,6408,6664,1546,133258,2570,1313802,3210,1053194,5258,6282,526604,265484,791569,5394,397588,398356,528664,660248,1052826,4124,6188,3440640,2129921,2129922,2129924,4374536,1081353,2277386,2277400,3457087])) (lf 1 [1329032,2378632,2380680,281488,1987472,936849,281504,1332128,6147,662531,1029,4101,530437,1030,658438,6408,1289,788745,133641,1444873,921865,1053193,6665,134282,4234,530442,789644,135180,2321,4242,791572,4120,659608,136216,5401,267801,4122,5276,4385,6312,3440640,2129921,2129922,2129924,4243464,3981321,2015256,3457087])))) (lf 3 [19154820,4213636,11686788,7359375,7361423,7359399,1049091,263171,264195,5123,530435,263300,787716,264324,264452,265348,265476,1314820,921732,266500,660484,267396,922884,268420,661764,1055748,2626565,2627590,528648,268808,3017225,2570,2363914,2361612,266380,530444,396302,266512,529040,2363921,529425,529938,136724,1970328,1577240,266524,137260,5963776,10518528,557057,557058,46186500,10534975])
private def r12_k3_tr : BnbTree := br 1 (br 2 (r12_k3_t0) (br 24 (lf 2 [12732290,2771842,7754626,4869007,4871055,4869031,656002,132226,132610,133250,133634,134274,134658,135298,135682,791554,136322,136706,137346,137730,793602,1315843,268291,132101,2053,135173,267269,1053958,530438,133128,526601,2569,528649,528905,1181834,2570,528906,137482,135436,1710092,5136,659985,1577106,266388,1315092,135194,4390912,6979584,29278210,3047448,6996031]) (lf 2 [12732290,2771842,7754626,4869007,4871055,4869031,1836162,394754,5901314,1054722,135427,1446915,1707013,133382,922630,400390,1545,135433,137354,1579019,136460,1317132,138254,133393,1969425,134290,136338,2231572,1708184,1708312,1184280,137752,397466,922138,136730,136220,4915200,6979584,33734658,10141720,6996031]))) (br 24 (lf 2 [12732289,2771841,7754625,4869007,4871055,4869031,656129,132353,132609,395521,133633,134401,134657,135425,135681,136449,136705,137473,399873,793601,1577987,6275,136325,1447941,132358,661510,264200,6280,266505,1315337,399369,1312906,266762,788620,266380,659724,5136,2578,1577106,135187,135188,528660,922644,135321,135714,4390912,6979584,28884993,3178520,6996031]) (lf 2 [12732289,2771841,7754625,4869007,4871055,4869031,656129,394753,133633,4197377,135681,269313,138753,132227,1444867,396293,1184773,920582,659977,1054729,6665,2232458,2316,1579020,136205,133393,659729,1184273,1838226,1707156,137364,1446168,136344,6680,136473,136729,137497,138266,1053723,5148,7196,4915200,6979584,30851073,6471704,6996031]))
private lemma r12_k3_ok : checkLayer (r := 6) (cd := 1) 3 (VTree.ofFun 6 (fun a => (maskWeightFast r12_ws a : ℤ) + (2 : ℤ) * (3 : ℤ) - (33 : ℤ))) (0 : ℤ) (patGens 12) r12_fi r12_prev r12_k3_fc r12_k3_tr = true := by decide +kernel
private def r12_k4_fc : List FCutCert := []
private def r12_k4_tr : BnbTree := br 0 (br 1 (br 2 (br 8 (lf 2 [283523,3295108,414596,1201029,150406,152454,1723273,1723276,1722256,2247568,1201041,674706,676756,3950496,283552,936865,414625,1329064,2247600,791555,656646,395402,133386,138250,135312,657938,134164,921880,922136,660002,6455296,3833857,3833858,4358152,7520319]) (lf 2 [3296132,414596,21381,3295112,5393288,5395336,3822480,1461152,2642848,656387,395267,656389,267269,656390,398342,1050760,133384,133640,135304,135432,135688,920073,399369,138249,659594,923658,919820,661516,395793,4113,398354,659736,1446424,791577,659745,6455296,3833857,3833858,14729224,7520319])) (lf 2 [14305154,3296130,8803202,5393295,5395343,5393319,1180162,1180290,394242,787586,1443330,266370,136194,922754,662018,138242,657411,399363,1706244,660484,395270,1182726,661510,133256,1444616,1576968,266376,790537,134154,1972234,3083,134156,659470,921616,135312,135440,922128,398864,266513,1053713,1709076,266392,266529,660002,6455296,3833857,31113218,7520319])) (lf 3 [21514113,5000065,13259649,8145807,8147855,8145831,4588033,1835777,3146753,2098433,1050881,1444353,1444865,3329,1183745,1052929,267265,2233857,269313,919042,4327426,267266,1840131,1049732,1838085,1052677,3414021,133256,264840,2626056,788489,2623753,1052937,395274,921611,264204,1181836,266512,266257,660497,3149970,266260,659604,2232345,9732096,56410113,11321407])) (br 4 (br 12 (lf 1 [7096192,1592192,4346752,2640783,2642831,2640807,264449,1446913,263298,659458,4226,529538,530435,264197,135173,132102,264198,2312,2568,921608,4360,397832,2057,268297,788618,4240,4368,529552,267792,135314,4626,4116,529428,1052952,135457,4641,7204,6185,10010624,1867780,819212,3719231]) (lf 2 [14305152,3296128,8803200,5393295,5395343,5393319,769,657409,1839105,397825,136705,138241,3409410,266754,656387,134147,135171,657413,134149,135173,657414,266758,135432,656905,133129,135177,399369,134154,135690,1185802,2492556,1706252,134156,2494604,1052940,398348,399372,919566,1576974,135440,135696,136976,1709076,1052824,4376,20103168,3833860,11976716,7520319])) (lf 3 [21514112,5000064,13259648,8145807,8147855,8145831,4719105,918785,4459010,267266,792066,1835523,1836164,1049860,5769220,2230404,265220,4100,2232580,1184772,269316,3017733,1708037,1709061,1841158,264456,3279624,529032,529160,1448456,264201,266249,397834,528524,398092,1447948,659469,266512,266257,2232850,1839124,1970324,1052693,30195712,16826372,11321407]))
private lemma r12_k4_ok : checkLayer (r := 6) (cd := 1) 4 (VTree.ofFun 6 (fun a => (maskWeightFast r12_ws a : ℤ) + (2 : ℤ) * (4 : ℤ) - (33 : ℤ))) (0 : ℤ) (patGens 12) r12_fi r12_prev r12_k4_fc r12_k4_tr = true := by decide +kernel
private def r12_k5_fc : List FCutCert := []
private def r12_k5_tr : BnbTree := br 0 (lf 2 [1984385,1722242,1461122,674691,1461124,1725316,676741,676742,2247560,936841,283530,935824,2773904,1201041,1201044,1460120,3164064,19360,414624,411553,281508,1722280,1181953,659592,659720,132617,791050,923660,137240,399394,5931008,8044607]) (lf 1 [7882624,1854336,4871040,2902927,2904975,2902951,264449,396289,267265,268289,528514,398338,399362,263171,525444,132356,526468,4356,266245,133126,4102,135176,397576,266760,268552,264202,526348,529680,135186,266260,136212,4120,135704,4121,135196,11845632,3981375])
private lemma r12_k5_ok : checkLayer (r := 6) (cd := 1) 5 (VTree.ofFun 6 (fun a => (maskWeightFast r12_ws a : ℤ) + (2 : ℤ) * (5 : ℤ) - (33 : ℤ))) (0 : ℤ) (patGens 12) r12_fi r12_prev r12_k5_fc r12_k5_tr = true := by decide +kernel
private def r12_k6_fc : List FCutCert := []
private def r12_k6_tr : BnbTree := lf 1 [280448,1985408,152448,1332097,1329026,21379,1332100,19333,1592200,280457,283530,150412,1197968,152464,283537,283538,283540,1591200,150433,281506,280484,411559,412583,149416,543664,3078,3084,4240,267288,4243519]
private lemma r12_k6_ok : checkLayer (r := 6) (cd := 1) 6 (VTree.ofFun 6 (fun a => (maskWeightFast r12_ws a : ℤ) + (2 : ℤ) * (6 : ℤ) - (33 : ℤ))) (0 : ℤ) (patGens 12) r12_fi r12_prev r12_k6_fc r12_k6_tr = true := by decide +kernel
private lemma solve_row12 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hpat : HasPattern F 12) (hprev : ∀ pr ∈ r12_prev, ¬ HasPattern F pr) :
    ∃ W : Fin 12 → ℕ, 0 < ∑ i, W i ∧ F.card * (∑ i, W i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, W i) := by
  dsimp only [HasPattern, patR] at hpat
  obtain ⟨e0, he⟩ := hpat
  let e : Fin r12_ws.length ↪ Fin 12 := e0
  have he' : ∀ g ∈ patGens 12, decode e g ∈ F := he
  have hGens : ∀ g ∈ patGens 12, g < 2 ^ r12_ws.length ∧ decode e g ∈ F := by
    intro g hg
    refine ⟨?_, he' g hg⟩
    have hall : (patGens 12).all (· < 2 ^ r12_ws.length) = true := by decide
    simp only [List.all_eq_true, decide_eq_true_eq] at hall
    exact hall g hg
  have hFi : ∀ b ∈ r12_fi, b < 2 ^ r12_ws.length ∧ decode e b ∈ F :=
    checkClosureAux_sound closed empty he' [] r12_fi (fun _ h => by cases h) (by decide)
  have hTop : 2 ^ r12_ws.length - 1 ∈ r12_fi := by decide
  apply weight_from_fibers (r := r12_ws.length) (by decide) F e full (fun i => r12_ws[i.val]'i.isLt) 2 33 (by decide) (by decide) (0 : ℤ) (by decide)
  intro K hKsub hne
  have hkle : K.card ≤ 6 := K_card_le e hKsub
  have htop_iff : K = univ \ univ.map e ↔ K.card = 6 := K_eq_top_iff e hKsub
  have hlo_iff : K = ∅ ↔ K.card = 0 := card_eq_zero.symm
  have hoff : (if K = univ \ univ.map e then (0 : ℤ) else 0) - (if K = ∅ then (0 : ℤ) else 0) =
      (if K.card = 6 then (0 : ℤ) else 0) - (if K.card = 0 then (0 : ℤ) else 0) := by
    simp only [htop_iff, hlo_iff]
  rw [hoff]
  match hk : K.card with
  | 0 =>
    have h := checkLayer_sound (cd := 1) 0 closed minSize (ws := r12_ws) hKsub hk hne hGens hFi hTop hprev r12_k0_fc r12_k0_tr r12_k0_ok
    simpa [hk] using h
  | 1 =>
    have h := checkLayer_sound (cd := 1) 1 closed minSize (ws := r12_ws) hKsub hk hne hGens hFi hTop hprev r12_k1_fc r12_k1_tr r12_k1_ok
    simpa [hk] using h
  | 2 =>
    have h := checkLayer_sound (cd := 3) 2 closed minSize (ws := r12_ws) hKsub hk hne hGens hFi hTop hprev r12_k2_fc r12_k2_tr r12_k2_ok
    simpa [hk] using h
  | 3 =>
    have h := checkLayer_sound (cd := 1) 3 closed minSize (ws := r12_ws) hKsub hk hne hGens hFi hTop hprev r12_k3_fc r12_k3_tr r12_k3_ok
    simpa [hk] using h
  | 4 =>
    have h := checkLayer_sound (cd := 1) 4 closed minSize (ws := r12_ws) hKsub hk hne hGens hFi hTop hprev r12_k4_fc r12_k4_tr r12_k4_ok
    simpa [hk] using h
  | 5 =>
    have h := checkLayer_sound (cd := 1) 5 closed minSize (ws := r12_ws) hKsub hk hne hGens hFi hTop hprev r12_k5_fc r12_k5_tr r12_k5_ok
    simpa [hk] using h
  | 6 =>
    have h := checkLayer_sound (cd := 1) 6 closed minSize (ws := r12_ws) hKsub hk hne hGens hFi hTop hprev r12_k6_fc r12_k6_tr r12_k6_ok
    simpa [hk] using h
  | _ + 7 => omega

-- ==================== Row 16 (r=5) ====================
private def r16_ws : List ℕ := [9,9,8,8,8]
private def r16_fi : List ℕ := [0,15,23,27,31]
private def r16_prev : List ℕ := [7,8,12]
private def r16_k0_fc : List FCutCert := []
private def r16_k0_tr : BnbTree := lf 1 [2392065,2392066,1212419,2523140,1343493,1343494,163847,2523144,1343497,1343498,163851,1474572,294925,294926,704527,2523152,1343505,1343506,163859,1474580,294933,294934,704535,1474584,294937,294938,704539,426012,1753119]
private lemma r16_k0_ok : checkLayer (r := 5) (cd := 1) 0 (VTree.ofFun 5 (fun a => (maskWeightFast r16_ws a : ℤ) + (2 : ℤ) * (0 : ℤ) - (28 : ℤ))) (0 : ℤ) (patGens 16) r16_fi r16_prev r16_k0_fc r16_k0_tr = true := by decide +kernel
private def r16_k1_fc : List FCutCert := []
private def r16_k1_tr : BnbTree := lf 1 [18317,18318,19349,19350,3609,3610,3309568,2129921,2129922,950275,2260996,1081349,1081350,2261000,1081353,1081354,1212428,2261008,1081361,1081362,1212436,1212440,2015263]
private lemma r16_k1_ok : checkLayer (r := 5) (cd := 1) 1 (VTree.ofFun 5 (fun a => (maskWeightFast r16_ws a : ℤ) + (2 : ℤ) * (1 : ℤ) - (28 : ℤ))) (0 : ℤ) (patGens 16) r16_fi r16_prev r16_k1_fc r16_k1_tr = true := by decide +kernel
private def r16_k2_fc : List FCutCert := [t [3,6,10,18] 98 [] 12,t [5,6,12,20] 100 [] 12,t [9,10,12,24] 104 [] 12,t [17,18,20,24] 112 [] 12]
private def r16_k2_tr : BnbTree := br 12 (lf 2 [673667,1067909,412550,1722249,806282,675217,805780,806296,393989,2565,3082,720896,983043,6193152,3833857,3833858,4096004,4096008,1998860,4096016,4636703]) (lf 3 [2247555,19333,412550,1199497,806282,3819404,805780,1592728,263685,263690,2623628,2623756,2162689,1376258,9338880,5799937,5799938,6193156,6193160,10665996,6193168,6995999])
private lemma r16_k2_ok : checkLayer (r := 5) (cd := 2) 2 (VTree.ofFun 5 (fun a => (maskWeightFast r16_ws a : ℤ) + (2 : ℤ) * (2 : ℤ) - (28 : ℤ))) (0 : ℤ) (patGens 16) r16_fi r16_prev r16_k2_fc r16_k2_tr = true := by decide +kernel
private def r16_k3_fc : List FCutCert := [t [1,2,4,8,16] 224 [] 12]
private def r16_k3_tr : BnbTree := br 12 (br 20 (br 24 (br 5 (br 4 (br 1 (lf 1 [1460098,1461640,1461136,2178,131843,133251,264454,133128,394505,2185,2314,2321,2785280,1605633,1736708,557061,688140,688148,950296,2539551]) (lf 2 [3032961,3033985,3034497,918273,394497,395521,394371,395395,1286,2310,657545,526602,3604480,5668864,11714561,1212421,1474572,1474580,1474584,5160991])) (lf 2 [3034498,3032964,3033988,3277313,1154,2178,918019,3539972,656516,656644,3540996,657540,657668,263433,2314,264465,5668864,17481732,4620293,5144588,5144596,1474584,5160991])) (lf 1 [19843,1460101,1461125,281993,281994,282001,150930,262787,1284,773,1029,132229,2053,133253,1286,264454,1638400,2785280,3719173,688140,688148,688152,2539551])) (lf 1 [18305,18306,18307,281475,149384,542601,149386,150416,150417,543634,1461656,134148,527365,527366,265226,265233,1507328,2785280,688140,688148,3063832,2539551])) (lf 2 [935811,149380,280453,1066886,149384,150928,1199505,413074,3034004,937368,773,657925,1182217,1182218,657938,396308,3342336,5668864,1474572,6209556,5160991])) (br 20 (lf 2 [936835,150404,1067909,281478,150920,413065,1199498,3032972,150416,937368,773,656902,656905,1181836,1181964,396300,3342336,5668864,6209548,1474580,5160991]) (lf 2 [19843,544136,3032972,675216,3034004,1461656,395777,394754,655875,1027,1183237,657926,396806,656905,395785,132618,920074,919692,1181964,2230796,133649,2818048,5668864,7782412,6995988,5160991]))
private lemma r16_k3_ok : checkLayer (r := 5) (cd := 1) 3 (VTree.ofFun 5 (fun a => (maskWeightFast r16_ws a : ℤ) + (2 : ℤ) * (3 : ℤ) - (28 : ℤ))) (0 : ℤ) (patGens 16) r16_fi r16_prev r16_k3_fc r16_k3_tr = true := by decide +kernel
private def r16_k4_fc : List FCutCert := []
private def r16_k4_tr : BnbTree := br 0 (br 2 (lf 2 [2770817,413059,673668,1461124,674694,2248072,1198992,19858,544152,656516,657925,657544,657418,919564,133650,265234,5144576,2785282,5685279]) (lf 3 [5392258,5393282,5393794,1310977,1049345,1049857,395777,1049218,1154,1836546,1050754,1837570,1838082,1183234,918531,1050883,263172,394372,3672068,264200,2755080,395273,7766016,23248898,8568863])) (br 2 (lf 1 [1722240,1723264,1723776,131585,394753,527361,131587,263300,133380,265348,526341,263174,2056,264328,2312,395784,264202,133133,2801664,1343490,2801695]) (br 1 (lf 3 [5392256,5393280,5393792,1049218,1049730,656898,1050754,1444354,4328450,131587,132099,133379,656388,1049860,2362628,133126,788742,2754568,658184,1443852,8568832,4227073,5947394,8568863]) (lf 1 [1722240,1723264,1723776,786689,262913,525825,526849,134145,131586,262786,263298,526850,134146,263171,657411,1028,263428,657412,132102,264328,264456,2801664,1359873,1359874,2801695])))
private lemma r16_k4_ok : checkLayer (r := 5) (cd := 1) 4 (VTree.ofFun 5 (fun a => (maskWeightFast r16_ws a : ℤ) + (2 : ℤ) * (4 : ℤ) - (28 : ℤ))) (0 : ℤ) (patGens 16) r16_fi r16_prev r16_k4_fc r16_k4_tr = true := by decide +kernel
private def r16_k5_fc : List FCutCert := []
private def r16_k5_tr : BnbTree := lf 1 [280448,936832,806272,1066881,281986,411524,675208,936848,131586,642,1154,133634,1284,2308,134148,263174,2184,133132,3063839]
private lemma r16_k5_ok : checkLayer (r := 5) (cd := 1) 5 (VTree.ofFun 5 (fun a => (maskWeightFast r16_ws a : ℤ) + (2 : ℤ) * (5 : ℤ) - (28 : ℤ))) (0 : ℤ) (patGens 16) r16_fi r16_prev r16_k5_fc r16_k5_tr = true := by decide +kernel
private def r16_k6_fc : List FCutCert := []
private def r16_k6_tr : BnbTree := lf 1 [149376,412544,1199488,805761,805762,935812,935816,937360,3325983]
private lemma r16_k6_ok : checkLayer (r := 5) (cd := 1) 6 (VTree.ofFun 5 (fun a => (maskWeightFast r16_ws a : ℤ) + (2 : ℤ) * (6 : ℤ) - (28 : ℤ))) (0 : ℤ) (patGens 16) r16_fi r16_prev r16_k6_fc r16_k6_tr = true := by decide +kernel
private def r16_k7_fc : List FCutCert := []
private def r16_k7_tr : BnbTree := lf 1 [1723776,542593,280450,150402,673668,673672,675216,3588127]
private lemma r16_k7_ok : checkLayer (r := 5) (cd := 1) 7 (VTree.ofFun 5 (fun a => (maskWeightFast r16_ws a : ℤ) + (2 : ℤ) * (7 : ℤ) - (28 : ℤ))) (0 : ℤ) (patGens 16) r16_fi r16_prev r16_k7_fc r16_k7_tr = true := by decide +kernel
private lemma solve_row16 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hpat : HasPattern F 16) (hprev : ∀ pr ∈ r16_prev, ¬ HasPattern F pr) :
    ∃ W : Fin 12 → ℕ, 0 < ∑ i, W i ∧ F.card * (∑ i, W i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, W i) := by
  dsimp only [HasPattern, patR] at hpat
  obtain ⟨e0, he⟩ := hpat
  let e : Fin r16_ws.length ↪ Fin 12 := e0
  have he' : ∀ g ∈ patGens 16, decode e g ∈ F := he
  have hGens : ∀ g ∈ patGens 16, g < 2 ^ r16_ws.length ∧ decode e g ∈ F := by
    intro g hg
    refine ⟨?_, he' g hg⟩
    have hall : (patGens 16).all (· < 2 ^ r16_ws.length) = true := by decide
    simp only [List.all_eq_true, decide_eq_true_eq] at hall
    exact hall g hg
  have hFi : ∀ b ∈ r16_fi, b < 2 ^ r16_ws.length ∧ decode e b ∈ F :=
    checkClosureAux_sound closed empty he' [] r16_fi (fun _ h => by cases h) (by decide)
  have hTop : 2 ^ r16_ws.length - 1 ∈ r16_fi := by decide
  apply weight_from_fibers (r := r16_ws.length) (by decide) F e full (fun i => r16_ws[i.val]'i.isLt) 2 28 (by decide) (by decide) (0 : ℤ) (by decide)
  intro K hKsub hne
  have hkle : K.card ≤ 7 := K_card_le e hKsub
  have htop_iff : K = univ \ univ.map e ↔ K.card = 7 := K_eq_top_iff e hKsub
  have hlo_iff : K = ∅ ↔ K.card = 0 := card_eq_zero.symm
  have hoff : (if K = univ \ univ.map e then (0 : ℤ) else 0) - (if K = ∅ then (0 : ℤ) else 0) =
      (if K.card = 7 then (0 : ℤ) else 0) - (if K.card = 0 then (0 : ℤ) else 0) := by
    simp only [htop_iff, hlo_iff]
  rw [hoff]
  match hk : K.card with
  | 0 =>
    have h := checkLayer_sound (cd := 1) 0 closed minSize (ws := r16_ws) hKsub hk hne hGens hFi hTop hprev r16_k0_fc r16_k0_tr r16_k0_ok
    simpa [hk] using h
  | 1 =>
    have h := checkLayer_sound (cd := 1) 1 closed minSize (ws := r16_ws) hKsub hk hne hGens hFi hTop hprev r16_k1_fc r16_k1_tr r16_k1_ok
    simpa [hk] using h
  | 2 =>
    have h := checkLayer_sound (cd := 2) 2 closed minSize (ws := r16_ws) hKsub hk hne hGens hFi hTop hprev r16_k2_fc r16_k2_tr r16_k2_ok
    simpa [hk] using h
  | 3 =>
    have h := checkLayer_sound (cd := 1) 3 closed minSize (ws := r16_ws) hKsub hk hne hGens hFi hTop hprev r16_k3_fc r16_k3_tr r16_k3_ok
    simpa [hk] using h
  | 4 =>
    have h := checkLayer_sound (cd := 1) 4 closed minSize (ws := r16_ws) hKsub hk hne hGens hFi hTop hprev r16_k4_fc r16_k4_tr r16_k4_ok
    simpa [hk] using h
  | 5 =>
    have h := checkLayer_sound (cd := 1) 5 closed minSize (ws := r16_ws) hKsub hk hne hGens hFi hTop hprev r16_k5_fc r16_k5_tr r16_k5_ok
    simpa [hk] using h
  | 6 =>
    have h := checkLayer_sound (cd := 1) 6 closed minSize (ws := r16_ws) hKsub hk hne hGens hFi hTop hprev r16_k6_fc r16_k6_tr r16_k6_ok
    simpa [hk] using h
  | 7 =>
    have h := checkLayer_sound (cd := 1) 7 closed minSize (ws := r16_ws) hKsub hk hne hGens hFi hTop hprev r16_k7_fc r16_k7_tr r16_k7_ok
    simpa [hk] using h
  | _ + 8 => omega

-- ==================== Row 26 (r=6) ====================
private def r26_ws : List ℕ := [6,6,6,6,6,4]
private def r26_fi : List ℕ := [0,15,23,31,47,63]
private def r26_prev : List ℕ := [7,8,12,16]
private def r26_k0_fc : List FCutCert := [d [39] 12 [0,1,2,5,3,4],q [43,45,46] [(43,45,16,[0,3,1,2,5]),(43,46,16,[1,3,0,2,5]),(45,46,16,[2,3,0,1,5])]]
private def r26_k0_tr : BnbTree := lf 2 [150451,150453,150454,7481,7737,7738,196609,4358145,4358146,2785283,4358148,2785285,2785286,1212423,4358152,2785289,2785290,1212427,2785292,1212429,1212430,180239,4358160,2785297,2785298,1212435,2785300,1212437,1212438,180247,2785304,1212441,1212442,1212444,1753119,4882464,3309601,3309602,1736739,3309604,1736741,1736742,196608,3309608,1736745,1736746,1736748,1228847,3309616,1736753,1736754,1736756,1736760,2801727]
private lemma r26_k0_ok : checkLayer (r := 6) (cd := 1) 0 (VTree.ofFun 6 (fun a => (maskWeightFast r26_ws a : ℤ) + (2 : ℤ) * (0 : ℤ) - (23 : ℤ))) (0 : ℤ) (patGens 26) r26_fi r26_prev r26_k0_fc r26_k0_tr = true := by decide +kernel
private def r26_k1_fc : List FCutCert := [d [7] 12 [0,1,2,6,3,4],q [11,13,14] [(11,13,16,[0,3,1,2,6]),(11,14,16,[1,3,0,2,6]),(13,14,16,[2,3,0,1,6])],q [19,21,22] [(19,21,16,[0,4,1,2,6]),(19,22,16,[1,4,0,2,6]),(21,22,16,[2,4,0,1,6])],t [19,21,25,49] 81 [] 12,t [35,38,42,50] 98 [] 12,t [35,37,41,49] 97 [] 12,t [37,38,44,52] 100 [] 12,t [41,42,44,56] 104 [] 12,t [49,50,52,56] 112 [] 12,v [19,35,49,50] 115 [],v [21,37,49,52] 117 []]
private def r26_k1_tr : BnbTree := br 41 (br 38 (br 49 (br 35 (lf 2 [149387,149389,149390,150419,150421,150422,673689,673690,673692,804778,804780,805810,805812,1186853,5674,137514,137772,6706,458753,458754,5406720,3833857,3833858,2260995,3833860,2260997,2260998,720896,3833864,2261001,2261002,2261004,3833872,2261009,2261010,2261012,2261016,4358176,2785313,2785314,1212451,2785316,1212454,2785320,1212457,2785328,1212465,3326015]) (lf 3 [280459,280461,280462,805779,804757,542614,150422,673690,1066908,2639779,2640803,1053081,266650,266915,267555,268579,1055779,267813,268837,662565,267818,1055274,1055020,268850,720897,196610,8159232,5799937,5799938,3440643,5799940,3440645,3440646,1114112,5799944,3440649,3440650,3440652,5799952,3440657,3440658,3440660,3440664,6586400,4227105,4227106,7389219,4227108,1867814,4227112,1867817,4227120,1867825,5029951])) (lf 6 [673675,673677,673678,804755,412563,1723285,2246550,2115481,673690,673692,2246563,3032997,5393329,1448090,1448092,661667,268453,3807402,3807404,268849,662577,1507329,65539,3080200,720905,327690,16416768,11698177,11698178,6979587,11698180,6979589,6979590,2293760,11698184,6979593,6979594,6979596,11698192,6979601,6979602,6979604,6979608,13271072,8552481,8552482,8552484,3833894,8552488,3833897,8552496,19316785,10141759])) (lf 3 [411531,411533,411534,281487,1066899,1067925,1066902,673689,2639782,2640806,268441,1054874,660252,268444,267045,267814,268838,1842214,589825,1900548,1507334,8159232,5799937,5799938,3440643,5799940,3440645,3440646,1114112,5799944,3440649,3440650,3440652,5799952,3440657,3440658,3440660,3440664,6586400,4227105,4227106,4227108,10928166,4227112,1867817,4227120,5029951])) (lf 1 [18315,18317,18318,150419,19349,280470,149401,18330,280476,543654,804777,19377,19378,5267,136341,5273,136346,5283,5285,399657,530985,196609,458757,589831,2654208,1867777,1867778,1081347,1867780,1081349,1081350,327680,1867784,1081353,1081354,1081356,1867792,1081361,1081362,1081364,1081368,2129952,1343521,1343522,1343524,1343528,3588137,1343536,1622079])
private lemma r26_k1_ok : checkLayer (r := 6) (cd := 4) 1 (VTree.ofFun 6 (fun a => (maskWeightFast r26_ws a : ℤ) + (2 : ℤ) * (1 : ℤ) - (23 : ℤ))) (0 : ℤ) (patGens 26) r26_fi r26_prev r26_k1_fc r26_k1_tr = true := by decide +kernel
private def r26_k2_fc : List FCutCert := [t [3,6,10,18,34] 194 [] 12,t [3,5,9,17,33] 193 [] 12,t [5,6,12,20,36] 196 [] 12,t [9,10,12,24,40] 200 [] 12,t [17,18,20,24,48] 208 [] 12,t [33,34,36,40,48] 224 [] 12,v [6,18,20] 214 [],v [6,34,36] 230 [],v [12,20,24] 220 [],v [18,34,48] 242 [],v [24,40,48] 248 []]
private def r26_k2_t0 : BnbTree := br 10 (br 40 (br 48 (br 5 (br 6 (br 12 (lf 4 [411527,411531,411533,411534,1197969,805777,2115474,1592212,1591192,411548,150435,149413,1199013,1461158,1460137,1460138,1197996,1461172,396435,396564,396309,136726,137494,1186083,1449009,1376260,9863168,6717441,6717442,3571715,6717444,3571717,3571718,6717448,3571721,3571722,3571724,6717456,7766048,4620321,4620322,4620324,4620328,3178544,7782463]) (lf 2 [150407,1197964,2771852,2250636,281490,150419,150420,19349,674723,674725,412582,150452,134155,1050764,919820,2700,134412,135948,660620,398604,661644,661772,662540,137741,137742,136721,136726,136729,136476,327684,1114120,4882432,3309569,3309570,1736707,3309572,1736709,1736710,3309576,1736713,1736714,12369932,3309584,3833888,2261025,2261026,2261028,2261032,1867824,3850303])) (lf 1 [1984390,543622,1070982,1330063,19363,281509,150438,150449,19380,265222,3334,3590,135558,267782,137478,6662,269318,4871,2315,264332,2700,5260,2573,6670,3218,6290,6419,5398,136489,196610,458756,2392064,1605633,1605634,819203,1605636,557061,5292038,1605640,819209,819210,1605648,1867808,1081377,1081378,819236,1081384,557104,1884223])) (lf 7 [14567301,4475781,8148869,9980815,1723301,2640806,1592242,1854388,3935237,1708421,2627077,2234501,268805,2628613,134150,791175,788619,133388,395917,268813,788750,789777,790929,2233489,923921,789650,790034,2626834,268434,789523,267413,789526,6094850,196612,17334272,11829249,11829250,6324227,11829252,41336837,11829256,6324233,6324234,11829264,13664288,8159265,8159266,1998884,8159272,7897136,13680703])) (lf 3 [1853317,674693,2639750,281479,2639756,2640783,2643855,281491,281493,280470,280473,280474,280476,542630,18345,3427248,268299,268301,268302,1054755,1054757,399398,399657,399913,1054762,1054764,1055793,530994,2686980,7372800,5013505,5013506,2654211,5013508,5013512,2654217,2654218,5013520,5799968,3440673,3440674,3440676,3440680,9093168,5816383])) (br 48 (br 5 (lf 4 [411526,411527,1460108,1985420,543633,1854354,280468,2901912,149401,412581,1461158,4605864,936882,1461172,397702,1446918,924678,398347,398349,400398,1447185,661009,922642,398355,1446932,922772,398357,398358,136729,398362,398492,922659,922661,1448104,399660,589828,9863168,6717441,6717442,3571715,6717444,3571717,6717448,3571721,3571722,6717456,7766048,4620321,4620322,4620324,10928168,3964976,7782463]) (lf 5 [10372997,3165061,5789573,7097231,1854373,674726,1067953,1199026,1838085,527493,1184133,529157,5772293,661637,1055237,1842181,398342,530695,529419,136460,526989,529422,1840145,922897,1447569,3150866,1185298,529427,398356,529430,2234008,529946,529436,529443,398374,662056,529705,1187113,3997698,196611,12353536,8421377,8421378,4489219,8421380,33472517,8421384,4227081,4227082,8421392,9732128,5799969,5799970,1736740,11714600,5799984,9748543])) (lf 6 [673671,3032972,2247564,2509713,2508690,2509716,1197975,673689,673690,673692,6965160,6966192,1054725,4201477,2234374,3021830,661515,661517,661518,661523,660501,660502,1053731,1054755,1053733,1054757,2233382,4986920,2234536,2234664,1055272,1053993,1054249,1055274,1054764,2818052,2555914,14843904,10125313,10125314,5406723,10125316,10125320,5406729,5406730,10125328,11698208,6979617,6979618,6979620,19841064,20758576,11714623]))) (lf 10 [5131141,6440842,14306186,11687818,1198997,2902950,8670128,2494853,398341,793606,1184391,6424714,5114378,1183242,1184138,2495626,3806730,3807370,3414282,3807754,269322,1185803,1182861,792590,268558,1709073,791314,1185043,922644,1185044,1185046,1184922,2497573,7405568,720898,8323075,720900,24805376,16941057,16941058,1605635,16941060,16941064,688137,72138762,16941072,19562528,11698209,4227106,10911780,19578943])
private def r26_k2_t1 : BnbTree := br 34 (br 3 (br 36 (br 9 (r26_k2_t0) (lf 2 [150405,150406,150407,1197961,2771849,2250633,150419,150421,19365,674726,543664,674737,660742,662534,1181961,1182217,659849,661001,661513,661769,662025,137227,137229,137230,4753,267410,267412,136214,135833,136218,135836,1507329,1769475,65540,4882432,3309569,3309570,163843,3309572,3309576,14598153,3309584,3833888,688161,2261026,2261028,3850303])) (br 48 (br 40 (lf 1 [18311,280457,412553,19338,18315,18321,412561,149394,18323,19349,149400,1066916,1067940,397834,137354,6669,4622,135697,135698,267538,4630,266776,135832,4633,4634,4764,266787,267428,6308,269350,268588,137774,851970,2392064,1605633,1605634,819203,1605636,1605640,1605648,1867808,1081377,1081378,4898852,1081384,1081392,1884223]) (lf 6 [4475781,1853318,2509702,280455,673677,673678,4474772,3164055,673692,6965156,6966180,266759,660491,2232849,3020305,2233362,3020306,660499,660501,660502,659993,659994,660003,1446947,3806244,2233508,2233636,2234660,1053477,1055781,1055782,2234536,2234920,851970,5439491,14843904,10125313,10125314,5406723,10125316,10125320,10125328,11698208,6979617,6979618,24035364,14073896,6979632,11714623])) (lf 3 [2378629,1853318,412550,2378636,280469,280470,935831,3426212,3427236,266759,1054729,1448457,1053194,1054730,268810,268299,268301,268302,268307,266777,266778,266780,266787,661539,1053860,1841188,661668,1055012,662564,267045,268325,269349,661542,1055274,268460,662316,196610,2686980,3473413,7372800,5013505,5013506,2654211,5013508,5013512,5013520,5799968,16302116,10534960,5816383]))) (br 48 (br 40 (lf 2 [4081539,1198979,2250627,2771855,1723300,150437,19378,19380,1182723,397827,136323,398595,661635,662531,135559,137483,133772,133900,134412,4748,135948,530956,133645,133646,136467,134292,135828,398100,137492,397720,5660,6428,5669,398889,1769472,1769473,4882432,3309569,3309570,13811715,3309572,3309576,3309584,3833888,426017,426018,2261032,2261040,3850303]) (lf 2 [4081539,1198979,2250627,2771855,674723,543652,543653,150438,658435,134275,659971,1971203,661763,662531,2315,3083,5133,6669,136718,791953,267282,267666,136211,791572,136213,136214,136218,136220,5157,398374,661672,398889,137769,268842,269866,851968,851969,851970,851971,4882432,3309569,3309570,13287427,3309572,3309576,3309584,3833888,1343521,1343522,4767784,2261040,3850303])) (lf 2 [4081539,1198979,2250627,2771855,2247600,789507,134403,397827,136195,1972227,662531,135559,397833,268809,792970,137227,6284,661772,137229,137230,3219,137237,136214,4633,137372,398371,529445,6181,661542,268712,661545,661546,661548,268333,268849,851968,851969,851970,851972,196613,4882432,3309569,3309570,12632067,3309572,3309576,3309584,3833888,1081377,1081378,7913520,3850303]))) (br 5 (br 9 (br 12 (br 17 (lf 2 [18307,18310,149383,18314,149387,149389,149390,19343,19346,149395,1066900,543636,150421,150422,1197976,2246562,2247586,397720,135449,135450,135452,660130,660642,661026,661666,400418,138275,661798,662058,1638400,2293765,4882432,3309569,3309570,3309572,1736709,3309576,1736713,1736716,3309584,1736721,3833888,10797090,3850303]) (lf 1 [411523,18311,1329041,1723281,1066914,395402,2187,2189,4366,659729,267281,267537,268817,5139,135444,3221,4374,1052951,135448,4378,4380,267426,267045,268460,269363,327680,589828,589829,458759,2392064,1605633,1605634,1605636,819205,1605640,819209,819212,1605648,5685265,1867808,426017,4898850,1884223])) (lf 3 [412547,150406,281479,1853324,4213644,3430284,19345,543636,3427234,134666,265227,1706124,395532,264972,265484,2232588,1053324,1054860,268556,137996,1055756,662796,3085,137229,264718,659729,266515,1315092,267797,1839384,266521,4380,1053475,1053993,661804,1055278,2162688,196610,196611,3211269,7372800,5013505,5013506,5013508,2392069,5013512,2392073,18006028,5013520,5799968,163873,12894242,5816383])) (lf 3 [1198979,150406,281479,1853321,4213641,3430281,3427234,788745,264585,1837577,134409,3019017,1053321,661641,1054985,1055241,265355,268429,268302,1052945,1447313,267410,659732,267413,266518,5530,266524,1055778,1053475,268329,1054250,137259,1376256,2686979,2424837,983047,7372800,5013505,5013506,5013508,2654213,5013512,20758537,5013520,5799968,950305,11976738,5816383])) (br 40 (lf 2 [4081541,1198981,2250629,2771855,2247586,1182725,659717,398853,399365,400389,133513,133258,133898,267018,137483,135821,135438,135829,135448,135576,135833,135578,135452,660642,661666,530978,138275,136486,6182,399658,137260,6702,851968,1507329,1769474,458757,851977,4882432,3309569,3309570,3309572,13025285,3309576,3309584,3833888,163873,6078498,1736744,3850303]) (lf 1 [1984389,543621,1070981,1330063,1067938,3589,266501,267269,268421,2443,2573,2574,135441,267281,136465,267284,136468,5141,5142,4377,4378,5154,267426,267810,268834,6435,269350,137512,851968,851971,1114117,2392064,1605633,1605634,1605636,4243461,1605640,1605648,1867808,4243490,2670632,1884223])))
private def r26_k2_tr : BnbTree := br 33 (r26_k2_t1) (br 10 (br 6 (br 12 (br 18 (lf 2 [19331,18309,149383,18313,149387,149389,149390,19345,150419,1460116,150420,150421,150422,1197976,2246561,2247585,397464,135833,135322,135324,660257,660769,136737,399649,662049,138273,137379,400419,398501,137513,399532,1638401,2293765,4882432,3309569,3309570,3309572,1736710,3309576,1736714,1736716,3309584,1736722,3833888,10797089,3850303]) (lf 1 [149379,149381,18311,1329042,1723282,1066913,133385,2315,4749,2318,921746,267410,3347,135316,4245,1052823,137624,4761,4764,267553,267043,268460,268850,269363,589825,589828,1114117,2392064,1605633,1605634,1605636,819206,1605640,819210,819212,1605648,4898834,1867808,4767777,1884223])) (lf 1 [19335,542604,1330060,1070988,19346,281492,1067937,4235,395532,2700,3212,3340,528524,5388,268428,6412,268812,3085,5646,135314,4243,266388,5780,5654,266392,266904,4252,267041,5409,5283,138275,137513,5674,7213,851969,1114117,2392064,1605633,1605634,1605636,819206,1605640,819210,4898828,1605648,1867808,4636705,1884223])) (lf 2 [4081542,1198982,2250630,2771855,2247585,1182726,659590,136710,6406,268806,138246,2315,4491,659596,6796,133773,135950,659602,136467,135958,397464,135321,135322,135324,398625,268833,5283,400419,399525,136742,530729,137388,1769473,851970,2293765,851974,4882432,3309569,3309570,3309572,10928134,3309576,1736714,3309584,3833888,8699937,3850303])) (lf 1 [19331,19333,19334,19335,542602,1330058,1070986,19346,1067937,395402,2442,133642,2826,528522,136714,268298,137354,268810,2315,4237,5390,136594,136468,4245,266392,4761,4250,4251,4252,267041,268577,269345,269475,136357,6316,327680,327681,327682,458755,720901,2392064,1605633,1605634,1605636,1605640,6209546,1605648,1867808,3981345,1884223]))
set_option maxRecDepth 8192 in
private lemma r26_k2_ok : checkLayer (r := 6) (cd := 4) 2 (VTree.ofFun 6 (fun a => (maskWeightFast r26_ws a : ℤ) + (2 : ℤ) * (2 : ℤ) - (23 : ℤ))) (0 : ℤ) (patGens 26) r26_fi r26_prev r26_k2_fc r26_k2_tr = true := by decide +kernel
private def r26_k3_fc : List FCutCert := [t [1,2,4,8,16,32] 448 [] 12]
private def r26_k3_t0 : BnbTree := br 36 (br 40 (br 48 (br 3 (br 2 (br 1 (br 32 (br 4 (lf 2 [1197957,546694,1592200,808840,415625,153482,411532,415628,149392,1723280,673682,542616,150435,150437,150438,150449,150450,150452,132102,265222,133129,395785,395402,134154,138250,133132,136336,133393,133649,136721,133650,136468,4358144,2785281,2785282,1212419,2785284,3309600,1736737,1736738,1736740,1736744,1736752,4374591]) (lf 1 [2508676,805764,1333124,1592207,19363,19365,19366,19378,19380,1156,1284,3076,5252,5380,7172,773,2053,134149,5637,2566,134150,6278,2184,395785,395402,526604,1245184,2129920,32769,32770,557059,5554180,294944,819233,819234,819236,819240,819248,2146367])) (lf 1 [542597,18310,412550,412553,412554,18316,19345,150418,280468,149400,1329056,1330080,1314820,1314824,2185,2314,264332,7180,1314832,2578,4882,3092,5272,6424,4771,6314,6700,2129920,1343489,1343490,557059,5423136,819233,819234,2261028,2261032,2261040,2146367])) (lf 1 [2508673,805761,1333121,1592207,19363,19365,19366,19377,19380,1281,2305,2561,3073,3585,135169,5377,5633,6401,7169,773,1541,134149,5253,1542,2310,134150,264457,133641,395402,2188,133644,1376256,2129920,6340609,557059,1081377,819234,819236,819240,819248,2146367])) (lf 1 [2508674,805762,1333122,1592207,19363,19365,19366,19377,19378,19380,642,1154,2178,2562,3074,135170,5250,5634,7170,1541,2181,134149,1542,134150,3590,5382,395529,264330,133642,2316,133644,1376256,2129920,6209538,557059,819233,1081378,819236,819240,819248,2146367])) (lf 1 [2508675,805763,1333123,1592207,150432,19363,19365,19366,19377,19380,1155,2179,527363,5251,5379,7171,773,1157,2181,5637,6405,1286,2566,2185,133641,133258,133642,526604,1376256,2129920,5554179,819233,819234,819236,819240,819248,2146367])) (lf 5 [939905,939906,677763,935812,542597,1066886,935816,1070985,542602,677772,935824,804753,1723281,3164050,2640788,3164056,2246560,7097264,2365443,2496517,1972230,1972233,2496522,2365452,395793,530467,530469,530470,530473,530474,530476,6449,400433,399922,7220,6094848,11042816,4489249,4489250,4489252,4489256,20889648,11059263])) (br 1 (br 2 (br 32 (lf 3 [542596,2640772,1984392,1985416,2508688,280472,281509,281510,4212648,2640816,281522,281524,265219,1446915,263300,269572,1840133,1840134,263433,264201,265737,267529,263690,657418,269322,658444,265484,267404,267920,1840145,1840146,1840148,266648,268460,65536,6586368,4096001,4096002,4882464,2654241,2654242,2654244,12894248,6602815]) (lf 2 [149384,543624,149385,936842,1197964,280464,412560,936849,150418,1197976,2770848,2771872,922627,137219,1052676,1184773,922630,137222,133256,923657,133130,922642,1184788,136227,137253,138278,137384,137512,137769,136746,1638400,4358144,1081345,1081346,5160992,1736737,1736738,2916388,4636712,4374591])) (lf 1 [2508674,805762,1333122,1592207,19363,19365,19366,805808,642,1154,1538,2178,2562,3074,135170,136194,529411,398341,3078,398342,132617,3081,5385,3084,5388,5133,398353,529426,267284,5396,5656,6312,6696,6441,7211,1376256,2129920,6209538,819233,1081378,819236,2932776,2146367])) (lf 1 [2508673,805761,1333121,1592207,19363,19365,19366,674736,19377,1281,1537,135169,660481,5377,643,2179,3075,136195,398341,529414,2185,2313,5641,6409,7177,1546,3082,136330,264332,398354,398356,5268,267416,6696,6185,1376256,2129920,6340609,1081377,819234,819236,2408488,2146367]))) (br 4 (br 5 (br 1 (lf 4 [150406,3557256,543624,2509708,804752,3296144,2508692,5654436,5655460,4198402,1970691,136195,137219,2233350,1970697,137225,137737,135690,1972234,137738,1970705,398353,2494994,2495000,397859,399524,398373,400422,399401,399402,399660,1376256,8814592,4227073,4227076,2523141,3571745,7897122,20627492,8831039]) (lf 1 [2508673,805761,1333121,1592207,1330084,769,1281,1537,2305,2561,135169,922113,4865,5377,6401,397827,6147,1542,2566,5126,6662,264713,137225,397834,266892,528913,397842,528920,5155,5284,6308,5157,531493,399400,6828,1376256,2129920,7258113,557061,1081377,819234,4636708,2146367])) (lf 1 [2508677,805765,1333125,1592207,1330084,4097,4098,643,1155,2179,5379,6147,1157,2181,527365,528901,4869,5637,530437,7173,1542,397958,2184,266761,528906,2060,2188,135820,6417,528914,529428,5155,6312,6185,6701,1245184,2129920,32772,6995973,950305,950306,2801700,2146367])) (lf 1 [2508676,805764,1333124,1592207,1330084,515,397827,1156,2180,3076,4484,6276,6404,398341,7685,1542,2566,268294,4617,137225,6665,528906,2188,264460,266769,3090,5650,4884,267284,266776,6181,7209,6186,1376256,2129920,5816324,819233,819234,2539556,2146367]))
private def r26_k3_t1 : BnbTree := br 34 (br 40 (br 1 (br 3 (br 4 (lf 4 [935810,281474,2508677,2509705,1460112,805776,2508689,2247572,5654433,5655457,921602,1446022,923654,2363400,1970314,135690,137226,2494604,1970322,397842,135316,2494616,1184289,398113,398625,399649,399905,397859,399524,400548,1185829,400421,399401,399404,3211264,8814592,2392065,2523139,2392068,22462497,4620322,6062120,8831039]) (lf 1 [2508676,805764,1333124,1592207,1330081,1284,2180,2308,397444,530437,266374,6150,6662,529033,397450,264332,137740,2321,266386,3092,135188,5268,6420,397464,4897,5409,4643,6188,7217,1376256,2129920,557059,5816324,3063841,819234,819240,2146367])) (lf 1 [2508675,805763,1333123,1592207,1330081,643,1155,2179,396291,528899,530435,1157,2181,6149,1286,264454,6150,133385,4489,397450,264332,4236,4748,266388,4884,6420,135190,6296,5665,6689,7201,5284,5412,1376256,2129920,6471683,1884193,819234,819240,2146367])) (lf 1 [2508673,805761,1333121,1592207,1330081,1281,1537,2305,5377,6401,6657,643,397827,396293,2566,399366,2185,137225,137353,397450,397452,2577,135185,5649,397458,266388,4248,4643,5284,6308,7205,6182,1376256,2129920,5685249,2539553,819234,819240,2146367])) (br 3 (br 36 (br 2 (br 1 (lf 2 [673672,281480,1198985,935820,805776,280465,805777,1197976,2770849,2771873,1052676,922629,137349,921734,136198,133130,659594,138250,137228,1183890,659604,398356,135969,922657,136481,137761,136227,136229,137512,1185833,137260,1638400,4358144,1081345,1081346,1212419,9617441,1736738,2916388,1753128,4374591]) (lf 1 [2508673,805761,1333121,1592207,1330081,1537,2561,3073,398337,396293,5125,528518,1289,264457,5385,266378,7178,264332,4236,2321,6417,4242,397460,5155,5157,5158,6696,530473,6188,1376256,2129920,5816321,557059,2277409,819234,819236,180264,2146367])) (lf 1 [2508674,805762,1333122,1592207,1330081,642,1154,1538,2178,135170,1970306,4738,1157,266629,529414,264457,264330,133386,397452,5393,528532,135320,266648,4250,4897,5153,5665,529443,530467,7203,6312,6440,6696,137257,1376256,2129920,7913474,557059,4505633,1081378,819236,835624,2146367])) (lf 4 [804737,674689,1592196,2508677,18312,1461128,2509705,2509708,1067920,5654433,5655457,1576962,1446022,922630,1970314,397834,398992,2496017,1970322,397842,1446036,922772,1446424,922264,4067873,398113,3019809,398625,399649,399905,397859,3019812,399524,3019813,400421,2496553,923692,3997696,8814592,2523139,24559649,5275682,7258148,6733864,8831039])) (lf 1 [2508675,805763,1333123,1592207,1330081,643,2179,528515,1446915,6275,397701,2310,136198,1289,1545,2313,7177,1546,266762,264332,4497,266386,397460,5140,397464,4504,267297,5665,6689,398500,4901,6440,792619,1376256,2129920,6864899,3194913,819234,1490984,2146367]))) (br 40 (br 3 (br 5 (br 1 (br 4 (br 2 (lf 1 [280454,19334,411529,1329040,149393,150417,412562,1329057,1330081,1286,1314824,2185,397450,397452,4364,4626,135316,266516,397464,4376,921889,4897,5409,5665,6689,7202,397859,530467,6308,6436,6181,6185,2129920,1343489,1343490,557059,1343492,557061,5292065,835618,2261032,2146367]) (lf 1 [2508674,805762,1333122,1592207,1330081,1154,1538,4226,2310,397446,397577,135306,266762,397452,2321,2577,266513,4242,4626,5650,397588,528536,135713,4897,5409,6689,6179,7203,6308,268325,6441,137259,1376256,2129920,5292034,557059,557061,3325985,442402,819240,2146367])) (lf 1 [2508676,805764,1333124,1592207,1330081,1156,1284,2180,2308,3076,659588,397577,264714,4618,266380,135436,2321,3089,135697,3090,135698,135444,135320,266529,5409,5665,6433,7201,529058,399395,5284,137253,6182,6705,1376256,2129920,557059,6340612,557061,2801697,1097762,819240,2146367])) (lf 1 [2508673,805761,1333121,1592207,1330081,769,1281,1537,2305,2561,528641,6401,2310,268294,2185,397577,135690,137226,264332,4236,5393,266386,397460,528536,5282,5666,6306,6690,528931,7203,6181,6182,1376256,2129920,6340609,557059,557061,2146337,704546,819240,2146367])) (lf 1 [2508677,805765,1333125,1592207,1330081,773,1157,528645,530437,1286,2310,137222,133641,135433,135306,135690,528524,2321,2577,3089,135441,135314,4626,3092,4884,266392,5409,6433,5666,6690,7202,6313,1376256,2129920,557059,5816325,2277409,573474,819240,2146367])) (lf 1 [2508675,805763,1333123,1592207,1330081,643,1155,2307,4611,5251,5379,137219,397573,1286,2566,268294,2185,264457,2314,266378,528524,2577,266513,266388,528536,5666,7202,6308,6181,6182,6706,1376256,2129920,5292035,2539553,180258,819240,2146367])) (br 36 (br 16 (br 3 (lf 3 [673665,936833,1723266,281477,674694,1723272,1854345,1853322,1197975,4212641,4213665,1708036,1446149,1053702,1446028,266508,1446161,267537,1840274,1840148,1446040,266648,1839393,1840161,267809,268833,269345,662817,266914,2626594,268450,1840163,267302,268585,2627626,2424832,6586368,1867779,1736720,14860321,6209570,4489252,7389224,6602815]) (lf 1 [2508675,805763,1333123,1592207,1330081,643,1155,2307,922627,6275,7171,1157,266501,1286,135302,136198,2185,133641,2186,264714,266380,135436,267537,397458,528536,5665,6689,660514,5157,5158,6440,399402,268331,1376256,2129920,5947395,2539553,442402,819236,1490984,2146367])) (lf 1 [149379,149385,280458,1591184,2247568,1329057,1155,134147,2053,397573,2054,398342,133385,2058,2186,528524,2494608,397584,4752,5776,2321,265233,134290,397460,4372,1314967,397601,4897,5665,1972386,6690,529443,530600,530728,1317288,1376256,2129920,7782416,6471713,2932770,819236,2932776,2146367])) (lf 2 [149379,674691,936837,1066886,1198985,1198986,280460,674700,2770849,2771873,131715,1542,921873,136465,135698,922642,921748,135444,1183896,2232609,922145,137761,1446434,137378,138274,1184291,1184803,922660,137508,1184805,1184806,399398,1185836,2818048,4358144,9879585,3850274,3588132,4112424,4374591])))
private def r26_k3_tr : BnbTree := br 33 (br 34 (r26_k3_t0) (br 36 (br 2 (br 3 (br 1 (lf 4 [150406,3557256,543624,2509706,804752,3296144,2508690,5654434,5655458,4198404,1970437,136197,137221,2233350,2494729,2496524,2494737,1970452,398356,2494744,397986,399906,400930,400419,398374,399401,399530,399660,137262,1376256,8814592,4227073,4227074,2523139,3571745,21413922,7897124,8831039]) (lf 1 [2508673,805761,1333121,1592207,1330082,769,1281,2305,135169,1577217,4865,5633,6657,1157,2181,135429,6149,1286,2310,135558,2185,264457,2186,137610,528652,5137,5393,528660,528664,6306,529443,661539,7203,5157,6441,1376256,2129920,7651329,557059,1081377,4505634,819236,2146367])) (lf 1 [2508675,805763,1333123,1592207,1330082,643,1155,2179,1315075,4867,398339,5379,6275,7171,1157,2181,5125,6149,2310,397702,2185,135433,2186,397706,2188,397580,397714,397588,5140,528664,5666,6690,5157,6185,530475,6443,1376256,2129920,7127043,819233,4112418,819236,2146367])) (lf 1 [2508674,805762,1333122,1592207,1330082,1154,1538,2178,3074,398339,6147,528645,2310,399366,395529,395786,4490,397580,397585,4372,397592,6181,5158,6440,6696,7209,6314,6188,1376256,2129920,5423106,819233,2801698,819236,2146367])) (br 3 (br 48 (br 1 (br 2 (lf 2 [805764,280454,805766,18312,674696,1198986,1197964,1197970,2770850,2771874,921861,136197,921865,135689,790544,921873,135697,921876,136212,921880,135704,660002,136354,137378,137762,138274,135715,136484,136229,922662,137516,1900544,4358144,819201,819202,1212419,1736737,10928162,180260,2654256,4374591]) (lf 1 [2508674,805762,1333122,1592207,1330082,1154,528898,773,1541,266501,1286,2310,4742,6406,397577,2186,2314,4618,6666,395404,268050,397588,5140,528664,4643,5284,5412,6308,660518,7212,1376256,2129920,5685250,557059,819233,2539554,311332,819248,2146367])) (lf 1 [2508673,805761,1333121,1592207,1330082,2305,135169,1577217,397825,773,1157,2181,136197,1542,2310,1289,135689,6409,397834,395404,266642,529044,528664,5666,6306,6690,528931,529443,7203,5284,1376256,2129920,7520257,557059,1081377,3194914,1097764,819248,2146367])) (lf 4 [1591170,673668,805764,2509702,1066892,1592208,2508690,2508692,1460119,5654434,5655458,1576961,1446149,923653,1579784,1970441,397833,2497034,399372,792844,1970449,397841,1446168,922136,6296098,397986,398498,1316898,399522,397859,2496548,400420,2495526,4200486,923944,399914,399404,3997696,8814592,2523139,5275681,24559650,8437796,6733872,8831039])) (lf 1 [2508675,805763,1333123,1592207,1330082,771,1155,2307,527363,397571,528899,267267,5379,1541,2181,268293,1542,2566,2185,266761,4490,399370,2188,2572,4364,4369,4625,397714,266516,135714,5666,6690,7202,5284,6308,6436,5157,267302,1376256,2129920,6995971,819233,2277410,835620,2146367])))) (r26_k3_t1)
set_option maxRecDepth 8192 in
private lemma r26_k3_ok : checkLayer (r := 6) (cd := 1) 3 (VTree.ofFun 6 (fun a => (maskWeightFast r26_ws a : ℤ) + (2 : ℤ) * (3 : ℤ) - (23 : ℤ))) (0 : ℤ) (patGens 26) r26_fi r26_prev r26_k3_fc r26_k3_tr = true := by decide +kernel
private def r26_k4_fc : List FCutCert := []
private def r26_k4_tr : BnbTree := br 0 (br 2 (br 1 (lf 1 [19331,673668,280456,674696,281481,284556,542608,281489,281490,18324,150420,542624,674720,542626,543652,150448,137219,263428,267269,264198,5136,266392,5153,6177,1867776,1081345,1081346,2408511]) (lf 3 [9324417,3427201,5003137,5786511,4213664,674721,1049345,1049857,919553,1050881,3073,659713,1315329,267265,1054209,792577,920579,5123,1050756,266500,1315844,399492,1049605,919688,266504,266632,4616,268296,395785,530441,526348,397452,266512,266768,922256,528532,5799936,23904257,3440642,7389247])) (lf 3 [9324418,3427202,5003138,5786511,3820448,1067938,2228481,394753,4609,267265,6401,1049218,132098,1050114,1051138,266370,266754,267266,268290,792706,1049603,1050627,1053699,787460,525444,395396,1051652,135300,1054726,1050888,395273,922122,268298,266252,1183888,4368,266768,528657,5799936,23117826,7389247])) (br 2 (lf 1 [3032960,1067904,1595264,1854351,1330080,19361,19376,263425,264705,4609,5121,6145,515,133123,132228,2308,4356,136196,138244,1029,4357,5125,132102,2054,264328,268296,4617,264204,4368,4624,5648,135698,266392,4385,5154,3981312,1081346,2408511]) (lf 3 [9324416,3427200,5003136,5786511,3820448,1067938,2228481,394753,4609,267265,6401,1049218,132098,1050114,1051138,266370,266754,267266,268290,792706,1049603,1050627,1053699,787460,525444,395396,1051652,135300,1054726,1050888,395273,922122,268298,266252,1183888,4368,266768,528657,12107776,5029890,7389247]))
private lemma r26_k4_ok : checkLayer (r := 6) (cd := 1) 4 (VTree.ofFun 6 (fun a => (maskWeightFast r26_ws a : ℤ) + (2 : ℤ) * (4 : ℤ) - (23 : ℤ))) (0 : ℤ) (patGens 26) r26_fi r26_prev r26_k4_fc r26_k4_tr = true := by decide +kernel
private def r26_k5_fc : List FCutCert := []
private def r26_k5_tr : BnbTree := lf 2 [2770816,412544,1723265,936834,1726340,153477,153478,1723272,153481,19340,1066896,149393,149394,149396,411543,1197984,805792,674721,543650,674724,674736,660482,133123,133130,3084,4368,4120,5423167]
private lemma r26_k5_ok : checkLayer (r := 6) (cd := 1) 5 (VTree.ofFun 6 (fun a => (maskWeightFast r26_ws a : ℤ) + (2 : ℤ) * (5 : ℤ) - (23 : ℤ))) (0 : ℤ) (patGens 26) r26_fi r26_prev r26_k5_fc r26_k5_tr = true := by decide +kernel
private def r26_k6_fc : List FCutCert := []
private def r26_k6_tr : BnbTree := lf 1 [1329024,149377,281473,543618,543620,543624,542608,804768,19361,18338,18340,18344,19376,2932799]
private lemma r26_k6_ok : checkLayer (r := 6) (cd := 1) 6 (VTree.ofFun 6 (fun a => (maskWeightFast r26_ws a : ℤ) + (2 : ℤ) * (6 : ℤ) - (23 : ℤ))) (0 : ℤ) (patGens 26) r26_fi r26_prev r26_k6_fc r26_k6_tr = true := by decide +kernel
private lemma solve_row26 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hpat : HasPattern F 26) (hprev : ∀ pr ∈ r26_prev, ¬ HasPattern F pr) :
    ∃ W : Fin 12 → ℕ, 0 < ∑ i, W i ∧ F.card * (∑ i, W i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, W i) := by
  dsimp only [HasPattern, patR] at hpat
  obtain ⟨e0, he⟩ := hpat
  let e : Fin r26_ws.length ↪ Fin 12 := e0
  have he' : ∀ g ∈ patGens 26, decode e g ∈ F := he
  have hGens : ∀ g ∈ patGens 26, g < 2 ^ r26_ws.length ∧ decode e g ∈ F := by
    intro g hg
    refine ⟨?_, he' g hg⟩
    have hall : (patGens 26).all (· < 2 ^ r26_ws.length) = true := by decide
    simp only [List.all_eq_true, decide_eq_true_eq] at hall
    exact hall g hg
  have hFi : ∀ b ∈ r26_fi, b < 2 ^ r26_ws.length ∧ decode e b ∈ F :=
    checkClosureAux_sound closed empty he' [] r26_fi (fun _ h => by cases h) (by decide)
  have hTop : 2 ^ r26_ws.length - 1 ∈ r26_fi := by decide
  apply weight_from_fibers (r := r26_ws.length) (by decide) F e full (fun i => r26_ws[i.val]'i.isLt) 2 23 (by decide) (by decide) (0 : ℤ) (by decide)
  intro K hKsub hne
  have hkle : K.card ≤ 6 := K_card_le e hKsub
  have htop_iff : K = univ \ univ.map e ↔ K.card = 6 := K_eq_top_iff e hKsub
  have hlo_iff : K = ∅ ↔ K.card = 0 := card_eq_zero.symm
  have hoff : (if K = univ \ univ.map e then (0 : ℤ) else 0) - (if K = ∅ then (0 : ℤ) else 0) =
      (if K.card = 6 then (0 : ℤ) else 0) - (if K.card = 0 then (0 : ℤ) else 0) := by
    simp only [htop_iff, hlo_iff]
  rw [hoff]
  match hk : K.card with
  | 0 =>
    have h := checkLayer_sound (cd := 1) 0 closed minSize (ws := r26_ws) hKsub hk hne hGens hFi hTop hprev r26_k0_fc r26_k0_tr r26_k0_ok
    simpa [hk] using h
  | 1 =>
    have h := checkLayer_sound (cd := 4) 1 closed minSize (ws := r26_ws) hKsub hk hne hGens hFi hTop hprev r26_k1_fc r26_k1_tr r26_k1_ok
    simpa [hk] using h
  | 2 =>
    have h := checkLayer_sound (cd := 4) 2 closed minSize (ws := r26_ws) hKsub hk hne hGens hFi hTop hprev r26_k2_fc r26_k2_tr r26_k2_ok
    simpa [hk] using h
  | 3 =>
    have h := checkLayer_sound (cd := 1) 3 closed minSize (ws := r26_ws) hKsub hk hne hGens hFi hTop hprev r26_k3_fc r26_k3_tr r26_k3_ok
    simpa [hk] using h
  | 4 =>
    have h := checkLayer_sound (cd := 1) 4 closed minSize (ws := r26_ws) hKsub hk hne hGens hFi hTop hprev r26_k4_fc r26_k4_tr r26_k4_ok
    simpa [hk] using h
  | 5 =>
    have h := checkLayer_sound (cd := 1) 5 closed minSize (ws := r26_ws) hKsub hk hne hGens hFi hTop hprev r26_k5_fc r26_k5_tr r26_k5_ok
    simpa [hk] using h
  | 6 =>
    have h := checkLayer_sound (cd := 1) 6 closed minSize (ws := r26_ws) hKsub hk hne hGens hFi hTop hprev r26_k6_fc r26_k6_tr r26_k6_ok
    simpa [hk] using h
  | _ + 7 => omega

-- ==================== Row 27 (r=6) ====================
private def r27_ws : List ℕ := [2,2,2,2,2,2]
private def r27_fi : List ℕ := [0,15,31,47,63]
private def r27_prev : List ℕ := [7,8,12,16,26]
private def r27_k0_fc : List FCutCert := [d [23] 26 [0,1,2,3,4,5],d [27] 26 [0,1,3,2,4,5],d [29] 26 [0,2,3,1,4,5],d [30] 26 [1,2,3,0,4,5],d [39] 26 [0,1,2,3,5,4],d [43] 26 [0,1,3,2,5,4],d [45] 26 [0,2,3,1,5,4],d [46] 26 [1,2,3,0,5,4],t [51,53,57] 49 [] 12]
private def r27_k0_tr : BnbTree := br 51 (lf 2 [138037,7481,7737,7738,1736705,1736706,1212419,1736708,1212421,1212422,688135,1736712,1212425,1212426,688139,1212428,688141,688142,1736720,1212433,1212434,688147,1212436,688149,688150,196608,1212440,688153,688154,196609,688156,196610,196611,180255,1736736,1212449,1212450,688163,1212452,688165,688166,196612,1212456,688169,688170,196613,688172,196614,196615,180271,1212464,688177,688178,163891,688180,688184,704575]) (lf 2 [138035,138547,7733,7737,65544,1736705,1736706,1212419,1736708,1212421,1212422,688135,1736712,1212425,1212426,688139,1212428,688141,688142,1736720,1212433,1212434,688147,1212436,688149,688150,196608,1212440,688153,688154,196609,688156,196610,196611,180255,1736736,1212449,1212450,688163,1212452,688165,688166,196612,1212456,688169,688170,196613,688172,196614,196615,180271,1212464,688177,688178,311347,688180,688184,704575])
private lemma r27_k0_ok : checkLayer (r := 6) (cd := 4) 0 (VTree.ofFun 6 (fun a => (maskWeightFast r27_ws a : ℤ) + (1 : ℤ) * (0 : ℤ) - (9 : ℤ))) (-7 : ℤ) (patGens 27) r27_fi r27_prev r27_k0_fc r27_k0_tr = true := by decide +kernel
private def r27_k1_fc0 : List FCutCert := [d [7] 26 [0,1,2,3,6,5],d [11] 26 [0,1,3,2,6,5],d [13] 26 [0,2,3,1,6,5],d [14] 26 [1,2,3,0,6,5],d [19,23,25] 26 [0,4,6,1,3,2],d [19,25,51] 26 [0,4,6,1,3,5],d [19,23,26] 26 [1,4,6,0,3,2],d [19,23,35] 26 [0,1,6,4,5,2],d [19,27,35] 26 [0,1,6,4,5,3],d [19,23,49] 26 [0,4,6,1,5,2],d [19,23,50] 26 [1,4,6,0,5,2],d [19,27,50] 26 [1,4,6,0,5,3],d [19,21,29] 26 [0,4,6,2,1,3],d [19,21,53] 26 [0,4,6,2,1,5],d [21,23,25] 26 [0,4,6,2,3,1],d [21,28,53] 26 [2,4,6,0,3,5],d [21,23,37] 26 [0,2,6,4,5,1],d [21,29,37] 26 [0,2,6,4,5,3],d [21,23,49] 26 [0,4,6,2,5,1],d [21,29,49] 26 [0,4,6,2,5,3],d [21,29,52] 26 [2,4,6,0,5,3],d [19,22,30] 26 [1,4,6,2,0,3],d [19,22,54] 26 [1,4,6,2,0,5],d [21,22,30] 26 [2,4,6,1,0,3],d [22,23,26] 26 [1,4,6,2,3,0],d [22,28,54] 26 [2,4,6,1,3,5],d [22,23,38] 26 [1,2,6,4,5,0],d [22,30,38] 26 [1,2,6,4,5,3],d [22,23,50] 26 [1,4,6,2,5,0],d [22,30,50] 26 [1,4,6,2,5,3],d [22,23,52] 26 [2,4,6,1,5,0],d [22,30,52] 26 [2,4,6,1,5,3],d [19,25,29] 26 [0,4,6,3,1,2],d [21,25,27] 26 [0,4,6,3,2,1],d [25,27,41] 26 [0,3,6,4,5,1],d [25,29,41] 26 [0,3,6,4,5,2],d [25,27,49] 26 [0,4,6,3,5,1],d [25,29,49] 26 [0,4,6,3,5,2],d [25,27,56] 26 [3,4,6,0,5,1],d [25,29,56] 26 [3,4,6,0,5,2],d [19,26,30] 26 [1,4,6,3,0,2],d [19,26,58] 26 [1,4,6,3,0,5],d [25,26,30] 26 [3,4,6,1,0,2],d [26,27,42] 26 [1,3,6,4,5,0],d [26,30,42] 26 [1,3,6,4,5,2],d [26,27,50] 26 [1,4,6,3,5,0],d [26,30,50] 26 [1,4,6,3,5,2],d [26,27,56] 26 [3,4,6,1,5,0],d [26,30,56] 26 [3,4,6,1,5,2],d [21,28,60] 26 [2,4,6,3,0,5],d [22,28,29] 26 [2,4,6,3,1,0],d [22,28,60] 26 [2,4,6,3,1,5],d [25,28,30] 26 [3,4,6,2,0,1],d [25,28,60] 26 [3,4,6,2,0,5],d [26,28,29] 26 [3,4,6,2,1,0],d [26,28,60] 26 [3,4,6,2,1,5],d [28,29,44] 26 [2,3,6,4,5,0],d [28,30,44] 26 [2,3,6,4,5,1],d [28,29,52] 26 [2,4,6,3,5,0],d [28,30,52] 26 [2,4,6,3,5,1]]
private def r27_k1_fc1 : List FCutCert := [d [28,29,56] 26 [3,4,6,2,5,0],d [28,30,56] 26 [3,4,6,2,5,1],d [19,35,39] 26 [0,1,6,5,4,2],d [19,35,43] 26 [0,1,6,5,4,3],d [35,37,43] 26 [0,5,6,1,2,3],d [35,37,51] 26 [0,5,6,1,2,4],d [35,38,43] 26 [1,5,6,0,2,3],d [35,38,51] 26 [1,5,6,0,2,4],d [35,39,42] 26 [1,5,6,0,3,2],d [35,39,49] 26 [0,5,6,1,4,2],d [35,43,49] 26 [0,5,6,1,4,3],d [35,39,50] 26 [1,5,6,0,4,2],d [21,37,39] 26 [0,2,6,5,4,1],d [21,37,45] 26 [0,2,6,5,4,3],d [35,37,45] 26 [0,5,6,2,1,3],d [35,37,53] 26 [0,5,6,2,1,4],d [37,39,41] 26 [0,5,6,2,3,1],d [37,39,44] 26 [2,5,6,0,3,1],d [37,44,53] 26 [2,5,6,0,3,4],d [37,39,49] 26 [0,5,6,2,4,1],d [37,45,49] 26 [0,5,6,2,4,3],d [37,39,52] 26 [2,5,6,0,4,1],d [37,45,52] 26 [2,5,6,0,4,3],d [22,38,39] 26 [1,2,6,5,4,0],d [35,38,46] 26 [1,5,6,2,0,3],d [38,39,42] 26 [1,5,6,2,3,0],d [38,39,44] 26 [2,5,6,1,3,0],d [38,39,50] 26 [1,5,6,2,4,0],d [38,39,52] 26 [2,5,6,1,4,0],d [25,41,45] 26 [0,3,6,5,4,2],d [41,42,45] 26 [3,5,6,0,1,2],d [41,42,57] 26 [3,5,6,0,1,4],d [41,44,57] 26 [3,5,6,0,2,4],d [41,45,49] 26 [0,5,6,3,4,2],d [41,45,56] 26 [3,5,6,0,4,2],d [42,46,50] 26 [1,5,6,3,4,2],d [37,44,46] 26 [2,5,6,3,0,1],d [37,44,60] 26 [2,5,6,3,0,4],d [38,44,60] 26 [2,5,6,3,1,4],d [41,44,60] 26 [3,5,6,2,0,4],d [42,44,60] 26 [3,5,6,2,1,4],d [21,49,51] 26 [0,4,6,5,2,1],d [35,49,53] 26 [0,5,6,4,1,2],d [35,49,57] 26 [0,5,6,4,1,3],d [37,49,51] 26 [0,5,6,4,2,1],d [41,49,51] 26 [0,5,6,4,3,1],d [49,51,52] 26 [4,5,6,0,2,1],d [49,51,56] 26 [4,5,6,0,3,1],d [50,51,56] 26 [4,5,6,1,3,0],d [22,52,53] 26 [2,4,6,5,1,0],t [19,22,26,50] 82 [] 12,t [21,22,28,52] 84 [] 12,t [25,26,28,56] 88 [] 12,t [35,38,42,50] 98 [] 12,t [35,37,41,49] 97 [] 12,t [37,38,44,52] 100 [] 12,t [41,42,44,56] 104 [] 12,t [49,50,52,56] 112 [] 12,v [19,21,22] 87 [],v [19,25,26] 91 []]
private def r27_k1_fc2 : List FCutCert := [v [19,35,49,50] 115 [],v [21,25,28] 93 [],v [21,37,49,52] 117 [],v [22,26,28] 94 [],v [22,38,50,52] 118 [],v [25,41,49,56] 121 [],v [26,42,50,56] 122 [],v [28,44,52,56] 124 [],v [35,37,38] 103 [],v [35,41,42] 107 [],v [37,41,44] 109 [],v [38,42,44] 110 []]
private def r27_k1_fc : List FCutCert := r27_k1_fc0 ++ r27_k1_fc1 ++ r27_k1_fc2
private def r27_k1_t0 : BnbTree := br 26 (br 35 (br 38 (br 41 (br 42 (lf 1 [151445,153516,196725,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163862,426008,163865,163866,163868,688160,426017,426018,163875,426020,163877,163878,426024,163881,163882,426032,442431]) (lf 1 [151445,149418,5674,137386,137770,65631,65652,65662,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163862,426008,163865,32794,163868,688160,426017,426018,163875,426020,163877,163878,426024,32809,966698,426032,442431])) (lf 3 [675733,673705,399529,661801,662057,196699,196700,458868,196733,3047424,2260993,2260994,1474563,2260996,1474565,1474566,720896,2261000,1474569,1474570,720897,1474572,720898,720899,2261008,1474577,1474578,688147,1474580,688150,1474584,426009,688154,688156,2261024,1474593,1474594,688163,1474596,688165,688166,1474600,3325993,1474608,1491007])) (br 41 (lf 1 [151445,149414,137382,138278,196732,196739,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,426008,163865,163866,163868,688160,426017,426018,163875,426020,163877,966694,426024,163881,426032,442431]) (lf 1 [151445,149414,137382,137513,137769,196724,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163862,426008,163865,163866,163868,688160,426017,426018,163875,426020,163877,180262,426024,442409,426032,442431]))) (br 56 (br 44 (lf 1 [151445,149411,137763,196721,196722,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163862,426008,163865,163866,163868,688160,426017,426018,704547,426020,426024,163884,426032,163896,442431]) (br 38 (lf 1 [151445,149411,137763,137388,137516,196724,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163862,426008,163865,163866,163868,688160,426017,426018,180259,426020,163877,163878,426024,442412,426032,442431]) (lf 0 [5670,65620,49187,180262,49196]))) (lf 1 [151445,149411,138275,138278,196724,196725,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163862,426008,163865,163866,163868,688160,426017,426018,180259,426020,163877,426024,426032,704568,442431]))) (br 21 (br 35 (lf 1 [149402,149414,136346,137754,137388,196734,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163861,163862,426008,163865,704538,163868,688160,426017,426018,163875,426020,163877,426024,426032,442431]) (lf 1 [149402,149411,135578,136730,5283,6307,137763,65602,65603,65650,196734,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163861,163862,426008,163865,704538,163868,688160,426017,426018,1097763,426020,32805,426024,426032,442431])) (br 35 (lf 1 [149397,149417,135957,136725,137370,137754,196734,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,442389,163862,426008,163865,442394,163868,688160,426017,426018,163875,426020,163877,426024,426032,442431]) (lf 1 [149397,149411,135573,136725,135578,137754,136355,6307,196674,65637,196734,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,573461,163862,426008,163865,442394,163868,688160,426017,426018,1097763,426020,163877,426024,426032,442431])))
private def r27_k1_t1 : BnbTree := br 19 (br 22 (br 25 (r27_k1_t0) (br 26 (br 21 (br 35 (lf 1 [149401,149414,136729,137497,137770,196733,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163861,163862,426008,704537,163866,163868,688160,426017,426018,163875,426020,163877,426024,426032,442431]) (lf 1 [149401,149411,135577,136729,137763,196721,196733,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163861,163862,426008,704537,163866,163868,688160,426017,426018,704547,426020,163877,426024,426032,442431])) (lf 2 [411541,280486,18346,1969301,4501,268565,135577,136473,398873,458772,458787,458789,458791,65649,1998848,1474561,1474562,950275,1474564,950277,950278,458752,1474568,950281,950282,458753,950284,458754,458755,1474576,950289,950290,426003,950292,3063829,426006,950296,4112409,426010,426012,1474592,950305,950306,950308,426021,950312,950320,966719])) (lf 1 [149401,149414,1445145,135577,137753,136730,196641,196642,196644,196651,196653,196655,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163862,426008,2801689,2277402,163868,688160,426017,426018,426020,163877,426024,426032,442431]))) (br 26 (br 21 (br 25 (br 35 (lf 1 [149398,18345,18348,5398,137366,7190,65652,196732,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163861,704534,426008,163865,163866,163868,688160,426017,426018,163875,426020,163877,426024,426032,442431]) (lf 1 [149398,149411,135574,5398,5654,138275,6316,65650,196732,65665,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163861,704534,426008,163865,163866,163868,688160,426017,426018,704547,426020,32805,426024,426032,442431])) (lf 3 [673686,411561,149418,135574,136470,399510,400406,397721,136473,661017,721020,196733,3047424,2260993,2260994,1474563,2260996,1474565,1474566,720896,2261000,1474569,1474570,720897,1474572,720898,720899,2261008,1474577,1474578,688147,1474580,688149,2277398,1474584,966681,688154,688156,2261024,1474593,1474594,1474596,688165,1474600,1474608,1491007])) (lf 2 [411541,18346,280492,2493205,267413,7189,397718,136470,138262,458766,458770,458778,458780,458782,65652,1998848,1474561,1474562,950275,1474564,950277,950278,458752,1474568,950281,950282,458753,950284,458754,458755,1474576,950289,950290,426003,950292,4112405,4636694,950296,426010,426012,1474592,950305,950306,950308,426021,950312,950320,966719])) (lf 1 [149398,149411,1707286,136726,137366,136346,196631,196635,196639,196650,196652,196654,196656,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,3063830,426008,2801690,163868,688160,426017,426018,426020,163877,426024,426032,442431]))) (br 52 (br 56 (br 41 (br 21 (br 22 (lf 1 [149395,149420,135955,136467,196727,196728,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,966675,426004,163861,163862,426008,163868,688160,426017,426018,426020,163877,426024,163881,426032,163892,163896,442431]) (lf 1 [149395,1444627,136467,136726,196612,196615,196617,196632,196634,196636,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,2539539,426004,163861,2277398,426008,163868,688160,426017,426018,426020,163877,426024,163881,426032,163892,163896,442431])) (lf 1 [149395,153516,1182355,136467,135957,196614,196615,196618,196622,196626,196726,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,2539539,426004,2015253,426008,163868,688160,426017,426018,426020,163877,426024,163881,426032,163892,163896,442431])) (br 22 (lf 1 [149395,149417,135955,136339,136341,196724,196727,196728,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,966675,426004,163862,426008,163868,688160,426017,426018,426020,163877,426024,704553,426032,163892,442431]) (lf 1 [149395,149417,1444627,136339,5398,5654,196612,196615,196617,196632,196634,196636,65652,196726,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,2801683,426004,2539542,426008,163868,688160,426017,426018,426020,163877,426024,311337,426032,163892,32824,442431]))) (br 26 (lf 3 [673683,149411,149418,149420,134291,660243,6419,662547,662549,662550,196646,65644,458868,458872,196733,3047424,2260993,2260994,1474563,2260996,1474565,1474566,720896,2261000,1474569,1474570,720897,1474572,720898,720899,2261008,1474577,1474578,2408467,1474580,1474584,688154,688156,2261024,1474593,1474594,1474596,688165,1474600,1474608,688180,2670648,1491007]) (lf 0 [7194,65577,49171,180250,49208]))) (br 22 (br 21 (br 25 (lf 1 [149395,149418,137747,138259,137754,137769,196723,196728,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,704531,426004,163861,163862,426008,163865,163868,688160,426017,426018,426020,426024,426032,704564,442431]) (lf 1 [149395,18342,18348,1182867,136467,137747,137753,196616,196619,196642,196644,196646,65651,196727,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,2539539,426004,163861,163862,426008,2277401,163868,688160,426017,426018,426020,32805,426024,426032,311348,442431])) (lf 0 [6677,65549,49171,180245,49204])) (lf 0 [6678,65558,49171,180246,49204])))
private def r27_k1_t2 : BnbTree := br 35 (br 37 (br 38 (br 41 (br 21 (br 22 (lf 1 [149404,149418,137372,137500,196720,196735,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163861,163862,426008,966684,688160,426017,426018,163875,426020,163877,163878,426024,163881,426032,442431]) (lf 1 [149398,149418,1183254,137366,196637,196660,196665,196667,196669,196731,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163861,2015254,426008,2277404,688160,426017,426018,163875,426020,163877,163878,426024,163881,426032,442431])) (lf 1 [149397,149418,1445397,137500,196627,196658,196662,196664,196666,196668,196729,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,2015253,426008,3063836,688160,426017,426018,163875,426020,163877,163878,426024,163881,426032,442431])) (lf 1 [149404,149417,136346,136348,137500,196719,196724,196733,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,426008,704540,688160,426017,426018,163875,426020,163877,163878,426024,966697,426032,442431])) (br 22 (br 21 (lf 1 [149404,149414,135964,136348,137382,196720,196721,196723,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163861,163862,426008,704540,688160,426017,426018,426020,966694,426024,426032,442431]) (lf 1 [149397,149414,1183253,135957,135964,136348,196627,196662,196664,196666,196668,196721,196729,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,2015253,163862,426008,2801692,688160,426017,426018,426020,163877,704550,426024,426032,442431])) (lf 0 [4886,65561,180246,49180,49190]))) (br 21 (br 22 (lf 1 [149404,149413,135836,136476,137509,196720,196722,196723,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163861,163862,426008,704540,688160,426017,426018,426020,966693,426024,426032,442431]) (lf 1 [149398,149413,1445398,135830,136470,135836,196635,196637,196660,196665,196667,196669,196722,196731,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163861,2801686,426008,2801692,688160,426017,426018,426020,704549,426024,426032,442431])) (lf 0 [4757,65551,180245,49180,49189]))) (br 44 (br 37 (br 49 (lf 3 [673692,673699,135573,135574,135577,135578,135964,660636,136476,137500,137763,138275,458863,458864,458865,3047424,2260993,2260994,1474563,2260996,1474565,1474566,720896,2261000,1474569,1474570,720897,1474572,720898,720899,2261008,1474577,1474578,688147,1474580,1474584,2539548,2261024,1474593,1474594,2015267,1474596,688165,1474600,688172,1474608,688177,1491007]) (lf 1 [149404,149411,137365,137366,137369,135578,137372,135971,136483,137385,137777,138289,196677,196678,458854,720999,196728,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,426004,426008,180252,688160,426017,426018,2801699,426020,163877,426024,163884,426032,3588145,442431])) (lf 3 [673692,673699,660117,659862,135577,135578,660124,660771,661795,138275,660645,661669,662053,720960,720961,720970,2293835,458864,721024,3047424,2260993,2260994,1474563,2260996,1474565,1474566,720896,2261000,1474569,1474570,720897,1474572,720898,720899,2261008,1474577,1474578,688147,1474580,1474584,1228828,2261024,1474593,1474594,8568867,1474596,8568869,1474600,688172,1474608,1491007])) (lf 1 [149404,149411,1971740,137388,137516,196657,196659,196661,196663,196705,196706,196707,196708,196735,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,426008,3325980,688160,426017,426018,426020,426024,3588140,426032,442431]))
private def r27_k1_t3 : BnbTree := br 28 (br 37 (r27_k1_t1) (br 21 (br 22 (br 26 (br 35 (br 19 (br 38 (br 41 (lf 1 [151449,149413,136741,137509,138277,137770,196688,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163861,163862,426008,163866,163868,688160,426017,426018,163875,426020,966693,163878,426024,163881,426032,442431]) (lf 1 [149413,1184933,137513,196690,196697,196698,196701,196702,196738,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163861,163862,426008,163866,163868,688160,426017,426018,163875,426020,1753125,163878,426024,2539561,426032,442431])) (lf 1 [151449,149413,1446693,138278,196684,196687,196693,196694,196695,196696,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,163859,426004,163861,163862,426008,163866,163868,688160,426017,426018,163875,426020,2015269,2539558,426024,426032,442431])) (lf 1 [149395,149413,135827,136467,137491,138277,196613,196722,196723,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,966675,426004,163861,163862,426008,163866,163868,688160,426017,426018,426020,966693,426024,426032,442431])) (lf 1 [149411,135577,1708707,138277,196670,196676,196679,196684,196685,196687,196689,196736,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,426004,163861,163862,426008,163866,163868,688160,426017,426018,3063843,426020,3063845,426024,426032,442431])) (lf 3 [673690,673701,660115,660121,135578,135962,136346,136730,137370,137754,458866,458867,721022,3047424,2260993,2260994,1474563,2260996,1474565,1474566,720896,2261000,1474569,1474570,720897,1474572,720898,720899,2261008,1474577,1474578,1474580,688149,688150,1474584,2277402,688156,2261024,1474593,1474594,1474596,2539557,1474600,1474608,1491007])) (br 38 (br 44 (lf 1 [149398,149413,135830,5398,7190,4761,5401,6693,7205,65645,196718,196722,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,426004,163861,835606,426008,163868,688160,426017,426018,426020,835621,163878,426024,163884,426032,442431]) (lf 1 [149398,149413,135830,136726,135833,135843,137381,136746,137772,138284,196685,196686,196704,458849,196718,196738,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,426004,163861,704534,426008,163868,688160,426017,426018,426020,2539557,163878,426024,2277420,426032,442431])) (lf 0 [4901,65619,49174,49189,180262]))) (lf 1 [149397,149413,133779,133909,134293,135843,135973,136357,136741,458768,196625,458824,458825,196730,196734,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,426004,2801685,426008,163868,688160,426017,426018,426020,3063845,426024,426032,442431]))) (br 19 (r27_k1_t2) (br 21 (br 22 (br 26 (br 25 (br 49 (br 35 (lf 1 [149395,149414,135827,136467,136348,137500,196735,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,442387,426004,163861,163862,426008,163865,163866,442396,688160,426017,426018,163875,426020,426024,426032,163889,442431]) (lf 1 [149395,149411,138259,135843,135971,136355,136483,137763,458814,458815,196728,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,1490963,426004,163861,163862,426008,163865,163866,688160,426017,426018,2539555,426020,426024,426032,442431])) (lf 1 [149395,149420,136467,923795,137372,137382,196712,196713,196714,196715,196728,950272,688129,688130,425987,688132,425989,425990,196608,688136,425993,425994,196609,425996,196610,196611,688144,426001,426002,1490963,426004,163861,163862,426008,163865,163866,688160,426017,426018,426020,426024,426032,2539569,442431])) (lf 0 [3609,65568,49171,180249,49180])) (lf 0 [3610,65576,49171,180250,49180])) (lf 0 [3606,65557,49171,180246,49180])) (lf 0 [3605,65548,49171,180245,49180])))
private def r27_k1_tr : BnbTree := r27_k1_t3
set_option maxRecDepth 8192 in
private lemma r27_k1_ok : checkLayer (r := 6) (cd := 8) 1 (VTree.ofFun 6 (fun a => (maskWeightFast r27_ws a : ℤ) + (1 : ℤ) * (1 : ℤ) - (9 : ℤ))) (0 : ℤ) (patGens 27) r27_fi r27_prev r27_k1_fc r27_k1_tr = true := by decide +kernel
private def r27_k2_fc0 : List FCutCert := [d [3,5,11] 26 [0,6,7,1,2,3],d [3,5,19] 26 [0,6,7,1,2,4],d [3,5,35] 26 [0,6,7,1,2,5],d [3,6,11] 26 [1,6,7,0,2,3],d [3,6,19] 26 [1,6,7,0,2,4],d [3,6,35] 26 [1,6,7,0,2,5],d [3,7,9] 26 [0,6,7,1,3,2],d [3,9,19] 26 [0,6,7,1,3,4],d [3,9,35] 26 [0,6,7,1,3,5],d [3,7,10] 26 [1,6,7,0,3,2],d [3,10,19] 26 [1,6,7,0,3,4],d [3,10,35] 26 [1,6,7,0,3,5],d [3,7,17] 26 [0,6,7,1,4,2],d [3,11,17] 26 [0,6,7,1,4,3],d [3,17,35] 26 [0,6,7,1,4,5],d [3,7,18] 26 [1,6,7,0,4,2],d [3,11,18] 26 [1,6,7,0,4,3],d [3,18,35] 26 [1,6,7,0,4,5],d [3,7,33] 26 [0,6,7,1,5,2],d [3,11,33] 26 [0,6,7,1,5,3],d [3,19,33] 26 [0,6,7,1,5,4],d [3,7,34] 26 [1,6,7,0,5,2],d [3,11,34] 26 [1,6,7,0,5,3],d [3,19,34] 26 [1,6,7,0,5,4],d [3,5,13] 26 [0,6,7,2,1,3],d [3,5,21] 26 [0,6,7,2,1,4],d [3,5,37] 26 [0,6,7,2,1,5],d [5,6,13] 26 [2,6,7,0,1,3],d [5,6,21] 26 [2,6,7,0,1,4],d [5,6,37] 26 [2,6,7,0,1,5],d [5,7,9] 26 [0,6,7,2,3,1],d [5,9,21] 26 [0,6,7,2,3,4],d [5,9,37] 26 [0,6,7,2,3,5],d [5,7,12] 26 [2,6,7,0,3,1],d [5,12,21] 26 [2,6,7,0,3,4],d [5,12,37] 26 [2,6,7,0,3,5],d [5,7,17] 26 [0,6,7,2,4,1],d [5,13,17] 26 [0,6,7,2,4,3],d [5,17,37] 26 [0,6,7,2,4,5],d [5,7,20] 26 [2,6,7,0,4,1],d [5,13,20] 26 [2,6,7,0,4,3],d [5,20,37] 26 [2,6,7,0,4,5],d [5,7,33] 26 [0,6,7,2,5,1],d [5,13,33] 26 [0,6,7,2,5,3],d [5,21,33] 26 [0,6,7,2,5,4],d [5,7,36] 26 [2,6,7,0,5,1],d [5,13,36] 26 [2,6,7,0,5,3],d [5,21,36] 26 [2,6,7,0,5,4],d [3,6,14] 26 [1,6,7,2,0,3],d [3,6,22] 26 [1,6,7,2,0,4],d [3,6,38] 26 [1,6,7,2,0,5],d [5,6,14] 26 [2,6,7,1,0,3],d [5,6,22] 26 [2,6,7,1,0,4],d [5,6,38] 26 [2,6,7,1,0,5],d [6,7,10] 26 [1,6,7,2,3,0],d [6,10,22] 26 [1,6,7,2,3,4],d [6,10,38] 26 [1,6,7,2,3,5],d [6,7,12] 26 [2,6,7,1,3,0],d [6,12,22] 26 [2,6,7,1,3,4],d [6,12,38] 26 [2,6,7,1,3,5]]
private def r27_k2_fc1 : List FCutCert := [d [6,7,18] 26 [1,6,7,2,4,0],d [6,14,18] 26 [1,6,7,2,4,3],d [6,18,38] 26 [1,6,7,2,4,5],d [6,7,20] 26 [2,6,7,1,4,0],d [6,14,20] 26 [2,6,7,1,4,3],d [6,20,38] 26 [2,6,7,1,4,5],d [6,7,34] 26 [1,6,7,2,5,0],d [6,14,34] 26 [1,6,7,2,5,3],d [6,22,34] 26 [1,6,7,2,5,4],d [6,7,36] 26 [2,6,7,1,5,0],d [6,14,36] 26 [2,6,7,1,5,3],d [6,22,36] 26 [2,6,7,1,5,4],d [3,9,13] 26 [0,6,7,3,1,2],d [3,9,25] 26 [0,6,7,3,1,4],d [3,9,41] 26 [0,6,7,3,1,5],d [5,9,11] 26 [0,6,7,3,2,1],d [5,9,25] 26 [0,6,7,3,2,4],d [5,9,41] 26 [0,6,7,3,2,5],d [9,10,13] 26 [3,6,7,0,1,2],d [9,10,25] 26 [3,6,7,0,1,4],d [9,10,41] 26 [3,6,7,0,1,5],d [9,11,12] 26 [3,6,7,0,2,1],d [9,12,25] 26 [3,6,7,0,2,4],d [9,12,41] 26 [3,6,7,0,2,5],d [9,11,17] 26 [0,6,7,3,4,1],d [9,13,17] 26 [0,6,7,3,4,2],d [9,17,41] 26 [0,6,7,3,4,5],d [9,11,24] 26 [3,6,7,0,4,1],d [9,13,24] 26 [3,6,7,0,4,2],d [9,24,41] 26 [3,6,7,0,4,5],d [9,11,33] 26 [0,6,7,3,5,1],d [9,13,33] 26 [0,6,7,3,5,2],d [9,25,33] 26 [0,6,7,3,5,4],d [9,11,40] 26 [3,6,7,0,5,1],d [9,13,40] 26 [3,6,7,0,5,2],d [9,25,40] 26 [3,6,7,0,5,4],d [3,10,14] 26 [1,6,7,3,0,2],d [3,10,26] 26 [1,6,7,3,0,4],d [3,10,42] 26 [1,6,7,3,0,5],d [6,10,11] 26 [1,6,7,3,2,0],d [6,10,26] 26 [1,6,7,3,2,4],d [6,10,42] 26 [1,6,7,3,2,5],d [9,10,14] 26 [3,6,7,1,0,2],d [9,10,26] 26 [3,6,7,1,0,4],d [9,10,42] 26 [3,6,7,1,0,5],d [10,11,12] 26 [3,6,7,1,2,0],d [10,12,26] 26 [3,6,7,1,2,4],d [10,12,42] 26 [3,6,7,1,2,5],d [10,11,18] 26 [1,6,7,3,4,0],d [10,14,18] 26 [1,6,7,3,4,2],d [10,18,42] 26 [1,6,7,3,4,5],d [10,11,24] 26 [3,6,7,1,4,0],d [10,14,24] 26 [3,6,7,1,4,2],d [10,24,42] 26 [3,6,7,1,4,5],d [10,11,34] 26 [1,6,7,3,5,0],d [10,14,34] 26 [1,6,7,3,5,2],d [10,26,34] 26 [1,6,7,3,5,4],d [10,11,40] 26 [3,6,7,1,5,0],d [10,14,40] 26 [3,6,7,1,5,2],d [10,26,40] 26 [3,6,7,1,5,4]]
private def r27_k2_fc2 : List FCutCert := [d [5,12,14] 26 [2,6,7,3,0,1],d [5,12,28] 26 [2,6,7,3,0,4],d [5,12,44] 26 [2,6,7,3,0,5],d [6,12,13] 26 [2,6,7,3,1,0],d [6,12,28] 26 [2,6,7,3,1,4],d [6,12,44] 26 [2,6,7,3,1,5],d [9,12,14] 26 [3,6,7,2,0,1],d [9,12,28] 26 [3,6,7,2,0,4],d [9,12,44] 26 [3,6,7,2,0,5],d [10,12,13] 26 [3,6,7,2,1,0],d [10,12,28] 26 [3,6,7,2,1,4],d [10,12,44] 26 [3,6,7,2,1,5],d [12,13,20] 26 [2,6,7,3,4,0],d [12,14,20] 26 [2,6,7,3,4,1],d [12,20,44] 26 [2,6,7,3,4,5],d [12,13,24] 26 [3,6,7,2,4,0],d [12,14,24] 26 [3,6,7,2,4,1],d [12,24,44] 26 [3,6,7,2,4,5],d [12,13,36] 26 [2,6,7,3,5,0],d [12,14,36] 26 [2,6,7,3,5,1],d [12,28,36] 26 [2,6,7,3,5,4],d [12,13,40] 26 [3,6,7,2,5,0],d [12,14,40] 26 [3,6,7,2,5,1],d [12,28,40] 26 [3,6,7,2,5,4],d [3,17,21] 26 [0,6,7,4,1,2],d [3,17,25] 26 [0,6,7,4,1,3],d [3,17,49] 26 [0,6,7,4,1,5],d [5,17,19] 26 [0,6,7,4,2,1],d [5,17,25] 26 [0,6,7,4,2,3],d [5,17,49] 26 [0,6,7,4,2,5],d [9,17,19] 26 [0,6,7,4,3,1],d [9,17,21] 26 [0,6,7,4,3,2],d [9,17,49] 26 [0,6,7,4,3,5],d [17,18,21] 26 [4,6,7,0,1,2],d [17,18,25] 26 [4,6,7,0,1,3],d [17,18,49] 26 [4,6,7,0,1,5],d [17,19,20] 26 [4,6,7,0,2,1],d [17,20,25] 26 [4,6,7,0,2,3],d [17,20,49] 26 [4,6,7,0,2,5],d [17,19,24] 26 [4,6,7,0,3,1],d [17,21,24] 26 [4,6,7,0,3,2],d [17,24,49] 26 [4,6,7,0,3,5],d [17,19,33] 26 [0,6,7,4,5,1],d [17,21,33] 26 [0,6,7,4,5,2],d [17,25,33] 26 [0,6,7,4,5,3],d [17,19,48] 26 [4,6,7,0,5,1],d [17,21,48] 26 [4,6,7,0,5,2],d [17,25,48] 26 [4,6,7,0,5,3],d [3,18,22] 26 [1,6,7,4,0,2],d [3,18,26] 26 [1,6,7,4,0,3],d [3,18,50] 26 [1,6,7,4,0,5],d [6,18,19] 26 [1,6,7,4,2,0],d [6,18,26] 26 [1,6,7,4,2,3],d [6,18,50] 26 [1,6,7,4,2,5],d [10,18,19] 26 [1,6,7,4,3,0],d [10,18,22] 26 [1,6,7,4,3,2],d [10,18,50] 26 [1,6,7,4,3,5],d [17,18,22] 26 [4,6,7,1,0,2],d [17,18,26] 26 [4,6,7,1,0,3],d [17,18,50] 26 [4,6,7,1,0,5]]
private def r27_k2_fc3 : List FCutCert := [d [18,19,20] 26 [4,6,7,1,2,0],d [18,20,26] 26 [4,6,7,1,2,3],d [18,20,50] 26 [4,6,7,1,2,5],d [18,19,24] 26 [4,6,7,1,3,0],d [18,22,24] 26 [4,6,7,1,3,2],d [18,24,50] 26 [4,6,7,1,3,5],d [18,19,34] 26 [1,6,7,4,5,0],d [18,22,34] 26 [1,6,7,4,5,2],d [18,26,34] 26 [1,6,7,4,5,3],d [18,19,48] 26 [4,6,7,1,5,0],d [18,22,48] 26 [4,6,7,1,5,2],d [18,26,48] 26 [4,6,7,1,5,3],d [5,20,22] 26 [2,6,7,4,0,1],d [5,20,28] 26 [2,6,7,4,0,3],d [5,20,52] 26 [2,6,7,4,0,5],d [6,20,21] 26 [2,6,7,4,1,0],d [6,20,28] 26 [2,6,7,4,1,3],d [6,20,52] 26 [2,6,7,4,1,5],d [12,20,21] 26 [2,6,7,4,3,0],d [12,20,22] 26 [2,6,7,4,3,1],d [12,20,52] 26 [2,6,7,4,3,5],d [17,20,22] 26 [4,6,7,2,0,1],d [17,20,28] 26 [4,6,7,2,0,3],d [17,20,52] 26 [4,6,7,2,0,5],d [18,20,21] 26 [4,6,7,2,1,0],d [18,20,28] 26 [4,6,7,2,1,3],d [18,20,52] 26 [4,6,7,2,1,5],d [20,21,24] 26 [4,6,7,2,3,0],d [20,22,24] 26 [4,6,7,2,3,1],d [20,24,52] 26 [4,6,7,2,3,5],d [20,21,36] 26 [2,6,7,4,5,0],d [20,22,36] 26 [2,6,7,4,5,1],d [20,28,36] 26 [2,6,7,4,5,3],d [20,21,48] 26 [4,6,7,2,5,0],d [20,22,48] 26 [4,6,7,2,5,1],d [20,28,48] 26 [4,6,7,2,5,3],d [9,24,26] 26 [3,6,7,4,0,1],d [9,24,28] 26 [3,6,7,4,0,2],d [9,24,56] 26 [3,6,7,4,0,5],d [10,24,25] 26 [3,6,7,4,1,0],d [10,24,28] 26 [3,6,7,4,1,2],d [10,24,56] 26 [3,6,7,4,1,5],d [12,24,25] 26 [3,6,7,4,2,0],d [12,24,26] 26 [3,6,7,4,2,1],d [12,24,56] 26 [3,6,7,4,2,5],d [17,24,26] 26 [4,6,7,3,0,1],d [17,24,28] 26 [4,6,7,3,0,2],d [17,24,56] 26 [4,6,7,3,0,5],d [18,24,25] 26 [4,6,7,3,1,0],d [18,24,28] 26 [4,6,7,3,1,2],d [18,24,56] 26 [4,6,7,3,1,5],d [20,24,25] 26 [4,6,7,3,2,0],d [20,24,26] 26 [4,6,7,3,2,1],d [20,24,56] 26 [4,6,7,3,2,5],d [24,25,40] 26 [3,6,7,4,5,0],d [24,26,40] 26 [3,6,7,4,5,1],d [24,28,40] 26 [3,6,7,4,5,2],d [24,25,48] 26 [4,6,7,3,5,0],d [24,26,48] 26 [4,6,7,3,5,1],d [24,28,48] 26 [4,6,7,3,5,2]]
private def r27_k2_fc4 : List FCutCert := [d [3,33,37] 26 [0,6,7,5,1,2],d [3,33,41] 26 [0,6,7,5,1,3],d [3,33,49] 26 [0,6,7,5,1,4],d [5,33,35] 26 [0,6,7,5,2,1],d [5,33,41] 26 [0,6,7,5,2,3],d [5,33,49] 26 [0,6,7,5,2,4],d [9,33,35] 26 [0,6,7,5,3,1],d [9,33,37] 26 [0,6,7,5,3,2],d [9,33,49] 26 [0,6,7,5,3,4],d [17,33,35] 26 [0,6,7,5,4,1],d [17,33,37] 26 [0,6,7,5,4,2],d [17,33,41] 26 [0,6,7,5,4,3],d [33,34,37] 26 [5,6,7,0,1,2],d [33,34,41] 26 [5,6,7,0,1,3],d [33,34,49] 26 [5,6,7,0,1,4],d [33,35,36] 26 [5,6,7,0,2,1],d [33,36,41] 26 [5,6,7,0,2,3],d [33,36,49] 26 [5,6,7,0,2,4],d [33,35,40] 26 [5,6,7,0,3,1],d [33,37,40] 26 [5,6,7,0,3,2],d [33,40,49] 26 [5,6,7,0,3,4],d [33,35,48] 26 [5,6,7,0,4,1],d [33,37,48] 26 [5,6,7,0,4,2],d [33,41,48] 26 [5,6,7,0,4,3],d [3,34,38] 26 [1,6,7,5,0,2],d [3,34,42] 26 [1,6,7,5,0,3],d [3,34,50] 26 [1,6,7,5,0,4],d [6,34,35] 26 [1,6,7,5,2,0],d [6,34,42] 26 [1,6,7,5,2,3],d [6,34,50] 26 [1,6,7,5,2,4],d [10,34,35] 26 [1,6,7,5,3,0],d [10,34,38] 26 [1,6,7,5,3,2],d [10,34,50] 26 [1,6,7,5,3,4],d [18,34,35] 26 [1,6,7,5,4,0],d [18,34,38] 26 [1,6,7,5,4,2],d [18,34,42] 26 [1,6,7,5,4,3],d [33,34,38] 26 [5,6,7,1,0,2],d [33,34,42] 26 [5,6,7,1,0,3],d [33,34,50] 26 [5,6,7,1,0,4],d [34,35,36] 26 [5,6,7,1,2,0],d [34,36,42] 26 [5,6,7,1,2,3],d [34,36,50] 26 [5,6,7,1,2,4],d [34,35,40] 26 [5,6,7,1,3,0],d [34,38,40] 26 [5,6,7,1,3,2],d [34,40,50] 26 [5,6,7,1,3,4],d [34,35,48] 26 [5,6,7,1,4,0],d [34,38,48] 26 [5,6,7,1,4,2],d [34,42,48] 26 [5,6,7,1,4,3],d [5,36,38] 26 [2,6,7,5,0,1],d [5,36,44] 26 [2,6,7,5,0,3],d [5,36,52] 26 [2,6,7,5,0,4],d [6,36,37] 26 [2,6,7,5,1,0],d [6,36,44] 26 [2,6,7,5,1,3],d [6,36,52] 26 [2,6,7,5,1,4],d [12,36,37] 26 [2,6,7,5,3,0],d [12,36,38] 26 [2,6,7,5,3,1],d [12,36,52] 26 [2,6,7,5,3,4],d [20,36,37] 26 [2,6,7,5,4,0],d [20,36,38] 26 [2,6,7,5,4,1],d [20,36,44] 26 [2,6,7,5,4,3]]
private def r27_k2_fc5 : List FCutCert := [d [33,36,38] 26 [5,6,7,2,0,1],d [33,36,44] 26 [5,6,7,2,0,3],d [33,36,52] 26 [5,6,7,2,0,4],d [34,36,37] 26 [5,6,7,2,1,0],d [34,36,44] 26 [5,6,7,2,1,3],d [34,36,52] 26 [5,6,7,2,1,4],d [36,37,40] 26 [5,6,7,2,3,0],d [36,38,40] 26 [5,6,7,2,3,1],d [36,40,52] 26 [5,6,7,2,3,4],d [36,37,48] 26 [5,6,7,2,4,0],d [36,38,48] 26 [5,6,7,2,4,1],d [36,44,48] 26 [5,6,7,2,4,3],d [9,40,42] 26 [3,6,7,5,0,1],d [9,40,44] 26 [3,6,7,5,0,2],d [9,40,56] 26 [3,6,7,5,0,4],d [10,40,41] 26 [3,6,7,5,1,0],d [10,40,44] 26 [3,6,7,5,1,2],d [10,40,56] 26 [3,6,7,5,1,4],d [12,40,41] 26 [3,6,7,5,2,0],d [12,40,42] 26 [3,6,7,5,2,1],d [12,40,56] 26 [3,6,7,5,2,4],d [24,40,41] 26 [3,6,7,5,4,0],d [24,40,42] 26 [3,6,7,5,4,1],d [24,40,44] 26 [3,6,7,5,4,2],d [33,40,42] 26 [5,6,7,3,0,1],d [33,40,44] 26 [5,6,7,3,0,2],d [33,40,56] 26 [5,6,7,3,0,4],d [34,40,41] 26 [5,6,7,3,1,0],d [34,40,44] 26 [5,6,7,3,1,2],d [34,40,56] 26 [5,6,7,3,1,4],d [36,40,41] 26 [5,6,7,3,2,0],d [36,40,42] 26 [5,6,7,3,2,1],d [36,40,56] 26 [5,6,7,3,2,4],d [40,41,48] 26 [5,6,7,3,4,0],d [40,42,48] 26 [5,6,7,3,4,1],d [40,44,48] 26 [5,6,7,3,4,2],d [17,48,56] 26 [4,6,7,5,0,3],d [18,48,52] 26 [4,6,7,5,1,2],d [20,48,49] 26 [4,6,7,5,2,0],d [20,48,50] 26 [4,6,7,5,2,1],d [20,48,56] 26 [4,6,7,5,2,3],d [24,48,49] 26 [4,6,7,5,3,0],d [24,48,52] 26 [4,6,7,5,3,2],d [33,48,50] 26 [5,6,7,4,0,1],d [33,48,52] 26 [5,6,7,4,0,2],d [33,48,56] 26 [5,6,7,4,0,3],d [34,48,49] 26 [5,6,7,4,1,0],d [34,48,56] 26 [5,6,7,4,1,3],d [36,48,49] 26 [5,6,7,4,2,0],d [36,48,50] 26 [5,6,7,4,2,1],d [40,48,49] 26 [5,6,7,4,3,0],d [40,48,50] 26 [5,6,7,4,3,1],d [40,48,52] 26 [5,6,7,4,3,2],t [3,5,9,17,33] 193 [] 12,t [9,10,12,24,40] 200 [] 12,t [17,18,20,24,48] 208 [] 12,t [33,34,36,40,48] 224 [] 12,v [3,5,6] 199 [],v [3,9,10] 203 [],v [3,17,18] 211 []]
private def r27_k2_fc6 : List FCutCert := [v [3,33,34] 227 [],v [5,9,12] 205 [],v [5,17,20] 213 [],v [5,33,36] 229 [],v [6,10,12] 206 [],v [6,18,20] 214 [],v [6,34,36] 230 [],v [9,17,24] 217 [],v [9,33,40] 233 [],v [10,18,24] 218 [],v [10,34,40] 234 [],v [12,20,24] 220 [],v [12,36,40] 236 [],v [17,33,48] 241 [],v [18,34,48] 242 [],v [20,36,48] 244 [],v [24,40,48] 248 []]
private def r27_k2_fc : List FCutCert := r27_k2_fc0 ++ r27_k2_fc1 ++ r27_k2_fc2 ++ r27_k2_fc3 ++ r27_k2_fc4 ++ r27_k2_fc5 ++ r27_k2_fc6
private def r27_k2_t0 : BnbTree := br 33 (br 34 (br 36 (br 40 (br 48 (br 7 (br 11 (lf 2 [149390,18323,149397,149398,18330,149417,149418,149420,134285,4883,6682,138268,135843,6694,137521,1736704,1212417,1212418,688131,1212420,688133,688134,163847,1212424,688137,688138,163851,688140,1212432,688145,688146,688148,688152,1212448,688161,688162,688164,688168,688176,1228863]) (lf 2 [149387,675723,677771,2443,3339,136331,137355,137483,138251,133773,137742,4499,4502,4886,135833,3610,4892,136746,1736704,1212417,1212418,688131,1212420,688133,688134,163847,1212424,688137,688138,2801675,688140,1212432,688145,688146,688148,688152,1212448,688161,688162,688164,688168,688176,1228863])) (lf 1 [18311,282503,284551,2439,4743,6279,6407,6663,4491,2701,2830,3353,7196,5414,5673,819200,557057,557058,294915,557060,294917,294918,1359879,557064,294921,294922,294924,557072,294929,294930,294932,294936,557088,294945,294946,294948,294952,294960,573503])) (lf 3 [280455,280467,18326,18329,18330,280476,280485,280486,280489,268299,268301,268302,268309,137238,137497,137754,268323,268330,268332,269361,6706,2654208,1867777,1867778,1081347,1867780,1081349,1081350,1867784,1081353,1081354,1081356,1867792,1081361,1081362,1081364,1081368,1867808,1081377,1081378,1081380,1081384,1753136,1884223])) (lf 1 [20359,20363,18318,18330,280488,7181,5139,5141,5142,3609,5155,5157,5158,6312,6440,6696,65869,65870,65871,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,294936,557088,294945,294946,294948,1490984,573503])) (br 40 (lf 1 [20365,18318,18325,18326,280484,6663,7179,4627,4633,4634,4636,4643,5284,5412,6308,6436,65845,65846,65847,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,294936,557088,294945,294946,1490980,294952,573503]) (lf 1 [20359,18317,20366,18329,280484,5131,4627,5141,4630,4634,4636,4643,136228,6308,6440,65842,65843,65844,65866,65867,65868,328015,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,294936,557088,294945,294946,1753124,1359912,573503]))) (br 40 (br 36 (lf 1 [18311,20363,20365,18330,280482,6414,4371,4373,5398,4377,4380,4770,5282,5666,6690,7202,65821,65822,65882,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,294936,557088,294945,1490978,294948,294952,573503]) (lf 1 [18311,20363,18329,18332,280482,4621,4366,4627,4373,4374,4378,135714,5282,6306,7204,65815,65816,65817,65839,65840,65841,327990,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,294936,557088,294945,1753122,1359908,294952,573503])) (lf 1 [18311,20363,20366,18329,280482,5133,5139,4373,4374,4378,4380,4770,529442,6306,6690,6952,65818,65819,65820,65863,65864,65865,328011,328014,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,294936,557088,294945,2277410,2146344,573503]))) (br 34 (br 36 (br 40 (lf 1 [18315,20366,18325,18329,280481,6407,4237,4243,4246,4250,4252,4897,5409,6689,7201,6316,65797,65798,65799,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,294936,557088,1490977,294946,294948,294952,573503]) (lf 1 [18311,20363,18329,280481,4237,5134,5139,5141,4246,4250,4252,4897,136225,6433,6689,65794,65795,65796,65860,65861,65862,328013,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,294936,557088,1884193,294946,294948,1359912,573503])) (lf 1 [18311,20363,18323,18329,280481,4237,4622,4245,4246,4250,4252,528929,5409,6433,7201,65791,65792,65793,65836,65837,65838,327986,327989,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,294936,557088,2408481,294946,1884196,573503])) (lf 1 [18311,20363,20365,18329,280481,4366,4243,4373,4246,4250,4252,921889,5665,6689,7201,65788,65789,65790,65812,65813,65814,327959,327962,327965,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,294936,557088,2670625,2801698,573503]))
private def r27_k2_t1 : BnbTree := br 20 (br 24 (r27_k2_t0) (br 33 (br 34 (br 36 (br 40 (lf 1 [18311,22411,22413,280472,18346,3086,3091,3093,7190,4504,4760,4888,5272,5656,6424,6298,65773,65775,65878,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,1490968,557088,294945,294946,294948,294952,573503]) (lf 1 [18311,280472,280488,5131,3085,7182,3091,5141,3094,4504,6296,6424,6680,5157,5158,65770,65771,65772,65857,65858,65859,328056,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,2015256,557088,294945,294946,294948,1622056,573503])) (lf 1 [18317,280472,280484,4615,3083,4622,4627,3093,7702,4504,266776,4760,4888,5400,6168,4633,4634,5284,6436,7729,65775,65844,65847,196940,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,1359896,557088,294945,294946,1753124,573503])) (lf 1 [18318,280472,280482,4359,3083,3085,7443,4373,3094,266520,4504,4632,4760,4888,4377,4380,5282,5666,6306,6690,7460,65771,65820,65823,65883,65892,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,1359896,557088,163873,1884194,573503])) (lf 4 [18315,280461,1460120,1460129,397447,265227,4237,396302,3091,266387,396309,397462,1446040,4376,397720,397848,397976,398104,268568,397466,397468,398625,267809,6433,399905,400546,269476,7340,458989,196862,196868,459073,65862,328025,590180,3571712,2523137,2523138,1474563,2523140,1474565,1474566,2523144,1474569,1474570,1474572,2523152,1474577,1474578,1474580,6733848,2523168,7389217,2539583]))) (br 24 (br 33 (br 34 (br 36 (br 40 (lf 1 [22407,18315,280468,18342,18348,2573,6670,2579,3348,4500,5268,5396,6292,6420,7188,4758,6169,65749,65751,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,1359892,294936,557088,294945,294946,294948,294952,573503]) (lf 2 [149387,673684,673704,133639,138765,136206,136211,134292,660500,136340,136468,6292,137492,5141,6677,136214,136218,136227,136229,138790,6316,196823,65871,196948,65888,1736704,1212417,1212418,688131,1212420,688133,688134,1212424,688137,688138,688140,1212432,688145,688146,2670612,688152,1212448,688161,688162,688164,2670632,1228863])) (lf 1 [18315,280468,280484,2567,4621,2574,4627,3220,5268,6292,6420,7188,4634,4643,267300,5412,65746,65747,65748,65833,65834,459051,328055,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,2408468,294936,557088,294945,294946,2539556,573503])) (lf 1 [18318,280468,280482,4359,4363,2573,2579,3348,135444,4500,4756,5140,5268,5396,4373,4377,4380,5666,6306,7202,6952,65750,65817,65822,65841,65892,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,1359892,294936,557088,163873,1753122,573503])) (lf 4 [280455,18317,1460116,1460129,2567,397451,264717,395790,264723,4243,3220,1446036,266516,397716,5140,398484,398612,6420,269332,397462,266393,397466,397468,398113,398881,268577,7201,400034,400040,458962,327937,65795,65796,327942,459096,590180,3571712,2523137,2523138,1474563,2523140,1474565,1474566,2523144,1474569,1474570,1474572,2523152,1474577,1474578,6209556,1474584,2523168,7913505,2539583])) (lf 1 [18311,22411,280468,18338,18345,2573,2574,2579,1444884,4244,4372,4500,5652,4760,4888,5400,6296,135324,4380,6428,65743,65744,65745,327892,65767,65768,65769,327916,327919,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,3588116,3194904,557088,573503]))
private def r27_k2_t2 : BnbTree := br 18 (br 20 (br 24 (br 33 (br 34 (br 36 (lf 2 [149388,675724,677772,137223,138251,133772,133900,4748,135948,5260,137228,137356,137484,137747,136729,137242,4771,5411,5417,196749,196750,196751,1736704,1212417,1212418,688131,1212420,688133,688134,1212424,688137,688138,3588108,1212432,688145,688146,688148,688152,1212448,688161,688162,688164,1228863]) (lf 1 [18316,282508,284556,4615,4491,2700,3340,266764,5260,5388,7180,4627,5654,4633,6308,6436,65674,65675,65676,65830,65831,65832,327991,328052,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,2670604,557072,294929,294930,294932,294936,557088,294945,294946,2146340,573503])) (lf 3 [280460,1068940,1070988,266503,266507,265356,265484,659724,267404,268428,268556,268812,268301,266515,266517,266518,266524,269346,6181,268334,327819,327959,327963,65823,196902,196927,328008,65892,2654208,1867777,1867778,1081347,1867780,1081349,1081350,1867784,1081353,1081354,5554188,1867792,1081361,1081362,1081364,1081368,1867808,950305,3719202,1884223])) (br 34 (lf 3 [280460,1068940,1070988,266375,266379,265356,265484,1052812,267532,268300,268556,266387,266389,266390,266396,269345,268454,268333,268845,65674,327819,196749,327935,65792,327939,196871,328005,65892,2654208,1867777,1867778,1081347,1867780,1081349,1081350,1867784,1081353,1081354,5423116,1867792,1081361,1081362,1081364,1081368,1867808,4374561,950306,1884223]) (lf 1 [18316,282508,284556,4231,4235,2700,4236,4364,7181,4243,4246,4249,4250,4380,266786,267298,268322,6691,65788,65789,65790,459028,459029,459030,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,835596,557072,294929,294930,294932,294936,557088,2408481,2932770,573503]))) (lf 1 [18316,282508,284556,2439,3083,2700,2828,1313804,4236,4876,6668,138380,135320,4504,4760,5272,6424,266524,6314,65671,65672,65673,327820,65758,65759,65760,327916,327919,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,3981324,557072,294929,294930,294932,3457048,557088,573503])) (lf 1 [18316,282508,284556,2567,2443,1444364,3212,3340,135436,5260,6412,7180,4372,4500,4756,5908,266396,4892,6314,65668,65669,65670,327823,65734,65735,65736,327892,327895,328051,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,4505612,557072,294929,294930,3719188,557088,573503])) (br 20 (br 24 (br 33 (br 34 (lf 2 [149388,675724,677772,133383,133387,395532,2700,3212,136332,136460,6156,137356,137484,7180,135570,135826,136210,136722,137746,4883,7189,5145,135710,196747,65676,196749,65679,65725,196798,196799,65831,1736704,1212417,1212418,688131,1212420,688133,688134,1212424,688137,688138,3981324,1212432,688145,2146322,688148,688152,1212448,688161,688162,1228863]) (lf 2 [149388,675724,677772,133383,133387,919820,135436,4748,137356,6668,3597,5645,6674,138258,135445,135449,5660,659742,660002,4770,660514,136354,196794,196795,196796,196881,983314,983315,721270,1736704,1212417,1212418,688131,1212420,688133,688134,1212424,688137,688138,2801676,1212432,688145,5029906,688148,688152,1212448,688161,6602786,1228863])) (lf 4 [411532,1462156,1464204,395527,133387,135307,919820,395916,921740,397580,399372,399500,399628,134290,1446034,397842,397970,136210,398482,136466,398866,397462,135321,397466,397468,137246,138270,398113,136481,399905,138273,399780,399784,399405,327819,458893,65678,458938,65797,327953,65892,3571712,2523137,2523138,1474563,2523140,1474565,1474566,2523144,1474569,1474570,7782412,2523152,1474577,5554194,1474580,1474584,2523168,4898849,2539583])) (lf 0 [3090,65759,49164,49170,180248])) (lf 0 [2578,65735,49164,49170,180244]))
private def r27_k2_t3 : BnbTree := br 12 (br 18 (br 20 (br 24 (br 33 (br 34 (br 36 (br 40 (lf 1 [18311,22411,22414,280465,18339,2189,2833,3345,4753,4881,5265,5393,5649,6417,6300,7220,65701,65702,65703,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,1490961,294930,294932,294936,557088,294945,294946,294948,294952,573503]) (lf 1 [18318,280465,280488,2183,2187,5133,3601,4753,136209,5649,6417,5139,5141,5142,5146,7331,5158,6696,5417,65703,65872,65886,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,1228817,294930,294932,294936,557088,294945,294946,294948,1228840,573503])) (lf 1 [18317,280465,280484,6791,2187,4622,3601,266769,4881,5137,5393,5649,6417,4627,4630,4633,4634,4643,5284,7204,6824,65702,65844,65845,65884,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,1359889,294930,294932,294936,557088,294945,294946,1753124,573503])) (lf 3 [280455,1066897,1066914,266507,264333,266510,264977,265489,659729,266769,267025,267281,267537,267665,267793,266517,266521,266524,266914,267426,268834,269346,268708,327845,65817,196890,196892,65821,328026,196964,2654208,1867777,1867778,1081347,1867780,1081349,1081350,1867784,1081353,1081354,1081356,1867792,4636689,1081362,1081364,1081368,1867808,819233,5685282,1884223])) (lf 1 [18318,280465,280481,4231,2187,6285,2833,3601,4881,6417,6673,7185,4250,266529,266785,267297,5409,5665,65698,65699,65700,459001,459002,459003,328053,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,3194897,294930,294932,294936,557088,3981345,573503])) (lf 1 [18311,22414,280465,18339,18340,2187,2189,2833,1575953,4753,4881,5265,5393,6417,4376,5656,135449,135705,6681,65695,65696,65697,327844,65761,65762,65763,327914,327917,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,3850257,294930,294932,3063832,557088,573503])) (lf 1 [18315,22414,280465,18339,18344,2183,2189,1706513,3345,4369,4753,4881,5137,5393,5649,5140,5268,6420,135445,7189,65692,65693,65694,327843,65737,65738,65739,327887,327890,327893,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,4112401,294930,3719188,557088,573503])) (lf 1 [18315,22413,280465,18340,18344,2183,2318,1837329,3601,4497,4625,4881,5137,5393,5649,7441,4626,4754,5138,5266,7186,6675,65689,65690,65691,327842,65713,65714,65715,327860,327863,327866,327869,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,4243473,4636690,557088,573503])) (br 18 (br 20 (br 24 (br 33 (br 34 (lf 2 [149388,675724,677772,133255,133259,919692,133900,135820,6156,137484,7180,136718,135569,135697,135953,136337,136465,137747,137370,660509,196746,196748,196774,196775,65872,1736704,1212417,1212418,688131,1212420,688133,688134,1212424,688137,688138,3588108,1212432,2670609,688146,688148,688152,1212448,688161,688162,1228863]) (lf 1 [18316,282508,284556,4359,2187,2188,2828,135436,4748,137228,6412,6285,397585,4625,4881,5137,5393,5649,7697,2707,4377,4378,4380,5282,6690,137636,6568,7214,65678,65821,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,1622028,557072,1097745,294930,294932,294936,557088,294945,1228834,573503])) (lf 2 [149388,675724,677772,133255,133259,919692,135308,4876,137484,6668,3598,5646,6673,138257,135318,135322,5660,659613,659745,660001,4897,660513,136481,196770,196771,196772,983289,983290,983291,721269,1736704,1212417,1212418,688131,1212420,688133,688134,1212424,688137,688138,2801676,1212432,5816337,688146,688148,688152,1212448,8175649,1228863])) (lf 0 [3089,65758,49164,49169,180248])) (lf 0 [2577,65734,49164,49169,180244])) (lf 1 [18316,282508,284556,2183,2187,395404,133388,4622,266385,4497,5137,5393,264722,265234,266514,4882,5138,5266,5650,268306,7196,135709,4765,6686,65677,65689,65690,458907,458929,458930,852147,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,1359884,557072,3850257,4636690,557088,573503]))
private def r27_k2_t4 : BnbTree := br 20 (br 17 (br 24 (br 33 (br 34 (br 36 (lf 2 [149386,675722,677770,133511,134282,134666,4490,135946,5258,137226,137354,137738,137229,5269,6421,136470,6435,138277,137260,196725,196726,196727,1736704,1212417,1212418,688131,1212420,688133,688134,1212424,688137,3588106,688140,1212432,688145,688146,688148,688152,1212448,688161,688162,688164,1228863]) (lf 1 [18314,282506,284554,4615,2442,3594,266762,5258,6154,4621,5653,4758,4633,4506,6308,6436,7204,6698,137262,65653,65654,65843,819200,557057,557058,294915,557060,294917,294918,557064,294921,1622026,294924,557072,294929,294930,294932,294936,557088,294945,294946,835620,573503])) (lf 1 [18314,282506,284554,4359,2442,3594,659722,5258,5642,7178,4749,4373,5398,4377,6306,6690,65650,65651,65652,65806,65807,65808,327960,327967,328050,819200,557057,557058,294915,557060,294917,294918,557064,294921,3063818,294924,557072,294929,294930,294932,294936,557088,294945,2932770,573503])) (br 34 (lf 3 [280458,1068938,1070986,266375,265354,265738,659594,4874,136714,268298,268426,268810,135309,6157,6158,266899,266389,266390,266394,5665,268577,269345,268331,327797,196726,327935,327936,196908,328004,65892,2654208,1867777,1867778,1081347,1867780,1081349,1081350,1867784,1081353,5292042,1081356,1867792,1081361,1081362,1081364,1081368,1867808,3850273,950306,1884223]) (lf 0 [4385,65806,49162,49185,180258]))) (lf 1 [18314,282506,284554,2695,2442,2826,1182730,135306,4618,6282,6410,6666,3085,4504,4632,4760,5272,5528,4634,5658,4897,65647,65648,65649,327796,65755,65756,65757,327915,327918,819200,557057,557058,294915,557060,294917,294918,557064,294921,3981322,294924,557072,294929,294930,294932,3194904,557088,573503])) (br 24 (br 33 (br 34 (lf 1 [18314,282506,284554,2183,133258,2826,4618,5258,6154,6282,6666,4621,6158,3601,4497,4625,4881,5393,5649,7185,6421,4761,5147,65653,65655,65701,819200,557057,557058,294915,557060,294917,294918,557064,294921,1753098,294924,557072,966673,294930,294932,294936,557088,294945,294946,573503]) (lf 1 [18314,282506,284554,2183,395402,3594,659722,5642,7178,2189,266513,4373,5398,6297,266523,5282,6565,6707,65650,65651,65652,65806,65807,65808,327960,327967,328050,819200,557057,557058,294915,557060,294917,294918,557064,294921,3325962,294924,557072,704529,294930,294932,294936,557088,294945,3325986,573503])) (lf 2 [149386,675722,677770,133255,919690,135306,5642,137738,7178,133261,3342,5390,5649,137489,7185,135318,5402,659611,135324,659745,660001,135969,660513,196770,196771,196772,983289,983290,983291,721269,1736704,1212417,1212418,688131,1212420,688133,688134,1212424,688137,2801674,688140,1212432,5947409,688146,688148,688152,1212448,8044577,1228863])) (lf 0 [3089,65755,49162,49169,180248]))) (br 17 (br 24 (br 40 (br 33 (lf 2 [149386,675722,677770,133639,657930,134282,135562,135690,137226,137354,133645,137747,135828,136340,136468,136724,137492,138261,135710,135966,196722,196723,196724,65748,196822,65751,65911,1736704,1212417,1212418,688131,1212420,688133,688134,1212424,688137,3850250,688140,1212432,688145,688146,2408468,688152,1212448,688161,688168,1228863]) (lf 1 [18314,282506,284554,4231,133642,266378,4618,6154,6282,6666,3339,4237,2579,266388,4500,4884,5268,5396,7188,4246,4249,4252,4638,6433,6818,137259,6828,65651,65746,65788,819200,557057,557058,294915,557060,294917,294918,557064,294921,1753098,294924,557072,294929,294930,1097748,294936,557088,1228833,294952,573503])) (lf 1 [18314,282506,284554,2567,2442,395786,4490,4874,922634,6282,6410,7693,267284,3605,6678,7705,267294,5157,65653,65654,65655,65851,65852,65853,328004,328011,328014,328050,819200,557057,557058,294915,557060,294917,294918,557064,294921,3850250,294924,557072,294929,294930,573460,294936,557088,3850280,573503])) (lf 0 [3092,65756,49162,49172,180248])) (lf 1 [18314,282506,284554,2183,264330,395786,5258,2189,4366,266385,4753,5393,5649,6417,265236,266772,5140,268308,5146,4507,7195,135454,4894,65653,65692,65693,458910,65737,458954,852171,819200,557057,557058,294915,557060,294917,294918,557064,294921,1622026,294924,557072,3457041,294930,3719188,557088,573503]))
private def r27_k2_t5 : BnbTree := br 20 (br 34 (br 36 (br 48 (lf 8 [935817,3035017,3037065,920327,919945,264841,527881,922249,922889,661641,923913,924169,138249,137355,662541,527630,267790,529557,266649,529945,267418,267036,529187,196686,196689,196695,196701,2818402,7241728,5144577,5144578,3047427,5144580,3047429,3047430,5144584,15384585,5144592,3047441,3047442,3047444,5144608,3047457,3047458,3047460,3047472,5161023]) (lf 4 [411529,1462153,1464201,399367,395913,396553,398601,398857,1447945,399625,399881,399370,399371,400524,399373,399374,400531,399382,399388,399395,399397,400422,65615,65619,327769,327775,196949,196958,852322,3571712,2523137,2523138,1474563,2523140,1474565,1474566,2523144,8699913,2523152,1474577,1474578,1474580,2523168,1474593,1474594,1474596,5161008,2539583])) (br 10 (br 12 (lf 2 [149385,675721,677769,135687,133513,133769,135561,659977,137481,137737,138249,135694,135702,136473,135706,135708,137380,399405,196695,196696,65625,196914,196918,196921,65866,65890,1736704,1212417,1212418,688131,1212420,688133,688134,1212424,4374537,557066,557068,1212432,688145,688146,688148,1212448,688161,688162,2146340,1228863]) (lf 0 [4620,65664,49161,180236,49188])) (lf 1 [18313,282505,284553,4615,1312009,2441,2697,4489,4617,2826,4618,6666,137227,7179,4636,6308,6437,6182,65614,65615,65616,65638,65639,65640,327785,327791,327797,819200,557057,557058,294915,557060,294917,294918,557064,3194889,3325962,557072,294929,294930,294932,557088,294945,294946,180260,573503]))) (br 36 (br 10 (br 12 (lf 2 [149385,675721,677769,135431,133513,528649,136713,137481,137737,138249,134157,135438,135445,135446,4760,4888,4377,135450,135452,137378,6181,268331,196695,65631,65819,196893,196920,196935,1736704,1212417,1212418,688131,1212420,688133,688134,1212424,3588105,688138,688140,1212432,688145,688146,688148,1212448,688161,2408482,688164,1228863]) (lf 1 [18313,282505,284553,4359,919049,2441,2697,4361,4745,2828,4364,6668,137229,7181,4378,6435,6182,6314,65617,65618,65619,65662,65663,65664,327815,327821,819200,557057,557058,294915,557060,294917,294918,557064,2801673,294922,2539532,557072,294929,294930,294932,557088,294945,49186,294948,573503])) (lf 0 [4362,65640,49161,180234,49186])) (lf 1 [18313,282505,284553,4359,3337,4361,4617,6281,266506,266764,2701,4366,4371,4374,4376,4632,4377,4380,267300,268324,7206,65623,65815,459032,65817,65839,852272,459057,819200,557057,557058,294915,557060,294917,294918,557064,1097737,557072,294929,294930,294932,557088,294945,3325986,3325988,573503]))) (br 34 (br 10 (br 24 (br 12 (lf 2 [149385,675721,677769,137735,657929,134409,4617,4745,136457,137481,138249,133646,133651,135572,135956,136340,136724,137364,397853,196701,196702,196703,196821,196822,196823,65833,1736704,1212417,1212418,688131,1212420,688133,688134,1212424,3850249,688138,688140,1212432,688145,688146,2670612,688152,1212448,688161,688162,1228863]) (lf 0 [2572,65663,49161,180236,49172])) (lf 0 [3092,65753,49161,49172,180248])) (lf 1 [18313,282505,284553,2567,918793,2441,264713,5641,6153,395786,6154,4500,6292,7188,6678,4764,135709,4638,4894,6430,65614,65615,65616,65638,65639,65640,327785,327791,327797,65749,819200,557057,557058,294915,557060,294917,294918,557064,3063817,3194890,557072,294929,294930,1097748,557088,294945,294946,573503])) (lf 1 [18313,282505,284553,2567,133641,3337,135433,4617,6153,6409,6665,2570,6924,4366,2579,135444,4500,5268,5396,5652,6292,4373,4375,4377,4380,6173,4770,7202,6187,65623,65630,65747,65834,196962,819200,557057,557058,294915,557060,294917,294918,557064,2146313,557072,294929,294930,1359892,557088,294945,966690,573503]))
private def r27_k2_t6 : BnbTree := br 9 (br 10 (br 17 (br 12 (br 18 (r27_k2_t1) (br 20 (br 24 (br 33 (br 34 (br 36 (br 40 (lf 1 [18317,22414,280466,18342,18346,6407,2315,2706,3602,4754,5266,5650,6290,6674,7186,6169,4506,65725,65726,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,1359890,294932,294936,557088,294945,294946,294948,294952,573503]) (lf 1 [18315,280466,280488,2311,5133,5134,3218,3602,4754,4882,136210,5266,5650,5139,7189,5142,7459,6312,6696,65727,65870,65887,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,1228818,294932,294936,557088,294945,294946,294948,1228840,573503])) (lf 1 [18318,280466,280484,2311,2315,4621,3602,266770,4754,5138,5266,5650,4627,6933,4633,4634,4643,5412,6308,7204,6952,65726,65843,65873,65885,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,1490962,294932,294936,557088,294945,294946,1622052,573503])) (lf 1 [18317,280466,280482,2311,2315,4366,3602,4754,5650,6290,6674,7186,4373,4377,266786,267298,5282,65722,65723,65724,65809,459026,459027,328054,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,2932754,294932,294936,557088,294945,3194914,573503])) (lf 4 [18311,280459,1460114,1460129,268679,2315,397453,395534,395922,265362,1446034,397842,397970,267282,398482,398866,7186,397462,4249,397466,397468,398113,398625,399905,269345,6564,399784,327866,65725,459006,196863,196869,459095,590180,3571712,2523137,2523138,1474563,2523140,1474565,1474566,2523144,1474569,1474570,1474572,2523152,1474577,6209554,1474580,1474584,2523168,7913505,2539583])) (lf 1 [18311,22411,280466,18339,18340,3085,2318,2706,1575954,4242,4754,4882,5266,5394,4248,5656,4250,135706,6298,6682,65719,65720,65721,327868,65764,65765,65766,327915,327918,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,3719186,294932,3194904,557088,573503])) (lf 1 [18311,22411,280466,18339,18348,2573,2318,1837586,3218,4242,4754,4882,5138,5266,5140,5396,6292,135318,5142,7190,65716,65717,65718,327867,65740,65741,65742,327888,327891,327894,819200,557057,557058,294915,557060,294917,294918,557064,294921,294922,294924,557072,294929,3981330,3981332,557088,573503]))) (r27_k2_t2)) (r27_k2_t3)) (br 18 (br 12 (r27_k2_t4) (lf 1 [18314,282506,284554,2183,1967626,2186,2826,135306,4874,6154,6282,2700,5260,6156,6412,6158,7182,6673,4243,5529,4771,65641,65642,65643,327795,65665,65666,65667,327813,327816,327819,327822,819200,557057,557058,294915,557060,294917,294918,557064,294921,4636682,4505612,557072,294930,557088,573503])) (lf 1 [18314,282506,284554,2311,2230538,3210,3594,4234,4618,6282,137610,6666,7178,2701,135314,4498,4754,4882,5650,4634,5284,327786,65644,65645,65646,327799,65710,65711,65712,327858,327861,327868,327871,328049,819200,557057,557058,294915,557060,294917,294918,557064,294921,5947402,557072,5554194,557088,573503]))) (br 17 (br 33 (br 18 (r27_k2_t5) (br 20 (br 34 (br 10 (br 12 (br 24 (lf 1 [18313,282505,284553,2311,133385,2697,4617,5385,6281,6409,6665,7181,2318,4498,4754,4882,5138,5266,5650,4633,4634,5147,6172,65629,65725,65726,819200,557057,557058,294915,557060,294917,294918,557064,1622025,294922,294924,557072,294929,1097746,294932,294936,557088,294945,294946,573503]) (lf 0 [3090,65752,49161,49170,180248])) (lf 1 [18313,282505,284553,2311,1050121,264457,2697,6409,395532,4876,7181,6674,4758,5402,4507,6299,268318,65617,65618,65619,65662,65663,65664,327815,327818,327821,819200,557057,557058,294915,557060,294917,294918,557064,3063817,294922,3325964,557072,294929,704530,294932,557088,294945,294946,573503])) (lf 0 [2314,65639,49161,180234,49170])) (lf 2 [149385,675721,677769,133383,919817,3593,135433,7177,659722,395532,3213,5261,133390,658450,137362,137746,7186,135445,5273,659739,4380,397598,660002,135842,660514,136738,196689,196794,196795,983228,196881,983314,1769747,721270,1736704,1212417,1212418,688131,1212420,688133,688134,1212424,2801673,1212432,688145,8175634,688148,1212448,688161,9486370,1228863])) (lf 1 [18313,282505,284553,2311,264457,133641,5385,264458,264716,7181,2318,266514,4498,4754,4882,5138,265236,266772,5268,268308,5145,5147,6299,5661,65716,458933,458934,65740,852173,852174,819200,557057,557058,294915,557060,294917,294918,557064,1228809,557072,294929,4636690,4636692,557088,294945,573503]))) (lf 1 [18313,282505,284553,6663,2569,3337,2363529,5385,5641,6409,137865,7177,2318,136338,4243,135316,4245,4246,4252,4897,327760,327763,327769,65626,65627,65628,65782,65783,65784,327933,327936,327943,328048,819200,557057,557058,294915,557060,294917,294918,557064,6340617,557072,294929,557088,5292065,573503])) (lf 1 [18313,282505,284553,2183,2754697,3337,3593,4361,4617,6409,6665,7177,2830,4369,4753,4881,5393,5649,4377,4633,4643,327759,327762,65620,65621,65622,327775,65686,65687,65688,327834,327837,327844,327847,328047,819200,557057,557058,294915,557060,294917,294918,557064,6602761,557072,5947409,557088,573503]))
private def r27_k2_t7 : BnbTree := br 17 (br 18 (br 10 (br 12 (br 20 (br 33 (br 34 (lf 2 [149382,675718,677766,133510,134662,135814,136454,137350,137734,138246,5259,6411,137229,135957,136729,137242,137251,6441,196677,196678,196679,1736704,1212417,1212418,688131,1212420,688133,3588102,1212424,688137,688138,688140,1212432,688145,688146,688148,688152,1212448,688161,688162,688168,1228863]) (lf 1 [18310,282502,284550,3334,266502,4742,5638,6278,6662,7174,4363,5261,4883,4373,4377,4380,65602,65603,65604,65803,65804,65805,327966,328046,819200,557057,557058,294915,557060,294917,2801670,557064,294921,294922,294924,557072,294929,294930,294932,294936,557088,294945,2015266,294952,573503])) (lf 3 [280454,1068934,1070982,264838,265478,1052806,267526,268294,269318,266379,268429,266387,266390,266393,266396,267809,268833,268327,268583,327747,327749,327932,65789,327935,196871,65812,196908,65892,2654208,1867777,1867778,1081347,1867780,1081349,5423110,1867784,1081353,1081354,1081356,1867792,1081361,1081362,1081364,1081368,1867808,4374561,950312,1884223])) (lf 2 [149382,675718,677766,133510,2230790,134406,135302,136710,137350,137478,138246,3211,4235,133645,135572,135828,136340,136468,135318,4249,196671,196672,196673,720964,196803,196804,196805,721107,721110,1736704,1212417,1212418,688131,1212420,688133,7520262,1212424,688137,688138,688140,1212432,688145,688146,5947412,688152,1212448,688168,1228863])) (lf 1 [18310,282502,284550,1312262,2438,3334,4486,5382,6662,4235,3212,4748,7180,268302,4245,6433,6313,65593,65594,65595,327747,65659,65660,65661,327813,327819,819200,557057,557058,294915,557060,294917,3719174,557064,294921,294922,2932748,557072,294929,294930,294936,557088,294952,573503])) (lf 1 [18310,282502,284550,1049862,2694,3590,4230,5638,6150,6278,7174,2442,4490,6410,4237,6158,4761,6689,6185,65590,65591,65592,327744,327750,65635,65636,65637,327795,328044,819200,557057,557058,294915,557060,294917,4505606,557064,294921,2670602,557072,294929,294930,294936,557088,294952,573503])) (lf 2 [149382,675718,677766,3803398,133766,134662,135302,136710,137350,137734,138246,133387,3213,4237,135570,135826,136338,136466,135318,4249,720954,196668,196669,196670,720967,196779,196780,196781,721071,721083,721086,721261,1736704,1212417,1212418,688131,1212420,688133,10665990,1212424,688137,1212432,688145,9093138,688152,1212448,688168,1228863])) (br 10 (br 12 (br 18 (br 20 (br 33 (lf 2 [149382,675718,677766,657542,134406,135814,137350,137478,138246,133259,133261,135438,135441,136337,136465,136721,137745,135575,137239,4377,4633,135964,196677,196679,196773,196774,65902,1736704,1212417,1212418,688131,1212420,688133,3719174,1212424,688137,688138,688140,1212432,2277393,688146,688148,688152,1212448,688161,688168,1228863]) (lf 2 [149382,675718,677766,919686,3334,135302,5382,6662,138246,133259,133261,2830,4878,136721,137489,6673,4886,659607,4250,135324,659745,660001,5409,196770,196771,196772,983289,983290,196859,721269,1736704,1212417,1212418,688131,1212420,688133,2932742,1212424,688137,688138,688140,1212432,5292049,688146,688148,688152,1212448,6209569,688168,1228863])) (lf 0 [2577,65731,49158,49169,180244])) (lf 0 [2321,65707,49158,49169,180242])) (lf 1 [18310,282502,284550,1312262,264326,3334,4230,5382,6278,2187,395404,5260,4497,6673,7187,4247,6423,6169,4765,137245,65593,65594,65595,327741,327747,65659,65660,65661,327813,327819,65699,819200,557057,557058,294915,557060,294917,4374534,557064,294921,294922,3194892,557072,966673,294936,557088,294952,573503])) (lf 1 [18310,282502,284550,1312006,133254,3590,6150,6278,7174,395402,4490,2189,5265,6417,6673,4759,5657,266395,65590,65591,65592,327744,327750,65635,65636,65637,327789,327795,65701,65702,328044,819200,557057,557058,294915,557060,294917,4636678,557064,294921,3588106,557072,1097745,294936,557088,294952,573503]))
private def r27_k2_t8 : BnbTree := br 24 (br 9 (r27_k2_t7) (br 20 (br 10 (br 12 (br 17 (br 18 (br 33 (br 34 (br 36 (lf 2 [149382,675718,677766,2694,134662,135558,136710,137350,137478,138246,2823,6151,133513,135817,5385,268297,137737,5259,7307,134285,137230,4885,5398,4890,5274,1736704,1212417,1212418,688131,1212420,688133,2670598,1212424,442377,688138,688140,1212432,688145,688146,688148,688152,1212448,688161,688162,688164,688168,1228863]) (lf 1 [18310,282502,284550,2438,3590,4486,135686,5382,6278,6406,3337,135689,5259,4629,4633,7204,65605,65606,65607,65827,65828,65829,327990,819200,557057,557058,294915,557060,294917,2277382,557064,294922,294924,557072,294929,294930,294932,294936,557088,294945,294946,1622052,294952,573503])) (lf 1 [18310,282502,284550,2438,135430,4742,5638,6662,3337,135433,5261,4373,4377,4380,6306,7202,65602,65603,65604,65803,65804,65805,327966,328046,819200,557057,557058,294915,557060,294917,2408454,557064,294922,294924,557072,294929,294930,294932,294936,557088,294945,2277410,294952,573503])) (lf 1 [18310,282502,284550,3334,4230,7174,2823,2441,2697,921737,5385,5641,4878,4252,6433,6689,65626,65627,65628,65782,65783,65784,327933,327936,327943,819200,557057,557058,294915,557060,294917,835590,557064,1884169,294922,294924,557072,294929,294930,294932,294936,557088,3063841,294952,573503])) (lf 1 [18310,282502,284550,919814,2694,3590,4742,5382,6278,6662,264457,4489,7177,3213,4242,5266,5650,135323,65596,65597,65598,327751,65707,65708,65709,327867,327870,819200,557057,557058,294915,557060,294917,3457030,557064,180233,294922,294924,557072,294929,2932754,294932,294936,557088,294952,573503])) (lf 1 [18310,282502,284550,264326,4742,6406,7174,1050761,3337,3593,4361,4617,6665,2830,4497,4881,5393,5649,135703,4377,65602,65620,65621,65622,65686,65687,65688,327834,327844,327847,819200,557057,557058,294915,557060,294917,1359878,557064,2146313,294922,294924,557072,3588113,294932,294936,557088,294952,573503])) (lf 0 [1545,65659,49158,49161,180236])) (lf 0 [1289,65635,49158,49161,180234])) (lf 1 [18310,282502,284550,2438,2230790,3334,4742,5382,6406,7174,395785,4489,6281,3211,5261,5654,266397,327735,65599,65600,65601,327748,65731,65732,65733,327879,327881,327891,327894,328045,819200,557057,557058,294915,557060,294917,5554182,557064,311305,557072,5160980,294936,557088,294952,573503]))) (br 10 (br 9 (br 12 (br 34 (br 17 (br 20 (br 18 (lf 1 [18310,282502,284550,2438,134150,4230,5638,6278,6406,7174,3083,5261,3093,4248,4504,4760,4888,5400,6680,4252,6174,65605,65606,65607,65773,65774,819200,557057,557058,294915,557060,294917,1884166,557064,294921,294922,294924,557072,294929,294930,294932,1097752,557088,294946,294952,573503]) (lf 0 [3090,65708,49158,180242,49176])) (lf 0 [3092,65732,49158,180244,49176])) (lf 1 [18310,282502,284550,133254,3078,6663,2187,2189,266385,4497,4625,4881,5265,5393,5649,265234,265236,4759,268312,6424,4633,65606,65695,65696,458913,458977,458978,458979,819200,557057,557058,294915,557060,294917,966662,557064,294921,294922,294924,557072,3588113,3325976,557088,294946,294952,573503])) (lf 1 [18310,282502,284550,2438,396294,1577222,5638,6662,4363,3085,4369,135953,4373,266520,4760,3353,7196,266526,7465,7473,327745,65602,65603,65604,65803,65804,65805,327954,327956,327966,328046,819200,557057,557058,294915,557060,294917,4636678,557064,294921,294922,294924,557072,704536,557088,4767778,294952,573503])) (lf 0 [3084,65660,49158,180236,49176])) (lf 2 [149382,675718,677766,789510,5638,137350,137478,133895,133513,133769,3804169,135689,136457,137737,4878,4376,135576,135704,135832,4888,4633,5657,528670,65606,196695,196696,196697,720988,196824,196825,196826,721118,721124,721127,721133,721263,1736704,1212417,1212418,688131,1212420,688133,2670598,1212424,7520265,688138,1212432,10534936,1212448,688168,1228863])) (lf 0 [3082,65636,49158,180234,49176]))
private def r27_k2_t9 : BnbTree := br 24 (br 9 (br 17 (br 10 (br 18 (br 20 (br 33 (br 34 (lf 2 [149379,675715,677763,133763,134275,135683,136451,137347,137731,138243,137223,137227,134669,135694,136339,135574,135962,137508,5669,6181,6188,1736704,1212417,1212418,2801667,1212420,688133,688134,1212424,688137,688138,688140,1212432,688145,688146,688148,688152,1212448,688161,688162,688168,1228863]) (lf 1 [18307,282499,284547,2691,3203,528643,4739,5251,6275,6659,7171,5645,4366,4374,4378,4380,65557,65558,65559,65800,65801,65802,327959,327965,819200,557057,557058,2801667,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,294936,557088,294945,2277410,294952,573503])) (lf 1 [18307,282499,284547,2691,3331,528515,4867,5379,6403,7171,4237,5646,4246,4249,4252,6689,65554,65555,65556,65776,65777,65778,327935,327941,328040,819200,557057,557058,3063811,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,294936,557088,2801697,294952,573503])) (br 34 (lf 2 [149379,675715,677763,395779,134275,4739,4867,136451,137347,137731,138243,137227,133645,135694,134420,135316,135572,4884,136340,136724,6420,137239,4764,196626,196628,196818,196819,65751,65875,1736704,1212417,1212418,3588099,1212420,688133,688134,1212424,688137,688138,688140,1212432,688145,688146,2277396,688152,1212448,688162,688168,1228863]) (lf 1 [18307,282499,284547,395779,3203,528643,4739,5251,6275,2573,2574,266516,6677,266519,4378,4380,6956,7222,65557,65558,65559,65800,65801,65802,327959,327965,328040,819200,557057,557058,3325955,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,704532,294936,557088,3194914,294952,573503]))) (lf 2 [149379,675715,677763,3016963,133763,134275,135683,137347,137731,138243,3597,4621,133390,135826,135954,136338,136466,136722,135699,4636,196623,196624,196625,720916,196776,196777,196778,721076,721082,721085,1736704,1212417,1212418,8044547,1212420,688133,688134,1212424,688137,688138,688140,1212432,688145,7782418,688152,1212448,688168,1228863])) (lf 1 [18307,282499,284547,1312003,2563,3203,4611,5251,6403,6659,2570,4618,7178,268299,3597,4756,4885,4630,6316,65545,65546,65547,327699,65632,65633,65634,327788,327794,819200,557057,557058,3850243,557060,294917,294918,557064,294921,2932746,294924,557072,294929,294936,557088,294952,573503])) (lf 2 [149379,675715,677763,3803267,133891,134403,135683,137475,137731,138243,133261,3598,4622,135825,135953,136337,136465,136721,135699,4636,720906,196620,196621,196622,720919,196752,196753,196754,721052,721058,721061,721255,1736704,1212417,1212418,10403843,1212420,688133,688134,1212424,688137,688140,1212432,9355281,688152,1212448,688168,1228863])) (lf 1 [18307,282499,284547,1705091,2563,3331,4739,5379,6403,6659,2697,135689,7177,268299,4622,4884,5780,3606,6316,65542,65543,65544,327696,327702,65608,65609,65610,327764,327770,328038,819200,557057,557058,5029891,557060,294917,294918,557064,3850249,294924,557072,294936,557088,294952,573503])) (br 9 (br 10 (br 20 (br 33 (br 17 (br 18 (lf 1 [18307,282499,284547,2691,134147,4611,5379,6403,6659,7171,6151,3085,5646,3094,4376,4504,4632,4760,4888,6296,4633,5275,65558,65559,65774,65775,819200,557057,557058,1753091,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,294932,1097752,557088,294945,294952,573503]) (lf 0 [3090,65705,49155,180242,49176])) (lf 0 [3089,65681,49155,180241,49176])) (lf 1 [18307,282499,284547,2691,396291,1314947,4867,5379,6403,7309,3086,4246,135320,5656,3609,7194,266395,6689,327697,65554,65555,65556,65776,65777,65778,327929,327935,327941,328040,819200,557057,557058,4505603,557060,294917,294918,557064,294921,294922,294924,557072,294932,573464,557088,4243489,294952,573503])) (lf 1 [18307,282499,284547,264707,3075,4487,5259,2573,2574,265233,265234,6419,134164,266772,4756,4884,5396,5652,135447,4376,268312,6296,266396,65743,65744,458961,458983,458984,458985,819200,557057,557058,966659,557060,294917,294918,557064,294921,294922,294924,557072,3719188,3719192,557088,294952,573503])) (lf 0 [3082,65633,49155,180234,49176])) (lf 0 [3081,65609,49155,180233,49176]))
private def r27_k2_t10 : BnbTree := br 40 (br 12 (r27_k2_t9) (br 20 (br 10 (br 9 (br 17 (br 18 (br 24 (br 33 (br 34 (br 36 (lf 2 [149379,675715,677763,2691,134275,4739,136323,137219,137731,138243,2823,4487,137227,2700,134412,4748,135948,137228,137356,6412,3597,5645,6414,7694,136467,4502,5660,1736704,1212417,1212418,2539523,1212420,688133,688134,1212424,688137,688138,573452,1212432,688145,688146,688148,688152,1212448,688161,688162,688164,688168,1228863]) (lf 1 [18307,282499,284547,3203,4611,6275,7171,2823,4491,135692,5260,5388,4627,4629,4634,6436,65674,65675,65676,65830,65831,65832,327991,819200,557057,557058,966659,557060,294917,294918,557064,294921,294922,835596,557072,294929,294930,294932,294936,557088,294945,294946,1622052,294952,573503])) (lf 1 [18307,282499,284547,2691,3331,659715,4739,5251,6275,3212,135436,5645,4502,4380,6690,7202,65557,65558,65559,65800,65801,65802,327959,327965,819200,557057,557058,2670595,557060,294917,294918,557064,294921,294922,557072,294929,294930,294932,294936,557088,294945,2539554,294952,573503])) (lf 1 [18307,282499,284547,2691,528515,4867,5379,6403,3212,135308,5646,4246,4250,4252,6689,7201,65554,65555,65556,65776,65777,65778,327935,327941,328040,819200,557057,557058,2801667,557060,294917,294918,557064,294921,294922,557072,294929,294930,294932,294936,557088,3063841,294952,573503])) (lf 1 [18307,282499,284547,134147,5251,2439,6283,2700,2828,789516,4236,135436,6668,4248,4376,4504,4760,4888,5912,6427,4252,5404,65671,65672,65673,327820,65758,65759,65760,327919,819200,557057,557058,835587,557060,294917,294918,557064,294921,294922,2408460,557072,294929,294930,294932,2670616,557088,294952,573503])) (lf 1 [18307,282499,284547,1313027,2691,3203,4867,5251,6275,6659,7171,395532,4748,3597,5646,5394,266782,65551,65552,65553,327700,65704,65705,65706,327863,327866,327869,819200,557057,557058,3981315,557060,294917,294918,557064,294921,294922,180236,557072,294929,3588114,294932,557088,294952,573503])) (lf 1 [18307,282499,284547,1312899,2819,3331,4867,5379,6659,7171,395404,6412,5645,3598,4753,5265,266781,65548,65549,65550,327703,65680,65681,65682,327839,327842,327845,328039,819200,557057,557058,4243459,557060,294917,294918,557064,294921,294922,180236,557072,4112401,294932,557088,294952,573503])) (lf 0 [1545,65608,49155,180233,49164])) (lf 0 [1546,65632,49155,180234,49164])) (lf 1 [18307,282499,284547,133635,5251,6275,137859,7171,4487,2443,2361868,3212,3340,4748,5388,6412,266388,4372,4375,4380,4892,327807,327810,65668,65669,65670,65734,65735,65736,327882,327885,327892,327895,328051,819200,557057,557058,1359875,557060,294917,294918,557064,4636684,557072,5554196,557088,294952,573503]))) (br 33 (br 10 (br 9 (br 12 (br 17 (br 18 (br 20 (br 24 (lf 3 [280451,1068931,1070979,264835,265347,266883,660483,268291,268803,269315,6151,267277,267278,267283,267286,267290,267292,6182,268456,268587,196629,327702,327962,196915,328010,328011,328015,65892,2654208,1867777,1867778,5292035,1867780,1081349,1081350,1867784,1081353,1081354,1081356,1867792,1081361,1081362,1081364,1081368,1867808,950305,4243496,1884223]) (lf 2 [149379,675715,677763,2691,920579,4867,136195,6403,2439,4487,134157,136206,4499,5141,134166,4888,137368,6424,137752,660507,660514,660516,136229,196842,196843,196844,196929,983362,983363,721272,1736704,1212417,1212418,2670595,1212420,688133,688134,1212424,688137,688138,688140,1212432,688145,688146,688148,5423128,1212448,688161,6340648,1228863])) (lf 1 [18307,282499,284547,133635,3075,4611,136195,6147,6659,7179,5133,7694,5139,3220,3348,4372,4500,267284,5268,5396,6292,5141,5142,6167,5528,7717,5158,6440,65557,65748,65859,65892,819200,557057,557058,1622019,557060,294917,294918,557064,294921,294922,294924,557072,294929,294930,1228820,557088,163873,1228840,573503])) (lf 1 [18307,282499,284547,1706243,2691,3203,5123,6275,6659,5133,2318,4754,267282,5650,267283,5148,138532,5158,7209,65551,65552,65553,65704,65705,65706,327860,327863,327866,327869,65867,819200,557057,557058,3719171,557060,294917,294918,557064,294921,294922,294924,557072,294929,4505618,557088,294945,966696,573503])) (lf 1 [18307,282499,284547,1837187,2819,4739,5123,6403,2189,5134,3345,4881,267281,5649,6673,4627,267283,7324,5284,7332,7210,65548,65549,65550,327703,65680,65681,65682,327836,327839,327845,328039,819200,557057,557058,4505603,557060,294917,294918,557064,294921,294922,294924,557072,4898833,557088,294945,573480,573503])) (lf 1 [18307,282499,284547,2691,3203,136195,6659,4487,6411,2188,2316,4748,4876,1709068,136721,5138,5650,5139,5142,5530,6312,327814,65677,65678,65679,65854,65855,65856,328003,328008,328015,328052,819200,557057,557058,1097731,557060,294917,294918,557064,294921,294922,3457036,557072,557088,294945,4505640,573503])) (lf 0 [5129,65610,49155,180233,49192])) (lf 0 [5130,65634,49155,180234,49192])) (lf 0 [5153,65777,49155,180257,49192]))
private def r27_k2_t11 : BnbTree := br 48 (br 3 (br 9 (br 6 (br 12 (br 17 (br 20 (lf 2 [149381,675717,677765,133893,134277,135941,136709,137477,137733,138245,137355,135694,135699,4501,135322,135836,136489,196651,65580,196653,65779,1736704,1212417,1212418,688131,1212420,3588101,688134,1212424,688137,688138,688140,1212432,688145,688146,688148,688152,1212448,688162,688168,688176,1228863]) (lf 1 [18309,282501,284549,2437,526853,3205,4869,5253,6277,6405,7173,3339,2574,4500,5396,5652,65575,65576,65577,327724,65728,65729,65730,327890,819200,557057,557058,294915,557060,3194885,294918,557064,294921,294922,294924,557072,294929,294930,1884180,294936,557088,294946,294952,294960,573503])) (lf 1 [18309,282501,284549,526469,2821,3589,4869,5637,6405,6661,7173,2187,3342,4497,5265,5393,65572,65573,65574,327727,65683,65684,65685,327843,328042,819200,557057,557058,294915,557060,3588101,294918,557064,294921,294922,294924,557072,2277393,294930,294936,557088,294946,294952,294960,573503])) (lf 2 [149381,675717,677765,2754053,2437,2821,134277,135557,136325,137477,137733,138245,136459,2828,3340,135948,137356,3347,196641,196642,196643,720933,720939,196728,196729,196730,721028,721034,1736704,1212417,1212418,688131,1212420,8830981,688134,1212424,688137,688138,5947404,1212432,688146,688152,1212448,688162,688168,688176,1228863])) (lf 2 [149381,675717,677765,3539717,133509,134277,135557,5253,5637,137349,137477,138245,134662,5382,5638,137734,3339,5259,5402,196635,196636,196637,720932,720938,196659,196660,196661,720953,720959,720965,1736704,1212417,1212418,688131,1212420,9617413,7520262,1212424,688137,688138,1212432,688146,688152,1212448,688162,688168,688176,1228863])) (lf 2 [149381,675717,677765,3540101,133509,134661,4485,4869,136709,137349,137477,138245,134409,4489,5385,137737,133902,5414,720923,196638,196639,196640,720936,720942,196683,196684,196685,720981,720987,721257,1736704,1212417,1212418,688131,1212420,11190277,1212424,7520265,688138,1212432,688146,688152,1212448,688162,688168,688176,1228863])) (lf 2 [149379,675715,677763,4326019,133891,134275,135939,136451,137347,137731,138243,134661,136325,137477,3342,5646,5658,196608,196609,196610,196632,196633,196634,720926,720929,720932,720935,720938,720941,721253,1736704,1212417,1212418,9617411,1212420,11452421,1212424,688138,1212432,688146,688152,1212448,688162,688168,688176,1228863])) (br 3 (br 36 (br 9 (br 6 (br 12 (lf 1 [18309,282501,284549,2821,4485,5637,268293,6405,7173,6151,6155,6157,6158,6163,6169,6170,6172,6822,6825,6698,65577,65749,65874,328033,819200,557057,557058,557060,2015237,294918,557064,294922,294924,557072,294930,294936,557088,294946,294948,294952,1228848,573503]) (lf 1 [18309,282501,284549,1312261,2437,3205,137221,6155,3340,5260,137228,268301,7702,6179,6822,6186,7217,6706,65569,65570,65571,327717,327723,65656,65657,65658,327812,819200,557057,557058,294915,557060,3981317,294918,557064,294921,294922,2670604,557072,294930,294936,557088,294946,294948,294952,835632,573503])) (lf 1 [18309,282501,284549,1704709,2437,3589,5253,137221,3334,4486,137222,268295,6155,6169,6170,6954,6828,6449,7220,65563,65564,65565,327716,327722,65587,65588,65589,327737,327743,819200,557057,557058,294915,557060,4505605,3457030,557064,294921,294922,557072,294930,294936,557088,294946,294948,294952,835632,573503])) (lf 1 [18309,282501,284549,1705093,2821,3589,4485,5637,6149,6405,3337,6153,268301,6158,6291,6182,6186,7220,327707,65566,65567,65568,327720,65611,65612,65613,327765,327771,328041,819200,557057,557058,294915,557060,5029893,557064,3588105,294922,557072,294930,294936,557088,294946,294948,294952,573488,573503])) (lf 0 [6180,65826,49157,180260,49200])) (lf 1 [18307,282499,284547,2622083,3203,137219,7171,2821,5637,137221,4871,268295,6158,6554,6812,6313,6186,6706,65536,65537,65538,65560,65561,65562,327710,327713,327716,327719,327722,327725,328037,819200,557057,557058,4898819,557060,6340613,557064,294922,557072,294930,294936,557088,294946,294952,704560,573503]))
private def r27_k2_t12 : BnbTree := br 40 (br 34 (br 18 (r27_k2_t11) (br 3 (br 9 (br 12 (br 6 (br 20 (br 17 (lf 2 [149381,675717,677765,133381,134661,135557,136325,137349,399749,138245,133387,133390,659602,135826,135954,136466,136722,137497,6682,196653,196654,196655,196797,196798,65727,65873,1736704,1212417,1212418,688131,1212420,3850245,688134,1212424,688137,688138,688140,1212432,688145,2539538,688148,688152,1212448,688162,688168,1228863]) (lf 0 [2321,65683,49157,180241,49170])) (lf 0 [2578,65728,49157,49170,180244])) (lf 0 [2310,65588,49157,180230,49170])) (lf 1 [18309,282501,284549,1836549,264453,3205,5253,7173,6411,264460,4876,6669,4498,3347,6294,137239,5406,6174,65569,65570,65571,327717,327723,65656,65657,65658,327803,327812,327818,819200,557057,557058,294915,557060,4767749,557064,294921,294922,3981324,557072,442386,294936,557088,294946,294952,573503])) (lf 1 [18309,282501,284549,1705093,395525,3589,4869,5637,6661,2313,6409,2318,4498,5394,7190,137239,6295,327707,65566,65567,65568,327720,327726,65611,65612,65613,327765,327771,65725,328041,819200,557057,557058,294915,557060,5685253,557064,3588105,294922,557072,704530,294936,557088,294946,294952,573503])) (lf 0 [2307,65537,180227,49157,49170]))) (br 3 (br 6 (br 9 (br 12 (br 17 (br 20 (br 18 (lf 3 [280453,1068933,1070981,264581,265349,659717,267781,268549,268805,269317,268299,266510,266517,266518,266522,266524,267426,268450,268327,327722,327726,65779,327932,65812,196887,327960,196894,65892,2654208,1867777,1867778,1081347,1867780,5554181,1081350,1867784,1081353,1081354,1081356,1867792,1081361,1081362,1081364,1081368,1867808,3850274,950312,1884223]) (lf 2 [149381,675717,677765,919813,3205,135429,6661,138245,133387,2701,4749,133390,136722,137362,6674,4757,659735,4377,135452,659745,660002,136354,196794,196795,196796,983313,983314,196883,721270,1736704,1212417,1212418,688131,1212420,2801669,688134,1212424,688137,688138,688140,1212432,688145,5292050,688148,688152,1212448,6340642,688168,1228863])) (lf 1 [18309,282501,284549,1837573,3205,4357,5253,6277,4363,2574,2707,397588,266517,6938,6435,5414,6956,7222,65575,65576,65577,327724,65728,65729,65730,327884,327890,327893,819200,557057,557058,294915,557060,4112389,294918,557064,294921,294922,294924,557072,294929,4112404,294936,557088,704546,294952,573503])) (lf 1 [18309,282501,284549,1706117,2821,3589,4357,5253,6661,6539,4366,397585,5649,266517,6554,5411,6438,7219,65572,65573,65574,327727,65683,65684,65685,327833,327843,327846,328042,819200,557057,557058,294915,557060,4505605,294918,557064,294921,294922,294924,557072,4374545,294936,557088,704546,294952,573503])) (lf 1 [18309,282501,284549,1312261,2821,3205,135429,5253,6405,7173,4363,3340,397580,268050,4371,6690,6310,6183,6186,65569,65570,65571,327717,327723,65656,65657,65658,327812,327818,65821,819200,557057,557058,294915,557060,4374533,294918,557064,294921,294922,3194892,557072,294936,557088,835618,294952,573503])) (lf 1 [18309,282501,284549,1311877,2437,266501,5637,6661,7173,2313,397577,4366,136082,4374,4378,4380,6435,6310,268331,65566,65567,65568,327720,327726,65611,65612,65613,327765,327771,328041,819200,557057,557058,294915,557060,4767749,294918,557064,3588105,294922,557072,294936,557088,966690,294952,573503])) (lf 0 [4358,65589,49157,180230,49186])) (lf 0 [4355,65538,180227,49157,49186]))) (br 12 (br 20 (br 3 (br 6 (br 9 (br 17 (br 18 (br 33 (lf 3 [280453,1068933,1070981,264581,265349,4485,135941,791557,268549,268805,138245,268295,267275,136206,7182,267285,267286,267290,267292,5158,268456,399405,327726,196890,327986,328007,328008,196939,65870,65892,2654208,1867777,1867778,1081347,1867780,5029893,1081350,1867784,1081353,1081354,1081356,1867792,1081361,1081362,1081364,1081368,1867808,950305,4374568,1884223]) (lf 0 [5153,65780,49157,180257,49192])) (lf 4 [411525,1462149,1464197,919813,396421,397573,922629,137221,399621,137733,400389,395531,395534,397458,135698,397970,1446930,398482,398866,137746,398355,398357,398358,397591,398364,400673,398371,400676,398374,399528,399405,327723,458797,65582,327868,65727,459086,65892,3571712,2523137,2523138,1474563,2523140,7782405,1474566,2523144,1474569,1474570,1474572,2523152,1474577,5160978,1474580,1474584,2523168,5292072,2539583])) (lf 1 [18309,282501,284549,1968261,2821,4485,5125,6661,7307,5134,4369,4881,267281,5393,3605,4373,267285,5146,5282,7212,7346,65572,65573,65574,327727,65683,65684,65685,327833,327843,327846,819200,557057,557058,294915,557060,4243461,294918,557064,294921,294922,294924,557072,4374545,294932,294936,557088,704552,573503])) (lf 0 [5129,65613,49157,180233,49192])) (lf 1 [18309,282501,284549,2097925,3205,4485,398341,3590,5126,7174,5131,5139,5402,6312,6696,6441,268333,65563,65564,65565,327710,327716,327722,65587,65588,65589,327740,327746,327749,819200,557057,557058,294915,557060,5423109,4112390,557064,294922,294924,557072,294932,294936,557088,704552,573503])) (lf 1 [18307,282499,284547,2228867,3203,4867,398339,3589,5125,7173,6151,2830,5530,6312,6440,6697,5674,137259,65536,65537,65538,327695,327701,65560,65561,65562,327710,327716,327722,327725,328037,819200,557057,557058,5554179,557060,5029893,557064,294922,294924,557072,294932,294936,557088,442408,573503])) (lf 1 [18309,282501,284549,2437,2886149,3205,4869,5125,6277,5131,2574,4372,4500,398356,267285,7706,138786,6440,7209,5674,327705,327711,65575,65576,65577,327724,65728,65729,65730,327875,327884,327890,327893,328042,819200,557057,557058,557060,6471685,557064,294922,294924,557072,6209556,294936,557088,835624,573503])) (lf 0 [5132,65658,49157,180236,49192]))
private def r27_k2_t13 : BnbTree := br 10 (br 24 (r27_k2_t12) (br 9 (br 12 (br 33 (br 3 (br 6 (br 18 (br 17 (br 20 (br 34 (lf 2 [149381,675717,677765,133509,789509,4869,136709,137221,137477,4743,134155,134158,138262,135576,4760,4888,136472,137368,137752,4634,5274,529437,65581,196654,196655,196845,196847,65857,1736704,1212417,1212418,688131,1212420,3719173,688134,1212424,688137,688138,688140,1212432,688145,688146,688148,2539544,1212448,688161,688162,1228863]) (lf 1 [18309,282501,284549,2437,134149,135429,5125,6149,6405,7173,7435,7438,4373,3094,266520,4504,4632,4760,4888,4377,4380,5149,5282,5666,6306,6690,6183,65581,65582,65771,65823,819200,557057,557058,294915,557060,1884165,294918,557064,294921,294922,294924,557072,294929,294930,294932,966680,557088,294945,1228834,573503])) (lf 0 [3092,65729,49157,180244,49176])) (lf 0 [3089,65684,49157,180241,49176])) (lf 1 [18309,282501,284549,2309,3077,6663,2315,2318,265233,3090,266514,4498,4882,5266,5394,5650,265236,4760,267288,268312,6296,135706,65582,65719,65720,458937,458980,458981,852198,819200,557057,557058,294915,557060,835589,294918,557064,294921,294922,294924,557072,3850258,4374552,557088,294945,573503])) (lf 1 [18309,282501,284549,1704709,2437,396293,5637,6277,6405,265222,5382,3083,4504,5272,7194,5148,268317,5150,6686,65563,65564,65565,327716,65587,65588,65589,327740,327743,327746,327749,65770,819200,557057,557058,294915,557060,4505605,4243462,557064,294921,294922,294924,557072,966680,557088,294945,573503])) (lf 1 [18307,282499,284547,1704579,2819,265219,6403,6659,7171,265221,5637,6149,3086,4888,5272,5402,136219,5149,6301,65536,65537,65538,327695,327701,65560,65561,65562,327716,327719,327725,65773,65775,328037,819200,557057,557058,5160963,557060,4374533,557064,294921,294922,294924,557072,966680,557088,294945,573503])) (lf 1 [18309,282501,284549,2309,396293,2625669,4869,5637,6661,4235,3086,4754,3091,4246,135320,4250,7196,266397,6433,7338,327709,327721,65578,65579,65580,65764,327920,65779,65780,65781,327930,327932,327939,327942,328043,819200,557057,557058,557060,6209541,557064,294921,294922,294924,557072,704536,557088,6602785,573503])) (lf 0 [3084,65657,49157,180236,49176])) (lf 0 [3081,65612,49157,180233,49176]))) (br 20 (br 36 (br 6 (br 12 (br 17 (br 3 (br 18 (br 33 (br 34 (br 9 (br 24 (br 40 (lf 1 [18309,282501,284549,2821,3205,5637,6277,6405,7173,4743,2442,3594,4874,6154,6666,5387,6157,6158,5269,4506,819200,557057,557058,294915,557060,1228805,294918,557064,294921,180234,294924,557072,294929,294930,294932,294936,557088,294945,294946,294948,294952,573503]) (lf 1 [18309,282501,284549,2437,3205,5125,6277,6405,4743,2826,4490,4874,267274,5141,5404,6696,65653,65654,65655,65851,65852,65853,328014,819200,557057,557058,294915,557060,1097733,294918,557064,294921,1097738,294924,557072,294929,294930,294932,294936,557088,294945,294946,294948,1490984,573503])) (lf 1 [18309,282501,284549,134149,4869,5637,6405,6661,2695,2442,2826,527370,6282,4504,4760,5277,65647,65648,65649,65755,65756,65757,327915,327918,819200,557057,557058,294915,557060,1228805,294918,557064,294921,1359882,294924,557072,294929,294930,294932,2277400,557088,294945,294946,294948,573503])) (lf 0 [1289,65611,49157,180233,49162])) (lf 1 [18309,282501,284549,3205,4357,7173,2823,2442,921866,5258,5642,4749,4373,4380,6306,6690,327784,327793,65650,65651,65652,65806,65807,65808,327967,328050,819200,557057,557058,294915,557060,835589,294918,557064,2932746,294924,557072,294929,294930,294932,557088,294945,2801698,294948,573503])) (lf 1 [18309,282501,284549,1446021,4869,5637,6405,6661,7173,2442,2826,266378,5390,4248,136600,4761,4250,4252,65578,65579,65580,65779,65780,65781,327927,327932,327939,327942,819200,557057,557058,294915,557060,3457029,294918,557064,180234,294924,557072,294929,294930,294932,557088,4243489,294948,573503])) (lf 1 [18309,282501,284549,264453,5637,6661,7173,4231,1313034,3210,3594,4874,5258,6282,2701,4498,4754,135319,327783,65644,65645,65646,327799,65710,65711,65712,327868,327871,328049,819200,557057,557058,294915,557060,1228805,294918,557064,3588106,294924,557072,294929,3588114,294932,557088,294948,573503])) (lf 0 [1283,65536,180227,49157,49162])) (lf 1 [18309,282501,284549,2623621,2821,3589,4869,5637,6405,6661,133258,4490,7178,3342,4369,5393,4373,267285,5275,65572,65573,65574,65650,327824,65683,65684,65685,327831,327833,327840,327843,327846,819200,557057,557058,557060,4767749,294918,557064,180234,294924,557072,5947409,294932,557088,294948,573503])) (lf 0 [1546,65656,49157,49162,180236])) (lf 0 [1286,65587,49157,180230,49162])) (lf 1 [18309,282501,284549,2309,3077,4485,2888197,5253,6405,2826,3210,266762,6282,7178,5387,4626,4627,136984,4634,4636,327706,327712,327718,65581,65582,65583,65645,65824,65825,65826,327971,327974,327983,327986,327989,328043,819200,557057,557058,557060,6471685,557064,573450,557072,294932,557088,6602788,573503])) (lf 1 [18309,282501,284549,2437,3410437,3205,4357,5125,6277,6405,395786,4490,7178,3339,5390,4884,5140,5268,5653,135454,5150,327705,327711,65575,65576,65577,327724,65728,65729,65730,327875,327878,327884,327887,327890,327893,328042,819200,557057,557058,557060,7127045,557064,311306,557072,7520276,557088,573503]))
private def r27_k2_tr : BnbTree := br 5 (br 3 (br 6 (r27_k2_t6) (br 40 (r27_k2_t8) (br 12 (br 10 (br 9 (br 17 (br 18 (br 20 (br 24 (br 33 (lf 3 [280454,1068934,1070982,133766,265478,266886,1184774,268422,268806,2823,267275,267277,267283,5141,136214,267289,267292,269347,268584,792622,196677,327750,327948,327963,196936,328010,65871,65892,2654208,1867777,1867778,1081347,1867780,1081349,5685254,1867784,1081353,1081354,1081356,1867792,1081361,1081362,1081364,1081368,1867808,950305,4112424,1884223]) (lf 1 [18310,282502,284550,2438,4230,5126,6407,4235,4237,2830,4245,4249,4250,5148,267298,267300,6694,268328,65794,65795,65796,459076,459077,459078,819200,557057,557058,294915,557060,294917,835590,557064,294921,294922,294924,557072,294929,294930,294932,294936,557088,2277409,2932776,573503])) (lf 2 [149382,675718,677766,2438,920582,4486,136198,6662,2823,4871,3083,5131,138253,3091,134165,4886,137368,137496,6680,660510,660513,660514,5155,660516,136229,196842,196843,196844,983361,983362,983363,721272,1736704,1212417,1212418,688131,1212420,688133,2670598,1212424,688137,688138,688140,1212432,688145,688146,688148,6078488,1212448,7782440,1228863])) (lf 1 [18310,282502,284550,2438,2099718,4742,5126,6406,5131,2573,4244,4500,136212,3350,135318,267286,5145,5673,7210,7729,65599,65600,65601,327748,65731,65732,65733,327888,327891,327894,819200,557057,557058,294915,557060,294917,4374534,557064,294921,294922,294924,557072,294929,294930,4374548,557088,573480,573503])) (lf 1 [18310,282502,284550,1837318,2694,4486,5126,6662,7435,5133,3602,4242,4754,267282,5266,4246,267286,5145,5409,7212,7473,65596,65597,65598,327751,65707,65708,65709,327864,327867,327870,328045,819200,557057,557058,294915,557060,294917,4505606,557064,294921,294922,294924,557072,294929,4767762,557088,704552,573503])) (lf 2 [149382,675718,677766,395398,134406,135302,398342,137350,137734,138246,133259,133261,4369,135697,135953,660497,136465,136721,6417,5138,136211,136212,136213,136214,4631,6167,136984,138396,138402,136227,136229,6440,196675,196677,65690,65700,196859,459107,65892,1736704,1212417,1212418,688131,1212420,688133,3850246,1212424,688137,688138,688140,1212432,3325969,1212448,2408488,1228863])) (lf 1 [18310,282502,284550,2694,267270,6278,4871,2313,2569,4489,4745,2102281,5266,5906,5139,5268,5142,5274,5148,6440,6702,65600,327766,65629,65630,65631,65848,65849,65850,328001,328007,328010,328013,328048,819200,557057,557058,294915,557060,294917,1228806,557064,3850249,294922,294924,557072,557088,5423144,573503])) (lf 0 [5130,65637,49158,180234,49192])) (lf 0 [5132,65661,49158,180236,49192])))) (br 6 (r27_k2_t10) (lf 1 [18307,282499,284547,3670787,2691,3331,4739,5251,6275,134150,5126,6406,7174,268295,5133,5656,5145,5404,6686,65539,65540,65541,327686,327692,327698,65584,65585,65586,327734,327737,327740,327743,327746,327749,819200,557057,557058,6864899,557060,294917,7127046,557064,557072,557088,573503]))) (r27_k2_t13)
set_option maxRecDepth 8192 in
private lemma r27_k2_ok : checkLayer (r := 6) (cd := 9) 2 (VTree.ofFun 6 (fun a => (maskWeightFast r27_ws a : ℤ) + (1 : ℤ) * (2 : ℤ) - (9 : ℤ))) (0 : ℤ) (patGens 27) r27_fi r27_prev r27_k2_fc r27_k2_tr = true := by decide +kernel
private def r27_k3_fc0 : List FCutCert := [d [1,2,5] 26 [6,7,8,0,1,2],d [1,2,9] 26 [6,7,8,0,1,3],d [1,2,17] 26 [6,7,8,0,1,4],d [1,2,33] 26 [6,7,8,0,1,5],d [1,3,4] 26 [6,7,8,0,2,1],d [1,4,33] 26 [6,7,8,0,2,5],d [1,3,8] 26 [6,7,8,0,3,1],d [1,5,8] 26 [6,7,8,0,3,2],d [1,8,33] 26 [6,7,8,0,3,5],d [1,3,16] 26 [6,7,8,0,4,1],d [1,5,16] 26 [6,7,8,0,4,2],d [1,9,16] 26 [6,7,8,0,4,3],d [1,16,33] 26 [6,7,8,0,4,5],d [1,3,32] 26 [6,7,8,0,5,1],d [1,5,32] 26 [6,7,8,0,5,2],d [1,9,32] 26 [6,7,8,0,5,3],d [1,17,32] 26 [6,7,8,0,5,4],d [1,2,6] 26 [6,7,8,1,0,2],d [1,2,10] 26 [6,7,8,1,0,3],d [1,2,18] 26 [6,7,8,1,0,4],d [1,2,34] 26 [6,7,8,1,0,5],d [2,3,4] 26 [6,7,8,1,2,0],d [2,4,34] 26 [6,7,8,1,2,5],d [2,3,8] 26 [6,7,8,1,3,0],d [2,6,8] 26 [6,7,8,1,3,2],d [2,8,18] 26 [6,7,8,1,3,4],d [2,8,34] 26 [6,7,8,1,3,5],d [2,3,16] 26 [6,7,8,1,4,0],d [2,6,16] 26 [6,7,8,1,4,2],d [2,10,16] 26 [6,7,8,1,4,3],d [2,16,34] 26 [6,7,8,1,4,5],d [2,3,32] 26 [6,7,8,1,5,0],d [2,6,32] 26 [6,7,8,1,5,2],d [2,10,32] 26 [6,7,8,1,5,3],d [1,4,6] 26 [6,7,8,2,0,1],d [1,4,12] 26 [6,7,8,2,0,3],d [1,4,20] 26 [6,7,8,2,0,4],d [1,4,36] 26 [6,7,8,2,0,5],d [2,4,5] 26 [6,7,8,2,1,0],d [2,4,12] 26 [6,7,8,2,1,3],d [2,4,20] 26 [6,7,8,2,1,4],d [4,5,8] 26 [6,7,8,2,3,0],d [4,6,8] 26 [6,7,8,2,3,1],d [4,8,20] 26 [6,7,8,2,3,4],d [4,8,36] 26 [6,7,8,2,3,5],d [4,5,16] 26 [6,7,8,2,4,0],d [4,6,16] 26 [6,7,8,2,4,1],d [4,12,16] 26 [6,7,8,2,4,3],d [4,16,36] 26 [6,7,8,2,4,5],d [4,5,32] 26 [6,7,8,2,5,0],d [4,6,32] 26 [6,7,8,2,5,1],d [4,12,32] 26 [6,7,8,2,5,3],d [4,20,32] 26 [6,7,8,2,5,4],d [1,8,12] 26 [6,7,8,3,0,2],d [1,8,24] 26 [6,7,8,3,0,4],d [2,8,9] 26 [6,7,8,3,1,0],d [4,8,9] 26 [6,7,8,3,2,0],d [4,8,10] 26 [6,7,8,3,2,1],d [4,8,24] 26 [6,7,8,3,2,4],d [4,8,40] 26 [6,7,8,3,2,5]]
private def r27_k3_fc1 : List FCutCert := [d [8,9,16] 26 [6,7,8,3,4,0],d [8,10,16] 26 [6,7,8,3,4,1],d [8,12,16] 26 [6,7,8,3,4,2],d [8,16,40] 26 [6,7,8,3,4,5],d [8,9,32] 26 [6,7,8,3,5,0],d [8,10,32] 26 [6,7,8,3,5,1],d [8,12,32] 26 [6,7,8,3,5,2],d [8,24,32] 26 [6,7,8,3,5,4],d [1,16,18] 26 [6,7,8,4,0,1],d [1,16,20] 26 [6,7,8,4,0,2],d [1,16,24] 26 [6,7,8,4,0,3],d [1,16,48] 26 [6,7,8,4,0,5],d [2,16,17] 26 [6,7,8,4,1,0],d [2,16,20] 26 [6,7,8,4,1,2],d [2,16,24] 26 [6,7,8,4,1,3],d [2,16,48] 26 [6,7,8,4,1,5],d [4,16,17] 26 [6,7,8,4,2,0],d [4,16,18] 26 [6,7,8,4,2,1],d [4,16,24] 26 [6,7,8,4,2,3],d [4,16,48] 26 [6,7,8,4,2,5],d [8,16,17] 26 [6,7,8,4,3,0],d [8,16,18] 26 [6,7,8,4,3,1],d [8,16,20] 26 [6,7,8,4,3,2],d [8,16,48] 26 [6,7,8,4,3,5],d [16,17,32] 26 [6,7,8,4,5,0],d [16,18,32] 26 [6,7,8,4,5,1],d [16,20,32] 26 [6,7,8,4,5,2],d [16,24,32] 26 [6,7,8,4,5,3],d [1,32,34] 26 [6,7,8,5,0,1],d [1,32,40] 26 [6,7,8,5,0,3],d [1,32,48] 26 [6,7,8,5,0,4],d [2,32,33] 26 [6,7,8,5,1,0],d [2,32,36] 26 [6,7,8,5,1,2],d [2,32,40] 26 [6,7,8,5,1,3],d [2,32,48] 26 [6,7,8,5,1,4],d [4,32,33] 26 [6,7,8,5,2,0],d [4,32,34] 26 [6,7,8,5,2,1],d [4,32,40] 26 [6,7,8,5,2,3],d [4,32,48] 26 [6,7,8,5,2,4],d [8,32,33] 26 [6,7,8,5,3,0],d [8,32,34] 26 [6,7,8,5,3,1],d [8,32,48] 26 [6,7,8,5,3,4],d [16,32,33] 26 [6,7,8,5,4,0],d [16,32,34] 26 [6,7,8,5,4,1],d [16,32,36] 26 [6,7,8,5,4,2],d [16,32,40] 26 [6,7,8,5,4,3],t [1,2,4,8,16,32] 448 [] 12]
private def r27_k3_fc : List FCutCert := r27_k3_fc0 ++ r27_k3_fc1
private def r27_k3_t0 : BnbTree := br 10 (br 1 (br 16 (br 2 (br 4 (br 8 (br 17 (br 36 (lf 1 [149388,149394,149396,411552,135320,136226,137258,688128,425985,425986,163843,425988,163845,163846,425992,163849,163850,426000,163857,163876,704575]) (lf 1 [149388,149396,149400,411556,135698,135457,135715,136228,137260,688128,425985,425986,163843,425988,163845,163846,425992,163849,163850,426000,163857,966692,704575])) (lf 2 [411532,935825,542624,280481,266257,4369,397841,398353,268434,7186,135444,138260,399384,4385,7203,1474560,950273,950274,425987,950276,425989,425990,950280,425993,425994,950288,2015249,1491007])) (lf 1 [149384,413576,415624,2696,135436,2577,5137,135698,5140,4248,65603,65635,196709,688128,425985,425986,163843,425988,163845,163846,1359880,163849,163850,426000,704575])) (br 8 (lf 1 [149380,413572,415620,133260,135698,136212,135320,196704,196706,688128,425985,425986,163843,1228804,163845,163846,425992,163849,163850,426000,704575]) (lf 1 [149380,413572,415620,1442820,133260,133388,135308,135436,137228,196651,196652,196666,196667,458818,688128,425985,425986,163843,3325956,163845,163846,2539528,163849,163850,426000,704575]))) (lf 1 [149378,413570,415618,393730,394242,133260,135314,135444,135704,196701,196702,688128,425985,2277378,163843,163845,688134,163849,688138,426000,704575])) (br 32 (br 2 (br 4 (br 8 (br 17 (br 18 (lf 1 [149388,411536,149412,149416,135444,135320,688128,425985,425986,163843,425988,163845,163846,425992,163849,163850,163857,163858,426016,704575]) (lf 1 [149388,411536,149410,18340,18344,133650,3090,135314,4626,5138,3094,6166,6170,688128,425985,425986,163843,425988,163845,163846,425992,163849,163850,163857,573458,426016,704575])) (lf 1 [149388,411536,149409,149416,133649,134161,135441,135697,133778,137241,688128,425985,425986,163843,425988,163845,163846,425992,163849,163850,704529,426016,704575])) (lf 1 [149384,413576,415624,395272,135320,135448,135704,196670,196671,196688,196689,196690,196691,688128,425985,425986,163843,425988,163845,163846,2801672,163849,163850,1490960,426016,704575])) (lf 1 [149380,413572,415620,919556,135316,135444,136212,196655,196656,196684,196685,196686,196687,458834,688128,425985,425986,163843,3325956,163845,163846,163849,163850,2539536,426016,704575])) (lf 1 [149378,413570,415618,393730,394242,657410,133388,135314,135698,136210,196638,196680,196681,196682,196683,688128,425985,3850242,163843,163845,688134,163849,688138,1490960,426016,704575])) (lf 1 [411536,411552,397314,397316,397320,137228,196692,196693,196694,196695,196710,720999,721000,721001,688128,425985,163843,163845,163846,163849,163850,3588112,5160992,704575]))) (br 16 (lf 1 [149377,413569,415617,393473,393729,394241,133260,135314,135444,135704,196697,196698,688128,2801665,688131,688133,163846,688137,163850,426000,704575]) (lf 1 [149377,413569,415617,657409,133260,135441,135697,136209,196620,196676,196677,196678,196679,458858,688128,3325953,163843,163845,163846,163849,163850,2015248,704575]))) (br 2 (br 8 (br 1 (lf 3 [673674,1462154,1464202,134148,657546,657930,659594,659978,661514,662540,136208,398360,135452,196685,458837,458848,458858,2260992,950273,950274,688131,688133,688134,950280,688137,6995978,2277439]) (lf 1 [149377,413569,415617,393729,656641,133130,133642,135690,134155,135179,137227,135308,4369,136218,65552,196676,65624,688128,2539521,425986,163843,688133,163846,425992,163849,1228810,704575])) (lf 1 [149384,413576,415624,394241,133258,133642,137226,135436,135698,135320,458809,458813,458817,688128,425986,163843,163845,163846,2801672,688137,2015242,704575])) (lf 1 [149378,413570,415618,393473,393730,134146,133258,135306,135690,137226,134412,136212,196633,196634,458781,458785,688128,3588098,688131,163845,688134,163849,1753098,704575]))
private def r27_k3_t1 : BnbTree := br 5 (br 6 (br 9 (r27_k3_t0) (br 8 (br 1 (br 2 (br 16 (lf 3 [673673,1462153,1464201,137220,138244,657673,657929,135433,659977,137225,137737,135178,397450,137228,398353,136465,135192,397592,458803,196703,196705,2260992,1474561,1474562,688131,688133,688134,1474568,6209545,1474576,2277439]) (lf 1 [149385,413577,415625,3204,395273,133385,135433,135689,137226,3212,136212,4121,4249,65583,196684,196695,65638,688128,425985,425986,163843,163845,163846,425992,2277385,704528,704575])) (lf 1 [149378,413570,415618,131586,394370,133641,135689,137225,134155,136203,133388,135441,196637,196699,196714,688128,163841,2277378,163843,163845,425990,163848,966665,704575])) (lf 1 [149377,413569,415617,393473,393729,133385,135433,135689,137226,133260,136212,135320,458763,458767,688128,2801665,688131,688133,163846,425992,1490953,704575])) (lf 3 [673672,1462152,1464200,657673,395785,134665,659977,398601,661513,135306,398346,134156,659729,136212,458760,458805,458806,1507383,1507384,1507388,1507392,2260992,688131,688133,688134,10141704,9093129,2277439]))) (br 9 (br 4 (br 2 (br 8 (br 1 (lf 3 [673670,1462150,1464198,133126,657542,265222,135174,659590,4614,660486,137478,264714,268298,264716,268300,135440,135698,135190,266776,267036,458837,458855,2260992,1474561,1474562,688131,1474564,688133,6733830,1474568,688137,2277439]) (lf 1 [149377,413569,415617,393985,132353,132609,137985,134150,136198,137222,133127,135687,133387,135309,135444,196624,196714,688128,2539521,163842,163843,163844,163845,966662,163848,163849,704575])) (lf 1 [149382,413574,415622,394241,394246,133254,134150,135302,137222,135182,135694,136978,136212,196669,196670,196708,688128,425986,163843,425988,163845,2539526,1228808,688137,704575])) (lf 1 [149378,413570,415618,393473,133254,135302,136198,137226,133388,135444,135704,458776,458780,458784,688128,2801666,688131,425988,163845,2015238,163849,704575])) (lf 3 [673668,1462148,1464196,1442305,395524,657542,659590,660486,661510,133642,396042,135436,136978,659992,458774,458791,458792,1507370,1507374,1507378,2260992,688131,10665988,2260997,6995974,688137,2277439])) (lf 1 [149382,413574,415622,133254,134150,135302,137222,133385,133641,135433,136713,135690,136204,458858,688128,163843,163845,2015238,704521,704575]))) (br 6 (br 10 (br 4 (br 1 (br 8 (br 2 (lf 3 [673669,1462149,1464197,395269,657669,397317,659717,660485,133641,395913,661516,135697,397969,659608,458838,458856,2260992,1474561,1474562,688131,1474564,6471685,688134,1474568,688138,2277439]) (lf 1 [149378,413570,415618,393858,132226,132610,133381,134149,136197,137221,135175,137351,133259,133646,135312,196638,196700,688128,425985,2277378,163843,425988,1228805,163846,425992,163850,704575])) (lf 1 [149381,413573,415621,394242,132101,133381,134149,135429,137221,135693,136212,196668,196674,196688,196707,688128,425985,163843,425988,2277381,163846,1228808,688138,704575])) (lf 1 [149377,413569,415617,393473,133381,135429,136197,137225,133260,135316,135704,458759,458762,458766,688128,2801665,688131,425988,2015237,163846,163850,704575])) (lf 3 [673668,1462148,1464196,1442306,657669,658437,659717,660485,137221,133641,399369,133260,397841,397469,196613,458787,458788,196645,1507369,1507373,1507377,2260992,688131,10141700,7258117,2260998,688138,2277439])) (lf 1 [149381,413573,415621,133381,135429,136197,137221,134409,133642,134154,135306,135690,133260,458858,688128,163843,2015237,163846,704522,704575])) (br 9 (br 10 (br 12 (lf 1 [149381,413573,415621,133381,134149,136197,137221,135302,137734,135441,135700,458858,688128,163843,2015237,180230,163849,163850,163852,704575]) (lf 1 [149381,413573,415621,133381,135429,136197,132614,134150,133260,137228,135694,135316,458858,688128,163843,1753093,180230,163849,163850,442380,704575])) (lf 1 [149381,413573,415621,133381,134149,135429,136197,132358,133258,133642,135306,135690,137230,458858,688128,163843,2015237,163849,966666,704575])) (br 1 (br 2 (br 4 (lf 1 [149381,413573,415621,393989,394373,132614,136198,133639,135175,133385,135433,137226,133261,135309,133134,135704,196668,196672,688128,425985,425986,163843,425988,2015237,704518,1228809,704575]) (lf 1 [149380,413572,415620,131845,133381,134150,136198,135687,133641,135433,137225,133258,135308,458797,458801,458808,688128,425985,425986,163843,2277380,1228805,442374,966665,704575])) (lf 1 [149378,413570,415618,131714,132226,132229,135429,134150,133639,133385,137225,135690,136203,133260,135309,458780,458784,458790,458807,688128,425985,3325954,163843,966661,966662,1228809,704575])) (lf 1 [149377,413569,415617,393473,134149,136197,133254,134662,135302,133385,135433,137225,135690,133644,458759,458762,458766,458786,688128,3325953,688131,1753093,966662,442377,704575]))))
private def r27_k3_t2 : BnbTree := br 9 (br 1 (br 10 (br 12 (br 2 (br 4 (br 8 (lf 3 [673667,1462147,1464195,2051,657923,658435,659971,660483,264197,266245,661510,266513,266897,135314,4115,266389,458837,65638,327783,2260992,1474561,1474562,6340611,1474564,1474568,688137,688138,688140,2277439]) (lf 1 [149379,413571,415619,394243,133635,135683,137219,1029,3077,132102,2059,2187,135435,4109,133390,196671,65603,65616,196707,688128,425985,425986,2277379,425988,1097736,163849,163850,163852,704575])) (lf 1 [149379,413571,415619,131587,133635,134147,135683,136195,394244,137223,135314,196653,196658,196684,196704,688128,425985,425986,2277379,1228804,163849,163850,688140,704575])) (lf 1 [149378,413570,415618,394242,134147,135683,136195,137221,133254,135314,135444,458773,458779,458783,688128,425985,2801666,2015235,163849,688138,163852,704575])) (lf 1 [149379,413571,415619,133635,134147,135683,136195,137219,133260,133388,135308,135436,458858,688128,2277379,163849,163850,704524,704575])) (br 5 (br 6 (br 4 (br 2 (lf 1 [149379,413571,415619,132355,133635,134147,135683,136195,137219,4106,135306,135435,133260,267664,5394,5522,65597,327745,688128,425985,425986,2539523,425988,163845,163846,163849,835594,704575]) (lf 1 [149378,413570,415618,3586,132355,133635,135683,137219,135306,133387,3084,4364,136209,4376,458775,458779,458783,688128,425985,2408450,2277379,425988,163845,163846,163849,180234,704575])) (lf 1 [149379,413571,415619,393730,393731,134147,136195,137219,132356,2055,2311,135303,135690,133260,133134,196660,458809,65613,196704,688128,425985,2277379,1884164,163845,688134,163849,704522,704575])) (br 4 (br 2 (lf 1 [149379,413571,415619,131843,394499,133635,137219,7171,1286,3078,135175,135690,133387,135435,2188,4236,2062,5136,5137,4248,196669,196673,688128,425985,425986,2408451,425988,163845,180230,163849,1097738,704575]) (lf 1 [149378,413570,415618,771,132355,134147,4611,2182,4230,136198,2311,133642,137226,135435,2188,4236,4626,458775,458779,458783,688128,425985,2277378,2015235,425988,163845,311302,163849,442378,704575])) (lf 1 [149379,413571,415619,131587,134147,4611,136195,1284,4230,137222,133383,133642,4618,2188,4236,4366,4369,458773,458798,458802,458809,688128,425985,2408451,1884164,163845,1097734,163849,704522,704575]))) (br 2 (br 4 (lf 1 [149379,413571,415619,132355,133635,134149,135429,136197,132358,133258,135690,135179,137228,133134,135314,196669,196673,688128,425985,425986,1490947,425988,442373,163849,1228810,704575]) (lf 1 [149379,413571,415619,132355,135683,136195,132356,133381,134149,133258,133642,137227,135308,135438,458797,458801,458809,688128,425985,425986,1753091,1228804,1228805,163849,1228810,704575])) (lf 1 [149378,413570,415618,135683,133381,134149,136197,137222,133258,133642,135306,135436,458775,458779,458783,458790,688128,425985,2801666,1490947,966661,163849,442378,704575])))) (br 2 (lf 1 [149377,413569,415617,394241,2563,3075,4611,5123,137219,3077,4357,2182,5126,2186,4234,2316,4364,4626,4244,458756,458761,458765,688128,2801665,425986,2015235,688137,704575]) (lf 1 [149377,413569,415617,393729,394241,395266,397314,133635,134147,135683,136195,137228,720896,196610,196611,196625,196626,720915,720916,688128,5160961,3850242,704515,688137,704575]))) (br 5 (br 16 (br 6 (br 12 (br 1 (br 2 (lf 1 [149379,413571,415619,133635,135683,136195,137219,132100,132228,133385,135433,135181,136593,135320,196672,688128,425985,425986,2015235,163845,163846,704521,425996,426000,704575]) (lf 1 [149378,413570,415618,393730,132226,133250,133635,135683,133385,137225,135307,136211,135448,458783,458807,688128,425985,2801666,704515,163845,688134,966665,163852,426000,704575])) (lf 1 [149377,413569,415617,393729,133635,135299,135683,136195,133385,137225,135569,135448,458753,458758,458765,688128,2801665,1753091,688133,163846,704521,163852,426000,704575])) (lf 1 [149379,413571,415619,132227,133635,134147,135683,136195,137227,133260,133388,135308,135436,458858,688128,2277379,163845,163846,704524,704575])) (br 1 (br 2 (lf 1 [149379,413571,415619,133635,137219,134150,135302,136198,133385,135433,135689,133260,196658,196665,196672,688128,425985,425986,1490947,163845,704518,704521,426000,704575]) (lf 1 [149378,413570,415618,131843,136195,133254,134150,135431,133385,133641,137225,135690,135308,458773,458783,458807,688128,425985,2277378,1228803,163845,442374,966665,426000,704575])) (lf 1 [149377,413569,415617,393729,133635,134150,135302,136198,133385,135433,135689,137225,133260,458758,458765,458769,688128,2801665,966659,688133,966662,704521,426000,704575]))) (lf 1 [149379,413571,415619,918659,133123,137219,133510,133129,133641,135689,134666,657419,135307,133132,135448,136217,397339,458763,458779,458812,196684,196685,688128,3063811,163845,2539529,3063824,704575])) (br 1 (br 2 (br 4 (br 8 (lf 1 [149379,413571,415619,643,132227,133635,4611,136195,1157,267397,2054,3078,4231,133385,397321,2826,4618,137227,2188,4364,2061,5264,5776,4369,4248,688128,425985,425986,2015235,425988,311301,425992,835593,704575]) (lf 1 [149379,413571,415619,131715,133635,136195,132101,135429,132102,137223,133385,135690,135308,133261,134158,458812,458816,688128,425985,425986,1753091,425988,442373,966664,966665,704575])) (lf 1 [149379,413571,415619,133635,136195,132228,135429,137221,134150,133385,135690,135308,133261,458797,458801,458808,688128,425985,425986,1490947,1228804,1228805,704521,704575])) (lf 1 [149378,413570,415618,133635,136195,132229,135429,137221,134150,133385,135690,135308,133261,458779,458783,458790,458807,688128,425985,2801666,1228803,966661,704521,704575])) (lf 1 [149377,413569,415617,134147,135683,137219,132229,133381,136198,135433,133642,133260,135309,458752,458756,458758,458761,458765,688128,3325953,2539523,704517,180233,704575])))
private def r27_k3_tr : BnbTree := br 3 (r27_k3_t1) (r27_k3_t2)
set_option maxRecDepth 8192 in
private lemma r27_k3_ok : checkLayer (r := 6) (cd := 7) 3 (VTree.ofFun 6 (fun a => (maskWeightFast r27_ws a : ℤ) + (1 : ℤ) * (3 : ℤ) - (9 : ℤ))) (0 : ℤ) (patGens 27) r27_fi r27_prev r27_k3_fc r27_k3_tr = true := by decide +kernel
private def r27_k4_fc : List FCutCert := []
private def r27_k4_tr : BnbTree := br 0 (br 8 (br 2 (lf 1 [282497,149380,22405,18310,149392,280480,18344,515,6153,3082,2060,2321,4244,4642,557056,294914,294920,835647]) (lf 3 [1066882,1855362,1857410,131329,131841,263425,133633,642,263682,264194,264322,265218,266754,267266,266243,137219,264452,266244,266372,133381,6150,2057,135177,135440,266768,4114,4372,1867776,6602754,1081352,2670655])) (lf 3 [1066888,1855368,1857416,1281,263681,264705,135425,131714,132226,135682,268290,264195,263172,266244,268292,5125,263174,264328,264456,266376,4360,266760,4617,136202,264204,266256,266264,1867776,6340616,2670655])) (br 1 (lf 1 [280448,544640,546688,1154,1538,4610,4099,3076,4228,5124,2053,2054,2184,4360,6152,2058,4114,4116,966656,294913,835647]) (br 16 (lf 6 [2246528,3821440,3823488,655617,656897,657665,657921,265217,4353,659969,529409,399361,656002,659970,515,656387,528387,1284,265220,1183748,5124,137220,525318,2182,4231,264328,397832,4105,528649,528522,135185,6209536,3194881,2261008,5423167]) (lf 1 [280448,544640,546688,1537,788481,2305,131586,642,1027,2180,264326,133256,2057,2058,4240,4368,4625,5137,6164,4120,135193,966656,704513,966672,835647])))
private lemma r27_k4_ok : checkLayer (r := 6) (cd := 1) 4 (VTree.ofFun 6 (fun a => (maskWeightFast r27_ws a : ℤ) + (1 : ℤ) * (4 : ℤ) - (9 : ℤ))) (0 : ℤ) (patGens 27) r27_fi r27_prev r27_k4_fc r27_k4_tr = true := by decide +kernel
private def r27_k5_fc : List FCutCert := []
private def r27_k5_tr : BnbTree := lf 1 [411520,151425,153474,151428,153480,149392,149408,966719]
private lemma r27_k5_ok : checkLayer (r := 6) (cd := 1) 5 (VTree.ofFun 6 (fun a => (maskWeightFast r27_ws a : ℤ) + (1 : ℤ) * (5 : ℤ) - (9 : ℤ))) (0 : ℤ) (patGens 27) r27_fi r27_prev r27_k5_fc r27_k5_tr = true := by decide +kernel
private def r27_k6_fc : List FCutCert := []
private def r27_k6_tr : BnbTree := lf 1 [280448,18305,20354,18308,20360,18320,18336,1097791]
private lemma r27_k6_ok : checkLayer (r := 6) (cd := 1) 6 (VTree.ofFun 6 (fun a => (maskWeightFast r27_ws a : ℤ) + (1 : ℤ) * (6 : ℤ) - (9 : ℤ))) (7 : ℤ) (patGens 27) r27_fi r27_prev r27_k6_fc r27_k6_tr = true := by decide +kernel
private lemma solve_row27 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hpat : HasPattern F 27) (hprev : ∀ pr ∈ r27_prev, ¬ HasPattern F pr) :
    ∃ W : Fin 12 → ℕ, 0 < ∑ i, W i ∧ F.card * (∑ i, W i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, W i) := by
  dsimp only [HasPattern, patR] at hpat
  obtain ⟨e0, he⟩ := hpat
  let e : Fin r27_ws.length ↪ Fin 12 := e0
  have he' : ∀ g ∈ patGens 27, decode e g ∈ F := he
  have hGens : ∀ g ∈ patGens 27, g < 2 ^ r27_ws.length ∧ decode e g ∈ F := by
    intro g hg
    refine ⟨?_, he' g hg⟩
    have hall : (patGens 27).all (· < 2 ^ r27_ws.length) = true := by decide
    simp only [List.all_eq_true, decide_eq_true_eq] at hall
    exact hall g hg
  have hFi : ∀ b ∈ r27_fi, b < 2 ^ r27_ws.length ∧ decode e b ∈ F :=
    checkClosureAux_sound closed empty he' [] r27_fi (fun _ h => by cases h) (by decide)
  have hTop : 2 ^ r27_ws.length - 1 ∈ r27_fi := by decide
  apply weight_from_fibers (r := r27_ws.length) (by decide) F e full (fun i => r27_ws[i.val]'i.isLt) 1 9 (by decide) (by decide) (7 : ℤ) (by decide)
  intro K hKsub hne
  have hkle : K.card ≤ 6 := K_card_le e hKsub
  have htop_iff : K = univ \ univ.map e ↔ K.card = 6 := K_eq_top_iff e hKsub
  have hlo_iff : K = ∅ ↔ K.card = 0 := card_eq_zero.symm
  have hoff : (if K = univ \ univ.map e then (7 : ℤ) else 0) - (if K = ∅ then (7 : ℤ) else 0) =
      (if K.card = 6 then (7 : ℤ) else 0) - (if K.card = 0 then (7 : ℤ) else 0) := by
    simp only [htop_iff, hlo_iff]
  rw [hoff]
  match hk : K.card with
  | 0 =>
    have h := checkLayer_sound (cd := 4) 0 closed minSize (ws := r27_ws) hKsub hk hne hGens hFi hTop hprev r27_k0_fc r27_k0_tr r27_k0_ok
    simpa [hk] using h
  | 1 =>
    have h := checkLayer_sound (cd := 8) 1 closed minSize (ws := r27_ws) hKsub hk hne hGens hFi hTop hprev r27_k1_fc r27_k1_tr r27_k1_ok
    simpa [hk] using h
  | 2 =>
    have h := checkLayer_sound (cd := 9) 2 closed minSize (ws := r27_ws) hKsub hk hne hGens hFi hTop hprev r27_k2_fc r27_k2_tr r27_k2_ok
    simpa [hk] using h
  | 3 =>
    have h := checkLayer_sound (cd := 7) 3 closed minSize (ws := r27_ws) hKsub hk hne hGens hFi hTop hprev r27_k3_fc r27_k3_tr r27_k3_ok
    simpa [hk] using h
  | 4 =>
    have h := checkLayer_sound (cd := 1) 4 closed minSize (ws := r27_ws) hKsub hk hne hGens hFi hTop hprev r27_k4_fc r27_k4_tr r27_k4_ok
    simpa [hk] using h
  | 5 =>
    have h := checkLayer_sound (cd := 1) 5 closed minSize (ws := r27_ws) hKsub hk hne hGens hFi hTop hprev r27_k5_fc r27_k5_tr r27_k5_ok
    simpa [hk] using h
  | 6 =>
    have h := checkLayer_sound (cd := 1) 6 closed minSize (ws := r27_ws) hKsub hk hne hGens hFi hTop hprev r27_k6_fc r27_k6_tr r27_k6_ok
    simpa [hk] using h
  | _ + 7 => omega

-- ==================== Row 28 (r=5) ====================
private def r28_ws : List ℕ := [3,3,3,2,2]
private def r28_fi : List ℕ := [0,15,23,31]
private def r28_prev : List ℕ := [7,8,12,16,26,27]
private def r28_k0_fc : List FCutCert := []
private def r28_k0_tr : BnbTree := lf 1 [819201,819202,425987,819204,425989,425990,32775,950280,557065,557066,163851,557068,163853,163854,49167,950288,557073,557074,163859,557076,163861,163862,49175,688152,294937,294938,294940,311327]
private lemma r28_k0_ok : checkLayer (r := 5) (cd := 1) 0 (VTree.ofFun 5 (fun a => (maskWeightFast r28_ws a : ℤ) + (1 : ℤ) * (0 : ℤ) - (10 : ℤ))) (-5 : ℤ) (patGens 28) r28_fi r28_prev r28_k0_fc r28_k0_tr = true := by decide +kernel
private def r28_k1_fc : List FCutCert := [d [11] 26 [0,1,2,3,4,5],d [13] 26 [0,2,3,1,5,4],d [14] 26 [0,1,2,3,4,5],d [19] 26 [0,1,4,2,5,3],d [21] 26 [0,2,4,1,5,3],d [22] 26 [1,2,4,0,5,3]]
private def r28_k1_tr : BnbTree := lf 1 [3353,3609,3610,1081344,688129,688130,294915,688132,294917,294918,819208,425993,425994,65536,425996,65537,65538,819216,426001,426002,65539,426004,65540,65541,557080,442399]
private lemma r28_k1_ok : checkLayer (r := 5) (cd := 3) 1 (VTree.ofFun 5 (fun a => (maskWeightFast r28_ws a : ℤ) + (1 : ℤ) * (1 : ℤ) - (10 : ℤ))) (0 : ℤ) (patGens 28) r28_fi r28_prev r28_k1_fc r28_k1_tr = true := by decide +kernel
private def r28_k2_fc : List FCutCert := [d [3,9,13] 26 [0,5,6,3,1,2],d [3,9,25] 26 [0,5,6,3,1,4],d [5,9,11] 26 [0,5,6,3,2,1],d [5,9,25] 26 [0,5,6,3,2,4],d [9,10,25] 26 [3,5,6,0,1,4],d [9,12,25] 26 [3,5,6,0,2,4],d [9,11,17] 26 [0,5,6,3,4,1],d [9,13,17] 26 [0,5,6,3,4,2],d [3,10,14] 26 [1,5,6,3,0,2],d [3,10,26] 26 [1,5,6,3,0,4],d [6,10,11] 26 [1,5,6,3,2,0],d [6,10,26] 26 [1,5,6,3,2,4],d [9,10,26] 26 [3,5,6,1,0,4],d [10,11,12] 26 [3,5,6,1,2,0],d [10,12,26] 26 [3,5,6,1,2,4],d [10,11,18] 26 [1,5,6,3,4,0],d [10,14,18] 26 [1,5,6,3,4,2],d [5,12,14] 26 [2,5,6,3,0,1],d [5,12,28] 26 [2,5,6,3,0,4],d [6,12,13] 26 [2,5,6,3,1,0],d [6,12,28] 26 [2,5,6,3,1,4],d [9,12,28] 26 [3,5,6,2,0,4],d [10,12,28] 26 [3,5,6,2,1,4],d [12,13,20] 26 [2,5,6,3,4,0],d [12,14,20] 26 [2,5,6,3,4,1],d [3,17,25] 26 [0,5,6,4,1,3],d [5,17,25] 26 [0,5,6,4,2,3],d [17,18,25] 26 [4,5,6,0,1,3],d [3,18,26] 26 [1,5,6,4,0,3],d [6,18,26] 26 [1,5,6,4,2,3],d [17,18,26] 26 [4,5,6,1,0,3],d [17,20,28] 26 [4,5,6,2,0,3],d [9,24,26] 26 [3,5,6,4,0,1],d [9,24,28] 26 [3,5,6,4,0,2],d [10,24,25] 26 [3,5,6,4,1,0],d [10,24,28] 26 [3,5,6,4,1,2],d [12,24,25] 26 [3,5,6,4,2,0],d [12,24,26] 26 [3,5,6,4,2,1],d [17,24,26] 26 [4,5,6,3,0,1],d [17,24,28] 26 [4,5,6,3,0,2],d [18,24,25] 26 [4,5,6,3,1,0],d [18,24,28] 26 [4,5,6,3,1,2],d [20,24,25] 26 [4,5,6,3,2,0],d [20,24,26] 26 [4,5,6,3,2,1],t [3,6,10,18] 98 [] 12,t [3,5,9,17] 97 [] 12,t [5,6,12,20] 100 [] 12,t [17,18,20,24] 112 [] 12,v [3,9,10] 107 [],v [3,17,18] 115 [],v [5,9,12] 109 [],v [6,10,12] 110 [],v [9,17,24] 121 [],v [10,18,24] 122 [],v [12,20,24] 124 []]
private def r28_k2_tr : BnbTree := br 24 (br 9 (br 10 (br 20 (br 17 (lf 4 [411523,674693,280454,19334,542604,543634,393987,134661,788748,265497,3609,3610,4096000,2523137,2523138,2523140,3047432,1474569,1474570,3047440,1474577,1474580,1998872,2539551]) (lf 2 [18309,411526,18316,674705,395404,2316,134417,134674,196635,327725,65585,1998848,1212417,1212418,1212420,1474568,294921,688138,1474576,1490961,688148,950296,1228831])) (lf 2 [411523,149388,674708,3602,134292,134420,65567,458798,589871,1998848,1212417,1212418,1212420,1474568,688137,688138,1474576,1753108,294936,1228831])) (br 12 (lf 5 [412549,1853322,674706,543636,527493,3589,1181834,1182218,396817,196617,196619,65566,983084,5144576,3178497,3178498,3178500,3833864,1867785,4112394,1867788,3833872,2523160,3194911]) (lf 1 [280458,281489,1181194,134282,134284,196616,65550,327696,196625,65558,327704,196659,950272,557057,557058,557060,688136,294921,2670602,2277388,688144,426008,573471]))) (br 10 (br 12 (lf 5 [412550,1853321,674705,543636,527622,3590,1181961,1182217,396818,196609,196611,65563,983085,5144576,3178497,3178498,3178500,3833864,4112393,1867786,1867788,3833872,2523160,3194911]) (lf 1 [280457,281490,1181193,3340,196608,65541,327687,196627,65557,327703,196658,950272,557057,557058,557060,688136,2408457,294922,2146316,688144,426008,573471])) (lf 1 [280457,281492,1574153,3593,196610,65540,327686,196618,65548,327693,327695,196656,950272,557057,557058,557060,688136,2932745,2801674,688144,426008,573471]))) (br 9 (br 10 (br 17 (br 18 (br 12 (lf 2 [18307,411525,18310,674708,265219,265222,3353,3609,3610,1998848,1212417,1212418,1212420,1474568,688137,688138,688140,1474576,688145,688146,1228831]) (lf 1 [150403,280460,265228,196626,196628,65572,65573,327734,950272,557057,557058,557060,688136,294921,294922,1490956,688144,294929,294930,442392,573471])) (lf 1 [149381,281490,1051666,196636,196637,327717,65576,65577,327723,950272,557057,557058,557060,688136,294921,294922,688144,294929,1884178,1622040,573471])) (lf 1 [149382,281489,1444881,196633,196634,327716,65574,65575,327720,327722,950272,557057,557058,557060,688136,294921,294922,688144,2277393,2408472,573471])) (lf 1 [150405,280458,1444874,196617,196619,65570,65571,327717,327718,327723,327733,950272,557057,557058,557060,688136,294921,2670602,688144,2801688,573471])) (lf 1 [150406,280457,1838089,196609,196611,65568,65569,327714,327716,327720,327722,327732,950272,557057,557058,557060,688136,3063817,688144,3588120,573471]))
set_option maxRecDepth 8192 in
private lemma r28_k2_ok : checkLayer (r := 5) (cd := 6) 2 (VTree.ofFun 5 (fun a => (maskWeightFast r28_ws a : ℤ) + (1 : ℤ) * (2 : ℤ) - (10 : ℤ))) (0 : ℤ) (patGens 28) r28_fi r28_prev r28_k2_fc r28_k2_tr = true := by decide +kernel
private def r28_k3_fc : List FCutCert := [d [1,2,9] 26 [5,6,7,0,1,3],d [1,4,17] 26 [5,6,7,0,2,4],d [1,8,17] 26 [5,6,7,0,3,4],d [1,3,16] 26 [5,6,7,0,4,1],d [1,5,16] 26 [5,6,7,0,4,2],d [2,4,10] 26 [5,6,7,1,2,3],d [2,4,18] 26 [5,6,7,1,2,4],d [2,3,16] 26 [5,6,7,1,4,0],d [2,6,16] 26 [5,6,7,1,4,2],d [2,10,16] 26 [5,6,7,1,4,3],d [4,8,20] 26 [5,6,7,2,3,4],d [4,5,16] 26 [5,6,7,2,4,0],d [4,12,16] 26 [5,6,7,2,4,3],d [1,8,10] 26 [5,6,7,3,0,1],d [1,8,12] 26 [5,6,7,3,0,2],d [1,8,24] 26 [5,6,7,3,0,4],d [2,8,9] 26 [5,6,7,3,1,0],d [2,8,12] 26 [5,6,7,3,1,2],d [2,8,24] 26 [5,6,7,3,1,4],d [4,8,9] 26 [5,6,7,3,2,0],d [4,8,10] 26 [5,6,7,3,2,1],d [4,8,24] 26 [5,6,7,3,2,4],d [8,9,16] 26 [5,6,7,3,4,0],d [8,10,16] 26 [5,6,7,3,4,1],d [8,12,16] 26 [5,6,7,3,4,2],d [1,16,24] 26 [5,6,7,4,0,3],d [2,16,17] 26 [5,6,7,4,1,0],d [2,16,20] 26 [5,6,7,4,1,2],d [2,16,24] 26 [5,6,7,4,1,3],d [4,16,18] 26 [5,6,7,4,2,1],d [4,16,24] 26 [5,6,7,4,2,3],d [8,16,17] 26 [5,6,7,4,3,0],d [8,16,18] 26 [5,6,7,4,3,1],d [8,16,20] 26 [5,6,7,4,3,2],t [1,2,4,8,16] 224 [] 12]
private def r28_k3_tr : BnbTree := br 8 (br 1 (br 2 (br 4 (br 9 (br 18 (lf 1 [149386,149388,412560,3075,3077,2054,2577,3601,3092,819200,425985,425986,425988,557064,163849,163858,704543]) (lf 1 [18309,18310,149386,412562,3075,133388,2321,3345,2578,134162,3348,819200,425985,425986,425988,557064,163849,966674,704543])) (lf 1 [411529,412560,3075,2181,2054,1289,1545,2313,133641,3337,3593,3082,3084,2321,819200,425985,425986,425988,557064,1097737,704543])) (lf 1 [411524,412548,515,132228,1284,2180,2308,3078,2570,2573,2321,65547,196620,196638,819200,425985,425986,1884164,557064,704543])) (br 16 (lf 2 [935810,936834,131714,132226,132610,133250,133634,134146,134147,1156,134150,2313,134412,133649,458757,327686,1736704,950273,3457026,1212424,1212432,1490975]) (lf 1 [411522,412546,131714,1154,1538,395266,2313,2316,65543,65544,196617,196634,196635,327708,458781,819200,425985,2932738,557064,1753104,704543]))) (br 24 (lf 2 [935809,936833,131841,132353,132609,133377,133633,643,133385,133641,133258,133260,65539,65540,983074,1736704,3588097,163848,688152,1490975]) (lf 1 [411521,412545,1281,1537,2305,2561,658433,642,3202,515,3204,3078,3210,3212,3218,3220,196608,196609,589849,819200,2932737,557064,1097752,704543]))) (br 24 (br 9 (br 10 (lf 1 [281476,411528,19346,394241,394242,1027,1029,1030,526344,133260,2578,65546,819200,2015240,688137,688138,950296,704543]) (lf 1 [150402,411528,150418,394241,1027,1029,1030,526344,133258,133642,196625,458772,819200,2146312,688137,704522,950296,704543])) (lf 1 [19329,19331,19333,411528,19345,1030,526344,1289,1545,133385,133641,65538,65549,65550,458768,458771,819200,2015240,1490953,950296,704543])) (br 16 (br 17 (br 9 (lf 1 [411528,150418,150420,394241,1027,1029,1030,132618,134158,458770,458773,819200,1753096,688137,557072,163857,835608,704543]) (lf 1 [19333,411528,19346,150420,1027,1030,1545,2313,265225,134282,3212,458767,458768,458771,819200,1622024,1359881,557072,163857,442392,704543])) (lf 1 [411528,412561,3075,1029,1030,2184,1289,2313,2186,133260,2321,2577,3220,458754,458770,458773,819200,1753096,557072,1490961,704536,704543])) (lf 1 [411528,412560,395265,395266,1027,395268,1029,2054,196630,196631,196632,720927,720928,720929,819200,3194888,4636688,704543])))
private lemma r28_k3_ok : checkLayer (r := 5) (cd := 6) 3 (VTree.ofFun 5 (fun a => (maskWeightFast r28_ws a : ℤ) + (1 : ℤ) * (3 : ℤ) - (10 : ℤ))) (0 : ℤ) (patGens 28) r28_fi r28_prev r28_k3_fc r28_k3_tr = true := by decide +kernel
private def r28_k4_fc : List FCutCert := [d [0,8,16] 27 [5,6,7,8,4,3]]
private def r28_k4_tr : BnbTree := br 9 (br 1 (br 0 (lf 2 [150402,280452,804744,936848,132610,134146,132356,3076,2184,2321,2578,3092,1474560,688129,163849,1753119]) (lf 2 [1197952,1198976,132610,2178,2562,134146,1284,2180,133380,134148,2570,983040,2015232,688129,163849,1753119])) (lf 2 [1197953,1198977,131329,393729,131841,918529,132353,132609,134145,131586,2562,3074,133123,395269,133393,3092,4636673,1212425,1753119])) (lf 1 [150400,281473,542601,1154,1538,3074,263300,1289,2185,2313,2569,3085,458752,1490953,835615])
private lemma r28_k4_ok : checkLayer (r := 5) (cd := 1) 4 (VTree.ofFun 5 (fun a => (maskWeightFast r28_ws a : ℤ) + (1 : ℤ) * (4 : ℤ) - (10 : ℤ))) (0 : ℤ) (patGens 28) r28_fi r28_prev r28_k4_fc r28_k4_tr = true := by decide +kernel
private def r28_k5_fc : List FCutCert := []
private def r28_k5_tr : BnbTree := lf 1 [280448,150400,19332,280456,281488,257,3073,514,966687]
private lemma r28_k5_ok : checkLayer (r := 5) (cd := 1) 5 (VTree.ofFun 5 (fun a => (maskWeightFast r28_ws a : ℤ) + (1 : ℤ) * (5 : ℤ) - (10 : ℤ))) (0 : ℤ) (patGens 28) r28_fi r28_prev r28_k5_fc r28_k5_tr = true := by decide +kernel
private def r28_k6_fc : List FCutCert := []
private def r28_k6_tr : BnbTree := lf 1 [411520,19329,19330,18308,149384,150416,1097759]
private lemma r28_k6_ok : checkLayer (r := 5) (cd := 1) 6 (VTree.ofFun 5 (fun a => (maskWeightFast r28_ws a : ℤ) + (1 : ℤ) * (6 : ℤ) - (10 : ℤ))) (0 : ℤ) (patGens 28) r28_fi r28_prev r28_k6_fc r28_k6_tr = true := by decide +kernel
private def r28_k7_fc : List FCutCert := []
private def r28_k7_tr : BnbTree := lf 1 [281472,18312,19344,1228831]
private lemma r28_k7_ok : checkLayer (r := 5) (cd := 1) 7 (VTree.ofFun 5 (fun a => (maskWeightFast r28_ws a : ℤ) + (1 : ℤ) * (7 : ℤ) - (10 : ℤ))) (5 : ℤ) (patGens 28) r28_fi r28_prev r28_k7_fc r28_k7_tr = true := by decide +kernel
private lemma solve_row28 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hpat : HasPattern F 28) (hprev : ∀ pr ∈ r28_prev, ¬ HasPattern F pr) :
    ∃ W : Fin 12 → ℕ, 0 < ∑ i, W i ∧ F.card * (∑ i, W i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, W i) := by
  dsimp only [HasPattern, patR] at hpat
  obtain ⟨e0, he⟩ := hpat
  let e : Fin r28_ws.length ↪ Fin 12 := e0
  have he' : ∀ g ∈ patGens 28, decode e g ∈ F := he
  have hGens : ∀ g ∈ patGens 28, g < 2 ^ r28_ws.length ∧ decode e g ∈ F := by
    intro g hg
    refine ⟨?_, he' g hg⟩
    have hall : (patGens 28).all (· < 2 ^ r28_ws.length) = true := by decide
    simp only [List.all_eq_true, decide_eq_true_eq] at hall
    exact hall g hg
  have hFi : ∀ b ∈ r28_fi, b < 2 ^ r28_ws.length ∧ decode e b ∈ F :=
    checkClosureAux_sound closed empty he' [] r28_fi (fun _ h => by cases h) (by decide)
  have hTop : 2 ^ r28_ws.length - 1 ∈ r28_fi := by decide
  apply weight_from_fibers (r := r28_ws.length) (by decide) F e full (fun i => r28_ws[i.val]'i.isLt) 1 10 (by decide) (by decide) (5 : ℤ) (by decide)
  intro K hKsub hne
  have hkle : K.card ≤ 7 := K_card_le e hKsub
  have htop_iff : K = univ \ univ.map e ↔ K.card = 7 := K_eq_top_iff e hKsub
  have hlo_iff : K = ∅ ↔ K.card = 0 := card_eq_zero.symm
  have hoff : (if K = univ \ univ.map e then (5 : ℤ) else 0) - (if K = ∅ then (5 : ℤ) else 0) =
      (if K.card = 7 then (5 : ℤ) else 0) - (if K.card = 0 then (5 : ℤ) else 0) := by
    simp only [htop_iff, hlo_iff]
  rw [hoff]
  match hk : K.card with
  | 0 =>
    have h := checkLayer_sound (cd := 1) 0 closed minSize (ws := r28_ws) hKsub hk hne hGens hFi hTop hprev r28_k0_fc r28_k0_tr r28_k0_ok
    simpa [hk] using h
  | 1 =>
    have h := checkLayer_sound (cd := 3) 1 closed minSize (ws := r28_ws) hKsub hk hne hGens hFi hTop hprev r28_k1_fc r28_k1_tr r28_k1_ok
    simpa [hk] using h
  | 2 =>
    have h := checkLayer_sound (cd := 6) 2 closed minSize (ws := r28_ws) hKsub hk hne hGens hFi hTop hprev r28_k2_fc r28_k2_tr r28_k2_ok
    simpa [hk] using h
  | 3 =>
    have h := checkLayer_sound (cd := 6) 3 closed minSize (ws := r28_ws) hKsub hk hne hGens hFi hTop hprev r28_k3_fc r28_k3_tr r28_k3_ok
    simpa [hk] using h
  | 4 =>
    have h := checkLayer_sound (cd := 1) 4 closed minSize (ws := r28_ws) hKsub hk hne hGens hFi hTop hprev r28_k4_fc r28_k4_tr r28_k4_ok
    simpa [hk] using h
  | 5 =>
    have h := checkLayer_sound (cd := 1) 5 closed minSize (ws := r28_ws) hKsub hk hne hGens hFi hTop hprev r28_k5_fc r28_k5_tr r28_k5_ok
    simpa [hk] using h
  | 6 =>
    have h := checkLayer_sound (cd := 1) 6 closed minSize (ws := r28_ws) hKsub hk hne hGens hFi hTop hprev r28_k6_fc r28_k6_tr r28_k6_ok
    simpa [hk] using h
  | 7 =>
    have h := checkLayer_sound (cd := 1) 7 closed minSize (ws := r28_ws) hKsub hk hne hGens hFi hTop hprev r28_k7_fc r28_k7_tr r28_k7_ok
    simpa [hk] using h
  | _ + 8 => omega

-- ==================== Row 29 (r=6) ====================
private def r29_ws : List ℕ := [3,3,3,3,3,3]
private def r29_fi : List ℕ := [0,31,47,63]
private def r29_prev : List ℕ := [7,8,12,16,26,27,28]
private def r29_k0_fc : List FCutCert := []
private def r29_k0_tr : BnbTree := lf 1 [1081345,1081346,688131,1081348,688133,688134,294919,1081352,688137,688138,294923,688140,294925,294926,1081360,688145,688146,294931,688148,294933,294934,688152,294937,294938,294940,311327,1081376,688161,688162,294947,688164,294949,294950,688168,294953,294954,294956,311343,688176,294961,294962,294964,294968,704575]
private lemma r29_k0_ok : checkLayer (r := 6) (cd := 1) 0 (VTree.ofFun 6 (fun a => (maskWeightFast r29_ws a : ℤ) + (1 : ℤ) * (0 : ℤ) - (12 : ℤ))) (0 : ℤ) (patGens 29) r29_fi r29_prev r29_k0_fc r29_k0_tr = true := by decide +kernel
private def r29_k1_fc : List FCutCert := [d [7,11] 28 [0,1,6,2,3],d [7,13] 28 [0,2,6,1,3],d [7,14] 28 [1,2,6,0,3],d [7,19] 28 [0,1,6,2,4],d [7,21] 28 [0,2,6,1,4],d [7,22] 28 [1,2,6,0,4],d [7,35] 28 [0,1,6,5,2],d [7,37] 28 [0,2,6,5,1],d [7,38] 28 [1,2,6,5,0],q [25,41,49,56] [(25,41,28,[0,3,6,5,4]),(25,49,28,[0,4,6,5,3]),(25,56,28,[3,4,6,5,0]),(41,49,28,[0,5,6,3,4]),(41,56,28,[3,5,6,0,4]),(49,56,28,[4,5,6,0,3])],q [11,19,25,26] [(11,19,28,[0,1,6,3,4]),(11,25,28,[0,3,6,1,4]),(11,26,28,[1,3,6,0,4]),(19,25,28,[0,4,6,1,3]),(19,26,28,[1,4,6,0,3]),(25,26,28,[3,4,6,0,1])],q [25,26,28,56] [(25,26,28,[3,4,6,0,1]),(25,28,28,[3,4,6,2,0]),(25,56,28,[3,4,6,5,0]),(26,28,28,[3,4,6,2,1]),(26,56,28,[3,4,6,5,1]),(28,56,28,[3,4,6,5,2])],q [26,42,50,56] [(26,42,28,[1,3,6,5,4]),(26,50,28,[1,4,6,5,3]),(26,56,28,[3,4,6,5,1]),(42,50,28,[1,5,6,3,4]),(42,56,28,[3,5,6,1,4]),(50,56,28,[4,5,6,1,3])],q [14,22,26,28] [(14,22,28,[1,2,6,3,4]),(14,26,28,[1,3,6,2,4]),(14,28,28,[2,3,6,1,4]),(22,26,28,[1,4,6,2,3]),(22,28,28,[2,4,6,3,1]),(26,28,28,[3,4,6,2,1])],q [28,44,52,56] [(28,44,28,[2,3,6,5,4]),(28,52,28,[2,4,6,5,3]),(28,56,28,[3,4,6,5,2]),(44,52,28,[2,5,6,3,4]),(44,56,28,[3,5,6,2,4]),(52,56,28,[4,5,6,2,3])],q [21,22,28,52] [(21,22,28,[2,4,6,0,1]),(21,28,28,[2,4,6,3,0]),(21,52,28,[2,4,6,5,0]),(22,28,28,[2,4,6,3,1]),(22,52,28,[2,4,6,5,1]),(28,52,28,[2,4,6,5,3])],q [41,42,44,56] [(41,42,28,[3,5,6,0,1]),(41,44,28,[3,5,6,0,2]),(41,56,28,[3,5,6,0,4]),(42,44,28,[3,5,6,1,2]),(42,56,28,[3,5,6,1,4]),(44,56,28,[3,5,6,2,4])],q [11,35,41,42] [(11,35,28,[0,1,6,5,3]),(11,41,28,[0,3,6,5,1]),(11,42,28,[1,3,6,5,0]),(35,41,28,[0,5,6,1,3]),(35,42,28,[1,5,6,0,3]),(41,42,28,[3,5,6,0,1])],q [13,37,41,44] [(13,37,28,[0,2,6,5,3]),(13,41,28,[0,3,6,5,2]),(13,44,28,[2,3,6,5,0]),(37,41,28,[0,5,6,2,3]),(37,44,28,[2,5,6,0,3]),(41,44,28,[3,5,6,0,2])],q [35,38,42,50] [(35,38,28,[1,5,6,0,2]),(35,42,28,[1,5,6,0,3]),(35,50,28,[1,5,6,0,4]),(38,42,28,[1,5,6,2,3]),(38,50,28,[1,5,6,2,4]),(42,50,28,[1,5,6,3,4])],q [14,38,42,44] [(14,38,28,[1,2,6,5,3]),(14,42,28,[1,3,6,5,2]),(14,44,28,[2,3,6,5,1]),(38,42,28,[1,5,6,2,3]),(38,44,28,[2,5,6,1,3]),(42,44,28,[3,5,6,1,2])],q [49,50,52,56] [(49,50,28,[4,5,6,0,1]),(49,52,28,[4,5,6,0,2]),(49,56,28,[4,5,6,0,3]),(50,52,28,[4,5,6,1,2]),(50,56,28,[4,5,6,1,3]),(52,56,28,[4,5,6,2,3])]]
private def r29_k1_tr : BnbTree := br 7 (lf 2 [20363,282509,22414,151443,151445,22435,284581,22438,153516,196617,196618,196621,196623,65553,65554,196627,65556,196629,2785280,1998849,1998850,1212419,1998852,1212421,1212422,425991,1998856,1212425,1212426,1212428,1998864,1212433,1212434,1212436,1212440,1998880,1212449,1212450,1212452,1212456,1212464,1753151]) (lf 3 [1462151,1464199,399495,399623,399879,720896,720897,720898,720899,720900,720901,720902,720903,720904,196617,458763,196620,196622,458768,4227072,3047425,3047426,1867779,3047428,1867781,1867782,10928135,3047432,1867785,1867786,1867788,3047440,1867793,1867794,1867796,1867800,3047456,1867809,1867810,1867812,1867816,1867824,2670655])
private lemma r29_k1_ok : checkLayer (r := 6) (cd := 5) 1 (VTree.ofFun 6 (fun a => (maskWeightFast r29_ws a : ℤ) + (1 : ℤ) * (1 : ℤ) - (12 : ℤ))) (0 : ℤ) (patGens 29) r29_fi r29_prev r29_k1_fc r29_k1_tr = true := by decide +kernel
private def r29_k2_fc0 : List FCutCert := [d [3,6] 28 [1,6,7,0,2],d [3,9] 28 [0,6,7,1,3],d [3,10] 28 [1,6,7,0,3],d [3,17] 28 [0,6,7,1,4],d [3,18] 28 [1,6,7,0,4],d [3,33] 28 [0,6,7,5,1],d [3,34] 28 [1,6,7,0,5],d [5,9] 28 [0,6,7,2,3],d [5,12] 28 [2,6,7,0,3],d [5,17] 28 [0,6,7,2,4],d [5,20] 28 [2,6,7,0,4],d [5,33] 28 [0,6,7,5,2],d [5,36] 28 [2,6,7,5,0],d [6,10] 28 [1,6,7,2,3],d [6,12] 28 [2,6,7,1,3],d [6,18] 28 [1,6,7,2,4],d [6,20] 28 [2,6,7,1,4],d [6,34] 28 [1,6,7,5,2],d [6,36] 28 [2,6,7,5,1],d [9,10] 28 [3,6,7,0,1],d [9,12] 28 [3,6,7,0,2],d [9,17] 28 [0,6,7,3,4],d [9,24] 28 [3,6,7,0,4],d [9,33] 28 [0,6,7,5,3],d [9,40] 28 [3,6,7,5,0],d [10,12] 28 [3,6,7,1,2],d [10,18] 28 [1,6,7,3,4],d [10,24] 28 [3,6,7,1,4],d [10,34] 28 [1,6,7,5,3],d [10,40] 28 [3,6,7,5,1],d [12,20] 28 [2,6,7,3,4],d [12,24] 28 [3,6,7,2,4],d [12,36] 28 [2,6,7,5,3],d [12,40] 28 [3,6,7,5,2],d [17,18] 28 [4,6,7,0,1],d [17,20] 28 [4,6,7,0,2],d [17,24] 28 [4,6,7,0,3],d [17,33] 28 [0,6,7,5,4],d [17,48] 28 [4,6,7,5,0],d [18,20] 28 [4,6,7,1,2],d [18,24] 28 [4,6,7,1,3],d [18,34] 28 [1,6,7,5,4],d [18,48] 28 [4,6,7,5,1],d [20,24] 28 [4,6,7,2,3],d [20,36] 28 [2,6,7,5,4],d [20,48] 28 [4,6,7,5,2],d [24,40] 28 [3,6,7,5,4],d [24,48] 28 [4,6,7,5,3],d [33,34] 28 [5,6,7,0,1],d [33,36] 28 [5,6,7,0,2],d [33,40] 28 [5,6,7,0,3],d [33,48] 28 [5,6,7,0,4],d [34,36] 28 [5,6,7,1,2],d [34,40] 28 [5,6,7,1,3],d [34,48] 28 [5,6,7,1,4],d [36,40] 28 [5,6,7,2,3],d [36,48] 28 [5,6,7,2,4],d [40,48] 28 [5,6,7,3,4],q [3,5,9,17,33] [(3,5,28,[0,6,7,1,2]),(3,9,28,[0,6,7,1,3]),(3,17,28,[0,6,7,1,4]),(3,33,28,[0,6,7,5,1]),(5,9,28,[0,6,7,2,3]),(5,17,28,[0,6,7,2,4]),(5,33,28,[0,6,7,5,2]),(9,17,28,[0,6,7,3,4]),(9,33,28,[0,6,7,5,3]),(17,33,28,[0,6,7,5,4])],q [3,33,34] [(3,33,28,[0,6,7,5,1]),(3,34,28,[1,6,7,0,5]),(33,34,28,[5,6,7,0,1])]]
private def r29_k2_fc1 : List FCutCert := [q [3,6,10,18,34] [(3,6,28,[1,6,7,0,2]),(3,10,28,[1,6,7,0,3]),(3,18,28,[1,6,7,0,4]),(3,34,28,[1,6,7,0,5]),(6,10,28,[1,6,7,2,3]),(6,18,28,[1,6,7,2,4]),(6,34,28,[1,6,7,5,2]),(10,18,28,[1,6,7,3,4]),(10,34,28,[1,6,7,5,3]),(18,34,28,[1,6,7,5,4])],q [9,10,12,24,40] [(9,10,28,[3,6,7,0,1]),(9,12,28,[3,6,7,0,2]),(9,24,28,[3,6,7,0,4]),(9,40,28,[3,6,7,5,0]),(10,12,28,[3,6,7,1,2]),(10,24,28,[3,6,7,1,4]),(10,40,28,[3,6,7,5,1]),(12,24,28,[3,6,7,2,4]),(12,40,28,[3,6,7,5,2]),(24,40,28,[3,6,7,5,4])],q [12,36,40] [(12,36,28,[2,6,7,5,3]),(12,40,28,[3,6,7,5,2]),(36,40,28,[5,6,7,2,3])],q [17,18,20,24,48] [(17,18,28,[4,6,7,0,1]),(17,20,28,[4,6,7,0,2]),(17,24,28,[4,6,7,0,3]),(17,48,28,[4,6,7,5,0]),(18,20,28,[4,6,7,1,2]),(18,24,28,[4,6,7,1,3]),(18,48,28,[4,6,7,5,1]),(20,24,28,[4,6,7,2,3]),(20,48,28,[4,6,7,5,2]),(24,48,28,[4,6,7,5,3])],q [20,36,48] [(20,36,28,[2,6,7,5,4]),(20,48,28,[4,6,7,5,2]),(36,48,28,[5,6,7,2,4])],q [24,40,48] [(24,40,28,[3,6,7,5,4]),(24,48,28,[4,6,7,5,3]),(40,48,28,[5,6,7,3,4])],q [33,34,36,40,48] [(33,34,28,[5,6,7,0,1]),(33,36,28,[5,6,7,0,2]),(33,40,28,[5,6,7,0,3]),(33,48,28,[5,6,7,0,4]),(34,36,28,[5,6,7,1,2]),(34,40,28,[5,6,7,1,3]),(34,48,28,[5,6,7,1,4]),(36,40,28,[5,6,7,2,3]),(36,48,28,[5,6,7,2,4]),(40,48,28,[5,6,7,3,4])]]
private def r29_k2_fc : List FCutCert := r29_k2_fc0 ++ r29_k2_fc1
private def r29_k2_t0 : BnbTree := br 10 (br 3 (br 9 (br 12 (br 18 (br 17 (br 20 (br 33 (br 34 (br 36 (br 40 (lf 2 [151431,151435,20365,22413,22414,151443,151446,20380,153509,153510,153513,153514,6414,137237,3353,6169,7194,6172,137251,137260,6449,6705,7220,2523136,1736705,1736706,950275,1736708,950277,950278,1736712,950281,950282,950284,1736720,950289,950290,950292,950296,1736736,950305,950306,950308,950312,2015295]) (lf 1 [20359,20363,20365,20366,20377,546728,5139,5141,5142,5146,5148,5155,5157,5158,6312,6440,6696,7209,5674,458809,1212416,819201,819202,425987,819204,425989,425990,819208,425993,425994,425996,819216,426001,426002,426004,426008,819232,426017,426018,426020,2015272,966719])) (lf 1 [20363,20365,20366,20374,20378,546724,4615,4627,4629,4633,4636,4643,5284,5412,6308,6436,7204,5669,6694,458807,458808,1212416,819201,819202,425987,819204,425989,425990,819208,425993,425994,425996,819216,426001,426002,426004,426008,819232,426017,426018,2539556,966719])) (lf 1 [20359,20363,20365,20366,20378,546722,4371,4373,4374,4377,4380,4770,5282,5666,6306,6690,7202,4899,6442,458804,458805,458806,1212416,819201,819202,425987,819204,425989,425990,819208,425993,425994,425996,819216,426001,426002,426004,426008,819232,426017,3063842,966719])) (lf 1 [20359,20363,20365,20366,20373,546721,4243,4246,4249,4250,4252,4897,5409,5665,6433,6689,7201,5283,6309,458800,458801,458802,458803,1212416,819201,819202,425987,819204,425989,425990,819208,425993,425994,425996,819216,426001,426002,426004,426008,819232,3588129,966719])) (lf 6 [284551,677771,3821460,415649,415650,677797,808872,264711,657933,657934,657939,658580,265492,266388,266516,659860,267028,660628,660756,661012,661652,661780,662548,264981,268821,265750,268826,267036,852012,852013,2162754,7766016,5406721,5406722,3047427,5406724,3047429,3047430,5406728,3047433,3047434,3047436,5406736,3047441,3047442,13156372,3047448,5406752,6209599])) (lf 3 [153479,284558,1855377,284579,284581,22440,284585,2183,264331,133261,6285,264977,265489,265745,266513,266769,267025,136209,267537,267793,137489,268817,269329,133779,6291,3221,6297,6425,1507363,327717,327718,1114178,3833856,2654209,2654210,1474563,2654212,1474565,1474566,2654216,1474569,1474570,1474572,2654224,7913489,1474578,1474584,2654240,3063871])) (lf 3 [284551,284557,1855378,153505,153510,153512,284586,264459,264462,264850,265362,265746,266642,135698,266898,4882,267410,267794,268434,268818,269330,264979,268570,1507362,1507367,196649,196650,1245250,3833856,2654209,2654210,1474563,2654212,1474565,1474566,2654216,1474569,1474570,1474572,2654224,9093138,1474584,2654240,3063871])) (lf 2 [1200012,1202060,132615,5259,5387,395404,133388,133772,133900,135308,397580,135820,137356,137484,137740,138252,132877,135570,135315,134425,135964,136733,5417,458782,458784,458785,458815,458818,2523136,1736705,1736706,950275,1736708,950277,950278,1736712,950281,950282,6733836,1736720,426008,1736736,2015295])) (lf 2 [1200009,1202057,135815,132873,395529,395785,135561,397833,136457,137353,137481,137737,138249,132747,2707,5267,2837,3606,135449,135962,5276,136738,983060,458773,458775,458776,458815,458818,2523136,1736705,1736706,950275,1736708,950277,950278,1736712,7520265,950282,1736720,426008,1736736,2015295])) (lf 1 [544643,546691,1667,1795,2563,2691,3203,3331,4739,4867,5251,5379,137219,6659,7171,6279,6155,5139,4500,6422,5660,458753,458755,458756,458757,458758,65566,327742,65600,1212416,819201,819202,5160963,819204,425989,425990,819208,425994,819216,426008,819232,966719])) (lf 2 [1200010,1202058,132359,395402,395786,135306,135562,397834,137354,137482,137738,138250,132875,135821,133779,136470,134681,5274,5658,135969,5673,983042,983059,983065,458778,458780,458781,458815,458818,2523136,1736705,1736706,1736708,950277,950278,1736712,9617418,1736720,426008,1736736,2015295])
private def r29_k2_tr : BnbTree := br 5 (br 6 (br 24 (r29_k2_t0) (lf 6 [677767,153483,3821464,2774948,269315,396299,658445,658446,265235,269331,658453,658454,659864,660120,660248,660632,660760,661016,661656,661784,662040,527641,4633,4634,266396,266524,3080214,3080219,3080223,3080228,3080232,3080235,3080238,3080239,2687035,7766016,5406721,5406722,5406724,3047429,3047430,5406728,5406736,37011480,5406752,6209599])) (lf 4 [2510726,2512774,394630,132742,395654,395910,396550,396806,135302,397702,398598,398854,137222,399494,137478,399878,400390,132871,135943,3213,5261,137486,135953,397974,267417,196608,1769485,1769486,2031631,2031632,2031633,2031634,1769530,196669,1769537,5144576,3571713,3571714,3571716,163845,22200326,3571720,3571728,3571744,4112447])) (lf 4 [2510725,2512773,394629,132869,395653,396037,396421,396805,397701,135941,398469,398853,399493,399621,399877,400389,132743,135815,137869,3342,5390,135829,135957,267546,2031623,2031624,2031625,2031626,2031627,2031628,2031676,2031681,5144576,3571713,3571714,3571716,22462469,3571720,3571728,3571744,4112447])
set_option maxRecDepth 8192 in
private lemma r29_k2_ok : checkLayer (r := 6) (cd := 7) 2 (VTree.ofFun 6 (fun a => (maskWeightFast r29_ws a : ℤ) + (1 : ℤ) * (2 : ℤ) - (12 : ℤ))) (0 : ℤ) (patGens 29) r29_fi r29_prev r29_k2_fc r29_k2_tr = true := by decide +kernel
private def r29_k3_fc : List FCutCert := [d [1,2] 28 [6,7,8,0,1],d [1,4] 28 [6,7,8,0,2],d [1,8] 28 [6,7,8,0,3],d [1,16] 28 [6,7,8,0,4],d [1,32] 28 [6,7,8,0,5],d [2,4] 28 [6,7,8,1,2],d [2,8] 28 [6,7,8,1,3],d [2,16] 28 [6,7,8,1,4],d [2,32] 28 [6,7,8,5,1],d [4,8] 28 [6,7,8,2,3],d [4,16] 28 [6,7,8,2,4],d [4,32] 28 [6,7,8,5,2],d [8,16] 28 [6,7,8,3,4],d [8,32] 28 [6,7,8,5,3],d [16,32] 28 [6,7,8,5,4],q [1,2,4,8,16,32] [(1,2,28,[6,7,8,0,1]),(1,4,28,[6,7,8,0,2]),(1,8,28,[6,7,8,0,3]),(1,16,28,[6,7,8,0,4]),(1,32,28,[6,7,8,0,5]),(2,4,28,[6,7,8,1,2]),(2,8,28,[6,7,8,1,3]),(2,16,28,[6,7,8,1,4]),(2,32,28,[6,7,8,5,1]),(4,8,28,[6,7,8,2,3]),(4,16,28,[6,7,8,2,4]),(4,32,28,[6,7,8,5,2]),(8,16,28,[6,7,8,3,4]),(8,32,28,[6,7,8,5,3]),(16,32,28,[6,7,8,5,4])],d [4,12,32] 26 [6,7,8,2,5,3],d [8,12,32] 26 [6,7,8,3,5,2]]
private def r29_k3_t0 : BnbTree := br 3 (br 5 (br 6 (br 9 (br 10 (br 17 (br 1 (br 32 (br 4 (br 2 (br 8 (br 16 (lf 1 [20364,151444,282520,284577,153506,22440,137228,266770,5140,7202,6184,1081344,688129,688130,294915,688132,294917,294918,688136,294921,294922,688144,294929,688160,1097791]) (br 18 (lf 1 [675728,284580,284584,268300,266388,266520,1081344,688129,688130,294915,688132,294917,294918,688136,294921,294922,294929,294930,688160,1097791]) (lf 1 [22412,675728,284578,22436,22440,133388,265234,266386,135698,5138,6674,3348,5140,6164,137242,1081344,688129,688130,294915,688132,294917,294918,688136,294921,294922,294929,1097746,688160,1097791]))) (lf 1 [675720,677768,268296,264460,266388,266520,269348,720908,1081344,688129,688130,294915,688132,294917,294918,1884168,294921,294922,294929,688160,1097791])) (lf 2 [1462146,1464194,266370,267266,267778,269314,657676,659732,266392,268312,266787,267300,268330,1507334,1507335,2260992,1474561,6209538,688131,1474564,688133,688134,688137,688138,688145,1474592,2277439])) (lf 1 [675716,677764,264460,266388,266520,269348,268328,720901,720905,720906,1081344,688129,294915,3063812,294917,294918,294921,294922,294929,688160,1097791])) (br 34 (br 12 (lf 1 [282516,282520,677792,266386,269348,268328,720904,720907,720909,720910,1081344,688129,294915,294917,294918,294921,294922,294924,294929,3063840,294946,1097791]) (lf 1 [675724,677772,659458,264460,266252,266380,267800,720910,720912,720913,1081344,688129,294915,294917,294918,294921,294922,3850252,294929,2670624,1081378,1097791])) (lf 1 [282514,282516,677792,266508,266520,267553,267298,268834,268324,720904,720907,720909,720910,1081344,688129,294915,294917,294918,294921,294922,294929,3063840,1097762,1097791]))) (lf 4 [3035009,3037057,265217,1054209,268545,269313,265356,1054732,1052818,268306,266388,1052948,266520,266776,267288,1053732,3080192,3080193,3080194,3080195,3080196,4620288,21151745,1474563,1474565,1474566,1474569,1474570,1474577,4636735])) (lf 1 [675729,284577,284584,264332,264977,266513,266769,269329,264722,268312,720911,1081344,294915,294917,294918,294921,294922,2277393,1097791])) (lf 2 [1462154,1464202,657546,264714,659594,659978,264460,268300,264722,267286,659736,1507343,2260992,688131,688133,688134,688137,5029898,2277439])) (lf 1 [675721,677769,263689,264457,264713,266505,266761,268297,267274,268429,266385,267544,720911,1081344,294915,294917,294918,3457033,1097791])) (lf 2 [1462150,1464198,656518,657542,265222,659590,660486,661510,264458,264714,264716,266764,267794,266776,266522,266524,1507343,2260992,688131,688133,6602758,2277439])) (br 48 (br 10 (lf 1 [675717,677765,264453,266501,267269,268805,263302,264332,266772,266392,720911,1081344,294915,2670597,294922,294960,1097791]) (lf 1 [675717,677765,263429,264453,266501,267269,265481,264714,265226,266378,266762,264332,720911,1081344,294915,2670597,1490954,294960,1097791])) (lf 1 [675717,677765,263429,264453,1054725,266374,266761,264332,266516,268952,268968,720911,1081344,294915,3063813,704560,1097791]))) (br 12 (br 5 (br 6 (lf 1 [675715,677763,264707,266755,267267,268291,264457,264330,266392,266523,720911,1081344,2670595,294917,294918,294924,1097791]) (lf 2 [1462147,1464195,657923,658435,659971,660483,661507,656518,265478,266502,661638,268550,264458,267018,659601,266514,1507343,2260992,6209539,688133,1884166,688140,2277439])) (br 9 (lf 1 [675715,677763,264707,266755,267267,263429,265221,266373,268293,266513,266898,720911,1081344,2277379,1097733,294921,294924,1097791]) (lf 1 [675715,677763,262787,263299,264707,267267,656517,266501,265222,263303,264457,266762,268299,264333,266381,720911,1081344,2670595,1097733,1490953,294924,1097791]))) (lf 1 [675715,677763,263683,265219,267267,268291,264453,266374,266761,264714,264332,266508,720911,1081344,2670595,704524,1097791]))
private def r29_k3_tr : BnbTree := r29_k3_t0
set_option maxRecDepth 8192 in
private lemma r29_k3_ok : checkLayer (r := 6) (cd := 5) 3 (VTree.ofFun 6 (fun a => (maskWeightFast r29_ws a : ℤ) + (1 : ℤ) * (3 : ℤ) - (12 : ℤ))) (0 : ℤ) (patGens 29) r29_fi r29_prev r29_k3_fc r29_k3_tr = true := by decide +kernel
private def r29_k4_fc : List FCutCert := [d [0,16,32] 27 [6,7,8,9,5,4],d [0,4,32] 27 [6,7,8,9,5,2],d [0,4,16] 27 [6,7,8,9,4,2],d [0,8,32] 27 [6,7,8,9,5,3],d [0,8,16] 27 [6,7,8,9,4,3],d [0,4,8] 27 [6,7,8,9,2,3],d [0,2,32] 27 [6,7,8,9,5,1],d [0,2,8] 27 [6,7,8,9,1,3],d [0,2,4] 27 [6,7,8,9,1,2],d [0,2,16] 27 [6,7,8,9,1,4]]
private def r29_k4_t0 : BnbTree := br 1 (br 5 (br 4 (br 16 (lf 6 [5394304,5396352,263302,659462,268294,659465,268297,394762,658442,135178,657932,135180,659473,135441,398353,657938,135186,399378,659480,659745,660001,398370,398372,137252,4636672,3833857,3833858,1474563,3833860,1474565,3833864,3833872,7782463]) (br 17 (br 18 (lf 1 [806784,808832,2054,4102,2057,4105,2058,4106,2060,6156,4240,4116,5140,4120,4376,4641,6178,5156,704512,557057,557058,163843,557060,163845,557064,163857,163858,1228863]) (lf 1 [806784,808832,2054,4102,2057,2313,2058,4106,137228,4368,135314,135698,136210,6674,135188,4120,4376,704512,557057,557058,163843,557060,163845,557064,163857,704530,1228863])) (lf 1 [806784,808832,2054,2182,2057,4105,2058,4106,2188,4108,4240,4368,5136,2321,2577,134161,4369,135697,5137,4242,4116,4121,6169,704512,557057,557058,163843,557060,163845,557064,49168,966673,1228863]))) (br 32 (br 6 (lf 1 [806784,808832,1156,1284,2308,4228,4356,5124,6148,2057,2058,2060,2188,4240,5136,2577,6162,4372,135704,704512,557057,557058,163843,180228,163845,163846,557064,557088,1228863]) (lf 1 [806784,808832,1156,1284,2180,2308,4228,4356,5124,1158,1542,134150,4614,5126,137222,2058,2060,2574,4240,4368,4624,2321,4884,704512,557057,557058,163843,180228,163845,704518,557064,557088,1228863])) (br 6 (lf 1 [806784,808832,1156,1284,2180,4228,4356,136196,4105,4106,4108,4364,4113,4114,4626,4116,4244,4120,4632,137260,589824,1359872,557057,557058,163843,180228,163845,163846,557064,835616,1228863]) (lf 1 [806784,808832,1156,1284,2180,3076,4228,137220,1158,2566,4102,4230,136198,6662,4106,4108,4364,4113,4114,4626,4372,4120,589824,1359872,557057,557058,163843,180228,163845,573446,557064,704544,1228863])))) (br 16 (lf 1 [806784,808832,1156,2180,2308,3076,4356,131845,132357,2309,3077,135173,4357,136197,6149,4103,4105,4620,4748,4113,135316,6180,704512,557057,557058,163843,1228805,557064,557072,1228863]) (lf 1 [806784,808832,1156,1284,3076,4228,4356,773,1285,264197,133381,3077,5125,6149,2054,2057,133772,4240,4368,5136,135697,6164,589824,1359872,557057,557058,163843,966661,557064,966672,1228863]))) (br 16 (br 4 (br 32 (lf 1 [806784,808832,769,1281,1537,2305,2561,3073,4353,4609,5121,6145,4357,6149,1158,4617,2570,2188,5137,4242,4248,704512,573441,557058,163843,557060,557064,557072,557088,1228863]) (br 5 (lf 1 [806784,808832,769,1281,1537,2305,2561,4353,4609,136193,6145,4230,2185,6153,4106,4108,5265,4114,4116,4120,4248,4642,704512,573441,557058,163843,557060,163845,557064,557072,1228863]) (lf 1 [806784,808832,769,1281,1537,2305,2561,3073,6145,1285,2309,3077,135173,135429,136197,6149,4102,4105,4617,4108,4625,4753,4116,704512,180225,557058,163843,557060,966661,557064,557072,49184,1228863]))) (br 6 (lf 2 [1724288,1726336,1180161,132353,132609,133377,133633,136193,137217,133380,3204,397444,132357,396293,397573,136197,137221,264329,4745,135692,4753,135700,1245185,2801664,1490945,1212418,425987,2146308,425990,1212424,1212432,2539583]) (lf 1 [806784,808832,513,131841,1281,1537,2305,2561,3073,4353,4609,5121,3076,4356,5124,6148,1285,2309,6149,132230,1542,133254,2566,135302,4615,589825,1359872,704513,557058,163843,573444,966662,557064,557072,1228863]))) (br 5 (lf 1 [806784,808832,524801,769,1281,1537,2305,2561,4609,5121,137217,2054,2057,2569,2058,2060,4240,4368,5136,4369,4625,4242,137368,589824,1359872,1097729,557058,163843,819205,557064,835600,1228863]) (lf 1 [806784,808832,769,1537,2305,3073,4609,132357,133125,2309,3077,135429,136197,137221,2054,133641,2060,4240,4624,4245,589824,589826,2015232,557058,163843,1228805,557064,1359888,1228863])))
private def r29_k4_t1 : BnbTree := br 8 (br 0 (br 1 (br 4 (br 16 (lf 2 [413573,151430,151434,151441,413586,939936,415649,153506,132227,133251,132358,136201,399372,134164,135188,4376,4632,4642,136228,1998848,1212417,1212418,1212420,1212424,1212432,2539583]) (lf 3 [22409,2641808,1857440,153506,284584,264195,264707,264197,2309,134149,264198,268294,264201,133385,264202,268298,2060,526476,266384,266512,397840,267280,6673,266386,134164,4372,135704,3047424,1867777,1867778,1867780,1867784,4505616,3850303])) (lf 3 [2641796,2643844,262659,132611,4611,263300,263428,264324,264452,266372,267268,137220,662532,264453,268293,659462,133129,4617,266250,2060,133644,6156,266384,266512,267024,267280,266769,266516,4628,659480,3047424,1867777,1867778,7258116,1867784,3850303])) (br 10 (lf 4 [3559297,3561345,393985,394753,395521,266241,397825,267265,1186305,132227,397315,137219,264452,397572,398340,661508,268420,395397,396293,2054,266374,395273,4105,4617,395276,790672,397584,266769,5137,4242,921620,397336,4096000,8830977,2523138,2523144,950282,5161023]) (lf 1 [806785,808833,769,918785,2305,2561,3073,4353,6145,1539,2563,1156,263556,3076,4101,4357,2054,5129,1546,133258,2314,135178,135306,135690,6154,133131,135179,5136,5392,950272,2932737,557058,557064,2146314,1228863]))) (br 3 (r29_k4_t0) (br 5 (br 16 (lf 1 [806784,808832,393729,769,1283,132611,2307,133635,134147,135171,4227,135683,136195,137219,4228,4102,4105,4361,4362,4113,4497,4498,704512,557058,1884163,688133,557064,557072,1228863]) (lf 1 [806784,808832,1281,1537,3073,4609,526339,2563,3075,4355,137219,133254,133513,2058,2060,4240,4368,4624,2578,4242,136211,589824,589826,2015232,557058,966659,163845,557064,1884176,1228863])) (lf 2 [1724288,1726336,132353,132609,133377,396289,1442435,132611,133635,134275,135171,397827,398339,399363,132357,264325,133381,135301,135429,133638,135430,394375,395271,135175,4240,4113,4245,589825,589826,2801664,1212418,3588099,2408453,1212424,2539583])))) (br 4 (br 16 (br 12 (br 20 (br 1 (br 9 (lf 2 [1724296,1726344,132099,135171,132101,135173,132102,135174,133384,135304,266760,137224,135178,4234,6154,398353,135186,266520,4632,6177,5666,1212417,1212418,1212420,4243464,425993,425996,1212432,426004,2539583]) (lf 1 [806792,808840,1027,4099,4229,5125,1030,1158,2312,4232,4616,2313,3081,135433,4617,5385,137225,135178,4113,5137,4120,557057,557058,557060,1753096,835593,163852,557072,163860,1228863])) (br 3 (lf 1 [806785,808833,769,1281,2305,4353,4609,5121,6145,1029,5125,1030,2184,4360,4616,6152,2313,2186,135320,589827,2015233,557058,163843,557060,704520,163852,557072,163860,1228863]) (lf 1 [806785,808833,769,2305,3073,4353,4609,525315,3075,136195,137219,1029,1285,1030,2312,4360,4105,4618,133259,135307,458755,1753089,557058,966659,557060,966664,163852,557072,163860,1228863]))) (lf 1 [806792,808840,2561,134657,4609,5121,133635,1029,6661,134662,2184,2312,1444360,4616,6152,3593,6153,133642,3601,2578,397332,5140,137752,4124,135324,135452,557058,557060,3325960,163852,557072,2670612,1228863])) (lf 2 [1724296,1726344,769,1025,132609,133633,134145,136193,132099,132611,394501,132102,2566,133384,135432,137224,2569,397833,395404,133388,134156,397452,135436,136204,137228,1245187,1212418,1212420,5029896,2277388,1212432,2539583])) (br 9 (br 10 (lf 1 [806792,808840,525313,1027,2051,1029,2053,1030,2054,2184,2312,2568,4232,4360,4616,2316,6156,4240,4368,5136,5137,6164,4632,589824,557058,557060,2932744,819209,163850,704528,1228863]) (lf 1 [806792,808840,525313,1027,2051,1029,2309,1030,2054,2184,2568,4232,4360,6152,526346,2186,2570,4106,6154,134412,4240,4368,5394,135704,136218,458752,557058,557060,2801672,819209,835594,966672,1228863])) (lf 1 [806792,808840,1537,2305,2561,5121,1027,3075,3077,4229,133254,133128,2312,788489,135433,134282,2060,4240,5136,4116,135704,397337,983044,557058,557060,2670600,835593,1884176,1228863]))) (br 5 (br 6 (br 0 (lf 1 [806788,808836,524801,515,1027,132100,1156,132356,2180,4228,4356,6148,2184,4232,4360,4616,4617,399372,2062,397328,2578,3090,3092,6184,950272,557058,3063812,819205,163846,180232,1228863]) (lf 1 [806784,808832,524801,515,1027,1156,1284,2180,2308,3076,4356,5124,6148,2184,2312,4360,6152,2569,4618,135308,5140,4632,589825,589826,2015232,557058,2408452,819205,163846,1228863])) (lf 1 [806788,808836,524801,515,1027,1156,2308,4228,6148,263174,1158,134150,4230,4614,136198,2184,2312,2568,4360,4616,6152,2186,2570,4364,2062,4110,458753,458754,557058,3457028,819205,966662,573448,1228863])) (lf 2 [1724292,1726340,2049,133377,133633,135681,136193,6145,131587,132099,394500,133380,268292,2229253,657157,6661,394246,526472,133640,397577,135180,919565,921613,4240,135704,136216,266393,2031621,1212418,5816324,2670597,4767752,2539583])))
private def r29_k4_t2 : BnbTree := br 16 (br 4 (br 8 (br 3 (br 6 (lf 1 [806786,808834,524545,642,1154,1538,2178,2562,4226,4610,5122,6146,7170,4357,4361,2314,6154,4108,4113,4626,4116,135192,5153,3063810,819203,557060,163846,557064,557072,1228863]) (lf 1 [806786,808834,524545,642,1154,2178,3074,4226,136194,4613,1158,1286,2182,2310,135174,4230,5382,137222,4618,135436,4114,4116,4884,4120,2670594,819203,557060,966662,557064,557072,1228863])) (br 32 (br 5 (br 6 (lf 2 [1724290,1726338,132353,132609,133377,136193,137217,132610,133634,135298,135682,136194,137218,133635,396291,135683,2185,266505,133258,4369,135314,3850242,442371,1212420,425989,425990,1212424,1212432,1212448,2539583]) (lf 1 [806786,808834,1281,1537,2305,4609,5121,4226,5122,771,1539,133635,4611,4867,137219,132230,1286,133254,2310,134150,4230,135430,1359874,704515,557060,163845,1228806,557064,557072,557088,1228863])) (lf 1 [806786,808834,1537,3073,4353,4609,5121,393858,1154,1538,3074,4610,5122,2307,133635,132357,2181,4357,137221,1158,2310,2183,135303,2277378,49155,557060,966661,557064,557072,557088,1228863])) (lf 1 [806786,808834,769,1281,1537,2305,3073,1538,135170,4610,5122,6146,397315,4611,5123,6147,4229,4357,4486,4233,4361,4490,4113,4369,4498,4116,4372,4120,983046,2932738,573443,557060,557064,557072,1490976,1228863]))) (br 3 (br 6 (lf 1 [806786,808834,524545,642,1154,1538,2178,2562,4226,4610,136194,6146,1029,2184,2312,2568,4232,4616,6152,5385,2316,135448,589827,3063810,819203,557060,163846,835592,557072,1228863]) (lf 1 [806786,808834,524545,642,1154,2178,3074,4610,1029,132102,1158,2310,3078,135302,267270,137222,2184,4104,4360,133642,4364,4620,2318,458755,2408450,819203,557060,1228806,573448,557072,1228863])) (lf 1 [806786,808834,1537,2305,3073,4353,5121,642,263170,4610,6146,525315,1285,1030,1158,2312,4360,6153,133258,133642,397323,4236,4120,4641,983047,2932738,311299,557060,1753096,557072,1228863]))) (br 3 (br 10 (lf 1 [806786,808834,524545,642,525314,1154,1538,2178,2562,3074,4226,135682,6146,1156,2180,3076,4228,6148,4357,136198,2316,4882,4372,589825,3719170,819203,573444,819210,557072,1228863]) (lf 1 [806786,808834,524545,393730,642,2562,4226,4610,1156,394500,4228,1285,1158,134150,5126,137222,133258,2314,4362,2316,5132,135182,4366,4628,327681,589829,2801666,819203,1622020,835594,557072,1228863])) (lf 1 [806786,808834,1537,2561,135425,6145,393730,1154,2562,5122,6146,918019,1539,2307,2308,5124,2821,4229,1030,133254,134150,4102,263175,397319,4232,4489,135690,983048,3194882,966659,2146308,557072,1228863]))) (br 0 (br 3 (lf 2 [1724290,1726338,1179905,131714,132226,1968130,264322,133634,135298,135682,132356,264452,527620,133125,2054,268294,919816,135432,2057,2313,133130,133132,133388,135312,136208,3089,135186,135698,136210,6163,135188,3094,266262,135448,266266,1998848,7389186,1736707,2277392,2539583]) (br 4 (lf 1 [806786,808834,769,1537,2561,4353,7169,1154,1538,526338,2562,4610,657411,134147,133381,2182,2312,133512,137224,2057,4106,6410,4240,4368,4624,4114,4242,136210,266259,950272,2277378,704515,557060,1228816,1228863]) (lf 1 [806786,808834,1281,1537,2561,3073,4609,655874,1538,919554,4226,6146,524803,919811,658179,3075,6148,919558,394247,2440,133385,2058,4113,4625,397331,136211,4246,135447,950272,3325954,2277379,835588,1490960,1228863]))) (br 3 (br 6 (lf 1 [806784,808832,524545,642,1154,1538,133122,2178,2562,3074,4226,4610,2053,2313,4362,6154,2060,4368,5136,3089,4242,4626,5138,6164,589830,589831,589832,2670592,3194882,819203,163846,49168,1228863]) (lf 1 [806784,808832,524545,1538,2050,3074,4226,6146,133381,132230,264198,133254,3078,4358,136198,6150,133898,2060,4240,4624,4626,4372,589830,589831,589832,2670592,2539522,819203,1228806,180240,1228863])) (lf 0 [65545,49152,49154,49168])))
private def r29_k4_tr : BnbTree := br 2 (r29_k4_t1) (r29_k4_t2)
set_option maxRecDepth 8192 in
private lemma r29_k4_ok : checkLayer (r := 6) (cd := 4) 4 (VTree.ofFun 6 (fun a => (maskWeightFast r29_ws a : ℤ) + (1 : ℤ) * (4 : ℤ) - (12 : ℤ))) (0 : ℤ) (patGens 29) r29_fi r29_prev r29_k4_fc r29_k4_tr = true := by decide +kernel
private def r29_k5_fc : List FCutCert := []
private def r29_k5_tr : BnbTree := br 0 (lf 2 [937857,675714,808836,22409,151440,939936,133634,133123,1156,134149,135430,133256,133384,135304,137224,135690,133132,136208,1736704,2801727]) (br 4 (lf 3 [3035008,3037056,1281,263681,133121,266753,267265,1154,526466,264706,268290,266243,264197,266246,264200,264456,266376,266504,133129,133130,659480,3457024,1474564,4243519]) (lf 3 [3035008,3037056,525057,2305,264705,266753,1442306,515,1027,4099,263300,263428,919556,264324,133380,3076,266372,266500,267268,268292,263173,263174,395270,266246,526856,266252,266260,135192,3457024,4243460,4243519]))
private lemma r29_k5_ok : checkLayer (r := 6) (cd := 1) 5 (VTree.ofFun 6 (fun a => (maskWeightFast r29_ws a : ℤ) + (1 : ℤ) * (5 : ℤ) - (12 : ℤ))) (0 : ℤ) (patGens 29) r29_fi r29_prev r29_k5_fc r29_k5_tr = true := by decide +kernel
private def r29_k6_fc : List FCutCert := []
private def r29_k6_tr : BnbTree := lf 1 [677760,282497,153474,282500,20360,151440,22432,5122,135176,5136,1491007]
private lemma r29_k6_ok : checkLayer (r := 6) (cd := 1) 6 (VTree.ofFun 6 (fun a => (maskWeightFast r29_ws a : ℤ) + (1 : ℤ) * (6 : ℤ) - (12 : ℤ))) (0 : ℤ) (patGens 29) r29_fi r29_prev r29_k6_fc r29_k6_tr = true := by decide +kernel
private lemma solve_row29 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hpat : HasPattern F 29) (hprev : ∀ pr ∈ r29_prev, ¬ HasPattern F pr) :
    ∃ W : Fin 12 → ℕ, 0 < ∑ i, W i ∧ F.card * (∑ i, W i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, W i) := by
  dsimp only [HasPattern, patR] at hpat
  obtain ⟨e0, he⟩ := hpat
  let e : Fin r29_ws.length ↪ Fin 12 := e0
  have he' : ∀ g ∈ patGens 29, decode e g ∈ F := he
  have hGens : ∀ g ∈ patGens 29, g < 2 ^ r29_ws.length ∧ decode e g ∈ F := by
    intro g hg
    refine ⟨?_, he' g hg⟩
    have hall : (patGens 29).all (· < 2 ^ r29_ws.length) = true := by decide
    simp only [List.all_eq_true, decide_eq_true_eq] at hall
    exact hall g hg
  have hFi : ∀ b ∈ r29_fi, b < 2 ^ r29_ws.length ∧ decode e b ∈ F :=
    checkClosureAux_sound closed empty he' [] r29_fi (fun _ h => by cases h) (by decide)
  have hTop : 2 ^ r29_ws.length - 1 ∈ r29_fi := by decide
  apply weight_from_fibers (r := r29_ws.length) (by decide) F e full (fun i => r29_ws[i.val]'i.isLt) 1 12 (by decide) (by decide) (0 : ℤ) (by decide)
  intro K hKsub hne
  have hkle : K.card ≤ 6 := K_card_le e hKsub
  have htop_iff : K = univ \ univ.map e ↔ K.card = 6 := K_eq_top_iff e hKsub
  have hlo_iff : K = ∅ ↔ K.card = 0 := card_eq_zero.symm
  have hoff : (if K = univ \ univ.map e then (0 : ℤ) else 0) - (if K = ∅ then (0 : ℤ) else 0) =
      (if K.card = 6 then (0 : ℤ) else 0) - (if K.card = 0 then (0 : ℤ) else 0) := by
    simp only [htop_iff, hlo_iff]
  rw [hoff]
  match hk : K.card with
  | 0 =>
    have h := checkLayer_sound (cd := 1) 0 closed minSize (ws := r29_ws) hKsub hk hne hGens hFi hTop hprev r29_k0_fc r29_k0_tr r29_k0_ok
    simpa [hk] using h
  | 1 =>
    have h := checkLayer_sound (cd := 5) 1 closed minSize (ws := r29_ws) hKsub hk hne hGens hFi hTop hprev r29_k1_fc r29_k1_tr r29_k1_ok
    simpa [hk] using h
  | 2 =>
    have h := checkLayer_sound (cd := 7) 2 closed minSize (ws := r29_ws) hKsub hk hne hGens hFi hTop hprev r29_k2_fc r29_k2_tr r29_k2_ok
    simpa [hk] using h
  | 3 =>
    have h := checkLayer_sound (cd := 5) 3 closed minSize (ws := r29_ws) hKsub hk hne hGens hFi hTop hprev r29_k3_fc r29_k3_tr r29_k3_ok
    simpa [hk] using h
  | 4 =>
    have h := checkLayer_sound (cd := 4) 4 closed minSize (ws := r29_ws) hKsub hk hne hGens hFi hTop hprev r29_k4_fc r29_k4_tr r29_k4_ok
    simpa [hk] using h
  | 5 =>
    have h := checkLayer_sound (cd := 1) 5 closed minSize (ws := r29_ws) hKsub hk hne hGens hFi hTop hprev r29_k5_fc r29_k5_tr r29_k5_ok
    simpa [hk] using h
  | 6 =>
    have h := checkLayer_sound (cd := 1) 6 closed minSize (ws := r29_ws) hKsub hk hne hGens hFi hTop hprev r29_k6_fc r29_k6_tr r29_k6_ok
    simpa [hk] using h
  | _ + 7 => omega

-- ==================== Row 30 (r=5) ====================
private def r30_ws : List ℕ := [3,3,3,3,3]
private def r30_fi : List ℕ := [0,15,31]
private def r30_prev : List ℕ := [7,8,12,16,26,27,28,29]
private def r30_k0_fc : List FCutCert := []
private def r30_k0_tr : BnbTree := lf 1 [950273,950274,557059,950276,557061,557062,163847,950280,557065,557066,163851,557068,163853,163854,49167,950288,557073,557074,163859,557076,163861,163862,557080,163865,163866,163868,442399]
private lemma r30_k0_ok : checkLayer (r := 5) (cd := 1) 0 (VTree.ofFun 5 (fun a => (maskWeightFast r30_ws a : ℤ) + (1 : ℤ) * (0 : ℤ) - (11 : ℤ))) (-6 : ℤ) (patGens 30) r30_fi r30_prev r30_k0_fc r30_k0_tr = true := by decide +kernel
private def r30_k1_fc : List FCutCert := [d [7] 26 [0,1,2,3,5,4],d [11] 26 [0,1,3,2,5,4],d [13] 26 [0,2,3,1,5,4],d [14] 26 [1,2,3,0,5,4],q [19,25,26] [(19,25,28,[0,4,5,1,3]),(19,26,28,[1,4,5,0,3]),(25,26,28,[3,4,5,0,1])],q [19,21,22] [(19,21,28,[0,4,5,1,2]),(19,22,28,[1,4,5,0,2]),(21,22,28,[2,4,5,0,1])],q [21,25,28] [(21,25,28,[0,4,5,2,3]),(21,28,28,[2,4,5,0,3]),(25,28,28,[3,4,5,0,2])],q [22,26,28] [(22,26,28,[1,4,5,2,3]),(22,28,28,[2,4,5,1,3]),(26,28,28,[3,4,5,1,2])]]
private def r30_k1_tr : BnbTree := lf 2 [65540,65541,65542,65543,2523136,1736705,1736706,950275,1736708,950277,950278,196608,1736712,950281,950282,196609,950284,196610,196611,1736720,950289,950290,950292,950296,1228831]
private lemma r30_k1_ok : checkLayer (r := 5) (cd := 3) 1 (VTree.ofFun 5 (fun a => (maskWeightFast r30_ws a : ℤ) + (1 : ℤ) * (1 : ℤ) - (11 : ℤ))) (0 : ℤ) (patGens 30) r30_fi r30_prev r30_k1_fc r30_k1_tr = true := by decide +kernel
private def r30_k2_fc : List FCutCert := [q [3,5,9,17] [(3,5,28,[0,5,6,1,2]),(3,9,28,[0,5,6,1,3]),(3,17,28,[0,5,6,1,4]),(5,9,28,[0,5,6,2,3]),(5,17,28,[0,5,6,2,4]),(9,17,28,[0,5,6,3,4])],q [3,6,10,18] [(3,6,28,[1,5,6,0,2]),(3,10,28,[1,5,6,0,3]),(3,18,28,[1,5,6,0,4]),(6,10,28,[1,5,6,2,3]),(6,18,28,[1,5,6,2,4]),(10,18,28,[1,5,6,3,4])],q [9,10,12,24] [(9,10,28,[3,5,6,0,1]),(9,12,28,[3,5,6,0,2]),(9,24,28,[3,5,6,0,4]),(10,12,28,[3,5,6,1,2]),(10,24,28,[3,5,6,1,4]),(12,24,28,[3,5,6,2,4])],q [5,6,12,20] [(5,6,28,[2,5,6,0,1]),(5,12,28,[2,5,6,0,3]),(5,20,28,[2,5,6,0,4]),(6,12,28,[2,5,6,1,3]),(6,20,28,[2,5,6,1,4]),(12,20,28,[2,5,6,3,4])],q [17,18,20,24] [(17,18,28,[4,5,6,0,1]),(17,20,28,[4,5,6,0,2]),(17,24,28,[4,5,6,0,3]),(18,20,28,[4,5,6,1,2]),(18,24,28,[4,5,6,1,3]),(20,24,28,[4,5,6,2,3])]]
private def r30_k2_tr : BnbTree := lf 4 [149379,149381,149382,149385,149386,149388,589824,589825,589826,589827,851972,4620288,3047425,3047426,3047428,3047432,3047440,3063839]
private lemma r30_k2_ok : checkLayer (r := 5) (cd := 3) 2 (VTree.ofFun 5 (fun a => (maskWeightFast r30_ws a : ℤ) + (1 : ℤ) * (2 : ℤ) - (11 : ℤ))) (0 : ℤ) (patGens 30) r30_fi r30_prev r30_k2_fc r30_k2_tr = true := by decide +kernel
private def r30_k3_fc : List FCutCert := [d [3,5] 29 [0,5,6,7,1,2],d [3,6] 29 [1,5,6,7,0,2],d [3,9] 29 [0,5,6,7,1,3],d [3,10] 29 [1,5,6,7,0,3],d [3,17] 29 [0,5,6,7,1,4],d [3,18] 29 [1,5,6,7,0,4],d [5,6] 29 [2,5,6,7,0,1],d [5,9] 29 [0,5,6,7,2,3],d [5,12] 29 [2,5,6,7,0,3],d [5,20] 29 [2,5,6,7,0,4],d [6,20] 29 [2,5,6,7,1,4],d [9,17] 29 [0,5,6,7,3,4],d [10,18] 29 [1,5,6,7,3,4],d [17,18] 29 [4,5,6,7,0,1],d [17,24] 29 [4,5,6,7,0,3],d [18,24] 29 [4,5,6,7,1,3],q [1,2,4,8,16] [(1,2,28,[5,6,7,0,1]),(1,4,28,[5,6,7,0,2]),(1,8,28,[5,6,7,0,3]),(1,16,28,[5,6,7,0,4]),(2,4,28,[5,6,7,1,2]),(2,8,28,[5,6,7,1,3]),(2,16,28,[5,6,7,1,4]),(4,8,28,[5,6,7,2,3]),(4,16,28,[5,6,7,2,4]),(8,16,28,[5,6,7,3,4])],q [5,17,20] [(5,17,29,[0,5,6,7,2,4]),(5,20,29,[2,5,6,7,0,4]),(17,20,29,[4,5,6,7,0,2])],q [6,18,20] [(6,18,29,[1,5,6,7,2,4]),(6,20,29,[2,5,6,7,1,4]),(18,20,29,[4,5,6,7,1,2])],q [9,10,12,24] [(9,10,29,[3,5,6,7,0,1]),(9,12,29,[3,5,6,7,0,2]),(9,24,29,[3,5,6,7,0,4]),(10,12,29,[3,5,6,7,1,2]),(10,24,29,[3,5,6,7,1,4]),(12,24,29,[3,5,6,7,2,4])],q [12,20,24] [(12,20,29,[2,5,6,7,3,4]),(12,24,29,[3,5,6,7,2,4]),(20,24,29,[4,5,6,7,2,3])]]
private def r30_k3_tr : BnbTree := br 3 (br 17 (br 5 (br 18 (lf 3 [411526,411529,411530,196618,1900560,196627,458772,3047424,688131,688133,688145,688146,2670623]) (lf 1 [149385,149388,196620,196623,589840,196626,950272,163843,163845,163857,442386,835615])) (lf 1 [411525,1281,642,1284,1029,2053,133381,134149,196614,196615,196616,196617,458768,950272,163843,2146309,163857,835615])) (lf 1 [149382,133258,133260,196619,196621,196622,589840,196625,950272,163843,1228817,835615])) (lf 1 [411523,1537,1538,515,1027,2051,133635,134147,196608,196609,196610,196611,196612,196613,458768,950272,2670595,835615])
private lemma r30_k3_ok : checkLayer (r := 5) (cd := 5) 3 (VTree.ofFun 5 (fun a => (maskWeightFast r30_ws a : ℤ) + (1 : ℤ) * (3 : ℤ) - (11 : ℤ))) (0 : ℤ) (patGens 30) r30_fi r30_prev r30_k3_fc r30_k3_tr = true := by decide +kernel
private def r30_k4_fc : List FCutCert := [q [1,2,4,8,16] [(1,2,29,[5,6,7,8,0,1]),(1,4,29,[5,6,7,8,0,2]),(1,8,29,[5,6,7,8,0,3]),(1,16,29,[5,6,7,8,0,4]),(2,4,29,[5,6,7,8,1,2]),(2,8,29,[5,6,7,8,1,3]),(2,16,29,[5,6,7,8,1,4]),(4,8,29,[5,6,7,8,2,3]),(4,16,29,[5,6,7,8,2,4]),(8,16,29,[5,6,7,8,3,4])]]
private def r30_k4_tr : BnbTree := br 3 (br 5 (br 10 (br 12 (br 17 (lf 2 [1197952,134150,2313,2569,2578,983040,163843,163845,163850,163852,163857,2015263]) (lf 1 [542592,2182,2185,2321,2577,3089,458752,32771,32773,32778,32780,442385,966687])) (lf 1 [542604,1542,1545,2188,2316,2572,3084,458752,32771,32773,32778,1228812,966687])) (lf 1 [542602,1286,1289,1546,2186,2314,2570,3082,458752,32771,32773,1359882,966687])) (lf 4 [2508677,1281,642,1284,393989,1029,394373,263685,2053,264325,395525,395781,396293,1546,2186,1900544,425987,5816325,4112415])) (lf 5 [3164035,1537,1538,515,393859,525059,1027,394371,525571,2051,526467,395523,526851,527363,1541,1545,2316,2424832,7782403,5160991])
private lemma r30_k4_ok : checkLayer (r := 5) (cd := 1) 4 (VTree.ofFun 5 (fun a => (maskWeightFast r30_ws a : ℤ) + (1 : ℤ) * (4 : ℤ) - (11 : ℤ))) (0 : ℤ) (patGens 30) r30_fi r30_prev r30_k4_fc r30_k4_tr = true := by decide +kernel
private def r30_k5_fc : List FCutCert := []
private def r30_k5_tr : BnbTree := br 4 (lf 1 [673664,131329,2049,3074,1027,2051,2056,2184,294916,1097759]) (lf 1 [673668,262657,262786,263172,264204,1097732,1097759])
private lemma r30_k5_ok : checkLayer (r := 5) (cd := 1) 5 (VTree.ofFun 5 (fun a => (maskWeightFast r30_ws a : ℤ) + (1 : ℤ) * (5 : ℤ) - (11 : ℤ))) (0 : ℤ) (patGens 30) r30_fi r30_prev r30_k5_fc r30_k5_tr = true := by decide +kernel
private def r30_k6_fc : List FCutCert := []
private def r30_k6_tr : BnbTree := lf 1 [542592,18305,18306,2049,514,1028,2056,1228831]
private lemma r30_k6_ok : checkLayer (r := 5) (cd := 1) 6 (VTree.ofFun 5 (fun a => (maskWeightFast r30_ws a : ℤ) + (1 : ℤ) * (6 : ℤ) - (11 : ℤ))) (0 : ℤ) (patGens 30) r30_fi r30_prev r30_k6_fc r30_k6_tr = true := by decide +kernel
private def r30_k7_fc : List FCutCert := []
private def r30_k7_tr : BnbTree := lf 1 [411520,18305,18308,18312,2050,1359903]
private lemma r30_k7_ok : checkLayer (r := 5) (cd := 1) 7 (VTree.ofFun 5 (fun a => (maskWeightFast r30_ws a : ℤ) + (1 : ℤ) * (7 : ℤ) - (11 : ℤ))) (6 : ℤ) (patGens 30) r30_fi r30_prev r30_k7_fc r30_k7_tr = true := by decide +kernel
private lemma solve_row30 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hpat : HasPattern F 30) (hprev : ∀ pr ∈ r30_prev, ¬ HasPattern F pr) :
    ∃ W : Fin 12 → ℕ, 0 < ∑ i, W i ∧ F.card * (∑ i, W i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, W i) := by
  dsimp only [HasPattern, patR] at hpat
  obtain ⟨e0, he⟩ := hpat
  let e : Fin r30_ws.length ↪ Fin 12 := e0
  have he' : ∀ g ∈ patGens 30, decode e g ∈ F := he
  have hGens : ∀ g ∈ patGens 30, g < 2 ^ r30_ws.length ∧ decode e g ∈ F := by
    intro g hg
    refine ⟨?_, he' g hg⟩
    have hall : (patGens 30).all (· < 2 ^ r30_ws.length) = true := by decide
    simp only [List.all_eq_true, decide_eq_true_eq] at hall
    exact hall g hg
  have hFi : ∀ b ∈ r30_fi, b < 2 ^ r30_ws.length ∧ decode e b ∈ F :=
    checkClosureAux_sound closed empty he' [] r30_fi (fun _ h => by cases h) (by decide)
  have hTop : 2 ^ r30_ws.length - 1 ∈ r30_fi := by decide
  apply weight_from_fibers (r := r30_ws.length) (by decide) F e full (fun i => r30_ws[i.val]'i.isLt) 1 11 (by decide) (by decide) (6 : ℤ) (by decide)
  intro K hKsub hne
  have hkle : K.card ≤ 7 := K_card_le e hKsub
  have htop_iff : K = univ \ univ.map e ↔ K.card = 7 := K_eq_top_iff e hKsub
  have hlo_iff : K = ∅ ↔ K.card = 0 := card_eq_zero.symm
  have hoff : (if K = univ \ univ.map e then (6 : ℤ) else 0) - (if K = ∅ then (6 : ℤ) else 0) =
      (if K.card = 7 then (6 : ℤ) else 0) - (if K.card = 0 then (6 : ℤ) else 0) := by
    simp only [htop_iff, hlo_iff]
  rw [hoff]
  match hk : K.card with
  | 0 =>
    have h := checkLayer_sound (cd := 1) 0 closed minSize (ws := r30_ws) hKsub hk hne hGens hFi hTop hprev r30_k0_fc r30_k0_tr r30_k0_ok
    simpa [hk] using h
  | 1 =>
    have h := checkLayer_sound (cd := 3) 1 closed minSize (ws := r30_ws) hKsub hk hne hGens hFi hTop hprev r30_k1_fc r30_k1_tr r30_k1_ok
    simpa [hk] using h
  | 2 =>
    have h := checkLayer_sound (cd := 3) 2 closed minSize (ws := r30_ws) hKsub hk hne hGens hFi hTop hprev r30_k2_fc r30_k2_tr r30_k2_ok
    simpa [hk] using h
  | 3 =>
    have h := checkLayer_sound (cd := 5) 3 closed minSize (ws := r30_ws) hKsub hk hne hGens hFi hTop hprev r30_k3_fc r30_k3_tr r30_k3_ok
    simpa [hk] using h
  | 4 =>
    have h := checkLayer_sound (cd := 1) 4 closed minSize (ws := r30_ws) hKsub hk hne hGens hFi hTop hprev r30_k4_fc r30_k4_tr r30_k4_ok
    simpa [hk] using h
  | 5 =>
    have h := checkLayer_sound (cd := 1) 5 closed minSize (ws := r30_ws) hKsub hk hne hGens hFi hTop hprev r30_k5_fc r30_k5_tr r30_k5_ok
    simpa [hk] using h
  | 6 =>
    have h := checkLayer_sound (cd := 1) 6 closed minSize (ws := r30_ws) hKsub hk hne hGens hFi hTop hprev r30_k6_fc r30_k6_tr r30_k6_ok
    simpa [hk] using h
  | 7 =>
    have h := checkLayer_sound (cd := 1) 7 closed minSize (ws := r30_ws) hKsub hk hne hGens hFi hTop hprev r30_k7_fc r30_k7_tr r30_k7_ok
    simpa [hk] using h
  | _ + 8 => omega

-- ==================== Row 31 (r=6) ====================
private def r31_ws : List ℕ := [3,3,3,3,3,3]
private def r31_fi : List ℕ := [0,15,51,63]
private def r31_prev : List ℕ := [7,8,12,16,26,27,28,29,30]
private def r31_k0_fc : List FCutCert := []
private def r31_k0_tr : BnbTree := lf 1 [1081345,1081346,688131,1081348,688133,688134,294919,1081352,688137,688138,294923,688140,294925,294926,1081360,688145,688146,294931,688148,294933,294934,688152,294937,294938,294940,1081376,688161,688162,294947,688164,294949,294950,688168,294953,294954,294956,688176,294961,294962,294964,294968,704575]
private lemma r31_k0_ok : checkLayer (r := 6) (cd := 1) 0 (VTree.ofFun 6 (fun a => (maskWeightFast r31_ws a : ℤ) + (1 : ℤ) * (0 : ℤ) - (12 : ℤ))) (-6 : ℤ) (patGens 31) r31_fi r31_prev r31_k0_fc r31_k0_tr = true := by decide +kernel
private def r31_k1_fc : List FCutCert := [d [7] 28 [0,1,2,6,3],d [11] 28 [0,1,3,6,2],d [13] 28 [0,2,3,1,6],d [14] 28 [1,2,3,6,0],d [19] 28 [0,1,4,5,6],d [35] 28 [0,1,5,6,4],d [49] 28 [0,4,5,6,1],d [50] 28 [1,4,5,6,0],q [28,44,52,56,60] [(28,44,28,[2,3,6,5,4]),(28,52,28,[2,4,6,5,3]),(28,56,28,[3,4,6,5,2]),(28,60,30,[2,3,4,6,5]),(44,52,28,[2,5,6,3,4]),(44,56,28,[3,5,6,2,4]),(44,60,30,[2,3,5,6,4]),(52,56,28,[4,5,6,2,3]),(52,60,30,[2,4,5,6,3]),(56,60,30,[3,4,5,6,2])]]
private def r31_k1_tr : BnbTree := lf 1 [149397,149398,154009,154010,154021,154022,149417,149418,196616,1343488,950273,950274,557059,950276,557061,557062,196608,950280,557065,557066,196609,557068,196610,196611,950288,557073,557074,196612,557076,557080,950304,557089,557090,196613,557092,557096,557104,196614,196615,835647]
private lemma r31_k1_ok : checkLayer (r := 6) (cd := 4) 1 (VTree.ofFun 6 (fun a => (maskWeightFast r31_ws a : ℤ) + (1 : ℤ) * (1 : ℤ) - (12 : ℤ))) (0 : ℤ) (patGens 31) r31_fi r31_prev r31_k1_fc r31_k1_tr = true := by decide +kernel
private def r31_k2_fc : List FCutCert := [d [3,10] 28 [1,6,7,0,3],d [3,18] 28 [1,6,7,0,4],d [6,10] 28 [1,6,7,2,3],d [6,18] 28 [1,6,7,2,4],d [9,10] 28 [3,6,7,0,1],d [9,24] 28 [3,6,7,0,4],d [10,12] 28 [3,6,7,1,2],d [10,18] 28 [1,6,7,3,4],d [10,24] 28 [3,6,7,1,4],d [10,34] 28 [1,6,7,5,3],d [10,40] 28 [3,6,7,5,1],d [10,11] 30 [1,3,6,7,0],d [10,14] 30 [1,3,6,7,2],d [10,26] 30 [1,3,6,7,4],d [10,42] 30 [1,3,6,7,5],d [12,24] 28 [3,6,7,2,4],d [17,18] 28 [4,6,7,0,1],d [17,24] 28 [4,6,7,0,3],d [18,20] 28 [4,6,7,1,2],d [18,24] 28 [4,6,7,1,3],d [18,34] 28 [1,6,7,5,4],d [18,48] 28 [4,6,7,5,1],d [18,19] 30 [1,4,6,7,0],d [18,22] 30 [1,4,6,7,2],d [18,26] 30 [1,4,6,7,3],d [18,50] 30 [1,4,6,7,5],d [20,24] 28 [4,6,7,2,3],d [24,40] 28 [3,6,7,5,4],d [24,48] 28 [4,6,7,5,3],d [24,25] 30 [3,4,6,7,0],d [24,26] 30 [3,4,6,7,1],d [24,28] 30 [3,4,6,7,2],d [24,56] 30 [3,4,6,7,5],q [3,5,9,17,33] [(3,5,28,[0,6,7,1,2]),(3,9,28,[0,6,7,1,3]),(3,17,28,[0,6,7,1,4]),(3,33,28,[0,6,7,5,1]),(5,9,28,[0,6,7,2,3]),(5,17,28,[0,6,7,2,4]),(5,33,28,[0,6,7,5,2]),(9,17,28,[0,6,7,3,4]),(9,33,28,[0,6,7,5,3]),(17,33,28,[0,6,7,5,4])],q [3,33,34,35] [(3,33,28,[0,6,7,5,1]),(3,34,28,[1,6,7,5,0]),(3,35,30,[0,1,6,7,5]),(33,34,28,[5,6,7,0,1]),(33,35,30,[0,5,6,7,1]),(34,35,30,[1,5,6,7,0])],q [3,7,11,19,35] [(3,7,30,[0,1,6,7,2]),(3,11,30,[0,1,6,7,3]),(3,19,30,[0,1,6,7,4]),(3,35,30,[0,1,6,7,5]),(7,11,29,[0,1,6,7,2,3]),(7,19,29,[0,1,6,7,2,4]),(7,35,29,[0,1,6,7,5,2]),(11,19,29,[0,1,6,7,3,4]),(11,35,29,[0,1,6,7,5,3]),(19,35,29,[0,1,6,7,5,4])],q [12,36,40,44] [(12,36,28,[2,6,7,5,3]),(12,40,28,[3,6,7,5,2]),(12,44,30,[2,3,6,7,5]),(36,40,28,[5,6,7,2,3]),(36,44,30,[2,5,6,7,3]),(40,44,30,[3,5,6,7,2])],q [5,6,12,20,36] [(5,6,28,[2,6,7,0,1]),(5,12,28,[2,6,7,0,3]),(5,20,28,[2,6,7,0,4]),(5,36,28,[2,6,7,5,0]),(6,12,28,[2,6,7,1,3]),(6,20,28,[2,6,7,1,4]),(6,36,28,[2,6,7,5,1]),(12,20,28,[2,6,7,3,4]),(12,36,28,[2,6,7,5,3]),(20,36,28,[2,6,7,5,4])],q [12,13,14,28,44] [(12,13,30,[2,3,6,7,0]),(12,14,30,[2,3,6,7,1]),(12,28,30,[2,3,6,7,4]),(12,44,30,[2,3,6,7,5]),(13,14,29,[2,3,6,7,0,1]),(13,28,29,[2,3,6,7,0,4]),(13,44,29,[2,3,6,7,5,0]),(14,28,29,[2,3,6,7,1,4]),(14,44,29,[2,3,6,7,5,1]),(28,44,29,[2,3,6,7,5,4])],q [5,7,13,21,37] [(5,7,30,[0,2,6,7,1]),(5,13,30,[0,2,6,7,3]),(5,21,30,[0,2,6,7,4]),(5,37,30,[0,2,6,7,5]),(7,13,29,[0,2,6,7,1,3]),(7,21,29,[0,2,6,7,1,4]),(7,37,29,[0,2,6,7,5,1]),(13,21,29,[0,2,6,7,3,4]),(13,37,29,[0,2,6,7,5,3]),(21,37,29,[0,2,6,7,5,4])],q [9,11,13,25,41] [(9,11,30,[0,3,6,7,1]),(9,13,30,[0,3,6,7,2]),(9,25,30,[0,3,6,7,4]),(9,41,30,[0,3,6,7,5]),(11,13,29,[0,3,6,7,1,2]),(11,25,29,[0,3,6,7,1,4]),(11,41,29,[0,3,6,7,5,1]),(13,25,29,[0,3,6,7,2,4]),(13,41,29,[0,3,6,7,5,2]),(25,41,29,[0,3,6,7,5,4])],q [6,7,14,22,38] [(6,7,30,[1,2,6,7,0]),(6,14,30,[1,2,6,7,3]),(6,22,30,[1,2,6,7,4]),(6,38,30,[1,2,6,7,5]),(7,14,29,[1,2,6,7,0,3]),(7,22,29,[1,2,6,7,0,4]),(7,38,29,[1,2,6,7,5,0]),(14,22,29,[1,2,6,7,3,4]),(14,38,29,[1,2,6,7,5,3]),(22,38,29,[1,2,6,7,5,4])],q [20,21,22,28,52] [(20,21,30,[2,4,6,7,0]),(20,22,30,[2,4,6,7,1]),(20,28,30,[2,4,6,7,3]),(20,52,30,[2,4,6,7,5]),(21,22,29,[2,4,6,7,0,1]),(21,28,29,[2,4,6,7,0,3]),(21,52,29,[2,4,6,7,5,0]),(22,28,29,[2,4,6,7,1,3]),(22,52,29,[2,4,6,7,5,1]),(28,52,29,[2,4,6,7,5,3])],q [17,19,21,25,49] [(17,19,30,[0,4,6,7,1]),(17,21,30,[0,4,6,7,2]),(17,25,30,[0,4,6,7,3]),(17,49,30,[0,4,6,7,5]),(19,21,29,[0,4,6,7,1,2]),(19,25,29,[0,4,6,7,1,3]),(19,49,29,[0,4,6,7,5,1]),(21,25,29,[0,4,6,7,2,3]),(21,49,29,[0,4,6,7,5,2]),(25,49,29,[0,4,6,7,5,3])],q [33,34,36,40,48] [(33,34,28,[5,6,7,0,1]),(33,36,28,[5,6,7,0,2]),(33,40,28,[5,6,7,0,3]),(33,48,28,[5,6,7,0,4]),(34,36,28,[5,6,7,1,2]),(34,40,28,[5,6,7,1,3]),(34,48,28,[5,6,7,1,4]),(36,40,28,[5,6,7,2,3]),(36,48,28,[5,6,7,2,4]),(40,48,28,[5,6,7,3,4])],q [36,37,38,44,52] [(36,37,30,[2,5,6,7,0]),(36,38,30,[2,5,6,7,1]),(36,44,30,[2,5,6,7,3]),(36,52,30,[2,5,6,7,4]),(37,38,29,[2,5,6,7,0,1]),(37,44,29,[2,5,6,7,0,3]),(37,52,29,[2,5,6,7,0,4]),(38,44,29,[2,5,6,7,1,3]),(38,52,29,[2,5,6,7,1,4]),(44,52,29,[2,5,6,7,3,4])],q [33,35,37,41,49] [(33,35,30,[0,5,6,7,1]),(33,37,30,[0,5,6,7,2]),(33,41,30,[0,5,6,7,3]),(33,49,30,[0,5,6,7,4]),(35,37,29,[0,5,6,7,1,2]),(35,41,29,[0,5,6,7,1,3]),(35,49,29,[0,5,6,7,1,4]),(37,41,29,[0,5,6,7,2,3]),(37,49,29,[0,5,6,7,2,4]),(41,49,29,[0,5,6,7,3,4])],q [7,35,37,38] [(7,35,29,[0,1,6,7,5,2]),(7,37,29,[0,2,6,7,5,1]),(7,38,29,[1,2,6,7,5,0]),(35,37,29,[0,5,6,7,1,2]),(35,38,29,[1,5,6,7,0,2]),(37,38,29,[2,5,6,7,0,1])],q [34,35,38,42,50] [(34,35,30,[1,5,6,7,0]),(34,38,30,[1,5,6,7,2]),(34,42,30,[1,5,6,7,3]),(34,50,30,[1,5,6,7,4]),(35,38,29,[1,5,6,7,0,2]),(35,42,29,[1,5,6,7,0,3]),(35,50,29,[1,5,6,7,0,4]),(38,42,29,[1,5,6,7,2,3]),(38,50,29,[1,5,6,7,2,4]),(42,50,29,[1,5,6,7,3,4])],q [40,41,42,44,56] [(40,41,30,[3,5,6,7,0]),(40,42,30,[3,5,6,7,1]),(40,44,30,[3,5,6,7,2]),(40,56,30,[3,5,6,7,4]),(41,42,29,[3,5,6,7,0,1]),(41,44,29,[3,5,6,7,0,2]),(41,56,29,[3,5,6,7,0,4]),(42,44,29,[3,5,6,7,1,2]),(42,56,29,[3,5,6,7,1,4]),(44,56,29,[3,5,6,7,2,4])],q [48,49,50,52,56] [(48,49,30,[4,5,6,7,0]),(48,50,30,[4,5,6,7,1]),(48,52,30,[4,5,6,7,2]),(48,56,30,[4,5,6,7,3]),(49,50,29,[4,5,6,7,0,1]),(49,52,29,[4,5,6,7,0,2]),(49,56,29,[4,5,6,7,0,3]),(50,52,29,[4,5,6,7,1,2]),(50,56,29,[4,5,6,7,1,3]),(52,56,29,[4,5,6,7,2,3])]]
private def r31_k2_tr : BnbTree := br 10 (br 24 (br 18 (lf 45 [1722243,8280451,6576517,14178694,22919,14309769,22923,9848716,14436241,149395,10110868,3955092,4343701,4217238,4348313,5790106,7620514,5654437,4212646,7358376,154024,4081577,4217258,3299760,8323105,4915235,8454181,5046310,720936,720937,720938,589867,15007788,65582,720944,720945,5046322,58884096,41189377,41189378,41189380,41189384,23494666,41189392,23494674,23494680,41189408,47104063]) (lf 3 [280453,678277,285063,547209,153995,149388,18318,1853330,678290,154009,1066913,280484,285094,285096,280490,285108,285112,264453,657673,526604,264850,3602,659986,660498,1507329,1507331,1507344,1507346,1507348,1507349,327702,327703,327704,327705,327716,196646,65576,327726,3833856,2654209,2654210,2654212,2654216,1474570,2654224,16039954,1474584,2654240,3063871])) (lf 3 [280451,285059,678277,285062,280461,285075,285077,1853336,1857944,673698,411556,285092,280490,149420,265219,658437,658438,265227,659608,266520,397848,268568,137752,1507333,1507343,1507345,1507347,1507354,1507355,1507356,327709,327710,327711,327712,327714,327721,65581,327726,3833856,2654209,2654210,2654212,2654216,1474570,2654224,19578904,2654240,3063871])) (lf 3 [1333637,673674,1857930,411537,18323,673684,22932,280470,18329,673697,18339,542628,154020,22950,280489,678320,657546,526858,3594,659594,528906,5642,399370,6410,6666,7178,1507328,1507330,1507332,1245190,1507335,1507336,1507337,1507338,327691,65548,327693,327694,196646,65575,196651,196655,196658,3833856,2654209,2654210,2654212,2654216,18792458,2654224,2654240,3063871])
set_option maxRecDepth 8192 in
private lemma r31_k2_ok : checkLayer (r := 6) (cd := 6) 2 (VTree.ofFun 6 (fun a => (maskWeightFast r31_ws a : ℤ) + (1 : ℤ) * (2 : ℤ) - (12 : ℤ))) (0 : ℤ) (patGens 31) r31_fi r31_prev r31_k2_fc r31_k2_tr = true := by decide +kernel
private def r31_k3_fc : List FCutCert := [q [1,2,4,8,16,32] [(1,2,28,[6,7,8,0,1]),(1,4,28,[6,7,8,0,2]),(1,8,28,[6,7,8,0,3]),(1,16,28,[6,7,8,0,4]),(1,32,28,[6,7,8,0,5]),(2,4,28,[6,7,8,1,2]),(2,8,28,[6,7,8,1,3]),(2,16,28,[6,7,8,1,4]),(2,32,28,[6,7,8,5,1]),(4,8,28,[6,7,8,2,3]),(4,16,28,[6,7,8,2,4]),(4,32,28,[6,7,8,5,2]),(8,16,28,[6,7,8,3,4]),(8,32,28,[6,7,8,5,3]),(16,32,28,[6,7,8,5,4])],q [1,3,5,9,17,33] [(1,3,30,[0,6,7,8,1]),(1,5,30,[0,6,7,8,2]),(1,9,30,[0,6,7,8,3]),(1,17,30,[0,6,7,8,4]),(1,33,30,[0,6,7,8,5]),(3,5,29,[0,6,7,8,1,2]),(3,9,29,[0,6,7,8,1,3]),(3,17,29,[0,6,7,8,1,4]),(3,33,29,[0,6,7,8,5,1]),(5,9,29,[0,6,7,8,2,3]),(5,17,29,[0,6,7,8,2,4]),(5,33,29,[0,6,7,8,5,2]),(9,17,29,[0,6,7,8,3,4]),(9,33,29,[0,6,7,8,5,3]),(17,33,29,[0,6,7,8,5,4])],q [2,3,6,10,18,34] [(2,3,30,[1,6,7,8,0]),(2,6,30,[1,6,7,8,2]),(2,10,30,[1,6,7,8,3]),(2,18,30,[1,6,7,8,4]),(2,34,30,[1,6,7,8,5]),(3,6,29,[1,6,7,8,0,2]),(3,10,29,[1,6,7,8,0,3]),(3,18,29,[1,6,7,8,0,4]),(3,34,29,[1,6,7,8,5,0]),(6,10,29,[1,6,7,8,2,3]),(6,18,29,[1,6,7,8,2,4]),(6,34,29,[1,6,7,8,5,2]),(10,18,29,[1,6,7,8,3,4]),(10,34,29,[1,6,7,8,5,3]),(18,34,29,[1,6,7,8,5,4])],q [4,5,6,12,20,36] [(4,5,30,[2,6,7,8,0]),(4,6,30,[2,6,7,8,1]),(4,12,30,[2,6,7,8,3]),(4,20,30,[2,6,7,8,4]),(4,36,30,[2,6,7,8,5]),(5,6,29,[2,6,7,8,0,1]),(5,12,29,[2,6,7,8,0,3]),(5,20,29,[2,6,7,8,0,4]),(5,36,29,[2,6,7,8,5,0]),(6,12,29,[2,6,7,8,1,3]),(6,20,29,[2,6,7,8,1,4]),(6,36,29,[2,6,7,8,5,1]),(12,20,29,[2,6,7,8,3,4]),(12,36,29,[2,6,7,8,5,3]),(20,36,29,[2,6,7,8,5,4])],q [8,9,10,12,24,40] [(8,9,30,[3,6,7,8,0]),(8,10,30,[3,6,7,8,1]),(8,12,30,[3,6,7,8,2]),(8,24,30,[3,6,7,8,4]),(8,40,30,[3,6,7,8,5]),(9,10,29,[3,6,7,8,0,1]),(9,12,29,[3,6,7,8,0,2]),(9,24,29,[3,6,7,8,0,4]),(9,40,29,[3,6,7,8,5,0]),(10,12,29,[3,6,7,8,1,2]),(10,24,29,[3,6,7,8,1,4]),(10,40,29,[3,6,7,8,5,1]),(12,24,29,[3,6,7,8,2,4]),(12,40,29,[3,6,7,8,5,2]),(24,40,29,[3,6,7,8,5,4])],q [16,17,18,20,24,48] [(16,17,30,[4,6,7,8,0]),(16,18,30,[4,6,7,8,1]),(16,20,30,[4,6,7,8,2]),(16,24,30,[4,6,7,8,3]),(16,48,30,[4,6,7,8,5]),(17,18,29,[4,6,7,8,0,1]),(17,20,29,[4,6,7,8,0,2]),(17,24,29,[4,6,7,8,0,3]),(17,48,29,[4,6,7,8,5,0]),(18,20,29,[4,6,7,8,1,2]),(18,24,29,[4,6,7,8,1,3]),(18,48,29,[4,6,7,8,5,1]),(20,24,29,[4,6,7,8,2,3]),(20,48,29,[4,6,7,8,5,2]),(24,48,29,[4,6,7,8,5,3])]]
private def r31_k3_tr : BnbTree := lf 8 [673666,809346,280451,1595780,285061,1988998,1464712,153993,1857930,1853324,1197968,1591186,1591188,1460120,2115488,804769,2508706,411556,1989028,2382248,2120112,3997696,2162689,458754,458755,589828,851973,9338880,9355327]
private lemma r31_k3_ok : checkLayer (r := 6) (cd := 3) 3 (VTree.ofFun 6 (fun a => (maskWeightFast r31_ws a : ℤ) + (1 : ℤ) * (3 : ℤ) - (12 : ℤ))) (0 : ℤ) (patGens 31) r31_fi r31_prev r31_k3_fc r31_k3_tr = true := by decide +kernel
private def r31_k4_fc : List FCutCert := [q [0,1,2,4,8,16,32] [(0,1,30,[6,7,8,9,0]),(0,2,30,[6,7,8,9,1]),(0,4,30,[6,7,8,9,2]),(0,8,30,[6,7,8,9,3]),(0,16,30,[6,7,8,9,4]),(0,32,30,[6,7,8,9,5]),(1,2,29,[6,7,8,9,0,1]),(1,4,29,[6,7,8,9,0,2]),(1,8,29,[6,7,8,9,0,3]),(1,16,29,[6,7,8,9,0,4]),(1,32,29,[6,7,8,9,0,5]),(2,4,29,[6,7,8,9,1,2]),(2,8,29,[6,7,8,9,1,3]),(2,16,29,[6,7,8,9,1,4]),(2,32,29,[6,7,8,9,5,1]),(4,8,29,[6,7,8,9,2,3]),(4,16,29,[6,7,8,9,2,4]),(4,32,29,[6,7,8,9,5,2]),(8,16,29,[6,7,8,9,3,4]),(8,32,29,[6,7,8,9,5,3]),(16,32,29,[6,7,8,9,5,4])]]
private def r31_k4_tr : BnbTree := lf 2 [18304,547200,411523,416133,416134,416137,416138,280460,411537,411538,149396,154004,411544,411553,411554,149412,154020,411560,285104,6156,1245184,2539583]
private lemma r31_k4_ok : checkLayer (r := 6) (cd := 1) 4 (VTree.ofFun 6 (fun a => (maskWeightFast r31_ws a : ℤ) + (1 : ℤ) * (4 : ℤ) - (12 : ℤ))) (0 : ℤ) (patGens 31) r31_fi r31_prev r31_k4_fc r31_k4_tr = true := by decide +kernel
private def r31_k5_fc : List FCutCert := []
private def r31_k5_tr : BnbTree := lf 1 [149376,547200,280449,416132,22917,22918,416136,22921,22922,411536,18322,18324,18328,280480,18338,18340,18344,1537,2178,4226,6146,4099,1359935]
private lemma r31_k5_ok : checkLayer (r := 6) (cd := 1) 5 (VTree.ofFun 6 (fun a => (maskWeightFast r31_ws a : ℤ) + (1 : ℤ) * (5 : ℤ) - (12 : ℤ))) (0 : ℤ) (patGens 31) r31_fi r31_prev r31_k5_fc r31_k5_tr = true := by decide +kernel
private def r31_k6_fc : List FCutCert := []
private def r31_k6_tr : BnbTree := lf 1 [673664,285057,285058,285060,285064,280464,280480,1491007]
private lemma r31_k6_ok : checkLayer (r := 6) (cd := 1) 6 (VTree.ofFun 6 (fun a => (maskWeightFast r31_ws a : ℤ) + (1 : ℤ) * (6 : ℤ) - (12 : ℤ))) (6 : ℤ) (patGens 31) r31_fi r31_prev r31_k6_fc r31_k6_tr = true := by decide +kernel
private lemma solve_row31 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hpat : HasPattern F 31) (hprev : ∀ pr ∈ r31_prev, ¬ HasPattern F pr) :
    ∃ W : Fin 12 → ℕ, 0 < ∑ i, W i ∧ F.card * (∑ i, W i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, W i) := by
  dsimp only [HasPattern, patR] at hpat
  obtain ⟨e0, he⟩ := hpat
  let e : Fin r31_ws.length ↪ Fin 12 := e0
  have he' : ∀ g ∈ patGens 31, decode e g ∈ F := he
  have hGens : ∀ g ∈ patGens 31, g < 2 ^ r31_ws.length ∧ decode e g ∈ F := by
    intro g hg
    refine ⟨?_, he' g hg⟩
    have hall : (patGens 31).all (· < 2 ^ r31_ws.length) = true := by decide
    simp only [List.all_eq_true, decide_eq_true_eq] at hall
    exact hall g hg
  have hFi : ∀ b ∈ r31_fi, b < 2 ^ r31_ws.length ∧ decode e b ∈ F :=
    checkClosureAux_sound closed empty he' [] r31_fi (fun _ h => by cases h) (by decide)
  have hTop : 2 ^ r31_ws.length - 1 ∈ r31_fi := by decide
  apply weight_from_fibers (r := r31_ws.length) (by decide) F e full (fun i => r31_ws[i.val]'i.isLt) 1 12 (by decide) (by decide) (6 : ℤ) (by decide)
  intro K hKsub hne
  have hkle : K.card ≤ 6 := K_card_le e hKsub
  have htop_iff : K = univ \ univ.map e ↔ K.card = 6 := K_eq_top_iff e hKsub
  have hlo_iff : K = ∅ ↔ K.card = 0 := card_eq_zero.symm
  have hoff : (if K = univ \ univ.map e then (6 : ℤ) else 0) - (if K = ∅ then (6 : ℤ) else 0) =
      (if K.card = 6 then (6 : ℤ) else 0) - (if K.card = 0 then (6 : ℤ) else 0) := by
    simp only [htop_iff, hlo_iff]
  rw [hoff]
  match hk : K.card with
  | 0 =>
    have h := checkLayer_sound (cd := 1) 0 closed minSize (ws := r31_ws) hKsub hk hne hGens hFi hTop hprev r31_k0_fc r31_k0_tr r31_k0_ok
    simpa [hk] using h
  | 1 =>
    have h := checkLayer_sound (cd := 4) 1 closed minSize (ws := r31_ws) hKsub hk hne hGens hFi hTop hprev r31_k1_fc r31_k1_tr r31_k1_ok
    simpa [hk] using h
  | 2 =>
    have h := checkLayer_sound (cd := 6) 2 closed minSize (ws := r31_ws) hKsub hk hne hGens hFi hTop hprev r31_k2_fc r31_k2_tr r31_k2_ok
    simpa [hk] using h
  | 3 =>
    have h := checkLayer_sound (cd := 3) 3 closed minSize (ws := r31_ws) hKsub hk hne hGens hFi hTop hprev r31_k3_fc r31_k3_tr r31_k3_ok
    simpa [hk] using h
  | 4 =>
    have h := checkLayer_sound (cd := 1) 4 closed minSize (ws := r31_ws) hKsub hk hne hGens hFi hTop hprev r31_k4_fc r31_k4_tr r31_k4_ok
    simpa [hk] using h
  | 5 =>
    have h := checkLayer_sound (cd := 1) 5 closed minSize (ws := r31_ws) hKsub hk hne hGens hFi hTop hprev r31_k5_fc r31_k5_tr r31_k5_ok
    simpa [hk] using h
  | 6 =>
    have h := checkLayer_sound (cd := 1) 6 closed minSize (ws := r31_ws) hKsub hk hne hGens hFi hTop hprev r31_k6_fc r31_k6_tr r31_k6_ok
    simpa [hk] using h
  | _ + 7 => omega

-- ==================== Row 32 (r=4) ====================
private def r32_ws : List ℕ := [5,5,5,5]
private def r32_fi : List ℕ := [0,15]
private def r32_prev : List ℕ := [7,8,12,16,26,27,28,29,30,31]
private def r32_k0_fc : List FCutCert := []
private def r32_k0_tr : BnbTree := lf 1 [1605633,1605634,950275,1605636,950277,950278,294919,1605640,950281,950282,294923,950284,294925,294926,180239]
private lemma r32_k0_ok : checkLayer (r := 4) (cd := 1) 0 (VTree.ofFun 4 (fun a => (maskWeightFast r32_ws a : ℤ) + (2 : ℤ) * (0 : ℤ) - (18 : ℤ))) (-16 : ℤ) (patGens 32) r32_fi r32_prev r32_k0_fc r32_k0_tr = true := by decide +kernel
private def r32_k1_fc : List FCutCert := [d [7] 28 [0,1,2,4,3],d [11] 28 [0,1,3,4,2],d [13] 28 [0,2,3,4,1],d [14] 28 [1,2,3,4,0]]
private def r32_k1_tr : BnbTree := lf 1 [1998848,1343489,1343490,688131,1343492,688133,688134,65536,1343496,688137,688138,65537,688140,65538,65539,442383]
private lemma r32_k1_ok : checkLayer (r := 4) (cd := 2) 1 (VTree.ofFun 4 (fun a => (maskWeightFast r32_ws a : ℤ) + (2 : ℤ) * (1 : ℤ) - (18 : ℤ))) (0 : ℤ) (patGens 32) r32_fi r32_prev r32_k1_fc r32_k1_tr = true := by decide +kernel
private def r32_k2_fc : List FCutCert := [d [3] 31 [0,1,4,5,2,3],d [5] 31 [0,2,4,5,1,3],d [6] 31 [1,2,4,5,0,3],d [9] 31 [0,3,4,5,1,2],d [10] 31 [1,3,4,5,0,2],d [12] 31 [2,3,4,5,0,1]]
private def r32_k2_tr : BnbTree := lf 1 [1736704,1081345,1081346,458752,1081348,458753,458754,1081352,458755,458756,458757,704527]
private lemma r32_k2_ok : checkLayer (r := 4) (cd := 3) 2 (VTree.ofFun 4 (fun a => (maskWeightFast r32_ws a : ℤ) + (2 : ℤ) * (2 : ℤ) - (18 : ℤ))) (0 : ℤ) (patGens 32) r32_fi r32_prev r32_k2_fc r32_k2_tr = true := by decide +kernel
private def r32_k3_fc : List FCutCert := [d [3,5] 29 [0,4,5,6,1,2],d [3,6] 29 [1,4,5,6,0,2],d [3,9] 29 [0,4,5,6,1,3],d [3,10] 29 [1,4,5,6,0,3],d [5,6] 29 [2,4,5,6,0,1],d [5,9] 29 [0,4,5,6,2,3],d [5,12] 29 [2,4,5,6,3,0],d [6,10] 29 [1,4,5,6,2,3],d [6,12] 29 [2,4,5,6,3,1],d [9,10] 29 [3,4,5,6,0,1],d [9,12] 29 [3,4,5,6,2,0],d [10,12] 29 [3,4,5,6,2,1],q [1,8,9] [(1,8,28,[4,5,6,0,3]),(1,9,30,[0,4,5,6,3]),(8,9,30,[3,4,5,6,0])],q [1,2,4,8] [(1,2,28,[4,5,6,0,1]),(1,4,28,[4,5,6,0,2]),(1,8,28,[4,5,6,0,3]),(2,4,28,[4,5,6,1,2]),(2,8,28,[4,5,6,1,3]),(4,8,28,[4,5,6,2,3])],q [1,2,3] [(1,2,28,[4,5,6,0,1]),(1,3,30,[0,4,5,6,1]),(2,3,30,[1,4,5,6,0])],q [1,4,5] [(1,4,28,[4,5,6,0,2]),(1,5,30,[0,4,5,6,2]),(4,5,30,[2,4,5,6,0])],q [2,8,10] [(2,8,28,[4,5,6,1,3]),(2,10,30,[1,4,5,6,3]),(8,10,30,[3,4,5,6,1])],q [4,8,12] [(4,8,28,[4,5,6,2,3]),(4,12,30,[2,4,5,6,3]),(8,12,30,[3,4,5,6,2])],q [2,4,6] [(2,4,28,[4,5,6,1,2]),(2,6,30,[1,4,5,6,2]),(4,6,30,[2,4,5,6,1])]]
private def r32_k3_tr : BnbTree := br 5 (br 6 (br 3 (br 9 (br 10 (lf 3 [132609,132610,2424845,196625,4620288,688131,688133,688134,688137,688138,3063823]) (lf 1 [263425,263428,196619,458767,851984,1474560,163843,163846,163849,1622026,966671])) (lf 1 [263298,263300,196617,196618,851980,458770,1474560,163843,163845,1884169,966671])) (lf 1 [262659,263171,196610,196611,851982,458769,1474560,1884163,163845,163846,966671])) (lf 1 [262913,263174,196609,196615,196616,458764,851986,1474560,163845,2146310,966671])) (lf 1 [262786,263173,196608,196612,196613,196614,851983,458768,1474560,2408453,966671])
private lemma r32_k3_ok : checkLayer (r := 4) (cd := 5) 3 (VTree.ofFun 4 (fun a => (maskWeightFast r32_ws a : ℤ) + (2 : ℤ) * (3 : ℤ) - (18 : ℤ))) (0 : ℤ) (patGens 32) r32_fi r32_prev r32_k3_fc r32_k3_tr = true := by decide +kernel
private def r32_k4_fc : List FCutCert := [q [0,1,2,4,8] [(0,1,30,[4,5,6,7,0]),(0,2,30,[4,5,6,7,1]),(0,4,30,[4,5,6,7,2]),(0,8,30,[4,5,6,7,3]),(1,2,29,[4,5,6,7,0,1]),(1,4,29,[4,5,6,7,0,2]),(1,8,29,[4,5,6,7,0,3]),(2,4,29,[4,5,6,7,1,2]),(2,8,29,[4,5,6,7,1,3]),(4,8,29,[4,5,6,7,2,3])]]
private def r32_k4_tr : BnbTree := lf 1 [589824,1228815]
private lemma r32_k4_ok : checkLayer (r := 4) (cd := 1) 4 (VTree.ofFun 4 (fun a => (maskWeightFast r32_ws a : ℤ) + (2 : ℤ) * (4 : ℤ) - (18 : ℤ))) (0 : ℤ) (patGens 32) r32_fi r32_prev r32_k4_fc r32_k4_tr = true := by decide +kernel
private def r32_k5_fc : List FCutCert := []
private def r32_k5_tr : BnbTree := br 1 (lf 2 [262658,263170,263172,688129,3063823]) (lf 2 [393473,393729,394241,514,1026,1028,704513,3063823])
private lemma r32_k5_ok : checkLayer (r := 4) (cd := 1) 5 (VTree.ofFun 4 (fun a => (maskWeightFast r32_ws a : ℤ) + (2 : ℤ) * (5 : ℤ) - (18 : ℤ))) (0 : ℤ) (patGens 32) r32_fi r32_prev r32_k5_fc r32_k5_tr = true := by decide +kernel
private def r32_k6_fc : List FCutCert := []
private def r32_k6_tr : BnbTree := lf 1 [1025,514,1753103]
private lemma r32_k6_ok : checkLayer (r := 4) (cd := 1) 6 (VTree.ofFun 4 (fun a => (maskWeightFast r32_ws a : ℤ) + (2 : ℤ) * (6 : ℤ) - (18 : ℤ))) (0 : ℤ) (patGens 32) r32_fi r32_prev r32_k6_fc r32_k6_tr = true := by decide +kernel
private def r32_k7_fc : List FCutCert := []
private def r32_k7_tr : BnbTree := lf 1 [2015247]
private lemma r32_k7_ok : checkLayer (r := 4) (cd := 1) 7 (VTree.ofFun 4 (fun a => (maskWeightFast r32_ws a : ℤ) + (2 : ℤ) * (7 : ℤ) - (18 : ℤ))) (0 : ℤ) (patGens 32) r32_fi r32_prev r32_k7_fc r32_k7_tr = true := by decide +kernel
private def r32_k8_fc : List FCutCert := []
private def r32_k8_tr : BnbTree := lf 1 [2277391]
private lemma r32_k8_ok : checkLayer (r := 4) (cd := 1) 8 (VTree.ofFun 4 (fun a => (maskWeightFast r32_ws a : ℤ) + (2 : ℤ) * (8 : ℤ) - (18 : ℤ))) (16 : ℤ) (patGens 32) r32_fi r32_prev r32_k8_fc r32_k8_tr = true := by decide +kernel
private lemma solve_row32 (F : Finset (Finset (Fin 12))) (closed : IsUnionClosed F)
    (empty : ∅ ∈ F) (full : univ ∈ F) (minSize : ∀ X ∈ F, X.Nonempty → 4 ≤ X.card)
    (hpat : HasPattern F 32) (hprev : ∀ pr ∈ r32_prev, ¬ HasPattern F pr) :
    ∃ W : Fin 12 → ℕ, 0 < ∑ i, W i ∧ F.card * (∑ i, W i) ≤ 2 * (∑ X ∈ F, ∑ i ∈ X, W i) := by
  dsimp only [HasPattern, patR] at hpat
  obtain ⟨e0, he⟩ := hpat
  let e : Fin r32_ws.length ↪ Fin 12 := e0
  have he' : ∀ g ∈ patGens 32, decode e g ∈ F := he
  have hGens : ∀ g ∈ patGens 32, g < 2 ^ r32_ws.length ∧ decode e g ∈ F := by
    intro g hg
    refine ⟨?_, he' g hg⟩
    have hall : (patGens 32).all (· < 2 ^ r32_ws.length) = true := by decide
    simp only [List.all_eq_true, decide_eq_true_eq] at hall
    exact hall g hg
  have hFi : ∀ b ∈ r32_fi, b < 2 ^ r32_ws.length ∧ decode e b ∈ F :=
    checkClosureAux_sound closed empty he' [] r32_fi (fun _ h => by cases h) (by decide)
  have hTop : 2 ^ r32_ws.length - 1 ∈ r32_fi := by decide
  apply weight_from_fibers (r := r32_ws.length) (by decide) F e full (fun i => r32_ws[i.val]'i.isLt) 2 18 (by decide) (by decide) (16 : ℤ) (by decide)
  intro K hKsub hne
  have hkle : K.card ≤ 8 := K_card_le e hKsub
  have htop_iff : K = univ \ univ.map e ↔ K.card = 8 := K_eq_top_iff e hKsub
  have hlo_iff : K = ∅ ↔ K.card = 0 := card_eq_zero.symm
  have hoff : (if K = univ \ univ.map e then (16 : ℤ) else 0) - (if K = ∅ then (16 : ℤ) else 0) =
      (if K.card = 8 then (16 : ℤ) else 0) - (if K.card = 0 then (16 : ℤ) else 0) := by
    simp only [htop_iff, hlo_iff]
  rw [hoff]
  match hk : K.card with
  | 0 =>
    have h := checkLayer_sound (cd := 1) 0 closed minSize (ws := r32_ws) hKsub hk hne hGens hFi hTop hprev r32_k0_fc r32_k0_tr r32_k0_ok
    simpa [hk] using h
  | 1 =>
    have h := checkLayer_sound (cd := 2) 1 closed minSize (ws := r32_ws) hKsub hk hne hGens hFi hTop hprev r32_k1_fc r32_k1_tr r32_k1_ok
    simpa [hk] using h
  | 2 =>
    have h := checkLayer_sound (cd := 3) 2 closed minSize (ws := r32_ws) hKsub hk hne hGens hFi hTop hprev r32_k2_fc r32_k2_tr r32_k2_ok
    simpa [hk] using h
  | 3 =>
    have h := checkLayer_sound (cd := 5) 3 closed minSize (ws := r32_ws) hKsub hk hne hGens hFi hTop hprev r32_k3_fc r32_k3_tr r32_k3_ok
    simpa [hk] using h
  | 4 =>
    have h := checkLayer_sound (cd := 1) 4 closed minSize (ws := r32_ws) hKsub hk hne hGens hFi hTop hprev r32_k4_fc r32_k4_tr r32_k4_ok
    simpa [hk] using h
  | 5 =>
    have h := checkLayer_sound (cd := 1) 5 closed minSize (ws := r32_ws) hKsub hk hne hGens hFi hTop hprev r32_k5_fc r32_k5_tr r32_k5_ok
    simpa [hk] using h
  | 6 =>
    have h := checkLayer_sound (cd := 1) 6 closed minSize (ws := r32_ws) hKsub hk hne hGens hFi hTop hprev r32_k6_fc r32_k6_tr r32_k6_ok
    simpa [hk] using h
  | 7 =>
    have h := checkLayer_sound (cd := 1) 7 closed minSize (ws := r32_ws) hKsub hk hne hGens hFi hTop hprev r32_k7_fc r32_k7_tr r32_k7_ok
    simpa [hk] using h
  | 8 =>
    have h := checkLayer_sound (cd := 1) 8 closed minSize (ws := r32_ws) hKsub hk hne hGens hFi hTop hprev r32_k8_fc r32_k8_tr r32_k8_ok
    simpa [hk] using h
  | _ + 9 => omega

theorem solve_H2 : OMA.R_UnionClosed_union_closed_variants_univ_card_R1.H2 := by
  intro F closed empty full hex4 minSize
  by_cases h7 : HasPattern F 7
  · exact solve_row7 F closed empty full minSize h7 (by intro pr h; cases h)
  by_cases h8 : HasPattern F 8
  · exact solve_row8 F closed empty full minSize h8 (by intro pr h; simp [r8_prev] at h; subst h; exact h7)
  by_cases h12 : HasPattern F 12
  · exact solve_row12 F closed empty full minSize h12 (by intro pr h; simp [r12_prev] at h; rcases h with rfl | rfl; exact h7; exact h8)
  by_cases h16 : HasPattern F 16
  · exact solve_row16 F closed empty full minSize h16 (by intro pr h; simp [r16_prev] at h; rcases h with rfl | rfl | rfl; exact h7; exact h8; exact h12)
  by_cases h26 : HasPattern F 26
  · exact solve_row26 F closed empty full minSize h26 (by intro pr h; simp [r26_prev] at h; rcases h with rfl | rfl | rfl | rfl; exact h7; exact h8; exact h12; exact h16)
  by_cases h27 : HasPattern F 27
  · exact solve_row27 F closed empty full minSize h27 (by intro pr h; simp [r27_prev] at h; rcases h with rfl | rfl | rfl | rfl | rfl; exact h7; exact h8; exact h12; exact h16; exact h26)
  by_cases h28 : HasPattern F 28
  · exact solve_row28 F closed empty full minSize h28 (by intro pr h; simp [r28_prev] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl; exact h7; exact h8; exact h12; exact h16; exact h26; exact h27)
  by_cases h29 : HasPattern F 29
  · exact solve_row29 F closed empty full minSize h29 (by intro pr h; simp [r29_prev] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl; exact h7; exact h8; exact h12; exact h16; exact h26; exact h27; exact h28)
  by_cases h30 : HasPattern F 30
  · exact solve_row30 F closed empty full minSize h30 (by intro pr h; simp [r30_prev] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl; exact h7; exact h8; exact h12; exact h16; exact h26; exact h27; exact h28; exact h29)
  by_cases h31 : HasPattern F 31
  · exact solve_row31 F closed empty full minSize h31 (by intro pr h; simp [r31_prev] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl; exact h7; exact h8; exact h12; exact h16; exact h26; exact h27; exact h28; exact h29; exact h30)
  exact solve_row32 F closed empty full minSize (hasPattern_32_of_exists_four hex4) (by intro pr h; simp [r32_prev] at h; rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl; exact h7; exact h8; exact h12; exact h16; exact h26; exact h27; exact h28; exact h29; exact h30; exact h31)

end H2Proof

theorem OMA.solution : OMA.R_UnionClosed_union_closed_variants_univ_card_R1.H2 :=
  H2Proof.solve_H2
