import OMAReductions.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1
import Mathlib

/-!
# Proof of Green100.green_100.parts.ii.R1.H2.R1.H2.R1.H2.R1.H1

Finite presentation on 74 generators (amalgamated double of the 48-generator Kazhdan compressor
group plus central involution `J` and stable letter `z`) and its Laurent matrix representation
over `𝔽₅[x₀±¹, x₁±¹, x₂±¹]`, following Gao, Yu, and Zhi (arXiv:2610.10248v2, Sections 3–4).

Credit: @zzzfu411
-/

namespace OMA.Green100H1

open Finset
open scoped commutatorElement

/- ### 1. Generator indexing and word helpers -/

private def rootIdx (i j : Fin 3) : ℕ :=
  if i = 0 then (if j = 1 then 0 else 1)
  else if i = 1 then (if j = 0 then 2 else 3)
  else (if j = 0 then 4 else 5)

private lemma rootIdx_lt (i j : Fin 3) : rootIdx i j < 6 := by
  unfold rootIdx; split_ifs <;> omega

private def xIdxQ (i j : Fin 3) (m : Fin 7) : Fin 48 :=
  if hm : m.val < 4 then
    ⟨4 * rootIdx i j + m.val, by have := rootIdx_lt i j; omega⟩
  else
    ⟨24 + 3 * rootIdx i j + (m.val - 4), by have := rootIdx_lt i j; omega⟩

private def cIdxQ (a b : Fin 3) : Fin 48 :=
  ⟨42 + rootIdx a b, by have := rootIdx_lt a b; omega⟩

private def emb1 (k : Fin 48) : Fin 74 := ⟨k.val, by omega⟩

private def emb2 (k : Fin 48) : Fin 74 :=
  if h : k.val < 24 then ⟨k.val, by omega⟩ else ⟨k.val + 24, by omega⟩

private lemma emb1_eq_emb2_of_lt {k : Fin 48} (hk : k.val < 24) : emb1 k = emb2 k := by
  simp [emb1, emb2, hk]

private lemma xIdxQ_val_lt_24 (i j : Fin 3) {m : Fin 7} (hm : m.val < 4) :
    (xIdxQ i j m).val < 24 := by
  simp only [xIdxQ, hm, ↓reduceDIte]
  have := rootIdx_lt i j
  omega

private def posLabel (c : Fin 3) : Fin 7 := ⟨c.val + 1, by omega⟩
private def negLabel (c : Fin 3) : Fin 7 := ⟨c.val + 4, by omega⟩
private def signLabel (s : Bool) (c : Fin 3) : Fin 7 := if s then posLabel c else negLabel c

private def thirdIdx (i j : Fin 3) : Fin 3 :=
  if i ≠ 0 ∧ j ≠ 0 then 0 else if i ≠ 1 ∧ j ≠ 1 then 1 else 2

private lemma thirdIdx_ne_left {i j : Fin 3} (h : i ≠ j) : thirdIdx i j ≠ i := by
  fin_cases i <;> fin_cases j <;> simp_all [thirdIdx]

private lemma thirdIdx_ne_right {i j : Fin 3} (h : i ≠ j) : thirdIdx i j ≠ j := by
  fin_cases i <;> fin_cases j <;> simp_all [thirdIdx]

private def nextIdx (c : Fin 3) : Fin 3 := ⟨(c.val + 1) % 3, by omega⟩

private lemma nextIdx_ne (c : Fin 3) : nextIdx c ≠ c := by
  fin_cases c <;> decide

private def wGen {α : Type*} (a : α) : List (α × Bool) := [(a, true)]

private def wInv {α : Type*} (w : List (α × Bool)) : List (α × Bool) :=
  (w.map fun p => (p.1, !p.2)).reverse

private def wPow {α : Type*} (w : List (α × Bool)) : ℕ → List (α × Bool)
  | 0 => []
  | n + 1 => w ++ wPow w n

private def wComm {α : Type*} (u v : List (α × Bool)) : List (α × Bool) :=
  u ++ v ++ wInv u ++ wInv v

private def wConj {α : Type*} (g u : List (α × Bool)) : List (α × Bool) :=
  g ++ u ++ wInv g

private def wRel {α : Type*} (u v : List (α × Bool)) : List (α × Bool) :=
  u ++ wInv v

private def mapWord {α β : Type*} (f : α → β) (w : List (α × Bool)) : List (β × Bool) :=
  w.map fun p => (f p.1, p.2)

private lemma mk_append {α : Type*} (u v : List (α × Bool)) :
    FreeGroup.mk (u ++ v) = FreeGroup.mk u * FreeGroup.mk v := rfl

private lemma mk_inv {α : Type*} (w : List (α × Bool)) :
    FreeGroup.mk (wInv w) = (FreeGroup.mk w)⁻¹ := rfl

private lemma lift_mk_gen {α G : Type*} [Group G] (φ : α → G) (a : α) :
    FreeGroup.lift φ (FreeGroup.mk (wGen a)) = φ a := by
  change FreeGroup.lift φ (FreeGroup.of a) = φ a
  exact FreeGroup.lift_apply_of

private lemma lift_mk_append {α G : Type*} [Group G] (φ : α → G) (u v : List (α × Bool)) :
    FreeGroup.lift φ (FreeGroup.mk (u ++ v)) =
      FreeGroup.lift φ (FreeGroup.mk u) * FreeGroup.lift φ (FreeGroup.mk v) := by
  rw [mk_append, map_mul]

private lemma lift_mk_inv {α G : Type*} [Group G] (φ : α → G) (w : List (α × Bool)) :
    FreeGroup.lift φ (FreeGroup.mk (wInv w)) = (FreeGroup.lift φ (FreeGroup.mk w))⁻¹ := by
  rw [mk_inv, map_inv]

private lemma lift_mk_pow {α G : Type*} [Group G] (φ : α → G) (w : List (α × Bool)) (n : ℕ) :
    FreeGroup.lift φ (FreeGroup.mk (wPow w n)) = (FreeGroup.lift φ (FreeGroup.mk w)) ^ n := by
  induction n with
  | zero => simp [wPow]
  | succ n ih => rw [wPow, lift_mk_append, ih, pow_succ']

private lemma lift_mk_comm {α G : Type*} [Group G] (φ : α → G) (u v : List (α × Bool)) :
    FreeGroup.lift φ (FreeGroup.mk (wComm u v)) =
      ⁅FreeGroup.lift φ (FreeGroup.mk u), FreeGroup.lift φ (FreeGroup.mk v)⁆ := by
  simp only [wComm, lift_mk_append, lift_mk_inv, commutatorElement_def, mul_assoc]

private lemma lift_mk_conj {α G : Type*} [Group G] (φ : α → G) (g u : List (α × Bool)) :
    FreeGroup.lift φ (FreeGroup.mk (wConj g u)) =
      FreeGroup.lift φ (FreeGroup.mk g) * FreeGroup.lift φ (FreeGroup.mk u) *
        (FreeGroup.lift φ (FreeGroup.mk g))⁻¹ := by
  simp only [wConj, lift_mk_append, lift_mk_inv]

private lemma lift_mk_rel {α G : Type*} [Group G] (φ : α → G) (u v : List (α × Bool)) :
    FreeGroup.lift φ (FreeGroup.mk (wRel u v)) =
      FreeGroup.lift φ (FreeGroup.mk u) * (FreeGroup.lift φ (FreeGroup.mk v))⁻¹ := by
  simp only [wRel, lift_mk_append, lift_mk_inv]

private lemma lift_mk_mapWord {α β G : Type*} [Group G] (φ : β → G) (f : α → β)
    (w : List (α × Bool)) :
    FreeGroup.lift φ (FreeGroup.mk (mapWord f w)) = FreeGroup.lift (φ ∘ f) (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons p ws ih =>
    rcases p with ⟨a, b⟩
    have h1 : mapWord f ((a, b) :: ws) = [(f a, b)] ++ mapWord f ws := rfl
    have h2 : (a, b) :: ws = [(a, b)] ++ ws := rfl
    rw [h1, lift_mk_append, ih, h2, lift_mk_append]
    congr 1

private lemma presented_mk_eq_lift {α : Type*} {S : Set (FreeGroup α)} (z : FreeGroup α) :
    PresentedGroup.mk S z = FreeGroup.lift (PresentedGroup.of (rels := S)) z := by
  have h : PresentedGroup.mk S = FreeGroup.lift (PresentedGroup.of (rels := S)) := by
    apply FreeGroup.lift.symm.injective
    ext a
    rfl
  exact congrArg (fun f => f z) h

private lemma mapWord_append {α β : Type*} (f : α → β) (u v : List (α × Bool)) :
    mapWord f (u ++ v) = mapWord f u ++ mapWord f v :=
  List.map_append

private lemma mapWord_wInv {α β : Type*} (f : α → β) (w : List (α × Bool)) :
    mapWord f (wInv w) = wInv (mapWord f w) := by
  simp only [mapWord, wInv, List.map_reverse, List.map_map]
  rfl

private lemma mapWord_wGen {α β : Type*} (f : α → β) (a : α) :
    mapWord f (wGen a) = wGen (f a) := rfl

private lemma mapWord_wRel {α β : Type*} (f : α → β) (u v : List (α × Bool)) :
    mapWord f (wRel u v) = wRel (mapWord f u) (mapWord f v) := by
  rw [wRel, wRel, mapWord_append, mapWord_wInv]

private lemma mapWord_wConj {α β : Type*} (f : α → β) (g u : List (α × Bool)) :
    mapWord f (wConj g u) = wConj (mapWord f g) (mapWord f u) := by
  rw [wConj, wConj, mapWord_append, mapWord_append, mapWord_wInv]

private lemma mapWord_wComm {α β : Type*} (f : α → β) (u v : List (α × Bool)) :
    mapWord f (wComm u v) = wComm (mapWord f u) (mapWord f v) := by
  rw [wComm, wComm, mapWord_append, mapWord_append, mapWord_append, mapWord_wInv, mapWord_wInv]

private lemma mapWord_wPow {α β : Type*} (f : α → β) (w : List (α × Bool)) (n : ℕ) :
    mapWord f (wPow w n) = wPow (mapWord f w) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [wPow, wPow, mapWord_append, ih]

/- ### 2. The finite set of relators R_Q and R_all -/

noncomputable section

private def wX (i j : Fin 3) (m : Fin 7) : List (Fin 48 × Bool) := wGen (xIdxQ i j m)
private def wC (a b : Fin 3) : List (Fin 48 × Bool) := wGen (cIdxQ a b)

private def wRC (c : Fin 3) : List (Fin 48 × Bool) :=
  wPow (wC c (nextIdx c) ++ wInv (wC (nextIdx c) c) ++ wC c (nextIdx c)) 2

private inductive IsRelQ : List (Fin 48 × Bool) → Prop
  | pow {i j : Fin 3} (hij : i ≠ j) (m : Fin 7) :
      IsRelQ (wPow (wX i j m) 5)
  | xcomm {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l) (hil : i ≠ l) (hjk : j ≠ k)
      (m n : Fin 7) :
      IsRelQ (wComm (wX i j m) (wX k l n))
  | ccomm {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l) (hil : i ≠ l) (hjk : j ≠ k) :
      IsRelQ (wComm (wC i j) (wC k l))
  | xstep1 {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (m : Fin 7) :
      IsRelQ (wRel (wComm (wX i j m) (wX j k 0)) (wX i k m))
  | xstep2 {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (m : Fin 7) :
      IsRelQ (wRel (wComm (wX i j 0) (wX j k m)) (wX i k m))
  | cstep {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
      IsRelQ (wRel (wComm (wC i j) (wC j k)) (wC i k))
  | xtriple {i j k a b : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (hab : a ≠ b)
      (hib : i ≠ b) (hka : k ≠ a) (m n l : Fin 7) :
      IsRelQ (wComm (wComm (wX i j m) (wX j k n)) (wX a b l))
  | ctorsion :
      IsRelQ (wPow (wC 0 1 ++ wInv (wC 1 0) ++ wC 0 1) 4)
  | act_zero {a b i j : Fin 3} (hab : a ≠ b) (hij : i ≠ j) (eps : Bool) :
      IsRelQ (wRel (wConj (if eps then wC a b else wInv (wC a b)) (wX i j 0)) (wX i j 0))
  | act_fix {a b i j c' : Fin 3} (hab : a ≠ b) (hij : i ≠ j) (hc' : c' ≠ b) (eps sig : Bool) :
      IsRelQ (wRel (wConj (if eps then wC a b else wInv (wC a b)) (wX i j (signLabel sig c')))
        (wX i j (signLabel sig c')))
  | act_mix {a b i j : Fin 3} (hab : a ≠ b) (hij : i ≠ j) (eps sig : Bool) :
      IsRelQ (wRel (wConj (if eps then wC a b else wInv (wC a b)) (wX i j (signLabel sig b)))
        (wComm (wX i (thirdIdx i j) (signLabel sig b))
          (wX (thirdIdx i j) j (signLabel (eps == sig) a))))
  | neg_rec {i j : Fin 3} (hij : i ≠ j) (c' : Fin 3) :
      IsRelQ (wRel (wConj (wRC c') (wX i j (posLabel c'))) (wX i j (negLabel c')))

private lemma isRelQ_finite : {w : List (Fin 48 × Bool) | IsRelQ w}.Finite := by
  let S1 : Set (List (Fin 48 × Bool)) :=
    Set.range fun p : Fin 3 × Fin 3 × Fin 7 => wPow (wX p.1 p.2.1 p.2.2) 5
  let S2 : Set (List (Fin 48 × Bool)) :=
    Set.range fun p : Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 7 × Fin 7 =>
      wComm (wX p.1 p.2.1 p.2.2.2.2.1) (wX p.2.2.1 p.2.2.2.1 p.2.2.2.2.2)
  let S3 : Set (List (Fin 48 × Bool)) :=
    Set.range fun p : Fin 3 × Fin 3 × Fin 3 × Fin 3 =>
      wComm (wC p.1 p.2.1) (wC p.2.2.1 p.2.2.2)
  let S4 : Set (List (Fin 48 × Bool)) :=
    Set.range fun p : Fin 3 × Fin 3 × Fin 3 × Fin 7 =>
      wRel (wComm (wX p.1 p.2.1 p.2.2.2) (wX p.2.1 p.2.2.1 0)) (wX p.1 p.2.2.1 p.2.2.2)
  let S5 : Set (List (Fin 48 × Bool)) :=
    Set.range fun p : Fin 3 × Fin 3 × Fin 3 × Fin 7 =>
      wRel (wComm (wX p.1 p.2.1 0) (wX p.2.1 p.2.2.1 p.2.2.2)) (wX p.1 p.2.2.1 p.2.2.2)
  let S6 : Set (List (Fin 48 × Bool)) :=
    Set.range fun p : Fin 3 × Fin 3 × Fin 3 =>
      wRel (wComm (wC p.1 p.2.1) (wC p.2.1 p.2.2)) (wC p.1 p.2.2)
  let S7 : Set (List (Fin 48 × Bool)) :=
    Set.range fun p : Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 7 × Fin 7 × Fin 7 =>
      wComm (wComm (wX p.1 p.2.1 p.2.2.2.2.2.1) (wX p.2.1 p.2.2.1 p.2.2.2.2.2.2.1))
        (wX p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.2.2)
  let S8 : Set (List (Fin 48 × Bool)) :=
    {wPow (wC 0 1 ++ wInv (wC 1 0) ++ wC 0 1) 4}
  let S9 : Set (List (Fin 48 × Bool)) :=
    Set.range fun p : Fin 3 × Fin 3 × Fin 3 × Fin 3 × Bool =>
      wRel (wConj (if p.2.2.2.2 then wC p.1 p.2.1 else wInv (wC p.1 p.2.1))
        (wX p.2.2.1 p.2.2.2.1 0)) (wX p.2.2.1 p.2.2.2.1 0)
  let S10 : Set (List (Fin 48 × Bool)) :=
    Set.range fun p : Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3 × Bool × Bool =>
      wRel (wConj (if p.2.2.2.2.2.1 then wC p.1 p.2.1 else wInv (wC p.1 p.2.1))
        (wX p.2.2.1 p.2.2.2.1 (signLabel p.2.2.2.2.2.2 p.2.2.2.2.1)))
        (wX p.2.2.1 p.2.2.2.1 (signLabel p.2.2.2.2.2.2 p.2.2.2.2.1))
  let S11 : Set (List (Fin 48 × Bool)) :=
    Set.range fun p : Fin 3 × Fin 3 × Fin 3 × Fin 3 × Bool × Bool =>
      wRel (wConj (if p.2.2.2.2.1 then wC p.1 p.2.1 else wInv (wC p.1 p.2.1))
        (wX p.2.2.1 p.2.2.2.1 (signLabel p.2.2.2.2.2 p.2.1)))
        (wComm (wX p.2.2.1 (thirdIdx p.2.2.1 p.2.2.2.1) (signLabel p.2.2.2.2.2 p.2.1))
          (wX (thirdIdx p.2.2.1 p.2.2.2.1) p.2.2.2.1
            (signLabel (p.2.2.2.2.1 == p.2.2.2.2.2) p.1)))
  let S12 : Set (List (Fin 48 × Bool)) :=
    Set.range fun p : Fin 3 × Fin 3 × Fin 3 =>
      wRel (wConj (wRC p.2.2) (wX p.1 p.2.1 (posLabel p.2.2))) (wX p.1 p.2.1 (negLabel p.2.2))
  have hfin : (S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ S7 ∪ S8 ∪ S9 ∪ S10 ∪ S11 ∪ S12).Finite :=
    (((((((((((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union
      (Set.finite_range _)).union (Set.finite_range _)).union (Set.finite_range _)).union
      (Set.finite_range _)).union (Set.finite_singleton _)).union (Set.finite_range _)).union
      (Set.finite_range _)).union (Set.finite_range _)).union (Set.finite_range _)
  refine hfin.subset fun w hw => ?_
  cases hw with
  | @pow i j _ m =>
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inl ⟨(i, j, m), rfl⟩))))))))))
  | @xcomm i j k l _ _ _ _ m n =>
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr ⟨(i, j, k, l, m, n), rfl⟩))))))))))
  | @ccomm i j k l _ _ _ _ =>
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr ⟨(i, j, k, l), rfl⟩)))))))))
  | @xstep1 i j k _ _ _ m =>
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr ⟨(i, j, k, m), rfl⟩))))))))
  | @xstep2 i j k _ _ _ m =>
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr ⟨(i, j, k, m), rfl⟩)))))))
  | @cstep i j k _ _ _ =>
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr ⟨(i, j, k), rfl⟩))))))
  | @xtriple i j k a b _ _ _ _ _ _ m n l =>
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
      (Or.inr ⟨(i, j, k, a, b, m, n, l), rfl⟩)))))
  | ctorsion =>
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl))))
  | @act_zero a b i j _ _ eps =>
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(a, b, i, j, eps), rfl⟩)))
  | @act_fix a b i j c' _ _ _ eps sig =>
    exact Or.inl (Or.inl (Or.inr ⟨(a, b, i, j, c', eps, sig), rfl⟩))
  | @act_mix a b i j _ _ eps sig =>
    exact Or.inl (Or.inr ⟨(a, b, i, j, eps, sig), rfl⟩)
  | @neg_rec i j _ c' =>
    exact Or.inr ⟨(i, j, c'), rfl⟩

private def wJ : List (Fin 74 × Bool) := wGen (72 : Fin 74)
private def wZ : List (Fin 74 × Bool) := wGen (73 : Fin 74)
private def wH : List (Fin 74 × Bool) := mapWord emb1 (wX 0 1 2)
private def wT1 : List (Fin 74 × Bool) := mapWord emb1 (wC 0 1)
private def wT2 : List (Fin 74 × Bool) := mapWord emb2 (wC 0 1)
private def wW : List (Fin 74 × Bool) := wComm wH (wT2 ++ wInv wT1)

private def R_Jz_set : Set (List (Fin 74 × Bool)) :=
  {wPow wJ 2, wRel (wConj wZ wW) (wW ++ wJ)} ∪
    Set.range fun g : Fin 74 => wComm wJ (wGen g)

private lemma R_Jz_set_finite : R_Jz_set.Finite :=
  ((Set.finite_singleton _).insert _).union (Set.finite_range _)

private def R_all_set : Set (List (Fin 74 × Bool)) :=
  (mapWord emb1 '' {w | IsRelQ w}) ∪ (mapWord emb2 '' {w | IsRelQ w}) ∪ R_Jz_set

private lemma R_all_set_finite : R_all_set.Finite :=
  ((isRelQ_finite.image _).union (isRelQ_finite.image _)).union R_Jz_set_finite

private def R_all : Finset (List (Fin 74 × Bool)) := R_all_set_finite.toFinset

private lemma mem_R_all_iff {w : List (Fin 74 × Bool)} : w ∈ R_all ↔ w ∈ R_all_set :=
  R_all_set_finite.mem_toFinset

/- ### 3. The Laurent matrix semidirect product K -/

private abbrev LR := AddMonoidAlgebra (ZMod 5) (Fin 3 → ℤ)
private abbrev GL3LR := (Matrix (Fin 3) (Fin 3) LR)ˣ
private abbrev GL3Z := (Matrix (Fin 3) (Fin 3) ℤ)ˣ

private lemma single_mul_single {R : Type*} [CommRing R] (i j k l : Fin 3) (a b : R) :
    Matrix.single i j a * Matrix.single k l b =
      if j = k then Matrix.single i l (a * b) else 0 := by
  ext r s
  simp only [Matrix.mul_apply, Matrix.single_apply]
  split_ifs with hjk
  · subst hjk
    rw [Finset.sum_eq_single j]
    · split_ifs <;> simp_all
    · intro m _ hm; simp [hm.symm]
    · intro h; exact absurd (Finset.mem_univ j) h
  · apply Finset.sum_eq_zero
    intro m _
    by_cases hjm : j = m
    · subst hjm; simp [Ne.symm hjk]
    · simp [hjm]

private def elemMat {R : Type*} [CommRing R] (i j : Fin 3) (hij : i ≠ j) (f : R) :
    (Matrix (Fin 3) (Fin 3) R)ˣ where
  val := 1 + Matrix.single i j f
  inv := 1 - Matrix.single i j f
  val_inv := by
    simp only [add_mul, mul_sub, one_mul, mul_one, single_mul_single, if_neg hij.symm]
    abel
  inv_val := by
    simp only [sub_mul, mul_add, one_mul, mul_one, single_mul_single, if_neg hij.symm]
    abel

private lemma elemMat_mul_same {R : Type*} [CommRing R] (i j : Fin 3) (hij : i ≠ j) (f g : R) :
    elemMat i j hij f * elemMat i j hij g = elemMat i j hij (f + g) := by
  apply Units.ext
  change (1 + Matrix.single i j f) * (1 + Matrix.single i j g) = 1 + Matrix.single i j (f + g)
  simp only [add_mul, mul_add, one_mul, mul_one, single_mul_single, if_neg hij.symm,
    Matrix.single_add]
  abel

private lemma elemMat_zero {R : Type*} [CommRing R] (i j : Fin 3) (hij : i ≠ j) :
    elemMat i j hij (0 : R) = 1 := by
  apply Units.ext
  change 1 + Matrix.single i j (0 : R) = 1
  simp

private lemma elemMat_pow {R : Type*} [CommRing R] (i j : Fin 3) (hij : i ≠ j) (f : R) (n : ℕ) :
    (elemMat i j hij f) ^ n = elemMat i j hij (n • f) := by
  induction n with
  | zero => simp [elemMat_zero]
  | succ n ih =>
    rw [pow_succ, ih, elemMat_mul_same, succ_nsmul]

private lemma elemMat_inv {R : Type*} [CommRing R] (i j : Fin 3) (hij : i ≠ j) (f : R) :
    (elemMat i j hij f)⁻¹ = elemMat i j hij (-f) := by
  apply Units.ext
  change 1 - Matrix.single i j f = 1 + Matrix.single i j (-f)
  rw [← Matrix.single_neg, sub_eq_add_neg]

private lemma elemMat_comm_disjoint {R : Type*} [CommRing R]
    {i j k l : Fin 3} (hij : i ≠ j) (hkl : k ≠ l) (hil : i ≠ l) (hjk : j ≠ k) (f g : R) :
    ⁅elemMat i j hij f, elemMat k l hkl g⁆ = 1 := by
  rw [commutatorElement_eq_one_iff_mul_comm]
  apply Units.ext
  change (1 + Matrix.single i j f) * (1 + Matrix.single k l g) =
    (1 + Matrix.single k l g) * (1 + Matrix.single i j f)
  simp only [add_mul, mul_add, one_mul, mul_one, single_mul_single,
    if_neg hjk, if_neg hil.symm]
  abel

private lemma elemMat_comm_step {R : Type*} [CommRing R]
    {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (f g : R) :
    ⁅elemMat i j hij f, elemMat j k hjk g⁆ = elemMat i k hik (f * g) := by
  rw [commutatorElement_def, elemMat_inv, elemMat_inv]
  apply Units.ext
  change (1 + Matrix.single i j f) * (1 + Matrix.single j k g) *
      (1 + Matrix.single i j (-f)) * (1 + Matrix.single j k (-g)) =
    1 + Matrix.single i k (f * g)
  have h1 : (1 + Matrix.single i j f) * (1 + Matrix.single j k g) =
      1 + Matrix.single i j f + Matrix.single j k g + Matrix.single i k (f * g) := by
    simp only [add_mul, mul_add, one_mul, mul_one, single_mul_single, ↓reduceIte]
    abel
  have h2 : (1 + Matrix.single i j (-f)) * (1 + Matrix.single j k (-g)) =
      1 - Matrix.single i j f - Matrix.single j k g + Matrix.single i k (f * g) := by
    simp only [add_mul, mul_add, one_mul, mul_one, single_mul_single, ↓reduceIte, neg_mul_neg,
      ← Matrix.single_neg]
    abel
  rw [mul_assoc _ (1 + Matrix.single i j (-f)), h1, h2]
  simp only [add_mul, mul_add, mul_sub, one_mul, mul_one, single_mul_single,
    if_neg hij.symm, if_neg hjk.symm, if_neg hik.symm, ↓reduceIte]
  abel

private def vecEquiv (A : GL3Z) : (Fin 3 → ℤ) ≃+ (Fin 3 → ℤ) where
  toFun v := A.val.mulVec v
  invFun v := A.inv.mulVec v
  left_inv v := by dsimp only; rw [Matrix.mulVec_mulVec, A.inv_val, Matrix.one_mulVec]
  right_inv v := by dsimp only; rw [Matrix.mulVec_mulVec, A.val_inv, Matrix.one_mulVec]
  map_add' u v := Matrix.mulVec_add _ u v

private def lrEquiv (A : GL3Z) : LR ≃+* LR :=
  (AddMonoidAlgebra.domCongr (ZMod 5) (ZMod 5) (vecEquiv A)).toRingEquiv

private lemma lrEquiv_single (A : GL3Z) (v : Fin 3 → ℤ) (c : ZMod 5) :
    lrEquiv A (AddMonoidAlgebra.single v c) = AddMonoidAlgebra.single (A.val.mulVec v) c := by
  change AddMonoidAlgebra.domCongr (ZMod 5) (ZMod 5) (vecEquiv A)
      (AddMonoidAlgebra.single v c) = _
  simp [vecEquiv]

private lemma lrEquiv_one (x : LR) : lrEquiv 1 x = x := by
  induction x using AddMonoidAlgebra.induction with
  | zero => exact map_zero _
  | single_add a b f _ _ ih =>
    rw [map_add, lrEquiv_single, ih]
    simp

private lemma lrEquiv_mul (A B : GL3Z) (x : LR) :
    lrEquiv (A * B) x = lrEquiv A (lrEquiv B x) := by
  induction x using AddMonoidAlgebra.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [map_add, map_add, map_add, lrEquiv_single, lrEquiv_single, lrEquiv_single, ih]
    simp [Matrix.mulVec_mulVec]

private def glEquiv (A : GL3Z) : GL3LR ≃* GL3LR :=
  Units.mapEquiv (RingEquiv.mapMatrix (lrEquiv A)).toMulEquiv

private lemma glEquiv_elemMat (A : GL3Z) (i j : Fin 3) (hij : i ≠ j) (f : LR) :
    glEquiv A (elemMat i j hij f) = elemMat i j hij (lrEquiv A f) := by
  apply Units.ext
  change (1 + Matrix.single i j f).map (lrEquiv A) = 1 + Matrix.single i j (lrEquiv A f)
  rw [Matrix.map_add (lrEquiv A) (map_add _),
    Matrix.map_one (lrEquiv A) (map_zero _) (map_one _), Matrix.map_single]

private def phiK : GL3Z →* MulAut GL3LR where
  toFun A := glEquiv A
  map_one' := by
    refine MulEquiv.ext fun g => Units.ext <| Matrix.ext fun r s => ?_
    exact lrEquiv_one (g.val r s)
  map_mul' A B := by
    refine MulEquiv.ext fun g => Units.ext <| Matrix.ext fun r s => ?_
    exact lrEquiv_mul A B (g.val r s)

private abbrev K := GL3LR ⋊[phiK] GL3Z

private lemma inr_conj_inl (A : GL3Z) (g : GL3LR) :
    (SemidirectProduct.inr A : K) * SemidirectProduct.inl g * (SemidirectProduct.inr A)⁻¹ =
      SemidirectProduct.inl (glEquiv A g) := by
  rw [← map_inv]
  apply SemidirectProduct.ext
  · change (1 * phiK A g) * phiK (A * 1) 1 = glEquiv A g
    simp [phiK]
  · simp [SemidirectProduct.mul_right]

private def labelVec : Fin 7 → (Fin 3 → ℤ)
  | 0 => 0
  | 1 => Pi.single 0 1
  | 2 => Pi.single 1 1
  | 3 => Pi.single 2 1
  | 4 => Pi.single 0 (-1)
  | 5 => Pi.single 1 (-1)
  | 6 => Pi.single 2 (-1)

private def labelMon (m : Fin 7) : LR :=
  AddMonoidAlgebra.single (labelVec m) (1 : ZMod 5)

private lemma labelMon_zero : labelMon 0 = 1 := rfl

private def xK (i j : Fin 3) (m : Fin 7) : K :=
  if h : i ≠ j then SemidirectProduct.inl (elemMat i j h (labelMon m)) else 1

private def cK (a b : Fin 3) : K :=
  if h : a ≠ b then SemidirectProduct.inr (elemMat a b h (1 : ℤ)) else 1

private def decodeK (k : Fin 48) : K :=
  let v := k.val
  if v < 24 then
    let r := v / 4
    let m : Fin 7 := ⟨v % 4, by omega⟩
    match r with
    | 0 => xK 0 1 m
    | 1 => xK 0 2 m
    | 2 => xK 1 0 m
    | 3 => xK 1 2 m
    | 4 => xK 2 0 m
    | _ => xK 2 1 m
  else if v < 42 then
    let r := (v - 24) / 3
    let m : Fin 7 := ⟨4 + (v - 24) % 3, by omega⟩
    match r with
    | 0 => xK 0 1 m
    | 1 => xK 0 2 m
    | 2 => xK 1 0 m
    | 3 => xK 1 2 m
    | 4 => xK 2 0 m
    | _ => xK 2 1 m
  else
    let r := v - 42
    match r with
    | 0 => cK 0 1
    | 1 => cK 0 2
    | 2 => cK 1 0
    | 3 => cK 1 2
    | 4 => cK 2 0
    | _ => cK 2 1

private lemma decodeK_xIdxQ {i j : Fin 3} (hij : i ≠ j) (m : Fin 7) :
    decodeK (xIdxQ i j m) = xK i j m := by
  fin_cases i <;> fin_cases j <;> fin_cases m <;>
    simp_all [decodeK, xIdxQ, rootIdx]

private lemma decodeK_cIdxQ {a b : Fin 3} (hab : a ≠ b) :
    decodeK (cIdxQ a b) = cK a b := by
  fin_cases a <;> fin_cases b <;>
    simp_all [decodeK, cIdxQ, rootIdx]

private lemma lift_decodeK_wX {i j : Fin 3} (hij : i ≠ j) (m : Fin 7) :
    FreeGroup.lift decodeK (FreeGroup.mk (wX i j m)) = xK i j m := by
  rw [wX, lift_mk_gen, decodeK_xIdxQ hij]

private lemma lift_decodeK_wC {a b : Fin 3} (hab : a ≠ b) :
    FreeGroup.lift decodeK (FreeGroup.mk (wC a b)) = cK a b := by
  rw [wC, lift_mk_gen, decodeK_cIdxQ hab]

private lemma lift_decodeK_shear {a b : Fin 3} (hab : a ≠ b) (eps : Bool) :
    FreeGroup.lift decodeK (FreeGroup.mk (if eps then wC a b else wInv (wC a b))) =
      SemidirectProduct.inr (if eps then elemMat a b hab (1 : ℤ) else (elemMat a b hab (1 : ℤ))⁻¹) := by
  cases eps
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
      lift_mk_inv, lift_decodeK_wC hab, cK, dif_pos hab, map_inv]
  · rw [if_pos rfl, if_pos rfl, lift_decodeK_wC hab, cK, dif_pos hab]

/- ### 4. Verification of all R_Q relators in K -/

private lemma shear_mulVec_zero (a b : Fin 3) (hab : a ≠ b) (eps : Bool) :
    ((if eps then elemMat a b hab (1 : ℤ) else (elemMat a b hab (1 : ℤ))⁻¹).val).mulVec
      (labelVec 0) = labelVec 0 := by
  simp [labelVec]

private lemma shear_mulVec_fix {a b c' : Fin 3} (hab : a ≠ b) (hc : c' ≠ b) (eps sig : Bool) :
    ((if eps then elemMat a b hab (1 : ℤ) else (elemMat a b hab (1 : ℤ))⁻¹).val).mulVec
      (labelVec (signLabel sig c')) = labelVec (signLabel sig c') := by
  fin_cases a <;> fin_cases b <;> fin_cases c' <;> cases eps <;> cases sig <;>
    simp_all [elemMat, signLabel, posLabel, negLabel, labelVec] <;>
    (ext r; fin_cases r <;> decide)

private lemma shear_mulVec_mix {a b : Fin 3} (hab : a ≠ b) (eps sig : Bool) :
    ((if eps then elemMat a b hab (1 : ℤ) else (elemMat a b hab (1 : ℤ))⁻¹).val).mulVec
      (labelVec (signLabel sig b)) =
      labelVec (signLabel sig b) + labelVec (signLabel (eps == sig) a) := by
  fin_cases a <;> fin_cases b <;> cases eps <;> cases sig <;>
    simp_all [elemMat, signLabel, posLabel, negLabel, labelVec] <;>
    (ext r; fin_cases r <;> decide)

private lemma rc_mulVec (c' : Fin 3) :
    (((elemMat c' (nextIdx c') (nextIdx_ne c').symm (1 : ℤ) *
        (elemMat (nextIdx c') c' (nextIdx_ne c') (1 : ℤ))⁻¹ *
        elemMat c' (nextIdx c') (nextIdx_ne c').symm (1 : ℤ)) ^ 2).val).mulVec
      (labelVec (posLabel c')) = labelVec (negLabel c') := by
  fin_cases c' <;>
    (ext r; fin_cases r <;>
      simp [nextIdx, elemMat, posLabel, negLabel, labelVec, pow_two,
        Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
        Matrix.single_apply, Pi.single_apply])

private lemma ctorsion_K :
    (elemMat 0 1 (by decide : (0 : Fin 3) ≠ 1) (1 : ℤ) *
      (elemMat 1 0 (by decide : (1 : Fin 3) ≠ 0) (1 : ℤ))⁻¹ *
      elemMat 0 1 (by decide : (0 : Fin 3) ≠ 1) (1 : ℤ)) ^ 4 = 1 := by
  apply Units.ext
  ext r s
  fin_cases r <;> fin_cases s <;>
    simp [elemMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply]

private lemma decodeK_rel_one : ∀ {w}, IsRelQ w → FreeGroup.lift decodeK (FreeGroup.mk w) = 1 := by
  intro w hw
  cases hw with
  | pow hij m =>
    rw [lift_mk_pow, lift_decodeK_wX hij]
    simp only [xK, dif_pos hij, ← map_pow, elemMat_pow]
    have h5 : (5 : ℕ) • labelMon m = 0 := by
      have : (5 : ℕ) • (1 : ZMod 5) = 0 := by decide
      rw [labelMon, AddMonoidAlgebra.smul_single, this, AddMonoidAlgebra.single_zero]
    rw [h5, elemMat_zero, map_one]
  | xcomm hij hkl hil hjk m n =>
    rw [lift_mk_comm, lift_decodeK_wX hij, lift_decodeK_wX hkl]
    simp only [xK, dif_pos hij, dif_pos hkl, ← map_commutatorElement,
      elemMat_comm_disjoint hij hkl hil hjk, map_one]
  | ccomm hij hkl hil hjk =>
    rw [lift_mk_comm, lift_decodeK_wC hij, lift_decodeK_wC hkl]
    simp only [cK, dif_pos hij, dif_pos hkl, ← map_commutatorElement,
      elemMat_comm_disjoint hij hkl hil hjk, map_one]
  | xstep1 hij hjk hik m =>
    rw [lift_mk_rel, lift_mk_comm, lift_decodeK_wX hij, lift_decodeK_wX hjk, lift_decodeK_wX hik]
    simp only [xK, dif_pos hij, dif_pos hjk, dif_pos hik, ← map_commutatorElement,
      elemMat_comm_step hij hjk hik, labelMon_zero, mul_one, mul_inv_cancel]
  | xstep2 hij hjk hik m =>
    rw [lift_mk_rel, lift_mk_comm, lift_decodeK_wX hij, lift_decodeK_wX hjk, lift_decodeK_wX hik]
    simp only [xK, dif_pos hij, dif_pos hjk, dif_pos hik, ← map_commutatorElement,
      elemMat_comm_step hij hjk hik, labelMon_zero, one_mul, mul_inv_cancel]
  | cstep hij hjk hik =>
    rw [lift_mk_rel, lift_mk_comm, lift_decodeK_wC hij, lift_decodeK_wC hjk, lift_decodeK_wC hik]
    simp only [cK, dif_pos hij, dif_pos hjk, dif_pos hik, ← map_commutatorElement,
      elemMat_comm_step hij hjk hik, mul_one, mul_inv_cancel]
  | xtriple hij hjk hik hab hib hka m n l =>
    rw [lift_mk_comm, lift_mk_comm, lift_decodeK_wX hij, lift_decodeK_wX hjk, lift_decodeK_wX hab]
    simp only [xK, dif_pos hij, dif_pos hjk, dif_pos hab, ← map_commutatorElement,
      elemMat_comm_step hij hjk hik, elemMat_comm_disjoint hik hab hib hka, map_one]
  | ctorsion =>
    rw [lift_mk_pow, lift_mk_append, lift_mk_append, lift_mk_inv,
      lift_decodeK_wC (by decide), lift_decodeK_wC (by decide)]
    simp only [cK, dif_pos (by decide : (0 : Fin 3) ≠ 1), dif_pos (by decide : (1 : Fin 3) ≠ 0),
      ← map_inv, ← map_mul, ← map_pow, ctorsion_K, map_one]
  | act_zero hab hij eps =>
    rw [lift_mk_rel, lift_mk_conj, lift_decodeK_wX hij, lift_decodeK_shear hab eps]
    simp only [xK, dif_pos hij, inr_conj_inl, glEquiv_elemMat, labelMon, lrEquiv_single,
      shear_mulVec_zero, mul_inv_cancel]
  | act_fix hab hij hc eps sig =>
    rw [lift_mk_rel, lift_mk_conj, lift_decodeK_wX hij, lift_decodeK_shear hab eps]
    simp only [xK, dif_pos hij, inr_conj_inl, glEquiv_elemMat, labelMon, lrEquiv_single,
      shear_mulVec_fix hab hc eps sig, mul_inv_cancel]
  | act_mix hab hij eps sig =>
    have hik : _ ≠ thirdIdx _ _ := (thirdIdx_ne_left hij).symm
    have hkj : thirdIdx _ _ ≠ _ := thirdIdx_ne_right hij
    rw [lift_mk_rel, lift_mk_conj, lift_mk_comm, lift_decodeK_wX hij,
      lift_decodeK_wX hik, lift_decodeK_wX hkj, lift_decodeK_shear hab eps]
    simp only [xK, dif_pos hij, dif_pos hik, dif_pos hkj, inr_conj_inl, glEquiv_elemMat,
      ← map_commutatorElement, elemMat_comm_step hik hkj hij,
      labelMon, lrEquiv_single, shear_mulVec_mix hab eps sig,
      AddMonoidAlgebra.single_mul_single, one_mul, mul_inv_cancel]
  | neg_rec hij c' =>
    have h1 : c' ≠ nextIdx c' := (nextIdx_ne c').symm
    have h2 : nextIdx c' ≠ c' := nextIdx_ne c'
    rw [lift_mk_rel, lift_mk_conj, lift_decodeK_wX hij, lift_decodeK_wX hij]
    have hrc : FreeGroup.lift decodeK (FreeGroup.mk (wRC c')) =
        SemidirectProduct.inr ((elemMat c' (nextIdx c') h1 (1 : ℤ) *
          (elemMat (nextIdx c') c' h2 (1 : ℤ))⁻¹ *
          elemMat c' (nextIdx c') h1 (1 : ℤ)) ^ 2) := by
      simp only [wRC, lift_mk_pow, lift_mk_append, lift_mk_inv, lift_decodeK_wC h1,
        lift_decodeK_wC h2, cK, dif_pos h1, dif_pos h2, ← map_inv, ← map_mul, ← map_pow]
    rw [hrc]
    simp only [xK, dif_pos hij, inr_conj_inl, glEquiv_elemMat,
      labelMon, lrEquiv_single, rc_mulVec c', mul_inv_cancel]

/- ### 5. The positive subgroup H_K and strict compression -/

private def natToIntHom : Multiplicative (Fin 3 → ℕ) →* LR where
  toFun m := AddMonoidAlgebra.single (fun r => (Multiplicative.toAdd m r : ℤ)) (1 : ZMod 5)
  map_one' := rfl
  map_mul' a b := by
    change AddMonoidAlgebra.single
        (fun r => (((Multiplicative.toAdd a + Multiplicative.toAdd b) r : ℕ) : ℤ)) 1 =
      AddMonoidAlgebra.single (fun r => (Multiplicative.toAdd a r : ℤ)) 1 *
      AddMonoidAlgebra.single (fun r => (Multiplicative.toAdd b r : ℤ)) 1
    rw [AddMonoidAlgebra.single_mul_single, one_mul]
    congr 1

private def posEmbed : AddMonoidAlgebra (ZMod 5) (Fin 3 → ℕ) →+* LR :=
  (AddMonoidAlgebra.lift (ZMod 5) LR (Fin 3 → ℕ) natToIntHom).toRingHom

private lemma posEmbed_single (v : Fin 3 → ℕ) (c : ZMod 5) :
    posEmbed (AddMonoidAlgebra.single v c) =
      AddMonoidAlgebra.single (fun r => (v r : ℤ)) c := by
  change AddMonoidAlgebra.lift (ZMod 5) LR (Fin 3 → ℕ) natToIntHom (AddMonoidAlgebra.single v c) = _
  rw [AddMonoidAlgebra.lift_single]
  change c • AddMonoidAlgebra.single (fun r => (v r : ℤ)) (1 : ZMod 5) = _
  rw [AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

private def Rplus : Subring LR := posEmbed.range

private lemma labelMon_mem_Rplus {m : Fin 7} (hm : m.val < 4) : labelMon m ∈ Rplus := by
  fin_cases m
  · refine ⟨AddMonoidAlgebra.single 0 1, ?_⟩
    rw [posEmbed_single]; rfl
  · refine ⟨AddMonoidAlgebra.single (Pi.single 0 1) 1, ?_⟩
    rw [posEmbed_single]; congr 1; ext r; fin_cases r <;> decide
  · refine ⟨AddMonoidAlgebra.single (Pi.single 1 1) 1, ?_⟩
    rw [posEmbed_single]; congr 1; ext r; fin_cases r <;> decide
  · refine ⟨AddMonoidAlgebra.single (Pi.single 2 1) 1, ?_⟩
    rw [posEmbed_single]; congr 1; ext r; fin_cases r <;> decide
  · exact absurd hm (by decide)
  · exact absurd hm (by decide)
  · exact absurd hm (by decide)

private def H_K : Subgroup K where
  carrier := {k | k.right = 1 ∧ (∀ i j, k.left.val i j ∈ Rplus) ∧
    (∀ i j, k.left.inv i j ∈ Rplus)}
  one_mem' := by
    refine ⟨rfl, ?_, ?_⟩
    · intro i j
      simp only [SemidirectProduct.one_left, Units.val_one, Matrix.one_apply]
      split_ifs <;> [exact Rplus.one_mem; exact Rplus.zero_mem]
    · intro i j
      simp only [SemidirectProduct.one_left, Units.inv_eq_val_inv, inv_one, Units.val_one,
        Matrix.one_apply]
      split_ifs <;> [exact Rplus.one_mem; exact Rplus.zero_mem]
  mul_mem' := by
    rintro ⟨a, u⟩ ⟨b, v⟩ ⟨hu, ha1, ha2⟩ ⟨hv, hb1, hb2⟩
    dsimp only at hu hv ha1 ha2 hb1 hb2
    subst hu; subst hv
    refine ⟨by simp, ?_, ?_⟩
    · intro i j
      simp only [SemidirectProduct.mul_left, map_one, MulAut.one_apply, Units.val_mul,
        Matrix.mul_apply]
      exact Rplus.sum_mem fun l _ => Rplus.mul_mem (ha1 i l) (hb1 l j)
    · intro i j
      simp only [SemidirectProduct.mul_left, map_one, MulAut.one_apply, Units.inv_eq_val_inv,
        mul_inv_rev, Units.val_mul, Matrix.mul_apply]
      exact Rplus.sum_mem fun l _ => Rplus.mul_mem (hb2 i l) (ha2 l j)
  inv_mem' := by
    rintro ⟨a, u⟩ ⟨hu, ha1, ha2⟩
    dsimp only at hu ha1 ha2
    subst hu
    refine ⟨by simp, ?_, ?_⟩
    · intro i j
      simp only [SemidirectProduct.inv_left, inv_one, map_one, MulAut.one_apply]
      exact ha2 i j
    · intro i j
      simp only [SemidirectProduct.inv_left, inv_one, map_one, MulAut.one_apply,
        Units.inv_eq_val_inv, inv_inv]
      exact ha1 i j

private lemma smul_mk_one_eq_iff (k : K) :
    k • (QuotientGroup.mk 1 : K ⧸ H_K) = QuotientGroup.mk 1 ↔ k ∈ H_K := by
  change (QuotientGroup.mk (k * 1) : K ⧸ H_K) = QuotientGroup.mk 1 ↔ k ∈ H_K
  rw [mul_one, QuotientGroup.eq, mul_one, H_K.inv_mem_iff]

private lemma xK_mem_H_K (i j : Fin 3) {m : Fin 7} (hm : m.val < 4) : xK i j m ∈ H_K := by
  by_cases hij : i ≠ j
  · simp only [xK, dif_pos hij]
    refine ⟨rfl, ?_, ?_⟩
    · intro r s
      change (1 + Matrix.single i j (labelMon m)) r s ∈ Rplus
      rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
      apply Rplus.add_mem
      · split_ifs <;> [exact Rplus.one_mem; exact Rplus.zero_mem]
      · split_ifs <;> [exact labelMon_mem_Rplus hm; exact Rplus.zero_mem]
    · intro r s
      change (1 - Matrix.single i j (labelMon m)) r s ∈ Rplus
      rw [Matrix.sub_apply, Matrix.one_apply, Matrix.single_apply]
      apply Rplus.sub_mem
      · split_ifs <;> [exact Rplus.one_mem; exact Rplus.zero_mem]
      · split_ifs <;> [exact labelMon_mem_Rplus hm; exact Rplus.zero_mem]
  · simp only [xK, dif_neg hij]
    exact H_K.one_mem

private lemma decodeK_mem_H_K {k : Fin 48} (hk : k.val < 24) : decodeK k ∈ H_K := by
  have hm : (⟨k.val % 4, by omega⟩ : Fin 7).val < 4 := by dsimp; omega
  simp only [decodeK, hk, ↓reduceIte]
  split <;> exact xK_mem_H_K _ _ hm

private lemma posEmbed_coeff_neg (p : AddMonoidAlgebra (ZMod 5) (Fin 3 → ℕ))
    (v : Fin 3 → ℤ) (hv : v 0 < 0) : (posEmbed p).coeff v = 0 := by
  induction p using AddMonoidAlgebra.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [map_add, posEmbed_single]
    change (AddMonoidAlgebra.single (fun r => (a r : ℤ)) b).coeff v + (posEmbed f).coeff v = 0
    rw [ih, add_zero, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg]
    intro heq
    have h0 := congrArg (fun g => g 0) heq
    dsimp only at h0
    omega

private lemma hK_not_mem_conj : (cK 0 1)⁻¹ * xK 0 1 2 * cK 0 1 ∉ H_K := by
  intro hmem
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have hconj : (cK 0 1)⁻¹ * xK 0 1 2 * cK 0 1 =
      SemidirectProduct.inl (elemMat 0 1 h01
        (AddMonoidAlgebra.single (labelVec 2 + labelVec 4) (1 : ZMod 5))) := by
    simp only [cK, xK, dif_pos h01, ← map_inv]
    have hinv := inr_conj_inl (elemMat 0 1 h01 (1 : ℤ))⁻¹ (elemMat 0 1 h01 (labelMon 2))
    rw [← map_inv, inv_inv] at hinv
    rw [hinv, glEquiv_elemMat, labelMon, lrEquiv_single]
    have hv : ((elemMat 0 1 h01 (1 : ℤ))⁻¹).val.mulVec (labelVec 2) = labelVec 2 + labelVec 4 := by
      ext r; fin_cases r <;>
        simp [elemMat, labelVec, Matrix.mulVec, dotProduct,
          Matrix.single_apply, Pi.single_apply]
    rw [hv]
  rw [hconj] at hmem
  obtain ⟨_, hpos, _⟩ := hmem
  have h01_mem : (1 + Matrix.single (0 : Fin 3) (1 : Fin 3)
      (AddMonoidAlgebra.single (labelVec 2 + labelVec 4) (1 : ZMod 5))) 0 1 ∈ Rplus := hpos 0 1
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, if_neg h01,
    and_self, ↓reduceIte, zero_add] at h01_mem
  obtain ⟨p, hp⟩ := h01_mem
  have hv0 : (labelVec 2 + labelVec 4) 0 < 0 := by decide
  have hzero := posEmbed_coeff_neg p (labelVec 2 + labelVec 4) hv0
  rw [hp, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_pos rfl] at hzero
  exact (by decide : (1 : ZMod 5) ≠ 0) hzero

/- ### 6. PresentedGroup helpers -/

private lemma rel_eq_one {S : Set (FreeGroup (Fin 74))} {w : List (Fin 74 × Bool)}
    (hw : FreeGroup.mk w ∈ S) :
    FreeGroup.lift (PresentedGroup.of (rels := S)) (FreeGroup.mk w) = 1 := by
  rw [← presented_mk_eq_lift]
  exact PresentedGroup.one_of_mem hw

private lemma rel_eq_of_wRel {S : Set (FreeGroup (Fin 74))} {u v : List (Fin 74 × Bool)}
    (hw : FreeGroup.mk (wRel u v) ∈ S) :
    FreeGroup.lift (PresentedGroup.of (rels := S)) (FreeGroup.mk u) =
      FreeGroup.lift (PresentedGroup.of (rels := S)) (FreeGroup.mk v) := by
  have h := rel_eq_one hw
  rw [lift_mk_rel] at h
  exact eq_of_mul_inv_eq_one h

private lemma mem_S_emb1 {w : List (Fin 48 × Bool)} (hw : IsRelQ w) :
    FreeGroup.mk (mapWord emb1 w) ∈ (FreeGroup.mk '' (↑R_all : Set (List (Fin 74 × Bool)))) :=
  ⟨mapWord emb1 w, Finset.mem_coe.mpr (mem_R_all_iff.mpr (Or.inl (Or.inl ⟨w, hw, rfl⟩))), rfl⟩

private lemma mem_S_emb2 {w : List (Fin 48 × Bool)} (hw : IsRelQ w) :
    FreeGroup.mk (mapWord emb2 w) ∈ (FreeGroup.mk '' (↑R_all : Set (List (Fin 74 × Bool)))) :=
  ⟨mapWord emb2 w, Finset.mem_coe.mpr (mem_R_all_iff.mpr (Or.inl (Or.inr ⟨w, hw, rfl⟩))), rfl⟩

private lemma mem_S_Jz {w : List (Fin 74 × Bool)} (hw : w ∈ R_Jz_set) :
    FreeGroup.mk w ∈ (FreeGroup.mk '' (↑R_all : Set (List (Fin 74 × Bool)))) :=
  ⟨w, Finset.mem_coe.mpr (mem_R_all_iff.mpr (Or.inr hw)), rfl⟩

private lemma commutator_mem_subgroup {G : Type*} [Group G] (H : Subgroup G) {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

end

end OMA.Green100H1

theorem OMA.solution : OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1.H1 := by
  open OMA.Green100H1 in
  open scoped commutatorElement in
  refine ⟨R_all, K, inferInstance, K ⧸ H_K, inferInstance, (QuotientGroup.mk 1 : K ⧸ H_K),
    xK 0 1 2, cK 0 1, ?_, ?_, ?_, ?_⟩
  · -- h • p = p
    rw [smul_mk_one_eq_iff]
    exact xK_mem_H_K 0 1 (by decide)
  · -- h • (t • p) ≠ t • p
    intro heq
    apply hK_not_mem_conj
    rw [← smul_mk_one_eq_iff, mul_smul, mul_smul, heq, inv_smul_smul]
  · -- Universal property
    intro G _ a b j z hab hj hcomm hcz hzw
    let φ : Fin 74 → G := fun i =>
      if h1 : i.val < 48 then a (decodeK ⟨i.val, h1⟩)
      else if h2 : i.val < 72 then b (decodeK ⟨i.val - 24, by omega⟩)
      else if i.val = 72 then j
      else z
    have hφ1 : φ ∘ emb1 = fun k => a (decodeK k) := by
      funext k
      simp only [Function.comp_apply, φ, emb1, k.isLt, ↓reduceDIte, Fin.eta]
    have hφ2 : φ ∘ emb2 = fun k => b (decodeK k) := by
      funext k
      simp only [Function.comp_apply, emb2]
      by_cases hk : k.val < 24
      · simp only [hk, ↓reduceDIte, φ, show k.val < 48 by omega, Fin.eta]
        apply hab
        rw [smul_mk_one_eq_iff]
        exact decodeK_mem_H_K hk
      · simp only [hk, ↓reduceDIte, φ, show ¬ k.val + 24 < 48 by omega,
          show k.val + 24 < 72 by omega]
        congr 2
    have hφJ : φ 72 = j := by simp [φ]
    have hφZ : φ 73 = z := by simp [φ]
    have hrels : ∀ r ∈ (FreeGroup.mk '' (↑R_all : Set (List (Fin 74 × Bool)))),
        FreeGroup.lift φ r = 1 := by
      rintro _ ⟨w, hw, rfl⟩
      rw [Finset.mem_coe, mem_R_all_iff] at hw
      rcases hw with (⟨w₀, hw₀, rfl⟩ | ⟨w₀, hw₀, rfl⟩) | hwJz
      · rw [lift_mk_mapWord, hφ1]
        have hcomp : FreeGroup.lift (fun k => a (decodeK k)) = a.comp (FreeGroup.lift decodeK) := by
          apply FreeGroup.lift.symm.injective; ext k; simp
        rw [hcomp, MonoidHom.comp_apply, decodeK_rel_one hw₀, map_one]
      · rw [lift_mk_mapWord, hφ2]
        have hcomp : FreeGroup.lift (fun k => b (decodeK k)) = b.comp (FreeGroup.lift decodeK) := by
          apply FreeGroup.lift.symm.injective; ext k; simp
        rw [hcomp, MonoidHom.comp_apply, decodeK_rel_one hw₀, map_one]
      · rcases hwJz with (rfl | rfl) | ⟨g, rfl⟩
        · rw [lift_mk_pow, wJ, lift_mk_gen, hφJ, hj]
        · rw [lift_mk_rel, lift_mk_conj, lift_mk_append, wZ, wJ, lift_mk_gen, lift_mk_gen,
            hφZ, hφJ]
          have hW : FreeGroup.lift φ (FreeGroup.mk wW) =
              ⁅a (xK 0 1 2), b (cK 0 1) * (a (cK 0 1))⁻¹⁆ := by
            simp only [wW, wH, wT1, wT2, lift_mk_comm, lift_mk_append, lift_mk_inv,
              lift_mk_mapWord, hφ1, hφ2, wX, wC, lift_mk_gen,
              decodeK_xIdxQ (by decide : (0 : Fin 3) ≠ 1),
              decodeK_cIdxQ (by decide : (0 : Fin 3) ≠ 1)]
          rw [hW, hzw, mul_inv_cancel]
        · rw [lift_mk_comm, wJ, lift_mk_gen, lift_mk_gen, hφJ,
            commutatorElement_eq_one_iff_mul_comm]
          dsimp only [φ]
          split_ifs with h1 h2 h3
          · exact (hcomm _).1.eq
          · exact (hcomm _).2.eq
          · rfl
          · exact hcz.eq
    refine ⟨PresentedGroup.toGroup hrels, ?_⟩
    exact PresentedGroup.toGroup.of hrels
  · -- x, c and all group relations + normalization kills J
    let S : Set (FreeGroup (Fin 74)) := FreeGroup.mk '' (↑R_all : Set (List (Fin 74 × Bool)))
    let x : Fin 3 → Fin 3 → Fin 7 → PresentedGroup S :=
      fun i j m => if i ≠ j then PresentedGroup.of (emb1 (xIdxQ i j m)) else 1
    let c : Fin 3 → Fin 3 → PresentedGroup S :=
      fun a b => if a ≠ b then PresentedGroup.of (emb1 (cIdxQ a b)) else 1
    let c2 : Fin 3 → Fin 3 → PresentedGroup S :=
      fun a b => if a ≠ b then PresentedGroup.of (emb2 (cIdxQ a b)) else 1
    have hx_eval : ∀ {i j : Fin 3} (hij : i ≠ j) (m : Fin 7),
        FreeGroup.lift (PresentedGroup.of (rels := S)) (FreeGroup.mk (mapWord emb1 (wX i j m))) =
          x i j m := by
      intro i j hij m
      rw [wX, mapWord_wGen, lift_mk_gen]
      simp [x, hij]
    have hx_eval2 : ∀ {i j : Fin 3} (hij : i ≠ j) {m : Fin 7} (hm : m.val < 4),
        FreeGroup.lift (PresentedGroup.of (rels := S)) (FreeGroup.mk (mapWord emb2 (wX i j m))) =
          x i j m := by
      intro i j hij m hm
      rw [wX, mapWord_wGen, lift_mk_gen, ← emb1_eq_emb2_of_lt (xIdxQ_val_lt_24 i j hm)]
      simp [x, hij]
    have hc_eval : ∀ {a b : Fin 3} (hab : a ≠ b),
        FreeGroup.lift (PresentedGroup.of (rels := S)) (FreeGroup.mk (mapWord emb1 (wC a b))) =
          c a b := by
      intro a b hab
      rw [wC, mapWord_wGen, lift_mk_gen]
      simp [c, hab]
    have hc2_eval : ∀ {a b : Fin 3} (hab : a ≠ b),
        FreeGroup.lift (PresentedGroup.of (rels := S)) (FreeGroup.mk (mapWord emb2 (wC a b))) =
          c2 a b := by
      intro a b hab
      rw [wC, mapWord_wGen, lift_mk_gen]
      simp [c2, hab]
    have hact_zero : ∀ {a b i j : Fin 3} (hab : a ≠ b) (hij : i ≠ j) (eps : Bool),
        (if eps then c a b else (c a b)⁻¹) * x i j 0 * (if eps then c a b else (c a b)⁻¹)⁻¹ =
          x i j 0 := by
      intro a b i j hab hij eps
      have h' := rel_eq_of_wRel (by rw [← mapWord_wRel]; exact mem_S_emb1 (IsRelQ.act_zero hab hij eps))
      rw [mapWord_wConj, lift_mk_conj, hx_eval hij] at h'
      cases eps
      · simpa only [Bool.false_eq_true, ↓reduceIte, mapWord_wInv, lift_mk_inv, hc_eval hab] using h'
      · simpa only [↓reduceIte, hc_eval hab] using h'
    have hact_fix : ∀ {a b i j c' : Fin 3} (hab : a ≠ b) (hij : i ≠ j) (hc' : c' ≠ b)
        (eps sig : Bool),
        (if eps then c a b else (c a b)⁻¹) * x i j (signLabel sig c') *
          (if eps then c a b else (c a b)⁻¹)⁻¹ = x i j (signLabel sig c') := by
      intro a b i j c' hab hij hc' eps sig
      have h' := rel_eq_of_wRel
        (by rw [← mapWord_wRel]; exact mem_S_emb1 (IsRelQ.act_fix hab hij hc' eps sig))
      rw [mapWord_wConj, lift_mk_conj, hx_eval hij] at h'
      cases eps
      · simpa only [Bool.false_eq_true, ↓reduceIte, mapWord_wInv, lift_mk_inv, hc_eval hab] using h'
      · simpa only [↓reduceIte, hc_eval hab] using h'
    have hact_mix : ∀ {a b i j : Fin 3} (hab : a ≠ b) (hij : i ≠ j) (eps sig : Bool),
        (if eps then c a b else (c a b)⁻¹) * x i j (signLabel sig b) *
          (if eps then c a b else (c a b)⁻¹)⁻¹ =
          ⁅x i (thirdIdx i j) (signLabel sig b),
            x (thirdIdx i j) j (signLabel (eps == sig) a)⁆ := by
      intro a b i j hab hij eps sig
      have hik : i ≠ thirdIdx i j := (thirdIdx_ne_left hij).symm
      have hkj : thirdIdx i j ≠ j := thirdIdx_ne_right hij
      have h' := rel_eq_of_wRel
        (by rw [← mapWord_wRel]; exact mem_S_emb1 (IsRelQ.act_mix hab hij eps sig))
      rw [mapWord_wConj, mapWord_wComm, lift_mk_conj, lift_mk_comm, hx_eval hij,
        hx_eval hik, hx_eval hkj] at h'
      cases eps
      · simpa only [Bool.false_eq_true, ↓reduceIte, mapWord_wInv, lift_mk_inv, hc_eval hab] using h'
      · simpa only [↓reduceIte, hc_eval hab] using h'
    refine ⟨x, c, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- x i i m = 1 ∧ c i i = 1
      intro i m
      simp [x, c]
    · -- x i j m ^ 5 = 1
      intro i j m
      by_cases hij : i ≠ j
      · have h := rel_eq_one (mem_S_emb1 (IsRelQ.pow hij m))
        rwa [mapWord_wPow, lift_mk_pow, hx_eval hij] at h
      · simp only [x, if_neg hij, one_pow]
    · -- disjoint commutators
      intro i j k l m n hil hjk
      constructor
      · by_cases hij : i ≠ j
        · by_cases hkl : k ≠ l
          · have h := rel_eq_one (mem_S_emb1 (IsRelQ.xcomm hij hkl hil hjk m n))
            rwa [mapWord_wComm, lift_mk_comm, hx_eval hij, hx_eval hkl] at h
          · simp only [x, if_neg hkl, commutatorElement_one_right]
        · simp only [x, if_neg hij, commutatorElement_one_left]
      · by_cases hij : i ≠ j
        · by_cases hkl : k ≠ l
          · have h := rel_eq_one (mem_S_emb1 (IsRelQ.ccomm hij hkl hil hjk))
            rwa [mapWord_wComm, lift_mk_comm, hc_eval hij, hc_eval hkl] at h
          · simp only [c, if_neg hkl, commutatorElement_one_right]
        · simp only [c, if_neg hij, commutatorElement_one_left]
    · -- Steinberg relations
      intro i j k m hij hjk hik
      refine ⟨?_, ?_, ?_⟩
      · have h := rel_eq_of_wRel
          (by rw [← mapWord_wRel]; exact mem_S_emb1 (IsRelQ.xstep1 hij hjk hik m))
        rwa [mapWord_wComm, lift_mk_comm, hx_eval hij, hx_eval hjk, hx_eval hik] at h
      · have h := rel_eq_of_wRel
          (by rw [← mapWord_wRel]; exact mem_S_emb1 (IsRelQ.xstep2 hij hjk hik m))
        rwa [mapWord_wComm, lift_mk_comm, hx_eval hij, hx_eval hjk, hx_eval hik] at h
      · have h := rel_eq_of_wRel
          (by rw [← mapWord_wRel]; exact mem_S_emb1 (IsRelQ.cstep hij hjk hik))
        rwa [mapWord_wComm, lift_mk_comm, hc_eval hij, hc_eval hjk, hc_eval hik] at h
    · -- Triple commutators
      intro i j k a b m n l hij hjk hik hib hka
      by_cases hab : a ≠ b
      · have h := rel_eq_one (mem_S_emb1 (IsRelQ.xtriple hij hjk hik hab hib hka m n l))
        rwa [mapWord_wComm, mapWord_wComm, lift_mk_comm, lift_mk_comm,
          hx_eval hij, hx_eval hjk, hx_eval hab] at h
      · simp only [x, if_neg hab, commutatorElement_one_right]
    · -- Shear torsion (c 0 1 * (c 1 0)⁻¹ * c 0 1) ^ 4 = 1
      have h := rel_eq_one (mem_S_emb1 IsRelQ.ctorsion)
      simp only [mapWord_wPow, mapWord_append, mapWord_wInv,
        lift_mk_pow, lift_mk_append, lift_mk_inv,
        hc_eval (by decide : (0 : Fin 3) ≠ 1), hc_eval (by decide : (1 : Fin 3) ≠ 0)] at h
      exact h
    · -- Normality, generation, compression
      intro a b i j m
      let E : Set (PresentedGroup S) := {g | ∃ i j m, i ≠ j ∧ m.val < 4 ∧ x i j m = g}
      have hmem_x : ∀ i' j' m', x i' j' m' ∈ Subgroup.closure (Set.range ↿x) := by
        intro i' j' m'
        exact Subgroup.subset_closure ⟨(i', j', m'), rfl⟩
      have hmem_E : ∀ i' j' m', i' ≠ j' → m'.val < 4 → x i' j' m' ∈ Subgroup.closure E := by
        intro i' j' m' hij' hm'
        exact Subgroup.subset_closure ⟨i', j', m', hij', hm', rfl⟩
      have hmem_E_union : ∀ i' j' m', i' ≠ j' → m'.val < 4 →
          x i' j' m' ∈ Subgroup.closure (E ∪ Set.range ↿c) := by
        intro i' j' m' hij' hm'
        exact Subgroup.subset_closure (Or.inl ⟨i', j', m', hij', hm', rfl⟩)
      have hmem_c_union : ∀ a' b', c a' b' ∈ Subgroup.closure (E ∪ Set.range ↿c) := by
        intro a' b'
        exact Subgroup.subset_closure (Or.inr ⟨(a', b'), rfl⟩)
      have hconj_X : ∀ (eps : Bool),
          (if eps then c a b else (c a b)⁻¹) * x i j m * (if eps then c a b else (c a b)⁻¹)⁻¹ ∈
            Subgroup.closure (Set.range ↿x) := by
        intro eps
        by_cases hab : a ≠ b
        · by_cases hij : i ≠ j
          · have hsign_mem : ∀ (sig : Bool) (c' : Fin 3),
                (if eps then c a b else (c a b)⁻¹) * x i j (signLabel sig c') *
                  (if eps then c a b else (c a b)⁻¹)⁻¹ ∈ Subgroup.closure (Set.range ↿x) := by
              intro sig c'
              by_cases hcb : c' = b
              · subst hcb
                rw [hact_mix hab hij eps sig]
                exact commutator_mem_subgroup _ (hmem_x _ _ _) (hmem_x _ _ _)
              · rw [hact_fix hab hij hcb eps sig]
                exact hmem_x _ _ _
            fin_cases m
            · change (if eps then c a b else (c a b)⁻¹) * x i j 0 *
                (if eps then c a b else (c a b)⁻¹)⁻¹ ∈ _
              rw [hact_zero hab hij eps]; exact hmem_x _ _ _
            · exact hsign_mem true 0
            · exact hsign_mem true 1
            · exact hsign_mem true 2
            · exact hsign_mem false 0
            · exact hsign_mem false 1
            · exact hsign_mem false 2
          · simp only [x, if_neg hij, mul_one, mul_inv_cancel]
            exact Subgroup.one_mem _
        · simp only [c, if_neg hab, inv_one, ite_self, one_mul, mul_one]
          exact hmem_x i j m
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa using hconj_X true
      · simpa using hconj_X false
      · -- x i j m ∈ Subgroup.closure (E ∪ Set.range ↿c)
        by_cases hij : i ≠ j
        · by_cases hm : m.val < 4
          · exact hmem_E_union i j m hij hm
          · have hrec : ∀ c' : Fin 3, x i j (negLabel c') ∈ Subgroup.closure (E ∪ Set.range ↿c) := by
              intro c'
              have h := rel_eq_of_wRel
                (by rw [← mapWord_wRel]; exact mem_S_emb1 (IsRelQ.neg_rec hij c'))
              rw [mapWord_wConj, lift_mk_conj, hx_eval hij, hx_eval hij] at h
              rw [← h]
              have hrc_val : FreeGroup.lift (PresentedGroup.of (rels := S)) (FreeGroup.mk (mapWord emb1 (wRC c'))) =
                  (c c' (nextIdx c') * (c (nextIdx c') c')⁻¹ * c c' (nextIdx c')) ^ 2 := by
                simp only [wRC, mapWord_wPow, mapWord_append, mapWord_wInv,
                  lift_mk_pow, lift_mk_append, lift_mk_inv,
                  hc_eval (nextIdx_ne c').symm, hc_eval (nextIdx_ne c')]
              rw [hrc_val]
              have hrc_mem : (c c' (nextIdx c') * (c (nextIdx c') c')⁻¹ * c c' (nextIdx c')) ^ 2 ∈
                  Subgroup.closure (E ∪ Set.range ↿c) :=
                Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hmem_c_union _ _)
                  (Subgroup.inv_mem _ (hmem_c_union _ _))) (hmem_c_union _ _)) 2
              exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hrc_mem
                (hmem_E_union i j (posLabel c') hij (by simp [posLabel]; omega)))
                (Subgroup.inv_mem _ hrc_mem)
            fin_cases m
            · exact absurd (by decide) hm
            · exact absurd (by decide) hm
            · exact absurd (by decide) hm
            · exact absurd (by decide) hm
            · exact hrec 0
            · exact hrec 1
            · exact hrec 2
        · simp only [x, if_neg hij]
          exact Subgroup.one_mem _
      · -- m.val < 4 → c a b * x i j m * (c a b)⁻¹ ∈ Subgroup.closure E
        intro hm
        by_cases hab : a ≠ b
        · by_cases hij : i ≠ j
          · have hik : i ≠ thirdIdx i j := (thirdIdx_ne_left hij).symm
            have hkj : thirdIdx i j ≠ j := thirdIdx_ne_right hij
            have hpos_mem : ∀ c' : Fin 3,
                c a b * x i j (posLabel c') * (c a b)⁻¹ ∈ Subgroup.closure E := by
              intro c'
              by_cases hcb : c' = b
              · subst hcb
                have h := hact_mix hab hij true true
                simp only [↓reduceIte, beq_self_eq_true, signLabel] at h
                rw [h]
                exact commutator_mem_subgroup _
                  (hmem_E i (thirdIdx i j) (posLabel c') hik (by simp [posLabel]; omega))
                  (hmem_E (thirdIdx i j) j (posLabel a) hkj (by simp [posLabel]; omega))
              · have h := hact_fix hab hij hcb true true
                simp only [↓reduceIte, signLabel] at h
                rw [h]
                exact hmem_E i j (posLabel c') hij (by simp [posLabel]; omega)
            fin_cases m
            · change c a b * x i j 0 * (c a b)⁻¹ ∈ Subgroup.closure E
              have h := hact_zero hab hij true
              simp only [↓reduceIte] at h
              rw [h]
              exact hmem_E i j 0 hij (by decide)
            · exact hpos_mem 0
            · exact hpos_mem 1
            · exact hpos_mem 2
            · exact absurd hm (by decide)
            · exact absurd hm (by decide)
            · exact absurd hm (by decide)
          · simp only [x, if_neg hij, mul_one, mul_inv_cancel]
            exact Subgroup.one_mem _
        · simp only [c, if_neg hab, inv_one, one_mul, mul_one]
          by_cases hij : i ≠ j
          · exact hmem_E i j m hij hm
          · simp only [x, if_neg hij]
            exact Subgroup.one_mem _
    · -- Normalization kills J
      intro G _ f hnorm
      have h01 : (0 : Fin 3) ≠ 1 := by decide
      have hagree : ∀ i j m, i ≠ j → m.val < 4 →
          c 0 1 * x i j m * (c 0 1)⁻¹ = c2 0 1 * x i j m * (c2 0 1)⁻¹ := by
        intro i j m hij hm
        have hik : i ≠ thirdIdx i j := (thirdIdx_ne_left hij).symm
        have hkj : thirdIdx i j ≠ j := thirdIdx_ne_right hij
        fin_cases m
        · have hmem := IsRelQ.act_zero h01 hij true
          have h1 := rel_eq_of_wRel (by rw [← mapWord_wRel]; exact mem_S_emb1 hmem)
          have h2 := rel_eq_of_wRel (by rw [← mapWord_wRel]; exact mem_S_emb2 hmem)
          simp only [↓reduceIte] at h1 h2
          rw [mapWord_wConj, lift_mk_conj, hc_eval h01, hx_eval hij] at h1
          rw [mapWord_wConj, lift_mk_conj, hc2_eval h01, hx_eval2 hij (by decide)] at h2
          exact h1.trans h2.symm
        · have hmem := IsRelQ.act_fix h01 hij h01 true true
          have h1 := rel_eq_of_wRel (by rw [← mapWord_wRel]; exact mem_S_emb1 hmem)
          have h2 := rel_eq_of_wRel (by rw [← mapWord_wRel]; exact mem_S_emb2 hmem)
          simp only [↓reduceIte] at h1 h2
          rw [mapWord_wConj, lift_mk_conj, hc_eval h01, hx_eval hij] at h1
          rw [mapWord_wConj, lift_mk_conj, hc2_eval h01, hx_eval2 hij (by decide)] at h2
          exact h1.trans h2.symm
        · have hmem := IsRelQ.act_mix h01 hij true true
          have h1 := rel_eq_of_wRel (by rw [← mapWord_wRel]; exact mem_S_emb1 hmem)
          have h2 := rel_eq_of_wRel (by rw [← mapWord_wRel]; exact mem_S_emb2 hmem)
          simp only [↓reduceIte, beq_self_eq_true] at h1 h2
          rw [mapWord_wConj, mapWord_wComm, lift_mk_conj, lift_mk_comm, hc_eval h01,
            hx_eval hij, hx_eval hik, hx_eval hkj] at h1
          rw [mapWord_wConj, mapWord_wComm, lift_mk_conj, lift_mk_comm, hc2_eval h01,
            hx_eval2 hij (by decide), hx_eval2 hik (by decide), hx_eval2 hkj (by decide)] at h2
          exact h1.trans h2.symm
        · have h21 : (2 : Fin 3) ≠ 1 := by decide
          have hmem := IsRelQ.act_fix h01 hij h21 true true
          have h1 := rel_eq_of_wRel (by rw [← mapWord_wRel]; exact mem_S_emb1 hmem)
          have h2 := rel_eq_of_wRel (by rw [← mapWord_wRel]; exact mem_S_emb2 hmem)
          simp only [↓reduceIte] at h1 h2
          rw [mapWord_wConj, lift_mk_conj, hc_eval h01, hx_eval hij] at h1
          rw [mapWord_wConj, lift_mk_conj, hc2_eval h01, hx_eval2 hij (by decide)] at h2
          exact h1.trans h2.symm
        · exact absurd hm (by decide)
        · exact absurd hm (by decide)
        · exact absurd hm (by decide)
      have hu_cent : f ((c 0 1)⁻¹ * c2 0 1) ∈ Subgroup.centralizer (f '' {g | ∃ i j m, i ≠ j ∧ m.val < 4 ∧ x i j m = g}) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨_, ⟨i, j, m, hij, hm, rfl⟩, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        have h := hagree i j m hij hm
        have h' : x i j m * (c 0 1)⁻¹ = (c 0 1)⁻¹ * (c2 0 1 * x i j m * (c2 0 1)⁻¹) := by
          rw [← h]; group
        calc x i j m * ((c 0 1)⁻¹ * c2 0 1)
            = (x i j m * (c 0 1)⁻¹) * c2 0 1 := by group
          _ = ((c 0 1)⁻¹ * (c2 0 1 * x i j m * (c2 0 1)⁻¹)) * c2 0 1 := by rw [h']
          _ = (c 0 1)⁻¹ * c2 0 1 * x i j m := by group
      have hconj_cent : f (c2 0 1 * (c 0 1)⁻¹) ∈ Subgroup.centralizer (f '' {g | ∃ i j m, i ≠ j ∧ m.val < 4 ∧ x i j m = g}) := by
        have hmem := (Subgroup.mem_normalizer_iff.mp hnorm (f ((c 0 1)⁻¹ * c2 0 1))).mp hu_cent
        have heq : f (c 0 1) * f ((c 0 1)⁻¹ * c2 0 1) * (f (c 0 1))⁻¹ = f (c2 0 1 * (c 0 1)⁻¹) := by
          rw [← map_inv, ← map_mul, ← map_mul]
          congr 1
          group
        rwa [heq] at hmem
      have hcomm_h : f (x 0 1 2) * f (c2 0 1 * (c 0 1)⁻¹) = f (c2 0 1 * (c 0 1)⁻¹) * f (x 0 1 2) :=
        Subgroup.mem_centralizer_iff.mp hconj_cent (f (x 0 1 2)) ⟨x 0 1 2, ⟨0, 1, 2, h01, by decide, rfl⟩, rfl⟩
      have hW_one : f ⁅x 0 1 2, c2 0 1 * (c 0 1)⁻¹⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcomm_h
      have hrel_Jz : wRel (wConj wZ wW) (wW ++ wJ) ∈ R_Jz_set :=
        Or.inl (Or.inr rfl)
      have hzw := rel_eq_of_wRel (mem_S_Jz hrel_Jz)
      rw [lift_mk_conj, lift_mk_append] at hzw
      have hW_eval : FreeGroup.lift (PresentedGroup.of (rels := S)) (FreeGroup.mk wW) =
          ⁅x 0 1 2, c2 0 1 * (c 0 1)⁻¹⁆ := by
        simp only [wW, wH, wT1, wT2, lift_mk_comm, lift_mk_append, lift_mk_inv,
          hx_eval h01, hc_eval h01, hc2_eval h01]
      have hJ_eval : FreeGroup.lift (PresentedGroup.of (rels := S)) (FreeGroup.mk wJ) =
          PresentedGroup.mk S (FreeGroup.of (72 : Fin 74)) := by
        rw [wJ, lift_mk_gen]; rfl
      rw [hW_eval, hJ_eval] at hzw
      have hfzw := congrArg f hzw
      simp only [map_mul, map_inv, hW_one, mul_one, one_mul, mul_inv_cancel] at hfzw
      exact hfzw.symm
