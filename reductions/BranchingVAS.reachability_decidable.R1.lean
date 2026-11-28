import FormalConjectures.Paper.BranchingVAS
import Mathlib.Computability.RE
import Mathlib.Computability.Primrec.List
import Mathlib.Tactic

/-!
# Reduction of `BranchingVAS.reachability_decidable`

Following C. Bizière, J. Leroux, and G. Sutre, *Solving the Reachability Problem for Branching
Vector Addition Systems via Semilinear Inductive Invariants* (`arXiv:2607.09558`, 2026), we reduce
the uniform decidability of BVAS reachability to two independent pillars via Post's theorem:
1. `H1`: **Uniform computability of checking a separating semilinear inductive invariant**
   (uniform decidability of Presburger arithmetic `Th(ℕ, +, 0, 1, ≤)` applied to the four
   first-order closure/exclusion clauses for an encoded semilinear set
   `S : List (List ℕ × List (List ℕ))`).
2. `H2`: **Completeness of separating semilinear inductive invariants for BVAS**
   (Bizière–Leroux–Sutre 2026, Main Theorem): every unreachable configuration `t` of a BVAS `b`
   of arbitrary dimension `d` is separated from the reachable set by a semilinear inductive
   invariant `S : List (List ℕ × List (List ℕ))`.

Inside `main`, we prove from scratch:
- Positive semidecidability `REPred (fun p => p.2.1.Reachable p.2.2)` via a primitive-recursive
  finite stage enumerator on list-encoded configurations, proving `Primrec` for all vector/stage
  operations, soundness and completeness of the stages, and `REPred` via `Partrec.rfind`.
- Invariant soundness by structural induction on `Bvas.Reachable`.
- Negative semidecidability `REPred (fun p => ¬ p.2.1.Reachable p.2.2)` from `H1` + `H2` by
  effective search over `Encodable.decode` codes of `List (List ℕ × List (List ℕ))`.
- Uniform decidability `ComputablePred` via Post's theorem (`ComputablePred.computable_iff_re_compl_re'`).

Thanks to @MechaNuggan for the finite-stage positive semidecision and separating semilinear
inductive invariant reduction architecture.
Credit: @tkaiman
-/

namespace OMA.R_BranchingVAS_reachability_decidable_R1

open BranchingVAS
open scoped BigOperators

/- ### Step 1: Primitive-recursive finite-stage enumerator for positive semidecidability -/

private abbrev Input := Σ d : ℕ, Bvas d × (Fin d → ℤ)
private abbrev RawInput := ℕ × List (List ℤ) × List (List ℤ) × List (List ℤ) × List ℤ
private abbrev SemilinearCode := List (List ℕ × List (List ℕ))

private def encodeInput (p : Input) : RawInput :=
  (p.1, p.2.1.1.map List.ofFn, p.2.1.unaryRules.map List.ofFn,
    p.2.1.binaryRules.map List.ofFn, List.ofFn p.2.2)

private lemma primrec_encodeInput : Primrec encodeInput :=
  Primrec.encode_iff.mp Primrec.encode

private def nonnegList (l : List ℤ) : Bool :=
  l.foldr (fun z acc => decide (0 ≤ z) && acc) true

private lemma nonnegList_eq_true_iff (l : List ℤ) :
    nonnegList l = true ↔ ∀ z ∈ l, (0 : ℤ) ≤ z := by
  induction l with
  | nil => simp [nonnegList]
  | cons a tl ih =>
    simp only [nonnegList, List.foldr_cons, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons,
      forall_eq_or_imp]
    exact and_congr_right fun _ => ih

private lemma nonnegList_ofFn_iff {d : ℕ} (v : Fin d → ℤ) :
    nonnegList (List.ofFn v) = true ↔ 0 ≤ v := by
  rw [nonnegList_eq_true_iff]
  constructor
  · intro h i
    exact h (v i) (by simp)
  · intro h z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact h i

private def addVec (d : ℕ) (v w : List ℤ) : List ℤ :=
  (List.range d).map fun i => v.getD i 0 + w.getD i 0

private lemma addVec_ofFn {d : ℕ} (v w : Fin d → ℤ) :
    addVec d (List.ofFn v) (List.ofFn w) = List.ofFn (v + w) := by
  refine List.ext_getElem (by simp [addVec]) fun i hi _ => ?_
  have hid : i < d := by simpa [addVec] using hi
  simp [addVec, List.getD_eq_getElem?_getD, hid]

private lemma encode_int_ofNat (m : ℕ) : Encodable.encode (Int.ofNat m) = 2 * m := rfl

private lemma encode_int_negSucc (n : ℕ) : Encodable.encode (Int.negSucc n) = 2 * n + 1 := rfl

private lemma bodd_two_mul (k : ℕ) : (2 * k).bodd = false := by
  rw [Nat.bodd_mul]; rfl

private lemma bodd_two_mul_add_one (k : ℕ) : (2 * k + 1).bodd = true := by
  rw [Nat.bodd_succ, bodd_two_mul]; rfl

private lemma div2_two_mul (k : ℕ) : (2 * k).div2 = k := by
  rw [Nat.div2_val]; omega

private lemma div2_two_mul_add_one (k : ℕ) : (2 * k + 1).div2 = k := by
  rw [Nat.div2_val]; omega

private lemma primrec_int_nonneg : Primrec (fun z : ℤ => decide ((0 : ℤ) ≤ z)) := by
  have h : ∀ z : ℤ, decide ((0 : ℤ) ≤ z) = !(Encodable.encode z).bodd := by
    rintro (m | n)
    · rw [encode_int_ofNat, bodd_two_mul]
      simp [Int.ofNat_eq_natCast]
    · rw [encode_int_negSucc, bodd_two_mul_add_one]
      simp [show ¬ ((0 : ℤ) ≤ Int.negSucc n) by omega]
  exact (Primrec.not.comp (Primrec.nat_bodd.comp Primrec.encode)).of_eq fun z => (h z).symm

private lemma primrec_int_add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  rw [Primrec₂, ← Primrec.encode_iff]
  let e1 : ℤ × ℤ → ℕ := fun p => Encodable.encode p.1
  let e2 : ℤ × ℤ → ℕ := fun p => Encodable.encode p.2
  let b1 : ℤ × ℤ → Bool := fun p => (e1 p).bodd
  let b2 : ℤ × ℤ → Bool := fun p => (e2 p).bodd
  let x1 : ℤ × ℤ → ℕ := fun p => (e1 p).div2
  let x2 : ℤ × ℤ → ℕ := fun p => (e2 p).div2
  have he1 : Primrec e1 := Primrec.encode.comp Primrec.fst
  have he2 : Primrec e2 := Primrec.encode.comp Primrec.snd
  have hb1 : Primrec b1 := Primrec.nat_bodd.comp he1
  have hb2 : Primrec b2 := Primrec.nat_bodd.comp he2
  have hx1 : Primrec x1 := Primrec.nat_div2.comp he1
  have hx2 : Primrec x2 := Primrec.nat_div2.comp he2
  have hff : Primrec (fun p => 2 * (x1 p + x2 p)) :=
    Primrec.nat_double.comp (Primrec.nat_add.comp hx1 hx2)
  have htt : Primrec (fun p => 2 * (x1 p + x2 p + 1) + 1) :=
    Primrec.nat_double_succ.comp (Primrec.succ.comp (Primrec.nat_add.comp hx1 hx2))
  have hft : Primrec (fun p => if x2 p < x1 p then 2 * (x1 p - (x2 p + 1)) else 2 * (x2 p - x1 p) + 1) :=
    Primrec.ite (Primrec.nat_lt.comp hx2 hx1)
      (Primrec.nat_double.comp (Primrec.nat_sub.comp hx1 (Primrec.succ.comp hx2)))
      (Primrec.nat_double_succ.comp (Primrec.nat_sub.comp hx2 hx1))
  have htf : Primrec (fun p => if x1 p < x2 p then 2 * (x2 p - (x1 p + 1)) else 2 * (x1 p - x2 p) + 1) :=
    Primrec.ite (Primrec.nat_lt.comp hx1 hx2)
      (Primrec.nat_double.comp (Primrec.nat_sub.comp hx2 (Primrec.succ.comp hx1)))
      (Primrec.nat_double_succ.comp (Primrec.nat_sub.comp hx1 hx2))
  have hcomb : Primrec (fun p : ℤ × ℤ =>
      cond (b1 p) (cond (b2 p) (2 * (x1 p + x2 p + 1) + 1)
                               (if x1 p < x2 p then 2 * (x2 p - (x1 p + 1)) else 2 * (x1 p - x2 p) + 1))
                  (cond (b2 p) (if x2 p < x1 p then 2 * (x1 p - (x2 p + 1)) else 2 * (x2 p - x1 p) + 1)
                               (2 * (x1 p + x2 p)))) :=
    Primrec.cond hb1 (Primrec.cond hb2 htt htf) (Primrec.cond hb2 hft hff)
  refine hcomb.of_eq fun ⟨z1, z2⟩ => ?_
  cases z1 with
  | ofNat m1 =>
    cases z2 with
    | ofNat m2 =>
      have heq : Int.ofNat m1 + Int.ofNat m2 = Int.ofNat (m1 + m2) := rfl
      rw [heq]
      simp only [b1, b2, x1, x2, e1, e2, encode_int_ofNat, bodd_two_mul, div2_two_mul,
        Bool.cond_false]
    | negSucc n2 =>
      simp only [b1, b2, x1, x2, e1, e2, encode_int_ofNat, encode_int_negSucc,
        bodd_two_mul, bodd_two_mul_add_one, div2_two_mul, div2_two_mul_add_one,
        Bool.cond_false, Bool.cond_true]
      split_ifs with h
      · have heq : Int.ofNat m1 + Int.negSucc n2 = Int.ofNat (m1 - (n2 + 1)) := by
          simp only [Int.ofNat_eq_natCast]; omega
        rw [heq, encode_int_ofNat]
      · have heq : Int.ofNat m1 + Int.negSucc n2 = Int.negSucc (n2 - m1) := by
          simp only [Int.ofNat_eq_natCast]; omega
        rw [heq, encode_int_negSucc]
  | negSucc n1 =>
    cases z2 with
    | ofNat m2 =>
      simp only [b1, b2, x1, x2, e1, e2, encode_int_ofNat, encode_int_negSucc,
        bodd_two_mul, bodd_two_mul_add_one, div2_two_mul, div2_two_mul_add_one,
        Bool.cond_false, Bool.cond_true]
      split_ifs with h
      · have heq : Int.negSucc n1 + Int.ofNat m2 = Int.ofNat (m2 - (n1 + 1)) := by
          simp only [Int.ofNat_eq_natCast]; omega
        rw [heq, encode_int_ofNat]
      · have heq : Int.negSucc n1 + Int.ofNat m2 = Int.negSucc (n1 - m2) := by
          simp only [Int.ofNat_eq_natCast]; omega
        rw [heq, encode_int_negSucc]
    | negSucc n2 =>
      have heq : Int.negSucc n1 + Int.negSucc n2 = Int.negSucc (n1 + n2 + 1) := by omega
      rw [heq]
      simp only [b1, b2, x1, x2, e1, e2, encode_int_negSucc,
        bodd_two_mul_add_one, div2_two_mul_add_one, Bool.cond_true]

private lemma primrec_nonnegList : Primrec nonnegList := by
  have hstep : Primrec₂ (fun (_ : List ℤ) (bs : ℤ × Bool) => decide ((0 : ℤ) ≤ bs.1) && bs.2) :=
    (Primrec.and.comp (primrec_int_nonneg.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr (Primrec.id (α := List ℤ)) (Primrec.const true) hstep

private lemma primrec_filter_nonnegList : Primrec (fun L : List (List ℤ) => L.filter nonnegList) := by
  have h : ∀ L : List (List ℤ),
      L.filter nonnegList = L.foldr (fun v acc => cond (nonnegList v) (v :: acc) acc) [] := by
    intro L
    induction L with
    | nil => rfl
    | cons a tl ih =>
      simp only [List.filter_cons, List.foldr_cons, ih]
      cases nonnegList a <;> rfl
  have hstep : Primrec₂ (fun (_ : List (List ℤ)) (bs : List ℤ × List (List ℤ)) =>
      cond (nonnegList bs.1) (bs.1 :: bs.2) bs.2) :=
    (Primrec.cond (primrec_nonnegList.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr (Primrec.id (α := List (List ℤ)))
    (Primrec.const ([] : List (List ℤ))) hstep).of_eq fun L => (h L).symm

private lemma primrec_addVec : Primrec (fun t : ℕ × List ℤ × List ℤ => addVec t.1 t.2.1 t.2.2) := by
  unfold addVec
  refine Primrec.list_map (Primrec.list_range.comp Primrec.fst) ?_
  have h1 : Primrec₂ (fun (t : ℕ × List ℤ × List ℤ) (i : ℕ) => t.2.1.getD i 0) :=
    (Primrec.list_getD (0 : ℤ)).comp₂ (Primrec.fst.comp₂ (Primrec.snd.comp₂ Primrec₂.left))
      Primrec₂.right
  have h2 : Primrec₂ (fun (t : ℕ × List ℤ × List ℤ) (i : ℕ) => t.2.2.getD i 0) :=
    (Primrec.list_getD (0 : ℤ)).comp₂ (Primrec.snd.comp₂ (Primrec.snd.comp₂ Primrec₂.left))
      Primrec₂.right
  exact primrec_int_add.comp₂ h1 h2

private lemma primrec_addVec3 :
    Primrec (fun t : ℕ × List ℤ × List ℤ × List ℤ => addVec t.1 (addVec t.1 t.2.1 t.2.2.1) t.2.2.2) := by
  have hd : Primrec (fun t : ℕ × List ℤ × List ℤ × List ℤ => t.1) := Primrec.fst
  have hv1 : Primrec (fun t : ℕ × List ℤ × List ℤ × List ℤ => t.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hv2 : Primrec (fun t : ℕ × List ℤ × List ℤ × List ℤ => t.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun t : ℕ × List ℤ × List ℤ × List ℤ => t.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have h12 : Primrec (fun t : ℕ × List ℤ × List ℤ × List ℤ => addVec t.1 t.2.1 t.2.2.1) :=
    primrec_addVec.comp (Primrec.pair hd (Primrec.pair hv1 hv2))
  exact primrec_addVec.comp (Primrec.pair hd (Primrec.pair h12 hr))

private def unaryStep (d : ℕ) (U : List (List ℤ)) (S : List (List ℤ)) : List (List ℤ) :=
  (S.flatMap fun v => U.map fun r => addVec d v r).filter nonnegList

private lemma primrec_unaryStep :
    Primrec (fun p : ℕ × List (List ℤ) × List (List ℤ) => unaryStep p.1 p.2.1 p.2.2) := by
  unfold unaryStep
  have hS : Primrec (fun p : ℕ × List (List ℤ) × List (List ℤ) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hinner : Primrec₂ (fun (p : ℕ × List (List ℤ) × List (List ℤ)) (v : List ℤ) =>
      p.2.1.map fun r => addVec p.1 v r) := by
    have hU : Primrec (fun q : (ℕ × List (List ℤ) × List (List ℤ)) × List ℤ => q.1.2.1) :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hmap : Primrec₂ (fun (q : (ℕ × List (List ℤ) × List (List ℤ)) × List ℤ) (r : List ℤ) =>
        addVec q.1.1 q.2 r) :=
      (primrec_addVec.comp
        (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂
    exact (Primrec.list_map hU hmap).to₂
  exact primrec_filter_nonnegList.comp (Primrec.list_flatMap hS hinner)

private def binaryMap (d : ℕ) (B : List (List ℤ)) (v₁ v₂ : List ℤ) : List (List ℤ) :=
  B.map fun r => addVec d (addVec d v₁ v₂) r

private lemma primrec_binaryMap :
    Primrec (fun t : (ℕ × List (List ℤ)) × (List ℤ × List ℤ) =>
      binaryMap t.1.1 t.1.2 t.2.1 t.2.2) := by
  unfold binaryMap
  have hB : Primrec (fun t : (ℕ × List (List ℤ)) × (List ℤ × List ℤ) => t.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hmap : Primrec₂ (fun (t : (ℕ × List (List ℤ)) × (List ℤ × List ℤ)) (r : List ℤ) =>
      addVec t.1.1 (addVec t.1.1 t.2.1 t.2.2) r) :=
    (primrec_addVec3.comp
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)))).to₂
  exact Primrec.list_map hB hmap

private def binaryStep (d : ℕ) (B : List (List ℤ)) (S : List (List ℤ)) : List (List ℤ) :=
  (S.flatMap fun v₁ => S.flatMap fun v₂ => binaryMap d B v₁ v₂).filter nonnegList

private lemma primrec_binaryStep :
    Primrec (fun p : ℕ × List (List ℤ) × List (List ℤ) => binaryStep p.1 p.2.1 p.2.2) := by
  unfold binaryStep
  have hS : Primrec (fun p : ℕ × List (List ℤ) × List (List ℤ) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hinner2 : Primrec₂ (fun (q : (ℕ × List (List ℤ) × List (List ℤ)) × List ℤ) (v₂ : List ℤ) =>
      binaryMap q.1.1 q.1.2.1 q.2 v₂) :=
    (primrec_binaryMap.comp
      (Primrec.pair
        (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
        (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂
  have hinner1 : Primrec₂ (fun (p : ℕ × List (List ℤ) × List (List ℤ)) (v₁ : List ℤ) =>
      p.2.2.flatMap fun v₂ => binaryMap p.1 p.2.1 v₁ v₂) := by
    have hS1 : Primrec (fun q : (ℕ × List (List ℤ) × List (List ℤ)) × List ℤ => q.1.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    exact (Primrec.list_flatMap hS1 hinner2).to₂
  exact primrec_filter_nonnegList.comp (Primrec.list_flatMap hS hinner1)

private lemma primrec_append_llz :
    Primrec (fun p : List (List ℤ) × List (List ℤ) => p.1 ++ p.2) :=
  @Primrec.list_append (List ℤ) _

private def stageStepUnary (d : ℕ) (U S : List (List ℤ)) : List (List ℤ) :=
  S ++ unaryStep d U S

private lemma primrec_stageStepUnary :
    Primrec (fun p : ℕ × List (List ℤ) × List (List ℤ) => stageStepUnary p.1 p.2.1 p.2.2) := by
  unfold stageStepUnary
  exact primrec_append_llz.comp
    (Primrec.pair
      ((Primrec.snd (α := List (List ℤ)) (β := List (List ℤ))).comp
        (Primrec.snd (α := ℕ) (β := List (List ℤ) × List (List ℤ))))
      primrec_unaryStep)

private def stageStepBinary (d : ℕ) (B S : List (List ℤ)) : List (List ℤ) :=
  S ++ binaryStep d B S

private lemma primrec_stageStepBinary :
    Primrec (fun p : ℕ × List (List ℤ) × List (List ℤ) => stageStepBinary p.1 p.2.1 p.2.2) := by
  unfold stageStepBinary
  exact primrec_append_llz.comp
    (Primrec.pair
      ((Primrec.snd (α := List (List ℤ)) (β := List (List ℤ))).comp
        (Primrec.snd (α := ℕ) (β := List (List ℤ) × List (List ℤ))))
      primrec_binaryStep)

private def stageStep (q : RawInput) (S : List (List ℤ)) : List (List ℤ) :=
  stageStepBinary q.1 q.2.2.2.1 (stageStepUnary q.1 q.2.2.1 S)

private lemma primrec_stageStep : Primrec₂ stageStep := by
  change Primrec (fun p : RawInput × List (List ℤ) =>
    stageStepBinary p.1.1 p.1.2.2.2.1 (stageStepUnary p.1.1 p.1.2.2.1 p.2))
  have hd : Primrec (fun p : RawInput × List (List ℤ) => p.1.1) :=
    (Primrec.fst (α := ℕ)).comp (Primrec.fst (α := RawInput) (β := List (List ℤ)))
  have hu : Primrec (fun p : RawInput × List (List ℤ) => p.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst (α := RawInput) (β := List (List ℤ)))))
  have hb : Primrec (fun p : RawInput × List (List ℤ) => p.1.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst (α := RawInput) (β := List (List ℤ))))))
  have hS : Primrec (fun p : RawInput × List (List ℤ) => p.2) :=
    Primrec.snd (α := RawInput) (β := List (List ℤ))
  have hUstep : Primrec (fun p : RawInput × List (List ℤ) =>
      stageStepUnary p.1.1 p.1.2.2.1 p.2) :=
    primrec_stageStepUnary.comp (Primrec.pair hd (Primrec.pair hu hS))
  exact primrec_stageStepBinary.comp (Primrec.pair hd (Primrec.pair hb hUstep))

private def stage (q : RawInput) : ℕ → List (List ℤ)
  | 0 => (q.2.1.map fun l => List.ofFn (vecOfList q.1 l)).filter nonnegList
  | n + 1 => stageStep q (stage q n)

private lemma primrec_stage : Primrec₂ stage := by
  have h0 : Primrec (fun q : RawInput =>
      (q.2.1.map fun l => List.ofFn (vecOfList q.1 l)).filter nonnegList) :=
    primrec_filter_nonnegList.comp
      (Primrec.list_map (Primrec.fst.comp Primrec.snd)
        (primrec_ofFn_vecOfList.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right))
  have hstep : Primrec₂ (fun (p : RawInput × ℕ) (ns : ℕ × List (List ℤ)) => stageStep p.1 ns.2) :=
    (primrec_stageStep.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)).to₂
  have hrec : Primrec (fun p : RawInput × ℕ =>
      Nat.rec (motive := fun _ => List (List ℤ)) (stage p.1 0)
        (fun _ acc => stageStep p.1 acc) p.2) :=
    Primrec.nat_rec' Primrec.snd (h0.comp Primrec.fst) hstep
  change Primrec (fun p : RawInput × ℕ => stage p.1 p.2)
  refine hrec.of_eq fun p => ?_
  rcases p with ⟨q, n⟩
  induction n with
  | zero => rfl
  | succ k ih => exact congrArg (stageStep q) ih

private lemma stage_mono (q : RawInput) {m n : ℕ} (h : m ≤ n) :
    ∀ x ∈ stage q m, x ∈ stage q n := by
  induction h with
  | refl => intro x hx; exact hx
  | step _ ih =>
    intro x hx
    simp only [stage, stageStep, stageStepBinary, stageStepUnary, List.mem_append]
    exact Or.inl (Or.inl (ih x hx))

private lemma stage_complete {d : ℕ} (b : Bvas d) (t : Fin d → ℤ) {v : Fin d → ℤ}
    (hv : b.Reachable v) :
    ∃ n : ℕ, List.ofFn v ∈ stage (encodeInput ⟨d, b, t⟩) n := by
  induction hv with
  | @base v hmem hcfg =>
    refine ⟨0, ?_⟩
    simp only [stage, encodeInput, List.mem_filter, List.mem_map]
    refine ⟨⟨List.ofFn v, ⟨v, hmem, rfl⟩, by simp [vecOfList_ofFn]⟩,
      (nonnegList_ofFn_iff v).mpr hcfg⟩
  | @unary v r w _ hr hcfg hw ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    simp only [stage, stageStep, stageStepBinary, stageStepUnary, unaryStep, encodeInput,
      List.mem_append, List.mem_filter, List.mem_flatMap, List.mem_map]
    refine Or.inl (Or.inr ⟨⟨List.ofFn v, hn, List.ofFn r, ⟨r, hr, rfl⟩, ?_⟩, ?_⟩)
    · rw [addVec_ofFn, hw]
    · exact (nonnegList_ofFn_iff w).mpr hcfg
  | @binary v₁ v₂ r w _ _ hr hcfg hw ih₁ ih₂ =>
    obtain ⟨n₁, hn₁⟩ := ih₁
    obtain ⟨n₂, hn₂⟩ := ih₂
    let n := max n₁ n₂
    have hm₁ : List.ofFn v₁ ∈ stage (encodeInput ⟨d, b, t⟩) n :=
      stage_mono _ (le_max_left _ _) _ hn₁
    have hm₂ : List.ofFn v₂ ∈ stage (encodeInput ⟨d, b, t⟩) n :=
      stage_mono _ (le_max_right _ _) _ hn₂
    refine ⟨n + 1, ?_⟩
    simp only [stage, stageStep, stageStepBinary, stageStepUnary, binaryStep, binaryMap, encodeInput,
      List.mem_append, List.mem_filter, List.mem_flatMap, List.mem_map]
    refine Or.inr ⟨⟨List.ofFn v₁, Or.inl hm₁, List.ofFn v₂, Or.inl hm₂,
      List.ofFn r, ⟨r, hr, rfl⟩, ?_⟩, ?_⟩
    · rw [addVec_ofFn, addVec_ofFn, hw]
    · exact (nonnegList_ofFn_iff w).mpr hcfg

private lemma stage_sound {d : ℕ} (b : Bvas d) (t : Fin d → ℤ) (n : ℕ) :
    ∀ l ∈ stage (encodeInput ⟨d, b, t⟩) n, ∃ v : Fin d → ℤ, l = List.ofFn v ∧ b.Reachable v := by
  induction n with
  | zero =>
    intro l hl
    simp only [stage, encodeInput, List.mem_filter, List.mem_map] at hl
    obtain ⟨⟨_, ⟨v, hv, rfl⟩, rfl⟩, hnn⟩ := hl
    rw [vecOfList_ofFn] at hnn ⊢
    exact ⟨v, rfl, .base hv ((nonnegList_ofFn_iff v).mp hnn)⟩
  | succ k ih =>
    have hU : ∀ l ∈ stageStepUnary d (b.unaryRules.map List.ofFn) (stage (encodeInput ⟨d, b, t⟩) k),
        ∃ v : Fin d → ℤ, l = List.ofFn v ∧ b.Reachable v := by
      intro l hl
      simp only [stageStepUnary, unaryStep, List.mem_append, List.mem_filter, List.mem_flatMap,
        List.mem_map] at hl
      rcases hl with hl | ⟨⟨vl, hvl, rl, ⟨r, hr, rfl⟩, rfl⟩, hnn⟩
      · exact ih l hl
      · obtain ⟨v, rfl, hv⟩ := ih vl hvl
        rw [addVec_ofFn] at hnn ⊢
        exact ⟨v + r, rfl, .unary hv hr ((nonnegList_ofFn_iff _).mp hnn) rfl⟩
    intro l hl
    simp only [stage, stageStep, stageStepBinary, encodeInput, List.mem_append] at hl
    rcases hl with hl | hl
    · exact hU l hl
    · simp only [binaryStep, binaryMap, List.mem_filter, List.mem_flatMap, List.mem_map] at hl
      obtain ⟨⟨v1l, hv1l, v2l, hv2l, rl, ⟨r, hr, rfl⟩, rfl⟩, hnn⟩ := hl
      obtain ⟨v₁, rfl, hv₁⟩ := hU v1l hv1l
      obtain ⟨v₂, rfl, hv₂⟩ := hU v2l hv2l
      rw [addVec_ofFn, addVec_ofFn] at hnn ⊢
      exact ⟨v₁ + v₂ + r, rfl, .binary hv₁ hv₂ hr ((nonnegList_ofFn_iff _).mp hnn) rfl⟩

private lemma primrec_list_mem_bool {α : Type*} [Primcodable α] [DecidableEq α] :
    Primrec₂ (fun (a : α) (L : List α) => decide (a ∈ L)) := by
  have h : ∀ (a : α) (L : List α),
      decide (a ∈ L) = L.foldr (fun x acc => decide (a = x) || acc) false := by
    intro a L
    induction L with
    | nil => simp
    | cons x tl ih =>
      simp only [List.mem_cons, List.foldr_cons, ← ih]
      by_cases hax : a = x <;> simp [hax]
  have hstep : Primrec₂ (fun (p : α × List α) (bs : α × Bool) => decide (p.1 = bs.1) || bs.2) :=
    (Primrec.or.comp
      (Primrec.eq.decide.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact ((Primrec.list_foldr (Primrec.snd (α := α) (β := List α)) (Primrec.const false) hstep).of_eq
    fun p => (h p.1 p.2).symm).to₂

private lemma rePred_reachable :
    REPred fun p : Input => p.2.1.Reachable p.2.2 := by
  let P : Input → ℕ → Bool :=
    fun p n => decide ((encodeInput p).2.2.2.2 ∈ stage (encodeInput p) n)
  have hP : Primrec₂ P := by
    change Primrec (fun p : Input × ℕ => P p.1 p.2)
    have hraw := primrec_list_mem_bool.comp
      ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp primrec_encodeInput)))).comp
        Primrec.fst)
      (primrec_stage.comp (primrec_encodeInput.comp Primrec.fst) Primrec.snd)
    exact hraw.of_eq fun p => by dsimp [P]; exact decide_eq_decide.mpr Iff.rfl
  have hpart : Partrec (fun p : Input => Nat.rfind (fun n => (Part.some (P p n) : Part Bool))) :=
    Partrec.rfind hP.to_comp.partrec
  refine (Partrec.dom_re hpart).of_eq fun p => ?_
  rcases p with ⟨d, b, t⟩
  change (Nat.rfind (fun n : ℕ => (Part.some (P ⟨d, b, t⟩ n) : Part Bool))).Dom ↔ b.Reachable t
  rw [Nat.rfind_dom (p := fun n : ℕ => (Part.some (P ⟨d, b, t⟩ n) : Part Bool))]
  constructor
  · rintro ⟨n, hn, -⟩
    have hdec : P ⟨d, b, t⟩ n = true := (Part.mem_some_iff.mp hn).symm
    have hmem : List.ofFn t ∈ stage (encodeInput ⟨d, b, t⟩) n :=
      of_decide_eq_true hdec
    obtain ⟨v, hv_eq, hv_reach⟩ := stage_sound b t n _ hmem
    have htv : t = v := by
      have := congrArg (vecOfList d) hv_eq
      simpa [vecOfList_ofFn] using this
    exact htv ▸ hv_reach
  · intro hreach
    obtain ⟨n, hn⟩ := stage_complete b t hreach
    refine ⟨n, ?_, fun {m} _ => trivial⟩
    have hdec : P ⟨d, b, t⟩ n = true := decide_eq_true hn
    exact Part.mem_some_iff.mpr hdec.symm

/- ### Step 2: Soundness of semilinear inductive invariants -/

private lemma reachable_mem_of_invariant {d : ℕ} (b : Bvas d) (I : (Fin d → ℤ) → Prop)
    (hbase : ∀ v ∈ b.1, 0 ≤ v → I v)
    (hunary : ∀ v r, I v → r ∈ b.unaryRules → 0 ≤ v + r → I (v + r))
    (hbinary : ∀ v₁ v₂ r, I v₁ → I v₂ → r ∈ b.binaryRules → 0 ≤ v₁ + v₂ + r → I (v₁ + v₂ + r))
    {v : Fin d → ℤ} (hv : b.Reachable v) : I v := by
  induction hv with
  | base hmem hcfg => exact hbase _ hmem hcfg
  | unary _ hr hcfg hw ih => rw [hw]; exact hunary _ _ ih hr (hw ▸ hcfg)
  | binary _ _ hr hcfg hw ih₁ ih₂ => rw [hw]; exact hbinary _ _ _ ih₁ ih₂ hr (hw ▸ hcfg)

/- ### Hypotheses and main reduction theorem -/

/-- **Uniform computability of checking a separating semilinear inductive invariant**
(via uniform decidability of Presburger arithmetic `Th(ℕ, +, 0, 1, ≤)`):
given a BVAS instance `(d, b, t)` and an encoded semilinear set `S : List (List ℕ × List (List ℕ))`,
the predicate asserting that `S` contains all valid base vectors of `b`, is closed under all unary
and binary rules of `b`, and excludes `t` is computable. -/
def H1 : Prop :=
  ComputablePred fun x : (Σ d : ℕ, Bvas d × (Fin d → ℤ)) × List (List ℕ × List (List ℕ)) =>
    let d := x.1.1
    let b := x.1.2.1
    let t := x.1.2.2
    let mem : (Fin d → ℤ) → Prop := fun v =>
      ∃ bp ∈ x.2, ∃ c : Fin bp.2.length → ℕ,
        ∀ i : Fin d, v i = (bp.1.getD i.1 0 : ℤ) +
          ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ)
    (∀ v ∈ b.1, 0 ≤ v → mem v) ∧
    (∀ v r, mem v → r ∈ b.unaryRules → 0 ≤ v + r → mem (v + r)) ∧
    (∀ v₁ v₂ r, mem v₁ → mem v₂ → r ∈ b.binaryRules → 0 ≤ v₁ + v₂ + r → mem (v₁ + v₂ + r)) ∧
    ¬ mem t

/-- **Completeness of separating semilinear inductive invariants for BVAS**
(Bizière–Leroux–Sutre 2026, `arXiv:2607.09558`):
for every dimension `d`, BVAS `b : Bvas d`, and unreachable target `t : Fin d → ℤ`, there exists
an encoded semilinear set `S : List (List ℕ × List (List ℕ))` that contains all valid base vectors,
is closed under all unary and binary rules, and excludes `t`. -/
def H2 : Prop :=
  ∀ (d : ℕ) (b : Bvas d) (t : Fin d → ℤ), ¬ b.Reachable t →
    ∃ S : List (List ℕ × List (List ℕ)),
      let mem : (Fin d → ℤ) → Prop := fun v =>
        ∃ bp ∈ S, ∃ c : Fin bp.2.length → ℕ,
          ∀ i : Fin d, v i = (bp.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ)
      (∀ v ∈ b.1, 0 ≤ v → mem v) ∧
      (∀ v r, mem v → r ∈ b.unaryRules → 0 ≤ v + r → mem (v + r)) ∧
      (∀ v₁ v₂ r, mem v₁ → mem v₂ → r ∈ b.binaryRules → 0 ≤ v₁ + v₂ + r → mem (v₁ + v₂ + r)) ∧
      ¬ mem t

theorem main : H1 → H2 → type_of% @BranchingVAS.reachability_decidable := by
  intro h1 h2
  rw [ComputablePred.computable_iff_re_compl_re']
  refine ⟨rePred_reachable, ?_⟩
  obtain ⟨f, hf_comp, hf_eq⟩ := ComputablePred.computable_iff.mp h1
  let decodeS : ℕ → SemilinearCode := fun n => (Encodable.decode (α := SemilinearCode) n).getD []
  let checkCode : Input → ℕ → Bool := fun p n => f (p, decodeS n)
  have hdecodeS : Primrec decodeS :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const ([] : SemilinearCode))
  have hcheck_comp : Computable₂ checkCode := by
    change Computable (fun q : Input × ℕ => f (q.1, decodeS q.2))
    exact hf_comp.comp
      (Computable.pair (Computable.fst (α := Input) (β := ℕ))
        (hdecodeS.to_comp.comp (Computable.snd (α := Input) (β := ℕ))))
  have hpart : Partrec (fun p : Input =>
      Nat.rfind (fun n => (Part.some (checkCode p n) : Part Bool))) :=
    Partrec.rfind hcheck_comp.partrec
  refine (Partrec.dom_re hpart).of_eq fun p => ?_
  rcases p with ⟨d, b, t⟩
  change (Nat.rfind (fun n : ℕ => (Part.some (checkCode ⟨d, b, t⟩ n) : Part Bool))).Dom ↔
    ¬ b.Reachable t
  rw [Nat.rfind_dom (p := fun n : ℕ => (Part.some (checkCode ⟨d, b, t⟩ n) : Part Bool))]
  constructor
  · rintro ⟨n, hn, -⟩
    have hft : f (⟨d, b, t⟩, decodeS n) = true := (Part.mem_some_iff.mp hn).symm
    have hsep : (let mem : (Fin d → ℤ) → Prop := fun v =>
        ∃ bp ∈ decodeS n, ∃ c : Fin bp.2.length → ℕ,
          ∀ i : Fin d, v i = (bp.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ)
        (∀ v ∈ b.1, 0 ≤ v → mem v) ∧
        (∀ v r, mem v → r ∈ b.unaryRules → 0 ≤ v + r → mem (v + r)) ∧
        (∀ v₁ v₂ r, mem v₁ → mem v₂ → r ∈ b.binaryRules → 0 ≤ v₁ + v₂ + r → mem (v₁ + v₂ + r)) ∧
        ¬ mem t) := by
      have hprop := congrFun hf_eq (⟨d, b, t⟩, decodeS n)
      exact of_eq_true (by rw [hprop, hft]; simp)
    intro hreach
    exact hsep.2.2.2 (reachable_mem_of_invariant b _ hsep.1 hsep.2.1 hsep.2.2.1 hreach)
  · intro hnot
    obtain ⟨S, hsep⟩ := h2 d b t hnot
    refine ⟨Encodable.encode S, ?_, fun {m} _ => trivial⟩
    have hdecS : decodeS (Encodable.encode S) = S := by
      dsimp [decodeS]
      rw [Encodable.encodek]
      rfl
    have hprop := congrFun hf_eq (⟨d, b, t⟩, S)
    have hft : f (⟨d, b, t⟩, S) = true := by
      have htrue : (f (⟨d, b, t⟩, S) : Prop) := hprop ▸ hsep
      simpa using htrue
    exact Part.mem_some_iff.mpr (by dsimp [checkCode]; rw [hdecS, hft])

end OMA.R_BranchingVAS_reachability_decidable_R1
