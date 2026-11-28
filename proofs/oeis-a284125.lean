-- The source module defines occurrences directly by their starting positions.
import OMAStatements.S_oeis_a284125

-- Problem: OEIS A284125. Credit: @dkkn96.
-- Count first occurrences of terminal patterns of length three and two.
-- This is a finite-state specialization of Guibas and Odlyzko's analysis of
-- string overlaps (J. Combin. Theory Ser. A 30 (1981), 183–208).
namespace A284125Proof

open OMA.S_oeis_a284125
abbrev Bit := Fin 2
abbrev Word (n : ℕ) := Fin n → Bit
abbrev Pair := Bit × Bit
abbrev Triple := Bit × Pair

private def atBit {n : ℕ} (w : Word n) (i : ℕ) : Bit := if h : i < n then w ⟨i,h⟩ else 0
private def pairAt {n : ℕ} (w : Word n) (i : ℕ) : Pair := (atBit w i,atBit w (i+1))
private def tripleAt {n : ℕ} (w : Word n) (i : ℕ) : Triple := (atBit w i,pairAt w (i+1))
private def rep {n : ℕ} (w : Word n) (l : ℕ) := ∃ i < n-l, ∀ j < l, atBit w (i+j) = atBit w (n-l+j)

private theorem rep_iff {n l : ℕ} (w : Word n) : sufAppearsTwice n l w ↔ rep w l := by
  constructor
  · rintro ⟨hl,i,hi,h⟩
    refine ⟨i,hi,?_⟩
    intro j hj
    simpa [atBit,show (i:ℕ)+j < n by omega,show n-l+j<n by omega] using h ⟨j,hj⟩
  · rintro ⟨i,hi,h⟩
    refine ⟨by omega,⟨i,by omega⟩,hi,?_⟩
    intro j
    simpa [atBit,show i+j.val<n by omega,show n-l+j.val<n by omega] using h j.val j.isLt

private theorem rep_mono {n : ℕ} (w : Word n) {k l : ℕ} (hkl : k ≤ l) : rep w l → rep w k := by
  rintro ⟨i,hi,h⟩
  refine ⟨i+(l-k),by omega,?_⟩
  intro j hj
  convert h (l-k+j) (by omega) using 2 <;> omega

private def clean (tr : Bool) (n : ℕ) (w : Word (n+3)) : Prop :=
  if tr then ∀ i < n, tripleAt w i ≠ tripleAt w n
  else ∀ i < n+1, pairAt w i ≠ pairAt w (n+1)

private theorem clean_iff_true {n : ℕ} (w : Word (n+3)) : clean true n w ↔ ¬ rep w 3 := by
  simp only [clean,if_true,rep, Nat.add_sub_cancel]
  constructor
  · rintro good ⟨i,hi,h⟩
    apply good i hi
    exact Prod.ext (by simpa [tripleAt] using h 0 (by decide)) (Prod.ext (h 1 (by decide)) (by simpa [tripleAt,pairAt,Nat.add_assoc] using h 2 (by decide)))
  · intro good i hi eqn
    apply good; refine ⟨i,hi,?_⟩
    intro j hj; interval_cases j
    · simpa [tripleAt] using congrArg Prod.fst eqn
    · exact congrArg (fun t : Triple => t.2.1) eqn
    · exact congrArg (fun t : Triple => t.2.2) eqn

private theorem clean_iff_false {n : ℕ} (w : Word (n+3)) : clean false n w ↔ ¬ rep w 2 := by
  simp only [clean,Bool.false_eq_true,if_false,rep,show n+3-2=n+1 by omega]
  constructor
  · rintro good ⟨i,hi,h⟩
    apply good i hi
    exact Prod.ext (by simpa [pairAt] using h 0 (by decide)) (h 1 (by decide))
  · intro good i hi eqn
    apply good; refine ⟨i,hi,?_⟩
    intro j hj; interval_cases j
    · simpa [pairAt] using congrArg Prod.fst eqn
    · exact congrArg Prod.snd eqn

private theorem valid_iff {n : ℕ} (w : Word (n+3)) :
    valid (n+3) w ↔ clean true n w ∧ ¬clean false n w := by
  rw [clean_iff_true,clean_iff_false,not_not]
  constructor
  · rintro ⟨pair,no⟩
    refine ⟨?_,(rep_iff w).mp pair⟩
    intro three
    obtain ⟨i,hi,hh⟩ := three
    exact no ⟨3,by omega⟩ (by change 2<3; decide) ((rep_iff w).mpr ⟨i,hi,hh⟩)
  · rintro ⟨no,pair⟩
    refine ⟨(rep_iff w).mpr pair,?_⟩
    intro l hl hr
    exact no (rep_mono w (by omega : 3 ≤ l.val) ((rep_iff w).mp hr))

private theorem clean_imp {n : ℕ} (w : Word (n+3)) : clean false n w → clean true n w := by
  rw [clean_iff_false,clean_iff_true]; exact fun h ht => h (rep_mono w (by decide) ht)

private abbrev Weight := Bool → Triple → Pair → ℚ
private def oneW : Weight := fun tr _ _ => if tr then 1 else -1
private def allowed (tr : Bool) (t : Triple) (c : Bit) (h : Pair) : Bool :=
  if tr then decide ((c,h) ≠ t) else decide ((c,h.1) ≠ t.2)
private def stepW (W : Weight) : Weight := fun tr t h =>
  (if allowed tr t 0 h then W tr t (0,h.1) else 0) +
  (if allowed tr t 1 h then W tr t (1,h.1) else 0)

noncomputable section
open Classical in
private def valW (n : ℕ) (W : Weight) : ℚ :=
  ∑ w : Word (n+3),
    ((if clean true n w then W true (tripleAt w n) (pairAt w 0) else 0) +
    (if clean false n w then W false (tripleAt w n) (pairAt w 0) else 0))

private theorem at_cons {n : ℕ} (w : Word n) (c : Bit) (i : ℕ) :
    atBit (Fin.cons c w) (i+1) = atBit w i := by
  unfold atBit; by_cases h : i<n
  · simp [h,show i+1<n+1 by omega]; rfl
  · simp [h,show ¬i+1<n+1 by omega]

private theorem at_cons_zero {n : ℕ} (w : Word n) (c : Bit) : atBit (Fin.cons c w) 0 = c := by
  simp [atBit, Fin.cons_zero]

private theorem pair_cons {n : ℕ} (w : Word n) (c : Bit) (i : ℕ) :
    pairAt (Fin.cons c w) (i+1) = pairAt w i := by simp [pairAt,at_cons]
private theorem triple_cons {n : ℕ} (w : Word n) (c : Bit) (i : ℕ) :
    tripleAt (Fin.cons c w) (i+1) = tripleAt w i := by simp [tripleAt,pair_cons,at_cons]
private theorem pair_cons_zero {n : ℕ} (w : Word n) (c : Bit) :
    pairAt (Fin.cons c w) 0 = (c,atBit w 0) := by simp [pairAt,at_cons_zero,at_cons]
private theorem triple_cons_zero {n : ℕ} (w : Word n) (c : Bit) :
    tripleAt (Fin.cons c w) 0 = (c,pairAt w 0) := by simp [tripleAt,at_cons_zero,pair_cons]

private theorem all_succ (n : ℕ) (p : ℕ → Prop) :
    (∀ i < n+1, p i) ↔ p 0 ∧ ∀ i < n, p (i+1) := by
  constructor
  · intro h; exact ⟨h 0 (by omega), fun i hi => h (i+1) (by omega)⟩
  · rintro ⟨h0,h⟩ (_|i) hi
    · exact h0
    · exact h i (by omega)

private theorem clean_cons (tr : Bool) {n : ℕ} (w : Word (n+3)) (c : Bit) :
    clean tr (n+1) (Fin.cons c w) ↔
      allowed tr (tripleAt w n) c (pairAt w 0) ∧ clean tr n w := by
  cases tr <;> simp only [clean,allowed,Bool.false_eq_true,if_false,if_true,decide_eq_true_eq,
    pair_cons,triple_cons] <;> rw [all_succ] <;>
    simp only [tripleAt,pairAt,at_cons,at_cons_zero]

private theorem seq_val (n : ℕ) : (a (n+3) : ℚ) = valW n oneW := by
  classical
  change ((Finset.univ.filter (valid (n+3))).card : ℚ) = _
  rw [Finset.natCast_card_filter]; unfold valW
  apply Finset.sum_congr rfl
  intro w _
  dsimp [oneW]
  simp only [valid_iff]
  by_cases h : clean false n w
  · simp [h,clean_imp w h]
  · simp [h]

private theorem sum_cons (n : ℕ) (f : Word (n+1) → ℚ) :
    ∑ w, f w = ∑ v : Word n, (f (Fin.cons 0 v) + f (Fin.cons 1 v)) := by
  have eqn := (Fin.consEquiv (fun _ : Fin (n+1) => Bit)).sum_comp f
  rw [← eqn,Fintype.sum_prod_type,Fin.sum_univ_two,← Finset.sum_add_distrib]
  rfl

private theorem val_step (n : ℕ) (W : Weight) : valW (n+1) W = valW n (stepW W) := by
  classical
  unfold valW
  rw [sum_cons]
  apply Finset.sum_congr rfl
  intro w _
  simp only [clean_cons,triple_cons,pair_cons_zero,stepW]
  by_cases h3 : clean true n w <;> by_cases h2 : clean false n w <;>
    simp [h3,h2,pairAt]
  all_goals ring

private def iterW : ℕ → Weight
  | 0 => oneW
  | m+1 => stepW (iterW m)

private theorem val_iter (n m : ℕ) : valW (n+m) oneW = valW n (iterW m) := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    rw [show n+(m+1)=(n+1)+m by omega,ih,val_step]; rfl

private def lin (n : ℕ) : Weight →ₗ[ℚ] ℚ where
  toFun := valW n
  map_add' W V := by
    classical
    unfold valW
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : clean true n w <;> by_cases g : clean false n w <;> simp [h,g]
    all_goals ring
  map_smul' c W := by
    classical
    unfold valW
    simp only [RingHom.id_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : clean true n w <;> by_cases g : clean false n w <;> simp [h,g]
    all_goals ring

private def initialW (W : Weight) : ℚ :=
  ∑ w : Word 3, (W true (tripleAt w 0) (pairAt w 0) +
    if pairAt w 0 ≠ pairAt w 1 then W false (tripleAt w 0) (pairAt w 0) else 0)

private theorem lin_zero (W : Weight) : lin 0 W = initialW W := by
  classical
  change valW 0 W = _
  simp [valW,initialW,clean]

private theorem expansion (n m : ℕ) : (a (n+m+3) : ℚ) = lin n (iterW m) :=
  (seq_val _).trans (val_iter n m)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1500000 in
private theorem states : ∀ tr t h,
    iterW 10 tr t h - 6*iterW 9 tr t h + 13*iterW 8 tr t h - 12*iterW 7 tr t h +
    5*iterW 6 tr t h - 3*iterW 5 tr t h + 2*iterW 4 tr t h + iterW 1 tr t h - iterW 0 tr t h = 0 := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1500000 in
private theorem first : ∀ i : Fin 10, initialW (iterW i) = ![2,4,12,26,52,98,178,316,556,972] i := by
  decide +kernel

private theorem initial : ∀ j : Fin 13, (a j : ℚ) = ![0,0,0,2,4,12,26,52,98,178,316,556,972] j := by
  intro j
  by_cases h : (j:ℕ)<3
  · obtain hj | hj | hj : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
    · obtain rfl : j = 0 := Fin.ext hj; decide +kernel
    · obtain rfl : j = 1 := Fin.ext hj; decide +kernel
    · obtain rfl : j = 2 := Fin.ext hj; decide +kernel
  · let i : Fin 10 := ⟨j-3,by omega⟩
    have eqn : 0+i.val+3 = j.val := by dsimp [i]; omega
    have e := expansion 0 i.val
    rw [eqn,lin_zero,first i] at e
    convert e using 1
    fin_cases j <;> first | contradiction | rfl

private theorem recurrence (n : ℕ) :
    (a (n+13):ℚ) - 6*a (n+12) + 13*a (n+11) - 12*a (n+10) + 5*a (n+9) -
      3*a (n+8) + 2*a (n+7) + a (n+4) - a (n+3) = 0 := by
  have rel : iterW 10 - (6:ℚ) • iterW 9 + (13:ℚ) • iterW 8 - (12:ℚ) • iterW 7 +
      (5:ℚ) • iterW 6 - (3:ℚ) • iterW 5 + (2:ℚ) • iterW 4 + iterW 1 - iterW 0 = 0 := by
    funext tr t h; exact states tr t h
  have eqn := congrArg (lin n) rel
  simp only [map_sub,map_add,map_smul,map_zero,smul_eq_mul] at eqn
  rw [expansion n 10,expansion n 9,expansion n 8,expansion n 7,expansion n 6,expansion n 5,
    expansion n 4,expansion n 1,expansion n 0]
  exact eqn

end
end A284125Proof

namespace A284125Proof

open PowerSeries

theorem finishGF (b : ℕ → ℚ)
    (init : ∀ j : Fin 13, b j = ![0, 0, 0, 2, 4, 12, 26, 52, 98, 178, 316, 556, 972] j)
    (rec : ∀ n : ℕ, b (n+13) - 6*b (n+12) + 13*b (n+11) - 12*b (n+10) + 5*b (n+9) - 3*b (n+8) + 2*b (n+7) + b (n+4) - b (n+3) = 0) :
    PowerSeries.mk b * ((1 - X) ^ 2 * (1 - X - X ^ 2) * (1 - 2 * X + X ^ 2 - X ^ 3) * (1 - X - X ^ 2 - X ^ 3)) =
      2 * X ^ 3 * (1 + X ^ 2) * (1 - 4 * X + 6 * X ^ 2 - 5 * X ^ 3 + X ^ 4 + 2 * X ^ 5 + 2 * X ^ 6 - 2 * X ^ 7) := by
  let f := PowerSeries.mk b
  change f * _ = _
  have lhs : f * ((1 - X) ^ 2 * (1 - X - X ^ 2) * (1 - 2 * X + X ^ 2 - X ^ 3) * (1 - X - X ^ 2 - X ^ 3)) =
      f - 6 • (f*X^1) + 13 • (f*X^2) - 12 • (f*X^3) + 5 • (f*X^4) - 3 • (f*X^5) + 2 • (f*X^6) + f*X^9 - f*X^10 := by
    simp only [nsmul_eq_mul]; ring
  have rhs : (2 * X ^ 3 * (1 + X ^ 2) * (1 - 4 * X + 6 * X ^ 2 - 5 * X ^ 3 + X ^ 4 + 2 * X ^ 5 + 2 * X ^ 6 - 2 * X ^ 7) : PowerSeries ℚ) =
      2 • X^3 - 8 • X^4 + 14 • X^5 - 18 • X^6 + 14 • X^7 - 6 • X^8 + 6 • X^9 + 4 • X^11 - 4 • X^12 := by
    simp only [nsmul_eq_mul]; ring
  rw [lhs, rhs]
  ext n
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow, f, coeff_mk]
  simp only [nsmul_eq_mul]
  by_cases hn : n < 13
  · have h0 : b 0 = 0 := init 0
    have h1 : b 1 = 0 := init 1
    have h2 : b 2 = 0 := init 2
    have h3 : b 3 = 2 := init 3
    have h4 : b 4 = 4 := init 4
    have h5 : b 5 = 12 := init 5
    have h6 : b 6 = 26 := init 6
    have h7 : b 7 = 52 := init 7
    have h8 : b 8 = 98 := init 8
    have h9 : b 9 = 178 := init 9
    have h10 : b 10 = 316 := init 10
    have h11 : b 11 = 556 := init 11
    have h12 : b 12 = 972 := init 12
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k+13 := ⟨n-13, by omega⟩
    simpa (disch := omega) [Nat.add_sub_assoc] using rec k

end A284125Proof


theorem OMA.solution : type_of% @OMA.S_oeis_a284125.main :=
  A284125Proof.finishGF _ A284125Proof.initial A284125Proof.recurrence
