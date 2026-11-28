import OMAStatements.S_oeis_a208286
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.Sort
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Binary arrays of width seven with forbidden triples

This proves Colin Barker's two conjectures for R. H. Hardin's OEIS A208286
(https://oeis.org/A208286). The first two rows determine the local
restriction on the next row. Exactly 42 of the 128 rows meet the horizontal
restriction. The 1,764 admissible row pairs admit a partition into 30
classes such that each pair in the same class has the same multiset of
successor classes. The finite certificate checks this property and the
vanishing eighth difference for each class. Linearity gives the recurrence
at every height, and a coefficient calculation verifies the numerator.
We also give the ordinary and shifted-binomial forms of the count.
-/

namespace Rows286

abbrev Row := Fin 7 → Fin 2

/-- A horizontal forbidden triple begins with two zeroes. -/
def horiz (r : Row) : Bool :=
  decide ((r 0 ≠ 0 ∨ r 1 ≠ 0) ∧ (r 1 ≠ 0 ∨ r 2 ≠ 0) ∧ (r 2 ≠ 0 ∨ r 3 ≠ 0) ∧
    (r 3 ≠ 0 ∨ r 4 ≠ 0) ∧ (r 4 ≠ 0 ∨ r 5 ≠ 0))

/-- In a column, two consecutive equal bits force the following bit. -/
def vert (u v w : Row) : Bool :=
  decide (∀ j : Fin 7, u j=v j → v j=w j)

/-- Count continuations after the two specified rows. -/
def D : ℕ → Row → Row → ℤ
  | 0, u, v => if horiz u && horiz v then 1 else 0
  | t+1, u, v => if horiz u then ∑ w : Row, if vert u v w then D t v w else 0 else 0

def total (t : ℕ) : ℤ := ∑ u : Row, ∑ v : Row, D t u v

end Rows286

namespace Rows286

abbrev Small := Fin 42

/-- The admissible rows in increasing order of their little-endian binary code. -/
def codes : Array ℕ := #[21,22,23,26,27,29,30,31,42,43,45,46,47,53,54,55,58,59,61,62,63,85,86,87,90,91,93,94,95,106,107,109,110,111,117,118,119,122,123,125,126,127]

def bits (i : Small) (j : Fin 7) : Fin 2 :=
  ⟨(codes[i.val]! / 2^j.val)%2,Nat.mod_lt _ (by decide)⟩

def allow (i j k : Small) : Bool := vert (bits i) (bits j) (bits k)

def smallD : ℕ → Small → Small → ℤ
  | 0, _, _ => 1
  | t+1, i, j => ∑ k : Small, if allow i j k then smallD t j k else 0

def smallTotal (t : ℕ) : ℤ := ∑ i : Small,∑ j : Small,smallD t i j

end Rows286

namespace Rows286

open OMA.S_oeis_a208286

private def rowValue (u : Row) (j : ℕ) : ℕ :=
  if h : j < 7 then (u ⟨j,h⟩).val else 0

private theorem get_rowValue {r i : ℕ} (x : Fin r → Row) (hi : i < r) (j : ℕ) :
    get x i j = rowValue (x ⟨i,hi⟩) j := by
  by_cases h : j < 7 <;> simp [OMA.S_oeis_a208286.get, rowValue, hi, h]

private theorem horiz_bits : ∀ a b c : Fin 2,
    ((a.val,b.val,c.val) ≠ (0,0,0) ∧ (a.val,b.val,c.val) ≠ (0,0,1)) ↔
      a ≠ 0 ∨ b ≠ 0 := by decide

private theorem vert_bits : ∀ a b c : Fin 2,
    ((a.val,b.val,c.val) ≠ (0,0,1) ∧ (a.val,b.val,c.val) ≠ (1,1,0)) ↔
      (a = b → b = c) := by decide

private theorem horiz_windows (u : Row) :
    horiz u = true ↔ ∀ j < 5,
      (rowValue u j, rowValue u (j+1), rowValue u (j+2)) ≠ (0,0,0) ∧
      (rowValue u j, rowValue u (j+1), rowValue u (j+2)) ≠ (0,0,1) := by
  simp only [horiz, decide_eq_true_eq]
  constructor
  · intro h j hj
    interval_cases j
    · exact (horiz_bits (u 0) (u 1) (u 2)).mpr h.1
    · exact (horiz_bits (u 1) (u 2) (u 3)).mpr h.2.1
    · exact (horiz_bits (u 2) (u 3) (u 4)).mpr h.2.2.1
    · exact (horiz_bits (u 3) (u 4) (u 5)).mpr h.2.2.2.1
    · exact (horiz_bits (u 4) (u 5) (u 6)).mpr h.2.2.2.2
  · intro h
    exact ⟨(horiz_bits (u 0) (u 1) (u 2)).mp (h 0 (by decide)),
      (horiz_bits (u 1) (u 2) (u 3)).mp (h 1 (by decide)),
      (horiz_bits (u 2) (u 3) (u 4)).mp (h 2 (by decide)),
      (horiz_bits (u 3) (u 4) (u 5)).mp (h 3 (by decide)),
      (horiz_bits (u 4) (u 5) (u 6)).mp (h 4 (by decide))⟩

private theorem vert_windows (u v w : Row) :
    vert u v w = true ↔ ∀ j < 7,
      (rowValue u j, rowValue v j, rowValue w j) ≠ (0,0,1) ∧
      (rowValue u j, rowValue v j, rowValue w j) ≠ (1,1,0) := by
  simp only [vert, decide_eq_true_eq]
  constructor
  · intro h j hj
    simpa only [rowValue, dif_pos hj] using
      (vert_bits (u ⟨j,hj⟩) (v ⟨j,hj⟩) (w ⟨j,hj⟩)).mpr (h ⟨j,hj⟩)
  · intro h j
    apply (vert_bits (u j) (v j) (w j)).mp
    simpa only [rowValue, dif_pos j.isLt] using h j.val j.isLt

private theorem avoids_windows {r : ℕ} (x : Fin r → Row) :
    avoids x = true ↔
      (∀ i : Fin r, horiz (x i) = true) ∧
      (∀ (i : ℕ) (hi : i + 2 < r), vert (x ⟨i,by omega⟩)
        (x ⟨i+1,by omega⟩) (x ⟨i+2,hi⟩) = true) := by
  simp only [avoids, decide_eq_true_eq]
  constructor
  · rintro ⟨hh,hv⟩
    constructor
    · intro i
      apply (horiz_windows _).mpr
      simpa only [get_rowValue x i.isLt] using hh i.val i.isLt
    · intro i hi
      apply (vert_windows _ _ _).mpr
      simpa only [get_rowValue x (show i < r by omega),
        get_rowValue x (show i+1 < r by omega), get_rowValue x hi] using
        hv i (by omega)
  · rintro ⟨hh,hv⟩
    constructor
    · intro i hi
      simpa only [get_rowValue x hi] using (horiz_windows _).mp (hh ⟨i,hi⟩)
    · intro i hi
      have h2 : i+2 < r := by omega
      simpa only [get_rowValue x (show i < r by omega),
        get_rowValue x (show i+1 < r by omega), get_rowValue x h2] using
        (vert_windows _ _ _).mp (hv i h2)

theorem avoids_cons {t : ℕ} (u : Row) (x : Fin (t+2) → Row) :
    avoids (Fin.cons u x) = true ↔
      horiz u = true ∧ vert u (x 0) (x 1) = true ∧ avoids x = true := by
  have hone : (1 : Fin (t+2)) = ⟨1, by omega⟩ := by
    apply Fin.ext
    change 1 % (t + 2) = 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [hone, avoids_windows, avoids_windows]
  constructor
  · rintro ⟨hh,hv⟩
    refine ⟨hh 0, ?_, ?_, ?_⟩
    · have top := hv 0 (by omega)
      exact top
    · intro i
      exact hh i.succ
    · intro i hi
      exact hv (i+1) (by omega)
  · rintro ⟨hu, ht, hh, hv⟩
    constructor
    · exact Fin.forall_fin_succ.mpr ⟨hu,hh⟩
    · rintro (_|i) hi
      · exact ht
      · exact hv i (by omega)

theorem avoids_two (u v : Row) :
    avoids ![u,v] = true ↔ horiz u = true ∧ horiz v = true := by
  rw [avoids_windows]
  constructor
  · intro h
    exact ⟨h.1 0, h.1 1⟩
  · rintro ⟨hu,hv⟩
    constructor
    · intro i
      fin_cases i <;> assumption
    · intro i hi
      omega

theorem avoids_one (u : Row) : avoids ![u] = true ↔ horiz u = true := by
  rw [avoids_windows]
  constructor
  · exact fun h => h.1 0
  · intro hu
    constructor
    · intro i
      fin_cases i
      exact hu
    · intro i hi
      omega

end Rows286

namespace Rows286
open Finset

theorem sum_cons_rows {t : ℕ} (f : (Fin (t+1) → Row) → ℤ) :
    ∑ x,f x = ∑ u : Row,∑ y : Fin t → Row,f (Fin.cons u y) := by
  rw [←(Fin.consEquiv (fun _ : Fin (t+1) => Row)).sum_comp f,Fintype.sum_prod_type]
  rfl

/-- The sums over all continuations of two prescribed rows agree with the
finite-state recurrence whenever the two local decomposition laws hold. -/
theorem count_continuations (P : {r : ℕ} → (Fin r → Row) → Bool)
    (step : ∀ {t : ℕ} (u : Row) (x : Fin (t+2) → Row), P (Fin.cons u x) = true ↔
      horiz u=true ∧ vert u (x 0) (x 1)=true ∧ P x=true)
    (pair : ∀ u v : Row, P ![u,v]=true ↔ horiz u=true ∧ horiz v=true)
    (t : ℕ) (u v : Row) :
    (∑ y : Fin t → Row, if P (Fin.cons u (Fin.cons v y)) then (1:ℤ) else 0)=D t u v := by
  induction t generalizing u v with
  | zero =>
    have he (y : Fin 0 → Row) : Fin.cons u (Fin.cons v y) = ![u,v] := by
      funext i; fin_cases i <;> rfl
    simp only [he,pair,D,Bool.and_eq_true]
    simp
  | succ t ih =>
    rw [sum_cons_rows,D]
    have eqv (w : Row) (y : Fin t → Row) : P (Fin.cons u (Fin.cons v (Fin.cons w y)))=true ↔
        horiz u=true ∧ vert u v w=true ∧ P (Fin.cons v (Fin.cons w y))=true := by
      simpa only [Fin.cons_zero,show (1 : Fin (t+2))=Fin.succ 0 by rfl,Fin.cons_succ] using
        step u (Fin.cons v (Fin.cons w y))
    simp only [eqv]
    by_cases hu : horiz u=true
    · simp only [hu,true_and,if_true]
      apply sum_congr rfl
      intro w _
      by_cases hw : vert u v w=true
      · simpa only [hw,if_true,true_and] using ih v w
      · simp [hw]
    · simp [hu]

theorem count_all_rows (P : {r : ℕ} → (Fin r → Row) → Bool)
    (step : ∀ {t : ℕ} (u : Row) (x : Fin (t+2) → Row), P (Fin.cons u x) = true ↔
      horiz u=true ∧ vert u (x 0) (x 1)=true ∧ P x=true)
    (pair : ∀ u v : Row, P ![u,v]=true ↔ horiz u=true ∧ horiz v=true)
    (t : ℕ) : (↑((univ.filter fun x : Fin (t+2) → Row => P x).card):ℤ) = total t := by
  have base : (↑((univ.filter fun x : Fin (t+2) → Row => P x).card):ℤ) =
      ∑ x : Fin (t+2) → Row,if P x then (1:ℤ) else 0 := by
    simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [base,sum_cons_rows]
  unfold total
  apply sum_congr rfl
  intro u _
  rw [sum_cons_rows]
  exact sum_congr rfl (fun v _ => count_continuations P step pair t u v)

theorem count_one_row (P : (Fin 1 → Row) → Bool)
    (one : ∀ u : Row, P ![u]=true ↔ horiz u=true) :
    (↑((univ.filter fun x : Fin 1 → Row => P x).card):ℤ) = 42 := by
  have base : (↑((univ.filter fun x : Fin 1 → Row => P x).card):ℤ) =
    ∑ x : Fin 1 → Row,if P x then (1:ℤ) else 0 := by
    simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [base,sum_cons_rows]
  have he (u : Row) (y : Fin 0 → Row) : Fin.cons u y = ![u] := by
    funext i; fin_cases i; rfl
  simp only [he,one]
  have h : (∑ u : Row,if horiz u then (1:ℤ) else 0)=42 := by decide +kernel
  simpa using h

end Rows286

namespace Rows286
open Finset

theorem bits_valid (i : Small) : horiz (bits i)=true := by
  revert i
  decide +kernel

set_option maxRecDepth 10000 in
theorem bits_injective : Function.Injective bits := by
  have h : ∀ i j : Small, bits i=bits j → i=j := by decide +kernel
  exact fun {i j} => h i j

theorem encoded_rows :
    univ.image bits = univ.filter (fun r : Row => horiz r=true) := by
  have hc : (univ.filter (fun r : Row => horiz r=true)).card=42 := by decide +kernel
  apply eq_of_subset_of_card_le
  · intro r hr
    obtain ⟨i,_,rfl⟩ := mem_image.mp hr
    exact mem_filter.mpr ⟨mem_univ _,bits_valid i⟩
  · rw [hc,card_image_of_injective _ bits_injective,card_univ,Fintype.card_fin]

theorem sum_encoded (f : Row → ℤ) (vanish : ∀ r, horiz r≠true → f r=0) :
    ∑ r : Row,f r = ∑ i : Small,f (bits i) := by
  calc
    _ = ∑ r ∈ univ.image bits,f r := by
      symm
      apply sum_subset (subset_univ _)
      intro r _ hr
      apply vanish
      intro h
      exact hr (encoded_rows ▸ mem_filter.mpr ⟨mem_univ _,h⟩)
    _ = _ := sum_image (fun _ _ _ _ h => bits_injective h)

theorem invalid_state (t : ℕ) (u v : Row) (h : horiz u≠true ∨ horiz v≠true) : D t u v=0 := by
  induction t generalizing u v with
  | zero => rcases h with h|h <;> simp [D,h]
  | succ t ih =>
    rcases h with h|h
    · simp [D,h]
    · rw [D]
      split_ifs
      · apply sum_eq_zero
        intro w _
        simp [ih v w (Or.inl h)]
      · rfl

theorem D_encoded (t : ℕ) (i j : Small) : D t (bits i) (bits j)=smallD t i j := by
  induction t generalizing i j with
  | zero => simp [D,smallD,bits_valid]
  | succ t ih =>
    rw [D,if_pos (bits_valid i),smallD,sum_encoded]
    · apply sum_congr rfl
      intro k _
      by_cases ha : vert (bits i) (bits j) (bits k)=true <;> simp [allow,ih,ha]
    · intro w hw
      simp [invalid_state t (bits j) w (Or.inr hw)]

theorem total_encoded (t : ℕ) : total t=smallTotal t := by
  unfold total smallTotal
  rw [sum_encoded]
  · apply sum_congr rfl
    intro i _
    rw [sum_encoded]
    · exact sum_congr rfl (fun j _ => D_encoded t i j)
    · intro r hr
      exact invalid_state t (bits i) r (Or.inr hr)
  · intro r hr
    exact sum_eq_zero (fun v _ => invalid_state t r v (Or.inl hr))

end Rows286

namespace Rows286

/-- Partition the row pairs according to the multiset of their successor classes. -/
private def kindTable : Array ℕ := #[
  1059652570653887983355799069424210729961194617551465818978617376,
  1050315087304984510785757962505759149672250041493842451808421889,
  701649096474575023015499792264698719335309305911879047759167554,
  1050204953276863473066144169779387464397290320069640271232504867,
  701237661572135210382458072031592671949721799651766433130546357,
  688090872707667362359479977160222255655267273589863240810797218,
  678762510772204705820606082279225555826714536920176187131631685,
  330096519941794624319358467533964238860390899796294525822109894,
  1050204950111312026955961262442180417061712247497135426651597927,
  701237658390120820242295886536122677997689622800224726935571836,
  688090860674874301131477287976999282176919653032763742898446165,
  678762498136313512651705006899793295292307737177172899860242106,
  330096507286584434737551936380281057310814532775088896609769207,
  688087025456930616961845221575196557541250602106032395932506274,
  678749542247190478097775673875094703285909230926275714817890373,
  330083555870595569147197843982445756494789404814020895288199366,
  678639555195258955113921001134510804368061132705054451092762795,
  329676824204742603963571311470958411904454852007128756142675351,
  316676223147407721953161938242258241802219210873422467185751430,
  312017779703804641834507567389537488450553307084464480633173196,
  112797026989481249689651871615490418482267666505110283549579693,
  688087025456815107377455562957641876622459368079483768418965666,
  678749542247094774518947224485330099780975423954249616241891397,
  330083555870545757562340449524292457327644648619219332701227206,
  678639555194872741645256875640942506948862546024089168818286763,
  329676824204357216741570441243242502221638669737151647688365463,
  316676223147047978492006600148730023752017997257043408697668998,
  312017779703423634836023720492929799939437738378272695079089356,
  112797026989235340255520125956013971865965828743019316593990061,
  678639552077216215734785053511046101787473549202253316400269678,
  329676822545999117204988579988316986212493334034678205591727709,
  316676211358334548148747228013136094963981252716240949742528375,
  312017767218829922952578731492657291529574380703802547521349371,
  112797018931609835175680445779685073450921673229653772635594553,
  316673655681242192883074722907022484648973237598605939048002950,
  312004963139410121481208615147832783708659057965545267838465228,
  112788778554976726761576338491491314478520633127573353992395181,
  311949994108119322672648167421043910885833429815603987840454034,
  112535979795402967812606600614980966359020758980302288705729145,
  104453581426978520603676075150079171856334478958430786771800685,
  102903774677297049908973610127019923260398352867440846361252275,
  3317745867711757030774028390041119597138596019872912845190804
]

private def kind (i j : Small) : ℕ := ((kindTable[i.val]?.getD 0) / 2^(5*j.val)) % 32

/-- Thirty denotes an illegal successor; every legal class has a smaller label. -/
private def rowTags (i j : Small) : List ℕ :=
  List.ofFn fun k : Small => if allow i j k then kind j k else 30

private def outgoing : Array (List ℕ) := #[
  [0,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,2,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,2,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,2,2,3,4,5,6,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,1,2,21,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,2,2,5,6,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,2,2,6,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,2,2,2,3,4,4,5,5,6,6,6,7,8,9,10,10,11,12,13,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,1,2,2,3,3,4,5,5,6,22,28,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,1,1,2,2,5,5,5,6,21,22,22,23,26,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,1,2,2,5,5,6,21,23,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,2,2,2,3,4,5,5,6,6,6,10,11,12,13,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,2,2,2,5,5,6,6,6,12,13,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,2,2,2,6,6,6,13,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,2,2,2,2,3,4,4,5,5,5,6,6,6,6,6,6,7,8,9,10,10,10,10,11,11,12,12,12,13,13,13,13,14,15,16,17,17,18,19,20],
  [0,1,1,2,2,2,3,3,4,5,5,5,5,6,6,6,10,11,11,12,12,13,22,24,28,29,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,1,1,2,2,2,5,5,5,5,5,5,6,6,6,12,12,12,13,21,22,22,23,23,24,24,25,26,27,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,1,2,2,2,5,5,5,5,6,6,6,12,12,13,21,23,23,25,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,2,2,2,2,3,4,5,5,5,6,6,6,6,6,6,10,10,11,11,12,12,12,13,13,13,13,17,18,19,20,30,30,30,30,30,30,30,30,30,30],
  [0,1,2,2,2,2,5,5,5,6,6,6,6,6,6,12,12,12,13,13,13,13,19,20,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,2,2,2,2,6,6,6,6,6,6,13,13,13,13,20,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,2,2,4,6,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,1,2,2,5,5,6,22,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,2,2,2,4,6,6,6,10,13,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,1,2,2,2,5,5,5,5,6,6,6,12,12,13,22,24,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,2,2,2,2,4,6,6,6,6,6,6,10,10,13,13,13,13,17,20,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,2,2,2,4,5,5,6,6,6,9,10,12,13,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,1,2,2,2,2,4,5,5,5,6,6,6,6,6,6,9,10,10,12,12,12,13,13,13,13,16,17,19,20,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,2,2,2,4,4,6,6,6,8,10,10,13,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30],
  [0,2,2,2,2,4,4,6,6,6,6,6,6,8,10,10,10,10,13,13,13,13,15,17,17,20,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30,30]
]

private def grouped (c : ℕ) : List ℕ := outgoing[c]?.getD []

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_0 : ∀ j : Small,
    (rowTags 0 j).insertionSort (· ≤ ·) = grouped (kind 0 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_1 : ∀ j : Small,
    (rowTags 1 j).insertionSort (· ≤ ·) = grouped (kind 1 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_2 : ∀ j : Small,
    (rowTags 2 j).insertionSort (· ≤ ·) = grouped (kind 2 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_3 : ∀ j : Small,
    (rowTags 3 j).insertionSort (· ≤ ·) = grouped (kind 3 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_4 : ∀ j : Small,
    (rowTags 4 j).insertionSort (· ≤ ·) = grouped (kind 4 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_5 : ∀ j : Small,
    (rowTags 5 j).insertionSort (· ≤ ·) = grouped (kind 5 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_6 : ∀ j : Small,
    (rowTags 6 j).insertionSort (· ≤ ·) = grouped (kind 6 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_7 : ∀ j : Small,
    (rowTags 7 j).insertionSort (· ≤ ·) = grouped (kind 7 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_8 : ∀ j : Small,
    (rowTags 8 j).insertionSort (· ≤ ·) = grouped (kind 8 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_9 : ∀ j : Small,
    (rowTags 9 j).insertionSort (· ≤ ·) = grouped (kind 9 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_10 : ∀ j : Small,
    (rowTags 10 j).insertionSort (· ≤ ·) = grouped (kind 10 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_11 : ∀ j : Small,
    (rowTags 11 j).insertionSort (· ≤ ·) = grouped (kind 11 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_12 : ∀ j : Small,
    (rowTags 12 j).insertionSort (· ≤ ·) = grouped (kind 12 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_13 : ∀ j : Small,
    (rowTags 13 j).insertionSort (· ≤ ·) = grouped (kind 13 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_14 : ∀ j : Small,
    (rowTags 14 j).insertionSort (· ≤ ·) = grouped (kind 14 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_15 : ∀ j : Small,
    (rowTags 15 j).insertionSort (· ≤ ·) = grouped (kind 15 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_16 : ∀ j : Small,
    (rowTags 16 j).insertionSort (· ≤ ·) = grouped (kind 16 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_17 : ∀ j : Small,
    (rowTags 17 j).insertionSort (· ≤ ·) = grouped (kind 17 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_18 : ∀ j : Small,
    (rowTags 18 j).insertionSort (· ≤ ·) = grouped (kind 18 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_19 : ∀ j : Small,
    (rowTags 19 j).insertionSort (· ≤ ·) = grouped (kind 19 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_20 : ∀ j : Small,
    (rowTags 20 j).insertionSort (· ≤ ·) = grouped (kind 20 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_21 : ∀ j : Small,
    (rowTags 21 j).insertionSort (· ≤ ·) = grouped (kind 21 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_22 : ∀ j : Small,
    (rowTags 22 j).insertionSort (· ≤ ·) = grouped (kind 22 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_23 : ∀ j : Small,
    (rowTags 23 j).insertionSort (· ≤ ·) = grouped (kind 23 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_24 : ∀ j : Small,
    (rowTags 24 j).insertionSort (· ≤ ·) = grouped (kind 24 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_25 : ∀ j : Small,
    (rowTags 25 j).insertionSort (· ≤ ·) = grouped (kind 25 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_26 : ∀ j : Small,
    (rowTags 26 j).insertionSort (· ≤ ·) = grouped (kind 26 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_27 : ∀ j : Small,
    (rowTags 27 j).insertionSort (· ≤ ·) = grouped (kind 27 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_28 : ∀ j : Small,
    (rowTags 28 j).insertionSort (· ≤ ·) = grouped (kind 28 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_29 : ∀ j : Small,
    (rowTags 29 j).insertionSort (· ≤ ·) = grouped (kind 29 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_30 : ∀ j : Small,
    (rowTags 30 j).insertionSort (· ≤ ·) = grouped (kind 30 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_31 : ∀ j : Small,
    (rowTags 31 j).insertionSort (· ≤ ·) = grouped (kind 31 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_32 : ∀ j : Small,
    (rowTags 32 j).insertionSort (· ≤ ·) = grouped (kind 32 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_33 : ∀ j : Small,
    (rowTags 33 j).insertionSort (· ≤ ·) = grouped (kind 33 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_34 : ∀ j : Small,
    (rowTags 34 j).insertionSort (· ≤ ·) = grouped (kind 34 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_35 : ∀ j : Small,
    (rowTags 35 j).insertionSort (· ≤ ·) = grouped (kind 35 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_36 : ∀ j : Small,
    (rowTags 36 j).insertionSort (· ≤ ·) = grouped (kind 36 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_37 : ∀ j : Small,
    (rowTags 37 j).insertionSort (· ≤ ·) = grouped (kind 37 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_38 : ∀ j : Small,
    (rowTags 38 j).insertionSort (· ≤ ·) = grouped (kind 38 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_39 : ∀ j : Small,
    (rowTags 39 j).insertionSort (· ≤ ·) = grouped (kind 39 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_40 : ∀ j : Small,
    (rowTags 40 j).insertionSort (· ≤ ·) = grouped (kind 40 j) := by decide +kernel

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
private theorem edges_41 : ∀ j : Small,
    (rowTags 41 j).insertionSort (· ≤ ·) = grouped (kind 41 j) := by decide +kernel

private theorem allEdges (i j : Small) :
    (rowTags i j).Perm (grouped (kind i j)) := by
  have he : (rowTags i j).insertionSort (· ≤ ·) = grouped (kind i j) := by
    fin_cases i
    · exact edges_0 j
    · exact edges_1 j
    · exact edges_2 j
    · exact edges_3 j
    · exact edges_4 j
    · exact edges_5 j
    · exact edges_6 j
    · exact edges_7 j
    · exact edges_8 j
    · exact edges_9 j
    · exact edges_10 j
    · exact edges_11 j
    · exact edges_12 j
    · exact edges_13 j
    · exact edges_14 j
    · exact edges_15 j
    · exact edges_16 j
    · exact edges_17 j
    · exact edges_18 j
    · exact edges_19 j
    · exact edges_20 j
    · exact edges_21 j
    · exact edges_22 j
    · exact edges_23 j
    · exact edges_24 j
    · exact edges_25 j
    · exact edges_26 j
    · exact edges_27 j
    · exact edges_28 j
    · exact edges_29 j
    · exact edges_30 j
    · exact edges_31 j
    · exact edges_32 j
    · exact edges_33 j
    · exact edges_34 j
    · exact edges_35 j
    · exact edges_36 j
    · exact edges_37 j
    · exact edges_38 j
    · exact edges_39 j
    · exact edges_40 j
    · exact edges_41 j
  rw [← he]
  exact (List.perm_insertionSort _ _).symm

/-- Transfer vectors for zero through eight extensions, represented on the quotient. -/
private def values : Array (Array ℕ) := #[
  #[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],
  #[1,3,2,8,5,6,4,21,13,15,10,16,12,8,42,26,30,20,32,24,16,5,9,10,18,20,15,30,13,26],
  #[1,6,3,31,14,18,9,157,70,84,42,93,54,27,471,210,252,126,279,162,81,14,36,42,108,126,84,252,70,210],
  #[1,10,4,85,30,40,16,707,246,300,120,340,160,64,2828,984,1200,480,1360,640,256,30,100,120,400,480,300,1200,246,984],
  #[1,15,5,190,55,75,25,2353,671,825,275,950,375,125,11765,3355,4125,1375,4750,1875,625,55,225,275,1125,1375,825,4125,671,3355],
  #[1,21,6,371,91,126,36,6405,1547,1911,546,2226,756,216,38430,9282,11466,3276,13356,4536,1296,91,441,546,2646,3276,1911,11466,1547,9282],
  #[1,28,7,658,140,196,49,15106,3164,3920,980,4606,1372,343,105742,22148,27440,6860,32242,9604,2401,140,784,980,5488,6860,3920,27440,3164,22148],
  #[1,36,8,1086,204,288,64,31998,5916,7344,1632,8688,2304,512,255984,47328,58752,13056,69504,18432,4096,204,1296,1632,10368,13056,7344,58752,5916,47328],
  #[1,45,9,1695,285,405,81,62349,10317,12825,2565,15255,3645,729,561141,92853,115425,23085,137295,32805,6561,285,2025,2565,18225,23085,12825,115425,10317,92853]
]

private def table (t c : ℕ) : ℤ := ((values[t]?.getD #[])[c]?.getD 0 : ℕ)

private theorem kind_lt : ∀ i j : Small, kind i j < 30 := by decide +kernel

private theorem baseValue : ∀ c : Fin 30, table 0 c.val = 1 := by decide +kernel

private theorem excludedValue : ∀ t : Fin 8, table t.val 30 = 0 := by decide +kernel

private theorem iterValue : ∀ t : Fin 8, ∀ c : Fin 30,
    table (t.val+1) c.val = ((grouped c.val).map (table t.val)).sum := by decide +kernel

private theorem rectValue : ∀ c : Fin 30,
    table 8 c.val = 8*table 7 c.val - 28*table 6 c.val + 56*table 5 c.val -
      70*table 4 c.val + 56*table 3 c.val - 28*table 2 c.val +
      8*table 1 c.val - table 0 c.val := by decide +kernel

private theorem baseD (t : ℕ) (ht : t ≤ 8) (i j : Small) :
    table t (kind i j) = smallD t i j := by
  induction t generalizing i j with
  | zero => exact baseValue ⟨kind i j, kind_lt i j⟩
  | succ t ih =>
    have ht' : t < 8 := by omega
    have hperm := ((allEdges i j).map (table t)).sum_eq
    rw [iterValue ⟨t,ht'⟩ ⟨kind i j,kind_lt i j⟩, ← hperm]
    simp only [rowTags, List.map_ofFn, Fin.sum_ofFn, smallD]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : allow i j k
    · simpa [hk, Function.comp_def] using ih (by omega) j k
    · simp [hk, excludedValue ⟨t, ht'⟩]

private def weightedStep (f : Small → Small → ℤ) (i j : Small) : ℤ :=
  ∑ k : Small, if allow i j k then f j k else 0

theorem small_state_recurrence (t : ℕ) (i j : Small) :
    smallD (t+8) i j = 8*smallD (t+7) i j - 28*smallD (t+6) i j + 56*smallD (t+5) i j -
      70*smallD (t+4) i j + 56*smallD (t+3) i j - 28*smallD (t+2) i j +
      8*smallD (t+1) i j - smallD t i j := by
  induction t generalizing i j with
  | zero =>
    simpa only [Nat.zero_add, baseD 0 (by decide), baseD 1 (by decide), baseD 2 (by decide), baseD 3 (by decide), baseD 4 (by decide), baseD 5 (by decide), baseD 6 (by decide), baseD 7 (by decide), baseD 8 (by decide)] using rectValue ⟨kind i j, kind_lt i j⟩
  | succ t ih =>
    change weightedStep (smallD (t+8)) i j =
      8*weightedStep (smallD (t+7)) i j - 28*weightedStep (smallD (t+6)) i j +
      56*weightedStep (smallD (t+5)) i j - 70*weightedStep (smallD (t+4)) i j +
      56*weightedStep (smallD (t+3)) i j - 28*weightedStep (smallD (t+2)) i j +
      8*weightedStep (smallD (t+1)) i j - weightedStep (smallD t) i j
    unfold weightedStep
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : allow i j k
    · simpa only [hk, if_true] using ih j k
    · simp [hk]

theorem small_total_recurrence (t : ℕ) :
    smallTotal (t+8) = 8*smallTotal (t+7) - 28*smallTotal (t+6) + 56*smallTotal (t+5) -
      70*smallTotal (t+4) + 56*smallTotal (t+3) - 28*smallTotal (t+2) +
      8*smallTotal (t+1) - smallTotal t := by
  simp only [smallTotal, small_state_recurrence t, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]

private theorem startValues :
    (∑ i : Small, ∑ j : Small, table 0 (kind i j)) = 1764 ∧
    (∑ i : Small, ∑ j : Small, table 1 (kind i j)) = 14946 ∧
    (∑ i : Small, ∑ j : Small, table 2 (kind i j)) = 70216 ∧
    (∑ i : Small, ∑ j : Small, table 3 (kind i j)) = 239490 ∧
    (∑ i : Small, ∑ j : Small, table 4 (kind i j)) = 665892 ∧
    (∑ i : Small, ∑ j : Small, table 5 (kind i j)) = 1604862 ∧
    (∑ i : Small, ∑ j : Small, table 6 (kind i j)) = 3478160 ∧
    (∑ i : Small, ∑ j : Small, table 7 (kind i j)) = 6942474 := by decide +kernel

theorem small_total_initial :
    smallTotal 0 = 1764 ∧
    smallTotal 1 = 14946 ∧
    smallTotal 2 = 70216 ∧
    smallTotal 3 = 239490 ∧
    smallTotal 4 = 665892 ∧
    smallTotal 5 = 1604862 ∧
    smallTotal 6 = 3478160 ∧
    smallTotal 7 = 6942474 := by
  simpa only [smallTotal, baseD 0 (by decide), baseD 1 (by decide), baseD 2 (by decide), baseD 3 (by decide), baseD 4 (by decide), baseD 5 (by decide), baseD 6 (by decide), baseD 7 (by decide), baseD 8 (by decide)] using startValues

end Rows286

namespace Rows286
open PowerSeries

theorem finish (a : ℕ → ℤ)
    (h1 : a 1=42) (h2 : a 2=1764) (h3 : a 3=14946) (h4 : a 4=70216)
    (h5 : a 5=239490) (h6 : a 6=665892) (h7 : a 7=1604862) (h8 : a 8=3478160)
    (rec : ∀ n : ℕ, 9≤n → a n = 8*a (n-1)-28*a (n-2)+56*a (n-3)-70*a (n-4)+56*a (n-5)-28*a (n-6)+8*a (n-7)-a (n-8)) :
    (PowerSeries.mk (fun n => if n<1 then 0 else (a n:ℚ))*((1-X)^8:PowerSeries ℚ) =
      2*X*(21+714*X+1005*X^2-1156*X^3+203*X^4+86*X^5-19*X^6)) ∧
    (∀ n : ℕ, 9≤n → (a n : ℚ) = 8*a (n-1)-28*a (n-2)+56*a (n-3)-70*a (n-4)+56*a (n-5)-28*a (n-6)+8*a (n-7)-a (n-8)) := by
  have hq (n : ℕ) (hn : 9≤n) : (a n:ℚ) = 8*a (n-1)-28*a (n-2)+56*a (n-3)-70*a (n-4)+56*a (n-5)-28*a (n-6)+8*a (n-7)-a (n-8) := by
    exact_mod_cast rec n hn
  refine ⟨?_,hq⟩
  let S : PowerSeries ℚ := PowerSeries.mk (fun n => if n<1 then 0 else (a n:ℚ))
  have vals (n : ℕ) : coeff n S = if n<1 then 0 else (a n:ℚ) := coeff_mk _ _
  have left : S*(1-X)^8 =
      S-C (8:ℚ)*(S*X^1)+C (28:ℚ)*(S*X^2)-C (56:ℚ)*(S*X^3)+C (70:ℚ)*(S*X^4)-
        C (56:ℚ)*(S*X^5)+C (28:ℚ)*(S*X^6)-C (8:ℚ)*(S*X^7)+S*X^8 := by
    simp only [map_ofNat]; ring
  have right : 2*X*(21+714*X+1005*X^2-1156*X^3+203*X^4+86*X^5-19*X^6 : PowerSeries ℚ) =
      C (42:ℚ)*X^1+C (1428:ℚ)*X^2+C (2010:ℚ)*X^3-C (2312:ℚ)*X^4+
        C (406:ℚ)*X^5+C (172:ℚ)*X^6-C (38:ℚ)*X^7 := by
    simp only [map_ofNat]; ring
  change S*_ = _
  rw [left,right]
  ext n
  simp only [map_add,map_sub,coeff_C_mul,coeff_mul_X_pow',coeff_C,vals]
  by_cases h : n<9
  · interval_cases n <;> norm_num [h1,h2,h3,h4,h5,h6,h7,h8]
  · simp (disch := omega) only [if_pos,if_neg]
    linarith [hq n (by omega)]

theorem closed_form (a : ℕ → ℤ)
    (h1 : a 1=42) (h2 : a 2=1764) (h3 : a 3=14946) (h4 : a 4=70216)
    (h5 : a 5=239490) (h6 : a 6=665892) (h7 : a 7=1604862) (h8 : a 8=3478160)
    (rec : ∀ n : ℕ, 9≤n → a n = 8*a (n-1)-28*a (n-2)+56*a (n-3)-70*a (n-4)+56*a (n-5)-28*a (n-6)+8*a (n-7)-a (n-8))
    (n : ℕ) (hn : 1≤n) : 180*a n = 61*(n:ℤ)^7+1089*(n:ℤ)^6+5785*(n:ℤ)^5+6375*(n:ℤ)^4-5846*(n:ℤ)^3-264*(n:ℤ)^2+360*(n:ℤ) := by
  let P (x : ℤ) := 61*x^7+1089*x^6+5785*x^5+6375*x^4-5846*x^3-264*x^2+360*x
  change 180*a n=P n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hs : n<9
    · interval_cases n <;> norm_num [P,h1,h2,h3,h4,h5,h6,h7,h8]
    have step (d : ℕ) (lo : 1≤d) (hi : d≤8) : 180*a (n-d) = P ((n:ℤ)-d) := by
      rw [← Nat.cast_sub (by omega : d≤n)]
      exact ih (n-d) (by omega) (by omega)
    calc
      180*a n = 8*(180*a (n-1))-28*(180*a (n-2))+56*(180*a (n-3))-70*(180*a (n-4))+56*(180*a (n-5))-28*(180*a (n-6))+8*(180*a (n-7))-(180*a (n-8)) := by
        rw [rec n (by omega)]; ring
      _ = P n := by
        rw [step 1 (by decide) (by decide),
            step 2 (by decide) (by decide),
            step 3 (by decide) (by decide),
            step 4 (by decide) (by decide),
            step 5 (by decide) (by decide),
            step 6 (by decide) (by decide),
            step 7 (by decide) (by decide),
            step 8 (by decide) (by decide)]
        dsimp [P]; ring

end Rows286

namespace Rows286

theorem binomial_formula (a : ℕ → ℤ)
    (h1 : a 1=42) (h2 : a 2=1764) (h3 : a 3=14946) (h4 : a 4=70216)
    (h5 : a 5=239490) (h6 : a 6=665892) (h7 : a 7=1604862) (h8 : a 8=3478160)
    (rec : ∀ n : ℕ, 9≤n → a n = 8*a (n-1)-28*a (n-2)+56*a (n-3)-70*a (n-4)+56*a (n-5)-28*a (n-6)+8*a (n-7)-a (n-8))
    (n : ℕ) (hn : 1≤n) : a n =
       42+1722*((n-1).choose 1 : ℤ)+
       11460*((n-1).choose 2 : ℤ)+
       30628*((n-1).choose 3 : ℤ)+
       41288*((n-1).choose 4 : ℤ)+
       29920*((n-1).choose 5 : ℤ)+
       11188*((n-1).choose 6 : ℤ)+
       1708*((n-1).choose 7 : ℤ) := by
  have H := closed_form a h1 h2 h3 h4 h5 h6 h7 h8 rec n hn
  have hq : (180:ℚ)*(a n:ℚ) = 61*(n:ℚ)^7+1089*(n:ℚ)^6+5785*(n:ℚ)^5+6375*(n:ℚ)^4-5846*(n:ℚ)^3-264*(n:ℚ)^2+360*(n:ℚ) := by exact_mod_cast H
  have target : (a n:ℚ) = 42+1722*((n-1).choose 1 : ℚ)+
       11460*((n-1).choose 2 : ℚ)+
       30628*((n-1).choose 3 : ℚ)+
       41288*((n-1).choose 4 : ℚ)+
       29920*((n-1).choose 5 : ℚ)+
       11188*((n-1).choose 6 : ℚ)+
       1708*((n-1).choose 7 : ℚ) := by
    simp only [Nat.cast_choose_eq_descPochhammer_div,descPochhammer_eval_eq_prod_range,
      Nat.cast_sub hn]
    norm_num [Finset.prod_range_succ,Nat.factorial]
    linear_combination (1/180:ℚ)*hq
  exact_mod_cast target

end Rows286

namespace Rows286
open OMA.S_oeis_a208286

theorem count_eq_total (t : ℕ) : a (t+2)=smallTotal t :=
  (count_all_rows (fun x => avoids x) avoids_cons avoids_two t).trans (total_encoded t)

theorem count_initial : a 1=42 ∧ a 2=1764 ∧ a 3=14946 ∧ a 4=70216 ∧ a 5=239490 ∧
    a 6=665892 ∧ a 7=1604862 ∧ a 8=3478160 ∧ a 9=6942474 := by
  obtain ⟨t0,t1,t2,t3,t4,t5,t6,t7⟩ := small_total_initial
  exact ⟨count_one_row (fun x => avoids x) avoids_one,(count_eq_total 0).trans t0,
    (count_eq_total 1).trans t1,(count_eq_total 2).trans t2,(count_eq_total 3).trans t3,
    (count_eq_total 4).trans t4,(count_eq_total 5).trans t5,(count_eq_total 6).trans t6,
    (count_eq_total 7).trans t7⟩

theorem count_recurrence (n : ℕ) (hn : 9≤n) :
    a n=8*a (n-1)-28*a (n-2)+56*a (n-3)-70*a (n-4)+56*a (n-5)-
      28*a (n-6)+8*a (n-7)-a (n-8) := by
  by_cases he : n=9
  · obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9⟩ := count_initial
    subst n
    norm_num [h1,h2,h3,h4,h5,h6,h7,h8,h9]
  obtain ⟨t,rfl⟩ : ∃ t : ℕ, n=t+10 := ⟨n-10,by omega⟩
  have tr := small_total_recurrence t
  rw [←count_eq_total (t+8),←count_eq_total (t+7),←count_eq_total (t+6),
    ←count_eq_total (t+5),←count_eq_total (t+4),←count_eq_total (t+3),
    ←count_eq_total (t+2),←count_eq_total (t+1),←count_eq_total t] at tr
  rw [show t+10-1=t+7+2 by omega,show t+10-2=t+6+2 by omega,
    show t+10-3=t+5+2 by omega,show t+10-4=t+4+2 by omega,
    show t+10-5=t+3+2 by omega,show t+10-6=t+2+2 by omega,
    show t+10-7=t+1+2 by omega,show t+10-8=t+2 by omega]
  exact tr

theorem row_array_polynomial (n : ℕ) (hn : 1≤n) :
    180*a n=61*(n:ℤ)^7+1089*(n:ℤ)^6+5785*(n:ℤ)^5+6375*(n:ℤ)^4-
      5846*(n:ℤ)^3-264*(n:ℤ)^2+360*(n:ℤ) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,_⟩ := count_initial
  exact closed_form a h1 h2 h3 h4 h5 h6 h7 h8 count_recurrence n hn

theorem row_array_binomial (n : ℕ) (hn : 1≤n) :
    a n=42+1722*((n-1).choose 1:ℤ)+11460*((n-1).choose 2:ℤ)+30628*((n-1).choose 3:ℤ)+
      41288*((n-1).choose 4:ℤ)+29920*((n-1).choose 5:ℤ)+11188*((n-1).choose 6:ℤ)+
      1708*((n-1).choose 7:ℤ) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,_⟩ := count_initial
  exact binomial_formula a h1 h2 h3 h4 h5 h6 h7 h8 count_recurrence n hn

end Rows286

theorem OMA.solution : type_of% @OMA.S_oeis_a208286.main := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,_⟩ := Rows286.count_initial
  exact Rows286.finish OMA.S_oeis_a208286.a h1 h2 h3 h4 h5 h6 h7 h8 Rows286.count_recurrence
