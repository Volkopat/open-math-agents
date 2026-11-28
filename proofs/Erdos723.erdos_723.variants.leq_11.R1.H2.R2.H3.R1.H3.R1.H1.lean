import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H3_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Linarith

section

namespace OrderTenSymmetricSupport

open Finset
open scoped symmDiff BigOperators

abbrev Incidence := Fin 111 → Fin 111 → Bool

def line (A : Incidence) (l : Fin 111) : Finset (Fin 111) :=
  Finset.univ.filter fun p => A l p = true

lemma filter_in_line (A : Incidence) (S : Finset (Fin 111)) (l : Fin 111) :
    S.filter (fun p => A l p = true) = S ∩ line A l := by
  ext p
  simp [line]

lemma symmDiff_card_sum {X : Type} [DecidableEq X] (S T : Finset X) :
    (S ∆ T).card + 2*(S ∩ T).card = S.card + T.card := by
  have apart : Disjoint (S \ T) (T \ S) := by
    rw [Finset.disjoint_left]
    intro x left right
    exact (Finset.mem_sdiff.mp left).2 (Finset.mem_sdiff.mp right).1
  have left := Finset.card_sdiff_add_card_inter S T
  have right := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at right
  rw [Finset.symmDiff_def,Finset.card_union_of_disjoint apart]
  omega

lemma intersect_symmDiff {X : Type} [DecidableEq X] (S T U : Finset X) :
    (S ∆ T) ∩ U = (S ∩ U) ∆ (T ∩ U) := by
  ext x
  by_cases present : x ∈ U <;> simp [Finset.mem_symmDiff,present]

lemma line_pair_odd (A : Incidence)
    (rows : ∀ l, (line A l).card = 11)
    (pairs : ∀ l m, l ≠ m → ∃! p, A l p = true ∧ A m p = true)
    (l m : Fin 111) : (line A l ∩ line A m).card % 2 = 1 := by
  by_cases same : l = m
  · subst m
    rw [Finset.inter_self,rows]
  obtain ⟨p,hp,unique⟩ := pairs l m same
  have identical : line A l ∩ line A m = {p} := by
    ext q
    simp only [line,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact ⟨unique q,fun h => h.symm ▸ hp⟩
  rw [identical,Finset.card_singleton]

lemma parity_with_line (A : Incidence)
    (rows : ∀ l, (line A l).card = 11)
    (pairs : ∀ l m, l ≠ m → ∃! p, A l p = true ∧ A m p = true)
    (S : Finset (Fin 111)) (l m : Fin 111) :
    ((S ∆ line A l) ∩ line A m).card % 2 = ((S ∩ line A m).card + 1) % 2 := by
  rw [intersect_symmDiff]
  have count := symmDiff_card_sum (S ∩ line A m) (line A l ∩ line A m)
  have odd := line_pair_odd A rows pairs l m
  omega

theorem six_secant_gives_odd_fifteen (A : Incidence)
    (rows : ∀ l, (line A l).card = 11)
    (pairs : ∀ l m, l ≠ m → ∃! p, A l p = true ∧ A m p = true)
    (S : Finset (Fin 111)) (size : S.card = 16)
    (even : ∀ l, 2 ∣ (S ∩ line A l).card)
    (l : Fin 111) (six : (S ∩ line A l).card = 6) :
    ∃ T : Finset (Fin 111), T.card = 15 ∧ ∀ m, (T ∩ line A m).card % 2 = 1 := by
  refine ⟨S ∆ line A l,?_,?_⟩
  · have count := symmDiff_card_sum S (line A l)
    rw [size, rows, six] at count
    omega
  · intro m
    rw [parity_with_line A rows pairs]
    have parity := even m
    omega

def through (A : Incidence) (p : Fin 111) : Finset (Fin 111) :=
  Finset.univ.filter fun l => A l p = true

lemma count_other_at_point (A : Incidence)
    (pairs : ∀ p q, p ≠ q → ∃! l, A l p = true ∧ A l q = true)
    (S : Finset (Fin 111)) (p : Fin 111) (hp : p ∉ S) :
    (∑ l ∈ through A p, (S ∩ line A l).card) = S.card := by
  calc
    _ = ∑ l ∈ through A p, ∑ q ∈ S, if A l q = true then (1 : Nat) else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_filter, filter_in_line]
      simp
    _ = ∑ q ∈ S, (1 : Nat) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      obtain ⟨l, both, unique⟩ := pairs p q (fun same => hp (same.symm ▸ hq))
      have one : (through A p).filter (fun k => A k q = true) = {l} := by
        ext k
        simp only [through,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
        exact ⟨unique k,fun same => same.symm ▸ both⟩
      rw [← Finset.sum_filter, one]
      simp
    _ = _ := by simp

lemma even_support_line_bound (A : Incidence)
    (columns : ∀ p, (through A p).card = 11)
    (pairs : ∀ p q, p ≠ q → ∃! l, A l p = true ∧ A l q = true)
    (S : Finset (Fin 111)) (even : ∀ l, 2 ∣ (S ∩ line A l).card) (l : Fin 111) :
    (S ∩ line A l).card ≤ S.card - 10 := by
  by_cases empty : (S ∩ line A l).card = 0
  · simp [empty]
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero empty)
  obtain ⟨hpS,hpL⟩ := Finset.mem_inter.mp hp
  let L := through A p
  let k (m : Fin 111) := (S.erase p ∩ line A m).card
  have l_mem : l ∈ L := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hpL).2⟩
  have lc : L.card = 11 := columns p
  have count : (∑ m ∈ L, k m) = S.card - 1 := by
    exact (count_other_at_point A pairs (S.erase p) p (by simp)).trans (Finset.card_erase_of_mem hpS)
  have restore (m : Fin 111) (hm : m ∈ L) : (S ∩ line A m).card = k m + 1 := by
    have on_m : p ∈ S ∩ line A m := Finset.mem_inter.mpr ⟨hpS,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hm).2⟩⟩
    have commutes : S.erase p ∩ line A m = (S ∩ line A m).erase p := by
      ext q
      simp [Finset.mem_erase,Finset.mem_inter,and_assoc]
    unfold k
    rw [commutes,Finset.card_erase_of_mem on_m]
    have := Finset.card_pos.mpr ⟨p,on_m⟩
    omega
  have each (m : Fin 111) (hm : m ∈ L) : 1 ≤ k m := by
    have two := even m
    rw [restore m hm] at two
    omega
  have others := Finset.sum_le_sum (s := L.erase l) (f := fun _ => (1 : Nat)) (g := k)
    (fun m hm => each m (Finset.mem_of_mem_erase hm))
  simp only [Finset.sum_const,Nat.nsmul_eq_mul,mul_one,Finset.card_erase_of_mem l_mem,lc] at others
  have separated := Finset.sum_erase_add L k l_mem
  rw [count] at separated
  have positive := each l l_mem
  rw [restore l l_mem]
  omega

theorem odd_fifteen_line_cases (A : Incidence)
    (rows : ∀ l, (line A l).card = 11)
    (columns : ∀ p, (through A p).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, A l p = true ∧ A m p = true)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, A l p = true ∧ A l q = true)
    (T : Finset (Fin 111)) (size : T.card = 15) (odd : ∀ m, (T ∩ line A m).card % 2 = 1)
    (l : Fin 111) :
    let k := (T ∩ line A l).card
    k = 1 ∨ k = 3 ∨ k = 5 := by
  let U := T ∆ line A l
  let k := (T ∩ line A l).card
  have hodd := odd l
  have decomp : U.card + 2*k = 26 := by
    change (T ∆ line A l).card + 2*(T ∩ line A l).card = 26
    rw [symmDiff_card_sum,size,rows]
  have kcap : k ≤ 11 := (Finset.card_le_card Finset.inter_subset_right).trans_eq (rows l)
  have even (m : Fin 111) : 2 ∣ (U ∩ line A m).card := by
    apply Nat.dvd_of_mod_eq_zero
    change ((T ∆ line A l) ∩ line A m).card % 2 = 0
    rw [parity_with_line A rows rowPairs]
    have at_m := odd m
    omega
  have on_old : (U ∩ line A l).card = 11-k := by
    have identical : U ∩ line A l = line A l \ T := by
      ext p
      simp [U,Finset.mem_symmDiff,Finset.mem_sdiff,Finset.mem_inter]
      tauto
    rw [identical,Finset.card_sdiff,rows]
  have bound := even_support_line_bound A columns columnPairs U even l
  rw [on_old] at bound
  have kOdd : k % 2 = 1 := hodd
  change k = 1 ∨ k = 3 ∨ k = 5
  by_contra absent
  have k9 : k = 7 ∨ k = 9 ∨ k = 11 := by omega
  rcases k9 with h | h | h
  · omega
  · omega
  · have U_nonempty : U.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨p,hp⟩ := U_nonempty
    have col := columns p
    obtain ⟨m,hm⟩ := Finset.card_pos.mp (by omega : 0 < (through A p).card)
    have on_m : p ∈ U ∩ line A m := Finset.mem_inter.mpr ⟨hp,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hm).2⟩⟩
    have positive := Finset.card_pos.mpr ⟨p,on_m⟩
    have impossible := even_support_line_bound A columns columnPairs U even m
    omega

end OrderTenSymmetricSupport

open Finset
open scoped BigOperators

namespace OrderTen

def pointsOnLine (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111)) (l : Fin 111) :
    Finset (Fin 111) :=
  S.filter fun p => incidence l p = true

lemma sum_pointsOnLine (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11)
    (S : Finset (Fin 111)) :
    (∑ l, (pointsOnLine incidence S l).card) = S.card * 11 := by
  calc
    _ = ∑ l : Fin 111, ∑ p ∈ S, if incidence l p = true then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_filter]
      simp [pointsOnLine]
    _ = ∑ p ∈ S, (Finset.univ.filter fun l => incidence l p = true).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_filter]
      simp
    _ = _ := by simp [columnSize]

-- Distinct lines through a point must meet a set that avoids that point in distinct points.
lemma pencil_bound (incidence : Fin 111 → Fin 111 → Bool)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (p : Fin 111) (L S : Finset (Fin 111)) (outside : p ∉ S)
    (through : ∀ l ∈ L, incidence l p = true)
    (meets : ∀ l ∈ L, ∃ q ∈ S, incidence l q = true) : L.card ≤ S.card := by
  classical
  have choiceSet (l : ↥L) := meets l l.property
  choose q in_S on_l using choiceSet
  let f : ↥L → ↥S := fun l => ⟨q l, in_S l⟩
  have injective : Function.Injective f := by
    intro l m same
    have same_point : q l = q m := congrArg Subtype.val same
    have distinct : p ≠ q l := fun h => outside (h.symm ▸ in_S l)
    obtain ⟨line, _, unique⟩ := columnPairs p (q l) distinct
    apply Subtype.ext
    exact (unique l ⟨through l l.property, on_l l⟩).trans
      (unique m ⟨through m m.property, by rw [same_point]; exact on_l m⟩).symm
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f injective


end OrderTen

namespace OrderTenCaseShapes

lemma sum_ordered_pairs (incidence : Fin 111 → Fin 111 → Bool)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) :
    (∑ l, (OrderTen.pointsOnLine incidence S l).offDiag.card) = S.offDiag.card := by
  classical
  have on_line (l : Fin 111) : (OrderTen.pointsOnLine incidence S l).offDiag =
      S.offDiag.filter (fun pq => incidence l pq.1 = true ∧ incidence l pq.2 = true) := by
    ext pq
    simp only [Finset.mem_offDiag, OrderTen.pointsOnLine, Finset.mem_filter]
    tauto
  calc
    _ = ∑ l : Fin 111, ∑ pq ∈ S.offDiag,
        if incidence l pq.1 = true ∧ incidence l pq.2 = true then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [on_line, ← Finset.sum_filter]
      simp
    _ = ∑ pq ∈ S.offDiag, (1 : ℕ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro pq member
      obtain ⟨l, on_both, unique⟩ := columnPairs pq.1 pq.2 (Finset.mem_offDiag.mp member).2.2
      have lines : (Finset.univ.filter (fun k => incidence k pq.1 = true ∧ incidence k pq.2 = true)) =
          {l} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨unique k, fun eq => eq.symm ▸ on_both⟩
      rw [← Finset.sum_filter, lines]
      simp
    _ = _ := by simp

def linesWithIntersection (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111)) (k : ℕ) :
    Finset (Fin 111) := Finset.univ.filter fun l => (OrderTen.pointsOnLine incidence S l).card = k

def atPoint (incidence : Fin 111 → Fin 111 → Bool) (p : Fin 111) : Finset (Fin 111) :=
  Finset.univ.filter fun l => incidence l p = true

lemma sum_pencil_avoiding_center (incidence : Fin 111 → Fin 111 → Bool)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (p : Fin 111) (not_center : p ∉ S) :
    (∑ l ∈ atPoint incidence p, (OrderTen.pointsOnLine incidence S l).card) = S.card := by
  classical
  calc
    _ = ∑ l ∈ atPoint incidence p, ∑ q ∈ S, if incidence l q = true then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_filter]
      simp [OrderTen.pointsOnLine]
    _ = ∑ q ∈ S, (1 : ℕ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      have distinct : p ≠ q := fun equal => not_center (equal.symm ▸ hq)
      obtain ⟨l, on_both, unique⟩ := columnPairs p q distinct
      have one_line : (atPoint incidence p).filter (fun k => incidence k q = true) = {l} := by
        ext k
        simp only [atPoint, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨unique k, fun eq => eq.symm ▸ on_both⟩
      rw [← Finset.sum_filter, one_line]
      simp
    _ = _ := by simp



lemma fifteen_point_line_counts (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) :
    (linesWithIntersection incidence S 1).card = 90 ∧
      (linesWithIntersection incidence S 3).card = 15 ∧
      (linesWithIntersection incidence S 5).card = 6 := by
  let k := fun l => (OrderTen.pointsOnLine incidence S l).card
  let n := fun j => (linesWithIntersection incidence S j).card
  have points : (∑ l, k l) = 165 := by
    change (∑ l, (OrderTen.pointsOnLine incidence S l).card) = _
    rw [OrderTen.sum_pointsOnLine incidence columnSize, size]
  have pairs : (∑ l, (k l*k l - k l)) = 210 := by
    calc
      _ = ∑ l, (OrderTen.pointsOnLine incidence S l).offDiag.card := by simp only [k, Finset.offDiag_card]
      _ = S.offDiag.card := sum_ordered_pairs incidence columnPairs S
      _ = _ := by rw [Finset.offDiag_card, size]
  have countIndicator (j : ℕ) : (∑ l : Fin 111, if k l = j then (1 : ℕ) else 0) = n j := by
    rw [← Finset.sum_filter]
    simp [n, linesWithIntersection, k]
  have sumCoeff (m j : ℕ) : (∑ l : Fin 111, m * (if k l = j then (1 : ℕ) else 0)) = m * n j := by
    rw [← Finset.mul_sum, countIndicator]
  have five_count (l : Fin 111) : (k l*k l - k l) + 3 = 3*k l + 8*(if k l = 5 then 1 else 0) := by
    rcases lineCases l with h | h | h <;> simp [k, h]
  have five := Finset.sum_congr (s₁ := Finset.univ) rfl (fun l _ => five_count l)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Fintype.card_fin, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, countIndicator, points, pairs] at five
  have three_count (l : Fin 111) : k l = 1 + 2*(if k l = 3 then 1 else 0) + 4*(if k l = 5 then 1 else 0) := by
    rcases lineCases l with h | h | h <;> simp [k, h]
  have three := Finset.sum_congr (s₁ := Finset.univ) rfl (fun l _ => three_count l)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Fintype.card_fin, Finset.card_univ,
    nsmul_eq_mul, mul_one, sumCoeff, points] at three
  have one_count (l : Fin 111) : (1 : ℕ) =
      (if k l = 1 then 1 else 0) + (if k l = 3 then 1 else 0) + (if k l = 5 then 1 else 0) := by
    rcases lineCases l with h | h | h <;> simp [k, h]
  have one := Finset.sum_congr (s₁ := Finset.univ) rfl (fun l _ => one_count l)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Fintype.card_fin, Finset.card_univ,
    nsmul_eq_mul, mul_one, countIndicator] at one
  change n 1 = 90 ∧ n 3 = 15 ∧ n 5 = 6
  omega

lemma sum_restricted_incidence (incidence : Fin 111 → Fin 111 → Bool)
    (L S : Finset (Fin 111)) :
    (∑ p ∈ S, (OrderTen.pointsOnLine (Function.swap incidence) L p).card) =
      ∑ l ∈ L, (OrderTen.pointsOnLine incidence S l).card := by
  calc
    _ = ∑ p ∈ S, ∑ l ∈ L, if incidence l p = true then (1 : ℕ) else 0 :=
      Finset.sum_congr rfl (fun p _ => (Finset.sum_boole (fun l => incidence l p = true) L).symm)
    _ = ∑ l ∈ L, ∑ p ∈ S, if incidence l p = true then (1 : ℕ) else 0 := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun l _ => Finset.sum_boole (fun p => incidence l p = true) S)

-- Each support point is the intersection of two of the six five-secants.
lemma fifteen_point_heavy_incidence (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) (p : Fin 111) (hp : p ∈ S) :
    (OrderTen.pointsOnLine (Function.swap incidence)
      (linesWithIntersection incidence S 5) p).card = 2 := by
  let L := linesWithIntersection incidence S 5
  let d := fun q => (OrderTen.pointsOnLine (Function.swap incidence) L q).card
  have six : L.card = 6 := (fifteen_point_line_counts incidence columnSize columnPairs S size lineCases).2.2
  have line_sum : (∑ q ∈ S, d q) = 30 := by
    dsimp only [d]
    rw [sum_restricted_incidence]
    have each (l : Fin 111) (hl : l ∈ L) :
        (OrderTen.pointsOnLine incidence S l).card = 5 :=
      (Finset.mem_filter.mp hl).2
    rw [Finset.sum_congr rfl each]
    simp [six]
  have pair_sum : (∑ q ∈ S,
      (OrderTen.pointsOnLine (Function.swap incidence) L q).offDiag.card) ≤ 30 := by
    calc
      _ ≤ ∑ q : Fin 111, (OrderTen.pointsOnLine (Function.swap incidence) L q).offDiag.card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = L.offDiag.card := sum_ordered_pairs (Function.swap incidence) rowPairs L
      _ = _ := by rw [Finset.offDiag_card, six]
  have square_sum : (∑ q ∈ S, d q * d q) ≤ 60 := by
    have identity (q : Fin 111) :
        (OrderTen.pointsOnLine (Function.swap incidence) L q).offDiag.card + d q = d q * d q := by
      rw [Finset.offDiag_card]
      change d q * d q - d q + d q = d q * d q
      exact Nat.sub_add_cancel (by nlinarith [sq_nonneg (d q - 1)])
    have total := Finset.sum_congr (s₁ := S) rfl (fun q _ => identity q)
    rw [Finset.sum_add_distrib, line_sum] at total
    omega
  have Cauchy (q : Fin 111) : 4 * d q ≤ d q * d q + 4 := by
    have inequality : (4 : ℤ) * (d q : ℤ) ≤ (d q : ℤ) * (d q : ℤ) + 4 := by
      nlinarith [sq_nonneg ((d q : ℤ) - 2)]
    exact_mod_cast inequality
  change d p = 2
  by_contra neq
  have strict : 4 * d p < d p * d p + 4 := by
    have nz : (d p : ℤ) - 2 ≠ 0 := by exact sub_ne_zero.mpr (by exact_mod_cast neq)
    have inequality : (4 : ℤ) * (d p : ℤ) < (d p : ℤ) * (d p : ℤ) + 4 := by
      nlinarith [sq_pos_of_ne_zero nz]
    exact_mod_cast inequality
  have sum_strict := Finset.sum_lt_sum (s := S) (fun q _ => Cauchy q) ⟨p, hp, strict⟩
  simp only [← Finset.mul_sum, line_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, size] at sum_strict
  omega

lemma outside_fifteen_point_heavy_incidence (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) (p : Fin 111) (hp : p ∉ S) :
    (OrderTen.pointsOnLine (Function.swap incidence)
      (linesWithIntersection incidence S 5) p).card ≤ 1 := by
  let L := linesWithIntersection incidence S 5
  let pairs := fun q => (OrderTen.pointsOnLine (Function.swap incidence) L q).offDiag.card
  have six : L.card = 6 := (fifteen_point_line_counts incidence columnSize columnPairs S size lineCases).2.2
  have all : (∑ q, pairs q) = 30 := by
    rw [show (∑ q, pairs q) = L.offDiag.card from sum_ordered_pairs (Function.swap incidence) rowPairs L,
      Finset.offDiag_card, six]
  have in_support (q : Fin 111) (hq : q ∈ S) : pairs q = 2 := by
    have degrees := fifteen_point_heavy_incidence incidence rowPairs columnSize columnPairs S size lineCases q hq
    dsimp only [pairs, L]
    rw [Finset.offDiag_card, degrees]
  have sum_support : (∑ q ∈ S, pairs q) = 30 := by
    rw [Finset.sum_congr rfl in_support]
    simp [size]
  have bound := Finset.sum_le_sum_of_subset (Finset.subset_univ (insert p S)) (f := pairs)
  rw [Finset.sum_insert hp, sum_support, all] at bound
  have vanished : pairs p = 0 := by omega
  change (OrderTen.pointsOnLine (Function.swap incidence) L p).offDiag.card = 0 at vanished
  rw [Finset.offDiag_card] at vanished
  let d := (OrderTen.pointsOnLine (Function.swap incidence) L p).card
  change d * d - d = 0 at vanished
  change d ≤ 1
  by_contra! large
  have grew : d * 2 ≤ d * d := Nat.mul_le_mul_left d large
  omega

def outsideHeavyPoints (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111)) :
    Finset (Fin 111) :=
  (Finset.univ \ S).filter fun p =>
    (OrderTen.pointsOnLine (Function.swap incidence) (linesWithIntersection incidence S 5) p).card = 1

-- A light line has four outside heavy points, a medium line has none,
-- and a heavy line has six.
theorem fifteen_point_block_sizes (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) (l : Fin 111) :
    let k := (OrderTen.pointsOnLine incidence S l).card
    let b := (OrderTen.pointsOnLine incidence (outsideHeavyPoints incidence S) l).card
    (k = 1 ∧ b = 4) ∨ (k = 3 ∧ b = 0) ∨ (k = 5 ∧ b = 6) := by
  classical
  intro k b
  let L := linesWithIntersection incidence S 5
  let d := fun q => (OrderTen.pointsOnLine (Function.swap incidence) L q).card
  let B := outsideHeavyPoints incidence S
  let M := Finset.univ.filter fun p => incidence l p = true
  have inside (q : Fin 111) (hq : q ∈ S) : d q = 2 :=
    fifteen_point_heavy_incidence incidence rowPairs columnSize columnPairs S size lineCases q hq
  have outside (q : Fin 111) (hq : q ∉ S) : d q ≤ 1 :=
    outside_fifteen_point_heavy_incidence incidence rowPairs columnSize columnPairs S size lineCases q hq
  have B_mem (q : Fin 111) : q ∈ B ↔ q ∉ S ∧ d q = 1 := by
    simp [B, outsideHeavyPoints, d, L]
  have point (q : Fin 111) :
      d q = (if q ∈ S then 2 else 0) + (if q ∈ B then 1 else 0) := by
    by_cases hq : q ∈ S
    · have notB : q ∉ B := fun h => (B_mem q).mp h |>.1 <| hq
      simp [inside q hq, hq, notB]
    · have le := outside q hq
      rw [if_neg hq, zero_add]
      by_cases h : q ∈ B
      · rw [if_pos h]
        exact ((B_mem q).mp h).2
      · rw [if_neg h]
        have not_one : d q ≠ 1 := fun eq => h ((B_mem q).mpr ⟨hq, eq⟩)
        omega
  have moment : (∑ q ∈ M, d q) = 2 * k + b := by
    rw [Finset.sum_congr rfl (fun q _ => point q), Finset.sum_add_distrib]
    have two (q : Fin 111) : (if q ∈ S then 2 else 0 : ℕ) = 2 * (if q ∈ S then 1 else 0) := by
      split_ifs <;> simp
    simp only [two, ← Finset.mul_sum, Finset.sum_boole]
    have filter (T : Finset (Fin 111)) : M.filter (· ∈ T) = OrderTen.pointsOnLine incidence T l := by
      ext q
      simp [M, OrderTen.pointsOnLine, and_comm]
    rw [filter, filter]
    rfl
  have six : L.card = 6 := (fifteen_point_line_counts incidence columnSize columnPairs S size lineCases).2.2
  have meet (m : Fin 111) (different : m ≠ l) : (OrderTen.pointsOnLine incidence M m).card = 1 := by
    obtain ⟨p, hp, unique⟩ := rowPairs m l different
    have singleton : OrderTen.pointsOnLine incidence M m = {p} := by
      ext q
      simp only [OrderTen.pointsOnLine, M, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, and_comm (a := incidence l q = true)]
      exact ⟨unique q, fun eq => eq.symm ▸ hp⟩
    rw [singleton]
    simp
  have swapped : (∑ q ∈ M, d q) = ∑ m ∈ L, (OrderTen.pointsOnLine incidence M m).card :=
    sum_restricted_incidence incidence L M
  have heavy_iff : l ∈ L ↔ k = 5 := by simp [L, linesWithIntersection, k]
  have nonheavy (h : k ≠ 5) : 2 * k + b = 6 := by
    rw [← moment, swapped]
    rw [Finset.sum_congr rfl (fun m hm => meet m (fun eq => h (heavy_iff.mp (eq ▸ hm))))]
    simp [six]
  rcases lineCases l with light | medium | heavy
  · left
    change k = 1 at light
    have eq := nonheavy (by omega)
    exact ⟨light, by omega⟩
  · right; left
    change k = 3 at medium
    have eq := nonheavy (by omega)
    exact ⟨medium, by omega⟩
  · right; right
    change k = 5 at heavy
    refine ⟨heavy, ?_⟩
    have in_L := heavy_iff.mpr heavy
    have rest : (∑ m ∈ L.erase l, (OrderTen.pointsOnLine incidence M m).card) = 5 := by
      rw [Finset.sum_congr rfl (fun m hm => meet m (Finset.mem_erase.mp hm).1)]
      simp [Finset.card_erase_of_mem in_L, six]
    have same : OrderTen.pointsOnLine incidence M l = M := by
      ext q
      simp [OrderTen.pointsOnLine, M]
    rw [← Finset.sum_erase_add _ _ in_L, rest, same] at swapped
    have M_size : M.card = 11 := rowSize l
    omega

theorem fifteen_point_support_labels (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) :
    let L := linesWithIntersection incidence S 5
    ∃ relabel : S ≃ ↥(L.powersetCard 2), ∀ (p : S) (l : Fin 111),
      l ∈ (relabel p).val ↔ l ∈ L ∧ incidence l p.val = true := by
  classical
  intro L
  let d := fun q => OrderTen.pointsOnLine (Function.swap incidence) L q
  have in_targets (p : S) : d p.val ∈ L.powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    exact fifteen_point_heavy_incidence incidence rowPairs columnSize columnPairs S size
      lineCases p.val p.property
  let f : S → ↥(L.powersetCard 2) := fun p => ⟨d p.val, in_targets p⟩
  have injective : Function.Injective f := by
    intro p q hf
    have eq : d p.val = d q.val := congrArg Subtype.val hf
    have card := (Finset.mem_powersetCard.mp (in_targets p)).2
    obtain ⟨l, m, different, pair⟩ := Finset.card_eq_two.mp card
    have on_l : l ∈ d p.val := by rw [pair]; simp
    have on_m : m ∈ d p.val := by rw [pair]; simp
    have q_l : l ∈ d q.val := eq ▸ on_l
    have q_m : m ∈ d q.val := eq ▸ on_m
    obtain ⟨r, _, unique⟩ := rowPairs l m different
    apply Subtype.ext
    exact (unique p.val ⟨(Finset.mem_filter.mp on_l).2, (Finset.mem_filter.mp on_m).2⟩).trans
      (unique q.val ⟨(Finset.mem_filter.mp q_l).2, (Finset.mem_filter.mp q_m).2⟩).symm
  have six : L.card = 6 := (fifteen_point_line_counts incidence columnSize columnPairs S size lineCases).2.2
  have cards : Fintype.card S = Fintype.card ↥(L.powersetCard 2) := by
    rw [Fintype.card_coe, Fintype.card_coe, Finset.card_powersetCard, six, size]
    decide
  have bijective := (Fintype.bijective_iff_injective_and_card f).mpr ⟨injective, cards⟩
  refine ⟨Equiv.ofBijective f bijective, ?_⟩
  intro p l
  exact Finset.mem_filter

end OrderTenCaseShapes

open Finset

namespace OrderTenCaseShapes

def supportDegree (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111))
    (k : ℕ) (p : Fin 111) : Finset (Fin 111) :=
  OrderTen.pointsOnLine (Function.swap incidence) (linesWithIntersection incidence S k) p

lemma mem_supportDegree {incidence : Fin 111 → Fin 111 → Bool} {S : Finset (Fin 111)}
    {k : ℕ} {p l : Fin 111} :
    l ∈ supportDegree incidence S k p ↔
      (OrderTen.pointsOnLine incidence S l).card = k ∧ incidence l p = true := by
  unfold supportDegree
  rw [OrderTen.pointsOnLine, Finset.mem_filter]
  unfold linesWithIntersection
  rw [Finset.mem_filter]
  simp

lemma sum_pencil_containing_center (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (p : Fin 111) (inside : p ∈ S) :
    (∑ l ∈ atPoint incidence p, (OrderTen.pointsOnLine incidence S l).card) = S.card + 10 := by
  have without := sum_pencil_avoiding_center incidence columnPairs (S.erase p) p (by simp)
  rw [Finset.card_erase_of_mem inside] at without
  have split (l : Fin 111) (hl : l ∈ atPoint incidence p) :
      (OrderTen.pointsOnLine incidence S l).card =
        (OrderTen.pointsOnLine incidence (S.erase p) l).card + 1 := by
    have member : p ∈ OrderTen.pointsOnLine incidence S l :=
      Finset.mem_filter.mpr ⟨inside, (Finset.mem_filter.mp hl).2⟩
    have same : OrderTen.pointsOnLine incidence (S.erase p) l =
        (OrderTen.pointsOnLine incidence S l).erase p := by
      ext q
      simp [OrderTen.pointsOnLine, and_assoc]
    rw [same, Finset.card_erase_of_mem member]
    have := Finset.card_pos.mpr ⟨p, member⟩
    omega
  calc
    _ = ∑ l ∈ atPoint incidence p, ((OrderTen.pointsOnLine incidence (S.erase p) l).card + 1) :=
      Finset.sum_congr rfl split
    _ = _ := by
      rw [Finset.sum_add_distrib, without]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, columnSize]
      have := Finset.card_pos.mpr ⟨p, inside⟩
      omega

lemma fifteen_point_degrees (incidence : Fin 111 → Fin 111 → Bool)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) (p : Fin 111) :
    let c := fun k => (supportDegree incidence S k p).card
    (if p ∈ S then c 3 + 2 * c 5 = 7 else c 3 + 2 * c 5 = 2) ∧
      c 1 + c 3 + c 5 = 11 := by
  classical
  intro c
  let L := atPoint incidence p
  let k := fun l => (OrderTen.pointsOnLine incidence S l).card
  have card_L : L.card = 11 := columnSize p
  have indicator (j : ℕ) : (∑ l ∈ L, if k l = j then (1 : ℕ) else 0) = c j := by
    have filtered : L.filter (fun l => k l = j) = supportDegree incidence S j p := by
      ext l
      rw [Finset.mem_filter, mem_supportDegree]
      change (l ∈ Finset.univ.filter (fun m => incidence m p = true) ∧ k l = j) ↔
        (k l = j ∧ incidence l p = true)
      simp [and_comm]
    rw [Finset.sum_boole, filtered]
    rfl
  have part (l : Fin 111) : (1 : ℕ) =
      (if k l = 1 then 1 else 0) + (if k l = 3 then 1 else 0) + (if k l = 5 then 1 else 0) := by
    rcases lineCases l with h | h | h <;> simp [k, h]
  have moments (l : Fin 111) : k l = 1 + 2 * (if k l = 3 then 1 else 0) +
      4 * (if k l = 5 then 1 else 0) := by
    rcases lineCases l with h | h | h <;> simp [k, h]
  have partition := Finset.sum_congr (s₁ := L) rfl (fun l _ => part l)
  have weighted := Finset.sum_congr (s₁ := L) rfl (fun l _ => moments l)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, card_L,
    ← Finset.mul_sum, indicator] at partition weighted
  change (∑ l ∈ L, k l) = 11 + 2 * c 3 + 4 * c 5 at weighted
  refine ⟨?_, partition.symm⟩
  by_cases hp : p ∈ S
  · rw [if_pos hp]
    have eq := sum_pencil_containing_center incidence columnSize columnPairs S p hp
    change (∑ l ∈ L, k l) = S.card + 10 at eq
    omega
  · rw [if_neg hp]
    have eq := sum_pencil_avoiding_center incidence columnPairs S p hp
    change (∑ l ∈ L, k l) = S.card at eq
    omega

def exteriorPoints (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111)) :
    Finset (Fin 111) :=
  Finset.univ.filter fun p => (supportDegree incidence S 5 p).card = 0

lemma exterior_has_two_medium_lines (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) (p : Fin 111) (hp : p ∈ exteriorPoints incidence S) :
    p ∉ S ∧ (supportDegree incidence S 3 p).card = 2 := by
  have zero : (supportDegree incidence S 5 p).card = 0 := (Finset.mem_filter.mp hp).2
  have out : p ∉ S := by
    intro in_S
    have two : (supportDegree incidence S 5 p).card = 2 :=
      fifteen_point_heavy_incidence incidence rowPairs columnSize columnPairs S size lineCases p in_S
    omega
  have degrees := (fifteen_point_degrees incidence columnSize columnPairs S size lineCases p).1
  rw [if_neg out] at degrees
  dsimp only at degrees
  rw [zero] at degrees
  exact ⟨out, by omega⟩

lemma medium_has_no_outside_heavy (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (m p : Fin 111) (medium : (OrderTen.pointsOnLine incidence S m).card = 3)
    (on_m : incidence m p = true) (hp : p ∉ S) :
    p ∈ exteriorPoints incidence S := by
  have le : (supportDegree incidence S 5 p).card ≤ 1 :=
    outside_fifteen_point_heavy_incidence incidence rowPairs columnSize columnPairs S size lineCases p hp
  have zero : (supportDegree incidence S 5 p).card = 0 := by
    by_contra h
    have one : (supportDegree incidence S 5 p).card = 1 := by omega
    have member : p ∈ outsideHeavyPoints incidence S :=
      Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hp⟩, one⟩
    have pos := Finset.card_pos.mpr
      (show (OrderTen.pointsOnLine incidence (outsideHeavyPoints incidence S) m).Nonempty from
        ⟨p, Finset.mem_filter.mpr ⟨member, on_m⟩⟩)
    have block := fifteen_point_block_sizes incidence rowSize rowPairs columnSize columnPairs S size lineCases m
    change ((OrderTen.pointsOnLine incidence S m).card = 1 ∧ _) ∨
      ((OrderTen.pointsOnLine incidence S m).card = 3 ∧ _) ∨
      ((OrderTen.pointsOnLine incidence S m).card = 5 ∧ _) at block
    rcases block with ⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩ <;> omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, zero⟩

lemma medium_matches_heavy_lines (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (m l : Fin 111) (m_size : (OrderTen.pointsOnLine incidence S m).card = 3)
    (l_size : (OrderTen.pointsOnLine incidence S l).card = 5) :
    ∃! p, p ∈ S ∧ incidence m p = true ∧ incidence l p = true := by
  have different : m ≠ l := by intro eq; rw [eq, l_size] at m_size; omega
  obtain ⟨p, meets, unique⟩ := rowPairs m l different
  have in_S : p ∈ S := by
    by_contra hp
    have out := medium_has_no_outside_heavy incidence rowSize rowPairs columnSize columnPairs
      S size lineCases m p m_size meets.1 hp
    have zero : (supportDegree incidence S 5 p).card = 0 := (Finset.mem_filter.mp out).2
    have pos := Finset.card_pos.mpr ⟨l, mem_supportDegree.mpr ⟨l_size, meets.2⟩⟩
    omega
  exact ⟨p, ⟨in_S, meets⟩, fun q h => unique q h.2⟩

lemma light_pencil_card (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) (p : Fin 111) (hp : p ∈ S) :
    (supportDegree incidence S 1 p).card = 6 := by
  have heavy : (supportDegree incidence S 5 p).card = 2 :=
    fifteen_point_heavy_incidence incidence rowPairs columnSize columnPairs S size lineCases p hp
  have counts := fifteen_point_degrees incidence columnSize columnPairs S size lineCases p
  dsimp only at counts
  rw [if_pos hp] at counts
  omega

lemma light_support_singleton (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111))
    {l p : Fin 111} (hp : p ∈ S) (light : l ∈ supportDegree incidence S 1 p) :
    OrderTen.pointsOnLine incidence S l = {p} := by
  obtain ⟨card, on_line⟩ := mem_supportDegree.mp light
  obtain ⟨q, eq⟩ := Finset.card_eq_one.mp card
  have mem : p ∈ OrderTen.pointsOnLine incidence S l := Finset.mem_filter.mpr ⟨hp, on_line⟩
  rw [eq, Finset.mem_singleton] at mem
  rwa [mem]

lemma light_meets_medium_away_from_secant (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (p l m : Fin 111) (hp : p ∈ S) (light : l ∈ supportDegree incidence S 1 p)
    (medium : (OrderTen.pointsOnLine incidence S m).card = 3)
    (avoids_secant : incidence m p = false) :
    ∃! q, q ∈ exteriorPoints incidence S ∧ incidence l q = true ∧ incidence m q = true := by
  have l_card := (mem_supportDegree.mp light).1
  have different : l ≠ m := by intro eq; rw [eq, medium] at l_card; omega
  obtain ⟨q, both, unique⟩ := rowPairs l m different
  have outside : q ∉ S := by
    intro in_S
    have member : q ∈ OrderTen.pointsOnLine incidence S l := Finset.mem_filter.mpr ⟨in_S, both.1⟩
    rw [light_support_singleton incidence S hp light, Finset.mem_singleton] at member
    rw [member, avoids_secant] at both
    exact Bool.noConfusion both.2
  exact ⟨q, ⟨medium_has_no_outside_heavy incidence rowSize rowPairs columnSize columnPairs
    S size lineCases m q medium both.2 outside, both⟩, fun r h => unique r h.2⟩

lemma light_star_avoids_secant_medium (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (p l q m : Fin 111) (hp : p ∈ S) (light : l ∈ supportDegree incidence S 1 p)
    (hq : q ∈ exteriorPoints incidence S) (on_l : incidence l q = true)
    (on_m : m ∈ supportDegree incidence S 3 q) :
    incidence m p = false := by
  have q_out := (exterior_has_two_medium_lines incidence rowPairs columnSize columnPairs
    S size lineCases q hq).1
  obtain ⟨l_card, at_p⟩ := mem_supportDegree.mp light
  obtain ⟨m_card, at_q⟩ := mem_supportDegree.mp on_m
  have different : l ≠ m := by intro eq; rw [eq, m_card] at l_card; omega
  obtain ⟨r, _, unique⟩ := rowPairs l m different
  by_contra! both
  have eq := (unique q ⟨on_l, at_q⟩).trans (unique p ⟨at_p, by simpa using both⟩).symm
  exact q_out (eq.symm ▸ hp)

lemma every_eligible_exterior_point_is_in_one_star (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (p q : Fin 111) (hp : p ∈ S) (hq : q ∈ exteriorPoints incidence S)
    (eligible : ∀ m ∈ supportDegree incidence S 3 q, incidence m p = false) :
    ∃! l, l ∈ supportDegree incidence S 1 p ∧ incidence l q = true := by
  have outside := (exterior_has_two_medium_lines incidence rowPairs columnSize columnPairs
    S size lineCases q hq).1
  have different : p ≠ q := fun eq => outside (eq ▸ hp)
  obtain ⟨l, meets, unique⟩ := columnPairs p q different
  have light : (OrderTen.pointsOnLine incidence S l).card = 1 := by
    rcases lineCases l with h | h | h
    · exact h
    · have eq := eligible l (mem_supportDegree.mpr ⟨h, meets.2⟩)
      rw [eq] at meets
      exact Bool.noConfusion meets.1
    · have pos := Finset.card_pos.mpr
        (show (supportDegree incidence S 5 q).Nonempty from ⟨l, mem_supportDegree.mpr ⟨h, meets.2⟩⟩)
      have zero : (supportDegree incidence S 5 q).card = 0 := (Finset.mem_filter.mp hq).2
      omega
  exact ⟨l, ⟨mem_supportDegree.mpr ⟨light, meets.1⟩, meets.2⟩,
    fun m hm => unique m ⟨(mem_supportDegree.mp hm.1).2, hm.2⟩⟩

def mediumLabel (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111)) (m : Fin 111) :
    Finset (Finset (Fin 111)) :=
  (OrderTen.pointsOnLine incidence S m).image (supportDegree incidence S 5)

def isPerfectMatching (L : Finset (Fin 111)) (M : Finset (Finset (Fin 111))) : Prop :=
  M.card = 3 ∧ (∀ e ∈ M, e ⊆ L ∧ e.card = 2) ∧
    ∀ l ∈ L, ∃! e, e ∈ M ∧ l ∈ e

lemma support_labels_injective (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) :
    Set.InjOn (supportDegree incidence S 5) (S : Set (Fin 111)) := by
  obtain ⟨equiv, agreement⟩ :=
    fifteen_point_support_labels incidence rowPairs columnSize columnPairs S size lineCases
  have same (p : S) : (equiv p).val = supportDegree incidence S 5 p.val := by
    ext l
    rw [agreement p l]
    unfold supportDegree OrderTen.pointsOnLine
    rw [Finset.mem_filter]
  intro p hp q hq eq
  let u : S := ⟨p, hp⟩
  let v : S := ⟨q, hq⟩
  have labels : equiv u = equiv v := by
    apply Subtype.ext
    rw [same, same]
    exact eq
  exact congrArg Subtype.val (equiv.injective labels)

lemma medium_label_is_matching (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (m : Fin 111) (m_size : (OrderTen.pointsOnLine incidence S m).card = 3) :
    isPerfectMatching (linesWithIntersection incidence S 5) (mediumLabel incidence S m) := by
  let labels := supportDegree incidence S 5
  let points := OrderTen.pointsOnLine incidence S m
  have inj := support_labels_injective incidence rowPairs columnSize columnPairs S size lineCases
  have card : (points.image labels).card = 3 := by
    rw [Finset.card_image_of_injOn]
    · exact m_size
    · intro p hp q hq
      exact inj (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1
  refine ⟨card, ?_, ?_⟩
  · intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    exact ⟨Finset.filter_subset _ _, fifteen_point_heavy_incidence incidence rowPairs
      columnSize columnPairs S size lineCases p (Finset.mem_filter.mp hp).1⟩
  · intro l hl
    have heavy : (OrderTen.pointsOnLine incidence S l).card = 5 := (Finset.mem_filter.mp hl).2
    obtain ⟨p, ⟨in_S, on_m, on_l⟩, unique⟩ := medium_matches_heavy_lines incidence rowSize rowPairs
      columnSize columnPairs S size lineCases m l m_size heavy
    refine ⟨labels p, ⟨Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨in_S, on_m⟩, rfl⟩,
      mem_supportDegree.mpr ⟨heavy, on_l⟩⟩, ?_⟩
    intro e ⟨he, le⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨in_S, on_m⟩ := Finset.mem_filter.mp hq
    exact congrArg labels (unique q ⟨in_S, on_m, (mem_supportDegree.mp le).2⟩)

lemma support_point_of_pair (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (e : Finset (Fin 111)) (contained : e ⊆ linesWithIntersection incidence S 5)
    (card : e.card = 2) :
    ∃ p ∈ S, supportDegree incidence S 5 p = e := by
  obtain ⟨equiv, agreement⟩ :=
    fifteen_point_support_labels incidence rowPairs columnSize columnPairs S size lineCases
  let edges : ↥((linesWithIntersection incidence S 5).powersetCard 2) :=
    ⟨e, Finset.mem_powersetCard.mpr ⟨contained, card⟩⟩
  let p := equiv.symm edges
  refine ⟨p.val, p.property, ?_⟩
  have labels : (equiv p).val = e := congrArg Subtype.val (equiv.apply_symm_apply edges)
  rw [← labels]
  ext l
  exact Finset.mem_filter.trans (agreement p l).symm

lemma perfect_matchings_share_two_pairs (L : Finset (Fin 111))
    (M N : Finset (Finset (Fin 111))) (hM : isPerfectMatching L M)
    (hN : isPerfectMatching L N) (a b : Finset (Fin 111)) (ne : a ≠ b)
    (aM : a ∈ M) (bM : b ∈ M) (aN : a ∈ N) (bN : b ∈ N) :
    M = N := by
  classical
  have remaining (K : Finset (Finset (Fin 111))) (hK : isPerfectMatching L K)
      (ha : a ∈ K) (hb : b ∈ K) : ((K.erase a).erase b).card = 1 := by
    have in_K : b ∈ K.erase a := Finset.mem_erase.mpr ⟨ne.symm, hb⟩
    rw [Finset.card_erase_of_mem in_K, Finset.card_erase_of_mem ha, hK.1]
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp (remaining M hM aM bM)
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp (remaining N hN aN bN)
  have xm := Finset.mem_erase.mp (show x ∈ (M.erase a).erase b by simp [hx])
  have yn := Finset.mem_erase.mp (show y ∈ (N.erase a).erase b by simp [hy])
  have in_M := (Finset.mem_erase.mp xm.2).2
  have in_N := (Finset.mem_erase.mp yn.2).2
  have x_ne_a := (Finset.mem_erase.mp xm.2).1
  have xy : x = y := by
    apply Finset.eq_of_subset_of_card_le
    · intro l in_x
      have in_L := (hM.2.1 x in_M).1 in_x
      obtain ⟨c, hc, unique⟩ := hM.2.2 l in_L
      have not_a : l ∉ a := fun in_a => x_ne_a ((unique x ⟨in_M, in_x⟩).trans
        (unique a ⟨aM, in_a⟩).symm)
      have not_b : l ∉ b := fun in_b => xm.1 ((unique x ⟨in_M, in_x⟩).trans
        (unique b ⟨bM, in_b⟩).symm)
      obtain ⟨d, ⟨hd, at_l⟩, _⟩ := hN.2.2 l in_L
      have other : d ∈ (N.erase a).erase b := Finset.mem_erase.mpr
        ⟨fun eq => not_b (eq ▸ at_l), Finset.mem_erase.mpr ⟨fun eq => not_a (eq ▸ at_l), hd⟩⟩
      rw [hy, Finset.mem_singleton] at other
      exact other ▸ at_l
    · rw [(hM.2.1 x in_M).2, (hN.2.1 y in_N).2]
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    by_cases ea : e = a
    · exact ea.symm ▸ aN
    by_cases eb : e = b
    · exact eb.symm ▸ bN
    have rest : e ∈ (M.erase a).erase b :=
      Finset.mem_erase.mpr ⟨eb, Finset.mem_erase.mpr ⟨ea, he⟩⟩
    rw [hx, Finset.mem_singleton, xy] at rest
    exact rest.symm ▸ in_N
  · rw [hM.1, hN.1]

lemma matching_is_medium_label (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (M : Finset (Finset (Fin 111))) (matching : isPerfectMatching (linesWithIntersection incidence S 5) M) :
    ∃ m, (OrderTen.pointsOnLine incidence S m).card = 3 ∧ mediumLabel incidence S m = M := by
  classical
  obtain ⟨a, aM, b, bM, different⟩ := Finset.one_lt_card.mp (by rw [matching.1]; decide)
  have point (e : Finset (Fin 111)) (he : e ∈ M) : ∃ p ∈ S, supportDegree incidence S 5 p = e :=
    support_point_of_pair incidence rowPairs columnSize columnPairs S size lineCases e
      (matching.2.1 e he).1 (matching.2.1 e he).2
  obtain ⟨p, in_S, p_eq⟩ := point a aM
  obtain ⟨q, q_in_S, q_eq⟩ := point b bM
  have pq : p ≠ q := by intro eq; apply different; rw [← p_eq, ← q_eq, eq]
  obtain ⟨m, on_both, _⟩ := columnPairs p q pq
  have p_mem : p ∈ OrderTen.pointsOnLine incidence S m := Finset.mem_filter.mpr ⟨in_S, on_both.1⟩
  have q_mem : q ∈ OrderTen.pointsOnLine incidence S m := Finset.mem_filter.mpr ⟨q_in_S, on_both.2⟩
  have card : (OrderTen.pointsOnLine incidence S m).card = 3 := by
    rcases lineCases m with h | h | h
    · exact (pq (Finset.card_le_one.mp (by omega) p p_mem q q_mem)).elim
    · exact h
    · have ml : m ∈ linesWithIntersection incidence S 5 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      obtain ⟨e, _, unique⟩ := matching.2.2 m ml
      have at_a : m ∈ a := p_eq ▸ mem_supportDegree.mpr ⟨h, on_both.1⟩
      have at_b : m ∈ b := q_eq ▸ mem_supportDegree.mpr ⟨h, on_both.2⟩
      exact (different ((unique a ⟨aM, at_a⟩).trans (unique b ⟨bM, at_b⟩).symm)).elim
  have m_matching := medium_label_is_matching incidence rowSize rowPairs columnSize columnPairs
    S size lineCases m card
  exact ⟨m, card, perfect_matchings_share_two_pairs _ _ _ m_matching matching a b different
    (Finset.mem_image.mpr ⟨p, p_mem, p_eq⟩)
    (Finset.mem_image.mpr ⟨q, q_mem, q_eq⟩) aM bM⟩

lemma medium_label_membership (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111))
    (inj : Set.InjOn (supportDegree incidence S 5) (S : Set (Fin 111)))
    (m p : Fin 111) (hp : p ∈ S) :
    supportDegree incidence S 5 p ∈ mediumLabel incidence S m ↔ incidence m p = true := by
  constructor
  · intro mem
    obtain ⟨q, hq, same⟩ := Finset.mem_image.mp mem
    obtain ⟨qS, on_m⟩ := Finset.mem_filter.mp hq
    rwa [inj qS hp same] at on_m
  · intro on_m
    exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, on_m⟩, rfl⟩

lemma medium_labels_injective (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (S : Finset (Fin 111))
    (inj : Set.InjOn (supportDegree incidence S 5) (S : Set (Fin 111))) :
    Set.InjOn (mediumLabel incidence S) (linesWithIntersection incidence S 3 : Set (Fin 111)) := by
  intro l hl m _ equal
  by_contra neq
  obtain ⟨p, hp, q, hq, different⟩ := Finset.one_lt_card.mp
    (show 1 < (OrderTen.pointsOnLine incidence S l).card by
      have size : (OrderTen.pointsOnLine incidence S l).card = 3 := (Finset.mem_filter.mp hl).2
      rw [size]; decide)
  obtain ⟨r, _, unique⟩ := rowPairs l m neq
  have both (s : Fin 111) (hs : s ∈ OrderTen.pointsOnLine incidence S l) :
      incidence l s = true ∧ incidence m s = true := by
    obtain ⟨in_S, on_l⟩ := Finset.mem_filter.mp hs
    have label := (medium_label_membership incidence S inj l s in_S).2 on_l
    rw [equal] at label
    exact ⟨on_l, (medium_label_membership incidence S inj m s in_S).1 label⟩
  exact different ((unique p (both p hp)).trans (unique q (both q hq)).symm)

def exteriorLabel (incidence : Fin 111 → Fin 111 → Bool) (S : Finset (Fin 111)) (q : Fin 111) :
    Finset (Finset (Finset (Fin 111))) :=
  (supportDegree incidence S 3 q).image (mediumLabel incidence S)

def isExteriorLabel (L : Finset (Fin 111)) (C : Finset (Finset (Finset (Fin 111)))) : Prop :=
  C.card = 2 ∧ (∀ M ∈ C, isPerfectMatching L M) ∧
    ∀ M ∈ C, ∀ N ∈ C, M ≠ N → Disjoint M N

lemma exterior_has_valid_label (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) (q : Fin 111) (hq : q ∈ exteriorPoints incidence S) :
    isExteriorLabel (linesWithIntersection incidence S 5) (exteriorLabel incidence S q) := by
  have injectLabels := support_labels_injective incidence rowPairs columnSize columnPairs S size lineCases
  have inj := medium_labels_injective incidence rowPairs S injectLabels
  obtain ⟨out, degree⟩ := exterior_has_two_medium_lines incidence rowPairs columnSize columnPairs
    S size lineCases q hq
  refine ⟨?_, ?_, ?_⟩
  · unfold exteriorLabel
    rw [Finset.card_image_of_injOn, degree]
    intro m hm n hn
    exact inj (Finset.mem_filter.mp hm).1 (Finset.mem_filter.mp hn).1
  · intro M hM
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hM
    exact medium_label_is_matching incidence rowSize rowPairs columnSize columnPairs S size lineCases
      m (mem_supportDegree.mp hm).1
  · intro M hM N hN different
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hM
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hN
    have mn : m ≠ n := fun eq => different (congrArg _ eq)
    obtain ⟨r, _, unique⟩ := rowPairs m n mn
    apply Finset.disjoint_left.mpr
    intro e em en
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp em
    obtain ⟨pS, at_m⟩ := Finset.mem_filter.mp hp
    have at_n := (medium_label_membership incidence S injectLabels n p pS).1 en
    have eq := (unique p ⟨at_m, at_n⟩).trans
      (unique q ⟨(mem_supportDegree.mp hm).2, (mem_supportDegree.mp hn).2⟩).symm
    exact out (eq ▸ pS)

lemma valid_exterior_label_occurs (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5)
    (C : Finset (Finset (Finset (Fin 111)))) (valid : isExteriorLabel (linesWithIntersection incidence S 5) C) :
    ∃ q ∈ exteriorPoints incidence S, exteriorLabel incidence S q = C := by
  obtain ⟨M, N, different, label⟩ := Finset.card_eq_two.mp valid.1
  obtain ⟨m, m_medium, lm⟩ := matching_is_medium_label incidence rowSize rowPairs columnSize columnPairs
    S size lineCases M (valid.2.1 M (by simp [label]))
  obtain ⟨n, n_medium, ln⟩ := matching_is_medium_label incidence rowSize rowPairs columnSize columnPairs
    S size lineCases N (valid.2.1 N (by simp [label]))
  have mn : m ≠ n := by intro e; apply different; rw [← lm, ← ln, e]
  obtain ⟨q, both, _⟩ := rowPairs m n mn
  have outside : q ∉ S := by
    intro in_S
    have disj := valid.2.2 M (by simp [label]) N (by simp [label]) different
    have lm_mem : supportDegree incidence S 5 q ∈ M :=
      lm ▸ Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨in_S, both.1⟩, rfl⟩
    have ln_mem : supportDegree incidence S 5 q ∈ N :=
      ln ▸ Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨in_S, both.2⟩, rfl⟩
    exact Finset.disjoint_left.mp disj lm_mem ln_mem
  have is_out := medium_has_no_outside_heavy incidence rowSize rowPairs columnSize columnPairs
    S size lineCases m q m_medium both.1 outside
  refine ⟨q, is_out, ?_⟩
  have q_valid := exterior_has_valid_label incidence rowSize rowPairs columnSize columnPairs
    S size lineCases q is_out
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le
  · intro E hE
    rw [label, Finset.mem_insert, Finset.mem_singleton] at hE
    rcases hE with rfl | rfl
    · exact Finset.mem_image.mpr ⟨m, mem_supportDegree.mpr ⟨m_medium, both.1⟩, lm⟩
    · exact Finset.mem_image.mpr ⟨n, mem_supportDegree.mpr ⟨n_medium, both.2⟩, ln⟩
  · rw [valid.1, q_valid.1]

lemma exterior_labels_injective (incidence : Fin 111 → Fin 111 → Bool)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) :
    Set.InjOn (exteriorLabel incidence S) (exteriorPoints incidence S : Set (Fin 111)) := by
  have inj := medium_labels_injective incidence rowPairs S
    (support_labels_injective incidence rowPairs columnSize columnPairs S size lineCases)
  intro p hp q _ labels
  have p_degree := (exterior_has_two_medium_lines incidence rowPairs columnSize columnPairs
    S size lineCases p hp).2
  obtain ⟨m, hm, n, hn, different⟩ := Finset.one_lt_card.mp
    (show 1 < (supportDegree incidence S 3 p).card by rw [p_degree]; decide)
  obtain ⟨r, _, unique⟩ := rowPairs m n different
  have on_q (m : Fin 111) (hm : m ∈ supportDegree incidence S 3 p) : incidence m q = true := by
    have member : mediumLabel incidence S m ∈ exteriorLabel incidence S p :=
      Finset.mem_image.mpr ⟨m, hm, rfl⟩
    rw [labels] at member
    obtain ⟨l, hl, eq⟩ := Finset.mem_image.mp member
    have same := inj (Finset.mem_filter.mp hl).1 (Finset.mem_filter.mp hm).1 eq
    exact same ▸ (mem_supportDegree.mp hl).2
  exact (unique p ⟨(mem_supportDegree.mp hm).2, (mem_supportDegree.mp hn).2⟩).trans
    (unique q ⟨on_q m hm, on_q n hn⟩).symm

-- Each star pairs the medium lines that avoid its support point. The six stars
-- at a support point partition the eligible exterior labels.
def HasStarCover : Prop :=
  ∃ L : Finset (Fin 111), L.card = 6 ∧
    ∃ stars : ↥(L.powersetCard 2) → Fin 6 → Finset (Finset (Finset (Finset (Fin 111)))),
      (∀ e i C, C ∈ stars e i → isExteriorLabel L C ∧ ∀ M ∈ C, e.val ∉ M) ∧
      (∀ e i M, isPerfectMatching L M → e.val ∉ M → ∃! C, C ∈ stars e i ∧ M ∈ C) ∧
      (∀ e C, isExteriorLabel L C → (∀ M ∈ C, e.val ∉ M) → ∃! i, C ∈ stars e i) ∧
      ∀ e f, e ≠ f → ∀ i j, (stars e i ∩ stars f j).card ≤ 1

theorem fifteen_point_configuration_has_star_cover (incidence : Fin 111 → Fin 111 → Bool)
    (rowSize : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnSize : ∀ p, (atPoint incidence p).card = 11)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 15)
    (lineCases : ∀ l, let k := (OrderTen.pointsOnLine incidence S l).card
      k = 1 ∨ k = 3 ∨ k = 5) :
    HasStarCover := by
  classical
  let L := linesWithIntersection incidence S 5
  let E := ↥(L.powersetCard 2)
  have six : L.card = 6 := (fifteen_point_line_counts incidence columnSize columnPairs S size lineCases).2.2
  have vertices (e : E) : ∃ p ∈ S, supportDegree incidence S 5 p = e.val := by
    obtain ⟨inside, card⟩ := Finset.mem_powersetCard.mp e.property
    exact support_point_of_pair incidence rowPairs columnSize columnPairs S size lineCases e.val inside card
  choose point point_mem point_label using vertices
  let light (e : E) : Fin 6 ≃ ↥(supportDegree incidence S 1 (point e)) :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, Fintype.card_coe,
        light_pencil_card incidence rowPairs columnSize columnPairs S size lineCases (point e) (point_mem e)])
  let star := fun (e : E) (i : Fin 6) =>
    (OrderTen.pointsOnLine incidence (exteriorPoints incidence S) (light e i).val).image
      (exteriorLabel incidence S)
  have in_star (e : E) (i : Fin 6) (C : Finset (Finset (Finset (Fin 111)))) :
      C ∈ star e i ↔ ∃ q ∈ exteriorPoints incidence S,
        incidence (light e i).val q = true ∧ exteriorLabel incidence S q = C := by
    simp only [star, Finset.mem_image, OrderTen.pointsOnLine, Finset.mem_filter]
    tauto
  have point_inj := support_labels_injective incidence rowPairs columnSize columnPairs S size lineCases
  have med_inj := medium_labels_injective incidence rowPairs S point_inj
  have ext_inj := exterior_labels_injective incidence rowPairs columnSize columnPairs S size lineCases
  have med_at (e : E) (m : Fin 111) :
      e.val ∈ mediumLabel incidence S m ↔ incidence m (point e) = true := by
    rw [← point_label e]
    exact medium_label_membership incidence S point_inj m (point e) (point_mem e)
  have med_label_iff (q m : Fin 111) (hm : (OrderTen.pointsOnLine incidence S m).card = 3) :
      mediumLabel incidence S m ∈ exteriorLabel incidence S q ↔ incidence m q = true := by
    constructor
    · intro h
      obtain ⟨r, r_mem, labels⟩ := Finset.mem_image.mp h
      have eq := med_inj (Finset.mem_filter.mp r_mem).1
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩) labels
      exact eq ▸ (mem_supportDegree.mp r_mem).2
    · intro on_m
      exact Finset.mem_image.mpr ⟨m, mem_supportDegree.mpr ⟨hm, on_m⟩, rfl⟩
  refine ⟨L, six, star, ?_, ?_, ?_, ?_⟩
  · intro e i C hC
    obtain ⟨q, in_C, on_light, label⟩ := (in_star e i C).mp hC
    rw [← label]
    refine ⟨exterior_has_valid_label incidence rowSize rowPairs columnSize columnPairs S size lineCases q in_C, ?_⟩
    intro M hM
    obtain ⟨m, m_mem, rfl⟩ := Finset.mem_image.mp hM
    have avoids := light_star_avoids_secant_medium incidence rowPairs columnSize columnPairs S size
      lineCases (point e) (light e i).val q m (point_mem e) (light e i).property in_C on_light m_mem
    simp [med_at, avoids]
  · intro e i M hM avoids
    obtain ⟨m, hm, rfl⟩ := matching_is_medium_label incidence rowSize rowPairs columnSize columnPairs
      S size lineCases M hM
    have not_on_m : incidence m (point e) = false := by
      rw [med_at] at avoids
      cases bit : incidence m (point e) <;> simp_all
    obtain ⟨q, ⟨q_mem, q_light, q_medium⟩, unique⟩ :=
      light_meets_medium_away_from_secant incidence rowSize rowPairs columnSize columnPairs S size
        lineCases (point e) (light e i).val m (point_mem e) (light e i).property hm not_on_m
    refine ⟨exteriorLabel incidence S q, ⟨(in_star e i _).mpr ⟨q, q_mem, q_light, rfl⟩,
      (med_label_iff q m hm).mpr q_medium⟩, ?_⟩
    intro C' ⟨star_mem, m_mem⟩
    obtain ⟨q', q'_out, q'_light, rfl⟩ := (in_star e i C').mp star_mem
    exact congrArg (exteriorLabel incidence S) (unique q' ⟨q'_out, q'_light,
      (med_label_iff q' m hm).mp m_mem⟩)
  · intro e C valid no_e
    obtain ⟨q, q_mem, rfl⟩ := valid_exterior_label_occurs incidence rowSize rowPairs columnSize
      columnPairs S size lineCases C valid
    have eligible (m : Fin 111) (hm : m ∈ supportDegree incidence S 3 q) :
        incidence m (point e) = false := by
      have h := no_e (mediumLabel incidence S m) (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
      rw [med_at] at h
      cases bit : incidence m (point e) <;> simp_all
    obtain ⟨l, ⟨l_mem, at_l⟩, unique⟩ := every_eligible_exterior_point_is_in_one_star incidence
      rowPairs columnSize columnPairs S size lineCases (point e) q (point_mem e) q_mem eligible
    let l' : ↥(supportDegree incidence S 1 (point e)) := ⟨l, l_mem⟩
    let i := (light e).symm l'
    have i_line : (light e i).val = l := congrArg Subtype.val ((light e).apply_symm_apply l')
    refine ⟨i, (in_star e i _).mpr ⟨q, q_mem, i_line.symm ▸ at_l, rfl⟩, ?_⟩
    intro j hj
    obtain ⟨q', q'_mem, q'_on, eq⟩ := (in_star e j _).mp hj
    have same := ext_inj q'_mem q_mem eq
    have result := unique (light e j).val ⟨(light e j).property, same ▸ q'_on⟩
    apply (light e).injective
    exact Subtype.ext (result.trans i_line.symm)
  · intro e f different i j
    let l := (light e i).val
    let m := (light f j).val
    have line_ne : l ≠ m := by
      intro equal
      have l_s := light_support_singleton incidence S (point_mem e) (light e i).property
      have m_s := light_support_singleton incidence S (point_mem f) (light f j).property
      change OrderTen.pointsOnLine incidence S l = {point e} at l_s
      change OrderTen.pointsOnLine incidence S m = {point f} at m_s
      rw [equal, m_s] at l_s
      have eq : point e = point f := (Finset.singleton_inj.mp l_s).symm
      apply different
      exact Subtype.ext ((point_label e).symm.trans (eq ▸ point_label f))
    obtain ⟨z, _, unique⟩ := rowPairs l m line_ne
    apply Finset.card_le_one.mpr
    intro C hC D hD
    have common (A : Finset (Finset (Finset (Fin 111)))) (hA : A ∈ star e i ∩ star f j) :
        A = exteriorLabel incidence S z := by
      obtain ⟨A_l, A_m⟩ := Finset.mem_inter.mp hA
      obtain ⟨q, q_mem, q_l, q_eq⟩ := (in_star e i A).mp A_l
      obtain ⟨r, r_mem, r_m, r_eq⟩ := (in_star f j A).mp A_m
      have qr := ext_inj q_mem r_mem (q_eq.trans r_eq.symm)
      have qz := unique q ⟨q_l, qr.symm ▸ r_m⟩
      exact q_eq.symm.trans (congrArg (exteriorLabel incidence S) qz)
    exact (common C hC).trans (common D hD).symm

end OrderTenCaseShapes

-- The line counts force the six heavy lines to determine the labels for the


theorem six_secant_star_cover (incidence : Fin 111 → Fin 111 → Bool)
    (rows : ∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11)
    (columns : ∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11)
    (rowPairs : ∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true)
    (columnPairs : ∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true)
    (S : Finset (Fin 111)) (size : S.card = 16)
    (even : ∀ l, 2 ∣ (S.filter fun p => incidence l p = true).card)
    (l : Fin 111) (six : (S.filter fun p => incidence l p = true).card = 6) :
    OrderTenCaseShapes.HasStarCover := by
  have sizeOn (U : Finset (Fin 111)) (r : Fin 111) :
      (U.filter fun p => incidence r p = true) = U ∩ OrderTenSymmetricSupport.line incidence r :=
    OrderTenSymmetricSupport.filter_in_line incidence U r
  have parity (r : Fin 111) : 2 ∣ (S ∩ OrderTenSymmetricSupport.line incidence r).card := by
    rw [← sizeOn]
    exact even r
  have witness : (S ∩ OrderTenSymmetricSupport.line incidence l).card = 6 := by
    rw [← sizeOn]
    exact six
  obtain ⟨T,cardT,odd⟩ :=
    OrderTenSymmetricSupport.six_secant_gives_odd_fifteen incidence rows rowPairs S size parity l witness
  apply OrderTenCaseShapes.fifteen_point_configuration_has_star_cover incidence rows rowPairs
    columns columnPairs T cardT
  intro r
  have cases := OrderTenSymmetricSupport.odd_fifteen_line_cases incidence rows columns rowPairs
    columnPairs T cardT odd r
  simpa only [OrderTen.pointsOnLine, sizeOn] using cases

end

theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H3_R1.H1 := by
  intro incidence rows columns rowPairs columnPairs S size even long
  obtain ⟨l, six⟩ := long
  exact six_secant_star_cover incidence rows columns rowPairs columnPairs S size even l six
