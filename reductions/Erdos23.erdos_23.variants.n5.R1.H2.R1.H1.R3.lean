import OMAReductions.R_Erdos23_erdos_23_variants_n5_R1_H2_R1
import Mathlib
/-! # Five cuts for a dominating pentagon with three exceptional vertices

The ordinary vertices fall into five independent classes. Their cycle representatives
give strict capacity bounds for the exceptional neighborhoods. A triangle at an
exception forbids a full rectangle of edges across its opposite class boundary. -/
namespace OMA.R_Erdos23_erdos_23_variants_n5_R1_H2_R1_H1_R3
open Finset SimpleGraph
open scoped Classical

/-- Soundness of a binary interval subdivision. An internal node encodes
a coordinate and a split point. Each child retains the half containing x. -/
private lemma interval_audit (leaf : (Fin 11 → ℕ) → (Fin 11 → ℕ) → Bool)
    (x : Fin 11 → ℕ) (P : Prop)
    (sound : ∀ lo hi, (∀ i,lo i ≤ x i) → (∀ i,x i ≤ hi i) → leaf lo hi=true → P) :
    let audit (tr : BinaryTree ℕ) := BinaryTree.rec (motive:=fun _ => (Fin 11 → ℕ) → (Fin 11 → ℕ) → Bool)
      leaf (fun s _ _ l r lo hi =>
        l lo (Function.update hi (Fin.ofNat 11 s) (s/11)) &&
        r (Function.update lo (Fin.ofNat 11 s) (s/11+1)) hi) tr
    ∀ tr lo hi, (∀ i,lo i≤x i) → (∀ i,x i≤hi i) → audit tr lo hi=true → P := by
  intro audit tr
  induction tr with
  | nil => exact sound
  | node s l r hl hr =>
    intro lo hi low high h
    let j : Fin 11 := (Fin.ofNat 11 s)
    change (_ && _) = true at h
    obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp h
    by_cases v : x j ≤ s/11
    · apply hl lo _ low _ left
      intro i
      by_cases eq : i=j
      · subst i; simpa [j] using v
      · change x i ≤ Function.update hi j (s/11) i
        rw [Function.update_of_ne eq]
        exact high i
    · apply hr _ hi _ high right
      intro i
      by_cases eq : i=j
      · subst i; simpa [j] using (show s/11+1 ≤ x j by omega)
      · change Function.update lo j (s/11+1) i ≤ x i
        rw [Function.update_of_ne eq]
        exact low i
/- For each pair of anchor positions, the following tree covers the five class
sizes and six side counts. At an internal node the remainder modulo 11
selects a coordinate and the quotient gives the split point. At a leaf the
kernel checks the size sum or one of the five cut inequalities. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 80000000 in
private lemma all_subdivisions :
  let fee (t a : Fin 5) (l r : ℕ) := if t=a ∨ t=a+1 then l else if t=a+2 then 0 else r
  let same (t b : Fin 5) := if b≠0 ∧ (((0:Fin 5)=t+2 ∨ (0:Fin 5)=t+4) ↔ (b=t+2 ∨ b=t+4)) then 1 else 0
  let ded (t a : Fin 5) (h : ℕ) := if t=a+2 then h else 0
  let leaf (b c : Fin 5) (lo hi : Fin 11 → ℕ) :=
    let total := lo 0+lo 1+lo 2+lo 3+lo 4
    let cap (i : Fin 5) := min (hi (Fin.ofNat 11 i.val)) (22+lo (Fin.ofNat 11 i.val)-total)
    let l (a : Fin 5) (i : Fin 11) := min (hi i) (cap (a+2)-1)
    let r (a : Fin 5) (i : Fin 11) := min (hi i) (cap (a+3)-1)
    decide (22 < total ∨ hi 0+hi 1+hi 2+hi 3+hi 4 < 22 ∨
      ∃ t : Fin 5, cap t*cap (t+1)+fee t 0 (l 0 5) (r 0 6)+fee t b (l b 7) (r b 8)+
        fee t c (l c 9) (r c 10)+(same t b+same t c) ≤
        25+max (ded t 0 (lo 5*lo 6)) (max (ded t b (lo 7*lo 8)) (ded t c (lo 9*lo 10))))
  let audit (b c : Fin 5) (tr : BinaryTree ℕ) := BinaryTree.rec
    (motive:=fun _ => (Fin 11 → ℕ) → (Fin 11 → ℕ) → Bool)
    (leaf b c) (fun s _ _ l r lo hi =>
      l lo (Function.update hi (Fin.ofNat 11 s) (s/11)) &&
      r (Function.update lo (Fin.ofNat 11 s) (s/11+1)) hi) tr
  let initLo (i : Fin 11) := if i.val<5 then 1 else 0
  let initHi (i : Fin 11) := if i.val<5 then 18 else 17
  ∀ b c : Fin 5, ∃ tr,audit b c tr initLo initHi=true := by
  intro fee same ded leaf audit initLo initHi b c
  let e : BinaryTree ℕ := .nil
  let v := @BinaryTree.node ℕ
  fin_cases b <;> fin_cases c
  · -- Anchor positions (0, 0, 0).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 e (v 59 (v 33 (v 34 e (v 35 e (v 37 (v 80
      (v 22 e (v 26 e (v 45 e (v 46 e e)))) (v 22 e (v 26 (v 45 e (v 46 e e)) e))) (v 80 (v 22 e (v 45 e
      e)) e)))) (v 34 (v 35 e (v 37 (v 80 (v 23 e (v 26 (v 44 e (v 46 e (v 69 e (v 15 e (v 39 e (v 41 e
      (v 43 e (v 27 e e)))))))) (v 44 e (v 46 e (v 28 (v 30 e (v 32 e (v 27 e (v 29 e e)))) (v 30 (v 32 e
      (v 27 e e)) (v 32 (v 27 e e) (v 27 e e)))))))) (v 23 e (v 26 (v 44 e (v 46 e (v 39 e (v 41 e (v 43
      e (v 27 e (v 29 e (v 31 e (v 61 e e))))))))) e))) (v 80 (v 23 e (v 44 e e)) e))) (v 35 e (v 80 (v
      26 (v 44 (v 45 (v 46 e (v 69 e (v 15 e (v 39 e (v 41 e (v 43 e (v 27 (v 29 e e) e))))))) (v 46 (v
      69 e (v 15 e (v 39 e (v 41 e (v 43 e (v 16 (v 18 e e) e)))))) (v 69 e e))) (v 45 (v 46 e (v 69 e
      e)) (v 46 (v 69 e e) e))) (v 44 (v 45 (v 46 e (v 28 e (v 30 e (v 32 e (v 27 (v 29 e e) e))))) e)
      e)) (v 44 (v 45 (v 46 e e) e) e))))) (v 33 (v 34 e (v 35 e e)) (v 34 (v 35 e e) e)))) (v 58 (v 59
      (v 33 (v 34 (v 36 e (v 37 e (v 79 (v 22 e (v 23 e (v 68 e (v 47 e e)))) (v 22 e (v 23 (v 12 (v 90 e
      (v 47 e e)) (v 90 (v 47 e e) e)) e))))) (v 36 e (v 37 e (v 79 (v 22 e (v 45 (v 68 (v 47 e e) e) e))
      e)))) (v 34 (v 36 e (v 37 (v 79 (v 23 (v 26 e (v 44 e (v 12 e (v 68 e (v 47 e (v 38 e (v 40 e (v 42
      e (v 28 e e))))))))) (v 26 e (v 44 e (v 68 (v 47 e (v 27 (v 29 e (v 31 e (v 28 e (v 30 e e)))) (v
      29 (v 31 e (v 28 e e)) (v 31 (v 28 e e) (v 28 e e))))) e)))) (v 23 (v 26 e (v 44 e (v 12 (v 90 (v
      47 e (v 38 e (v 40 e (v 42 e (v 28 e (v 30 e (v 32 e (v 60 e e)))))))) e) e))) (v 26 e e))) (v 79
      (v 23 (v 44 (v 12 e (v 68 e (v 47 (v 48 e (v 38 e (v 40 e (v 42 e (v 17 (v 19 e e) e))))) (v 38 e
      (v 40 e (v 42 e (v 28 (v 30 e e) e))))))) (v 12 e (v 68 e e))) (v 44 (v 68 (v 47 e (v 27 e (v 29 e
      (v 31 e (v 28 (v 30 e e) e))))) e) e)) (v 44 (v 12 (v 90 e e) e) e)))) (v 36 e (v 79 (v 26 e (v 44
      (v 45 (v 68 (v 47 e e) e) e) e)) e)))) (v 33 (v 34 (v 36 (v 79 e (v 81 (v 22 e (v 23 (v 25 e (v 12
      (v 90 e e) e)) e)) (v 22 e e))) (v 79 (v 81 (v 22 e (v 23 e e)) (v 22 e e)) (v 22 (v 23 (v 81 (v 11
      e (v 12 (v 90 e e) e)) e) e) e))) (v 36 (v 79 e (v 22 e e)) (v 11 e e))) (v 34 (v 36 (v 79 e (v 23
      (v 25 e e) e)) (v 44 (v 12 e e) e)) e))) (v 48 (v 33 (v 34 (v 79 (v 80 (v 26 e (v 22 e (v 23 e (v
      68 e e)))) (v 26 (v 22 e (v 23 e (v 68 e e))) (v 22 e e))) (v 80 (v 26 e (v 22 (v 23 (v 11 e (v 12
      (v 90 e (v 69 e e)) (v 90 e e))) (v 11 e e)) (v 12 (v 90 e e) e))) (v 26 (v 22 (v 23 (v 11 (v 12 e
      (v 90 e (v 91 e e))) (v 12 (v 90 e (v 91 e (v 49 e (v 50 e (v 51 e (v 52 e (v 53 e (v 54 e (v 71 e
      (v 72 e (v 73 e (v 74 e (v 75 e (v 76 e (v 82 e e))))))))))))))) (v 90 e e))) (v 11 (v 90 e e) e))
      (v 12 (v 90 e e) e)) (v 11 (v 12 e e) e)))) (v 79 (v 80 (v 26 e (v 22 (v 11 e (v 45 (v 68 e e) e))
      e)) (v 22 (v 26 (v 11 e (v 45 (v 68 e e) e)) e) e)) (v 22 (v 80 e e) e))) (v 34 (v 79 (v 80 (v 26
      (v 23 (v 44 (v 12 e (v 68 e (v 69 e (v 15 e (v 38 e (v 39 e (v 40 e (v 41 e (v 42 e (v 43 e (v 60 e
      e))))))))))) (v 12 e (v 68 e (v 69 e e)))) (v 44 (v 68 (v 69 e (v 15 e (v 39 e (v 41 e (v 43 e (v
      27 e (v 29 e (v 31 e (v 49 (v 61 e e) e))))))))) (v 69 e e)) (v 68 (v 69 e e) e))) (v 23 (v 44 (v
      12 e (v 68 e (v 38 e (v 40 e (v 42 e (v 28 e (v 30 e (v 32 e (v 60 e e))))))))) (v 12 e e)) (v 27 e
      (v 28 e (v 29 e (v 30 e (v 31 e (v 32 e (v 49 (v 50 (v 51 e e) e) e))))))))) (v 23 (v 26 (v 44 (v
      12 e (v 68 e e)) (v 12 e e)) e) e)) (v 23 (v 80 (v 26 (v 44 (v 12 (v 90 e (v 69 e e)) (v 90 (v 69 e
      e) e)) (v 12 (v 90 (v 69 e e) e) e)) e) e) e)) (v 44 (v 45 (v 68 (v 69 e e) e) e) e))) (v 22 (v 23
      (v 79 e (v 11 e e)) (v 11 e e)) (v 33 e e))))) (v 57 (v 58 e (v 48 (v 33 (v 35 (v 78 (v 80 e (v 26
      (v 22 e (v 24 e (v 67 e e))) (v 22 e e))) (v 80 e (v 26 (v 22 e e) e))) (v 78 (v 80 (v 26 e (v 22
      (v 11 e (v 67 e e)) e)) (v 22 (v 26 (v 11 e (v 67 e e)) e) e)) (v 22 (v 80 e e) e))) (v 35 (v 78 (v
      80 e (v 24 e e)) e) (v 44 (v 67 (v 46 (v 69 e e) e) e) e))) (v 22 (v 78 e e) e))) (v 47 (v 48 e (v
      22 e e)) (v 22 (v 78 (v 79 (v 69 e e) e) e) e)))) (v 56 (v 57 (v 58 e (v 48 (v 34 (v 35 e (v 77 (v
      80 (v 26 (v 23 e (v 66 (v 46 e (v 69 (v 15 e (v 28 e (v 30 e (v 32 e (v 27 e e))))) e)) (v 46 e
      e))) (v 23 e e)) (v 23 e e)) (v 23 e e))) (v 35 e (v 66 (v 45 (v 46 e e) e) e))) e)) (v 47 (v 48 e
      (v 77 (v 23 (v 79 (v 25 e (v 66 (v 12 e e) e)) e) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 (v 66 (v 12
      e (v 68 (v 58 e (v 15 e (v 27 e (v 28 e (v 29 e (v 30 e (v 31 e (v 32 e (v 49 (v 50 (v 51 e e) e)
      e))))))))) (v 58 e e))) (v 12 e (v 68 (v 58 e e) e))) (v 66 (v 12 e (v 27 e (v 29 e (v 31 e (v 28 e
      e))))) e)) (v 66 (v 12 e e) e)) (v 66 (v 12 (v 90 (v 58 e e) e) e) e)) (v 66 (v 34 (v 68 (v 58 e e)
      e) e) e)) (v 88 (v 12 e e) e)))) (v 46 (v 47 e (v 77 (v 78 (v 24 e e) e) e)) e))) (v 55 (v 56 (v 57
      (v 58 e e) (v 22 (v 23 (v 79 e e) e) e)) e) e)) (v 55 (v 56 (v 57 (v 157 (v 59 (v 33 (v 34 e (v 35
      e (v 22 e e))) (v 34 (v 35 e (v 23 e e)) e)) e) e) (v 22 (v 23 (v 79 e (v 11 (v 12 e e) e)) (v 11 e
      e)) (v 33 e e))) (v 22 (v 78 e e) e)) e)) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 (v 34 (v 134 (v 36 e
      (v 37 e (v 22 e e))) (v 36 e e)) (v 134 (v 36 e e) e)) (v 34 (v 134 (v 36 e (v 23 (v 123 (v 26 e e)
      e) e)) e) e)) (v 22 (v 23 (v 123 (v 25 e e) e) e) e)) (v 22 (v 23 (v 123 (v 80 (v 26 e (v 11 e e))
      (v 11 (v 12 (v 112 (v 91 e e) e) e) e)) e) e) (v 33 e e))) e) e) e)) (v 55 (v 155 (v 57 (v 58 e (v
      22 (v 122 (v 24 e e) e) e)) e) e) e)) (v 154 (v 56 (v 57 (v 58 e e) e) e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 0, 1).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 (v 34 e (v 35 e (v 36 e (v 37
      e (v 22 e (v 45 e (v 46 e (v 47 e e)))))))) (v 34 (v 35 e (v 36 e (v 37 e (v 23 e (v 44 e (v 46 e
      (v 47 e (v 27 e (v 28 (v 29 e (v 30 e e)) e))))))))) (v 35 e (v 36 e (v 37 e (v 44 (v 45 (v 46 e (v
      47 e (v 27 (v 28 e (v 29 e (v 30 e e))) (v 28 e e)))) (v 46 e e)) (v 45 (v 46 e e) e))))))) (v 33
      (v 34 (v 35 e (v 36 e (v 81 e (v 22 e (v 23 e e))))) (v 35 e (v 36 e (v 81 (v 22 e (v 45 (v 46 e e)
      e)) (v 11 e e))))) (v 34 (v 35 e (v 36 e (v 81 (v 23 e (v 44 (v 46 e e) e)) e))) (v 35 e e)))) (v
      59 (v 33 (v 34 e (v 35 e (v 37 (v 80 e (v 22 e (v 26 e e))) (v 80 (v 22 e (v 45 e e)) e)))) (v 34
      (v 35 e (v 37 (v 80 (v 23 e (v 26 e (v 44 e (v 46 e (v 28 e (v 30 e (v 31 e (v 27 e (v 29 e (v 50
      (v 52 e e) e)))))))))) (v 23 e (v 26 e e))) (v 80 (v 23 e (v 44 e e)) e))) (v 35 (v 37 (v 80 e (v
      24 e (v 26 (v 44 e (v 45 e e)) e))) (v 80 e e)) (v 80 (v 26 e (v 44 (v 45 (v 46 (v 69 (v 37 e (v 28
      (v 30 e (v 31 e (v 16 e (v 18 e e)))) (v 30 (v 31 e (v 16 e e)) (v 31 e (v 16 e e))))) e) e) e) (v
      28 e (v 30 e (v 31 e (v 16 e e)))))) (v 44 e e))))) (v 33 (v 34 (v 35 e (v 80 (v 81 e (v 22 e e))
      e)) (v 35 (v 80 e (v 22 e e)) e)) (v 34 (v 35 e e) e)))) (v 58 (v 59 (v 33 (v 34 (v 36 e (v 37 e (v
      79 (v 22 e (v 23 e (v 68 e (v 47 e e)))) (v 22 e (v 23 (v 12 e (v 90 e e)) e))))) (v 36 e (v 37 e
      (v 79 (v 22 e (v 45 (v 68 (v 47 e e) e) e)) e)))) (v 34 (v 36 e (v 37 e (v 79 (v 23 (v 44 e (v 12 e
      (v 68 e e))) (v 44 (v 68 (v 47 (v 48 e (v 27 e (v 29 e (v 32 e (v 17 e e))))) (v 27 e (v 29 e (v 28
      e e)))) e) e)) (v 44 (v 12 e e) e)))) (v 36 e (v 79 (v 26 e (v 44 (v 45 (v 68 (v 47 e e) e) e) e))
      e)))) (v 33 (v 34 (v 36 (v 79 e (v 81 e (v 22 (v 23 (v 25 e (v 11 e e)) e) e))) (v 79 (v 81 (v 22 e
      (v 23 e e)) (v 22 (v 23 e e) e)) (v 22 (v 23 (v 81 (v 11 e (v 12 e e)) e) e) e))) (v 36 (v 79 e (v
      22 (v 25 e e) e)) (v 11 e e))) (v 34 (v 36 (v 79 e (v 23 (v 25 e e) e)) (v 44 (v 12 e e) e)) e)))
      (v 48 (v 33 (v 34 (v 79 e (v 80 (v 26 e (v 22 e (v 12 e e))) (v 26 e e))) (v 79 (v 80 (v 26 e (v 22
      e e)) (v 22 e e)) e)) (v 34 (v 79 (v 80 (v 26 e (v 23 (v 44 e (v 12 e e)) e)) (v 23 e e)) (v 23 (v
      80 (v 26 e e) e) e)) e)) (v 22 (v 23 (v 79 e (v 11 e e)) (v 11 e e)) (v 33 e e))))) (v 57 (v 58 (v
      59 (v 33 (v 35 e (v 36 e (v 37 e (v 78 (v 22 e (v 67 (v 46 e e) e)) e)))) (v 35 e (v 36 e (v 78 (v
      26 e (v 44 (v 67 (v 46 e e) e) e)) e)))) (v 33 (v 35 e (v 36 e (v 11 e e))) (v 35 e e))) (v 48 (v
      33 (v 35 (v 78 (v 80 (v 26 e (v 22 e (v 24 e (v 67 (v 69 e e) e)))) (v 26 e (v 22 e e))) (v 80 (v
      26 e (v 22 e e)) (v 26 e e))) (v 78 (v 80 (v 26 e (v 22 e e)) (v 22 e e)) e)) (v 35 (v 78 (v 80 (v
      26 e (v 24 e e)) (v 24 e e)) (v 24 e e)) e)) (v 22 (v 78 (v 24 e (v 11 e e)) e) e))) (v 47 (v 48 e
      (v 22 (v 78 (v 79 (v 25 e e) e) e) e)) (v 22 e e)))) (v 56 (v 57 (v 58 (v 59 (v 34 (v 35 e (v 36 e
      (v 37 e (v 77 (v 23 e (v 66 (v 46 e e) e)) e)))) (v 35 e (v 36 e (v 77 (v 26 e (v 66 (v 45 (v 46 e
      e) e) e)) e)))) (v 34 (v 35 e (v 36 e e)) (v 35 e e))) (v 48 (v 34 (v 35 e (v 77 (v 80 (v 26 (v 23
      e (v 66 e (v 46 e e))) (v 23 e e)) (v 23 e e)) (v 23 e e))) (v 35 (v 77 (v 80 e (v 24 e e)) (v 24 e
      e)) (v 66 e e))) (v 77 (v 23 e e) e))) (v 47 (v 48 e (v 77 (v 23 (v 79 (v 25 e (v 66 (v 12 e e) e))
      e) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 e (v 66 (v 12 e e) e)) (v 66 (v 12 e e) e)) e) e) e))) (v
      46 (v 47 e (v 77 (v 78 (v 24 e e) e) e)) e))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33 (v 34 (v 35 e (v
      36 e (v 22 (v 23 e e) e))) (v 35 e e)) (v 34 (v 35 e e) e)) e) (v 22 (v 23 e e) e)) (v 22 (v 23 (v
      79 (v 25 e (v 11 e e)) e) e) e)) e) e)) (v 55 (v 56 (v 57 (v 157 (v 59 (v 33 (v 34 e (v 35 e (v 22
      e e))) (v 34 (v 35 e (v 23 e e)) (v 24 e e))) (v 22 e e)) (v 22 e e)) (v 22 (v 23 e e) e)) (v 22 (v
      78 e e) (v 33 e e))) (v 77 (v 23 e e) e))) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 (v 34 (v 134 (v 36
      e (v 37 e (v 22 e e))) (v 36 e e)) (v 134 (v 36 e e) e)) (v 34 (v 134 (v 36 e e) e) e)) (v 22 (v 23
      (v 123 (v 25 e (v 11 e e)) e) e) e)) (v 22 (v 23 (v 123 (v 80 e e) e) e) e)) e) e) e)) (v 55 (v 155
      (v 57 (v 58 (v 59 (v 33 (v 133 (v 35 e (v 36 e e)) (v 35 e e)) (v 133 (v 35 e e) e)) e) (v 22 (v
      122 (v 24 (v 80 e e) e) e) e)) e) e) e)) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34 (v 35 e (v 36
      e e)) (v 35 e e)) (v 34 (v 35 e e) e)) e) (v 121 (v 23 e e) e)) e) e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 0, 2).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 (v 35 e (v 36 e (v 37
      e (v 23 e (v 44 e (v 46 e (v 47 e (v 27 e (v 28 (v 29 e (v 30 e e)) e))))))))) (v 35 e (v 36 e (v
      37 e (v 44 (v 45 (v 46 e (v 47 e e)) (v 46 e e)) (v 45 (v 46 e e) e))))))) (v 33 e (v 34 (v 35 e (v
      36 e (v 81 (v 23 e (v 44 e e)) e))) (v 35 e (v 25 e (v 44 (v 45 (v 46 e e) e) e)))))) (v 59 (v 33 e
      (v 34 (v 35 e (v 37 (v 80 (v 23 e (v 26 e (v 44 e (v 46 e (v 28 e (v 30 e (v 27 e e))))))) (v 23 e
      (v 26 (v 44 e (v 46 e e)) e))) (v 80 (v 23 e (v 44 e e)) e))) (v 35 e (v 80 (v 26 e (v 44 (v 45 (v
      46 e e) e) (v 28 e (v 30 e (v 32 e (v 16 e e)))))) (v 44 e e))))) (v 33 e (v 34 (v 35 e e) e)))) (v
      58 (v 59 (v 33 e (v 34 (v 36 e (v 37 e (v 79 (v 23 (v 44 e (v 12 e (v 68 e (v 38 e (v 40 e (v 32 e
      (v 17 e e))))))) (v 44 (v 68 e e) (v 27 (v 29 e (v 32 e (v 17 e (v 19 e e)))) (v 29 (v 32 e (v 17 e
      e)) (v 32 (v 17 e e) (v 17 e e)))))) (v 44 (v 12 e e) e)))) (v 36 e (v 79 (v 26 e (v 44 e e)) e))))
      (v 33 (v 34 (v 36 (v 79 e (v 81 (v 22 e (v 23 e e)) (v 22 e e))) (v 79 e (v 22 e e))) (v 36 (v 79
      (v 81 (v 22 e (v 25 e e)) (v 22 e e)) (v 22 e e)) e)) (v 34 (v 36 (v 79 (v 81 (v 23 (v 25 e (v 44 e
      (v 12 e e))) (v 25 e e)) (v 23 (v 25 e e) e)) (v 23 (v 25 (v 81 e e) e) e)) (v 44 e e)) e))) (v 48
      (v 33 (v 34 (v 79 e (v 80 e (v 26 e e))) (v 79 (v 80 e (v 22 e e)) e)) (v 34 (v 79 (v 80 (v 26 e (v
      23 (v 44 e (v 12 e e)) e)) (v 23 (v 26 (v 44 e (v 12 e e)) e) e)) (v 23 (v 80 (v 26 e e) e) e)) e))
      (v 22 e e)))) (v 57 (v 58 (v 59 (v 33 e (v 35 e (v 36 e (v 78 (v 26 e (v 44 e e)) e)))) (v 33 (v 35
      e (v 36 e e)) (v 35 e e))) (v 48 (v 33 (v 35 (v 78 (v 80 e (v 26 e (v 22 e e))) (v 80 e (v 26 e
      e))) (v 78 (v 80 e (v 22 e e)) e)) (v 35 (v 78 (v 80 e (v 24 e e)) (v 24 e e)) e)) (v 22 e e))) (v
      47 (v 48 (v 33 e (v 78 (v 79 (v 25 e e) e) e)) (v 22 e e)) (v 22 e e)))) (v 56 (v 57 (v 58 (v 59 (v
      34 (v 35 e (v 36 e (v 37 (v 77 (v 23 e (v 26 e (v 66 (v 46 e (v 47 e (v 32 e (v 27 (v 28 e (v 29 e
      (v 30 e e))) (v 28 e e))))) (v 46 e e)))) (v 23 (v 26 e (v 88 e (v 12 e e))) (v 26 e e))) (v 77 (v
      23 e (v 66 (v 46 e e) e)) (v 88 e e))))) (v 35 e (v 36 e (v 77 (v 26 e (v 66 (v 45 (v 46 e e) e)
      e)) e)))) (v 34 (v 35 e (v 36 e e)) (v 35 e e))) (v 48 (v 34 (v 35 e (v 77 (v 80 (v 26 (v 23 e (v
      66 e (v 46 e e))) (v 23 e e)) (v 23 e e)) (v 23 (v 80 (v 26 (v 88 e (v 12 e e)) e) e) e))) (v 35 (v
      77 e (v 24 e e)) (v 66 e e))) (v 77 (v 23 e e) e))) (v 47 (v 48 (v 34 (v 77 (v 79 (v 25 e (v 26 e
      (v 23 (v 66 (v 12 e (v 68 (v 36 e (v 37 e (v 27 e (v 29 e (v 32 e (v 17 e e)))))) (v 36 e e))) (v
      12 e (v 68 (v 36 e e) e))) (v 66 (v 68 (v 36 e e) e) e)))) (v 25 e (v 26 e (v 66 (v 12 (v 90 e e)
      e) e)))) (v 79 (v 25 e (v 26 e (v 88 (v 12 (v 68 e e) e) e))) (v 25 e e))) (v 77 (v 79 (v 25 e e)
      e) e)) (v 77 (v 23 (v 79 (v 25 e (v 66 (v 12 e e) e)) e) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 e (v
      66 (v 12 e (v 27 e (v 29 e (v 32 e (v 28 e e))))) e)) (v 66 (v 12 e e) e)) e) e) e))) (v 46 (v 47 e
      (v 77 (v 78 (v 24 e e) e) e)) (v 77 (v 78 (v 68 (v 25 e e) e) e) e)))) (v 55 (v 56 (v 57 (v 58 (v
      158 (v 33 e (v 34 (v 35 e (v 23 e e)) e)) e) e) (v 22 e e)) (v 22 e e)) (v 77 (v 23 e e) e))) (v 55
      (v 56 (v 57 (v 157 (v 59 (v 33 e (v 34 (v 35 e (v 23 e e)) e)) e) e) (v 22 e e)) (v 22 e e)) (v 77
      (v 23 e e) e))) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 e (v 34 (v 134 (v 36 e e) e) e)) (v 22 e e))
      (v 22 e e)) e) e) (v 77 (v 23 (v 123 (v 25 e e) e) e) e))) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 e
      (v 133 (v 35 e e) e)) e) (v 22 e e)) e) e) e)) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34 (v 35 e
      (v 36 e (v 121 (v 23 (v 26 e e) e) e))) (v 35 e e)) (v 34 (v 35 e e) e)) e) (v 121 (v 23 e e) e))
      (v 121 (v 23 (v 79 (v 25 e e) e) e) e)) e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 0, 3).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 e (v 35 e (v 36 e (v
      37 (v 26 e (v 44 e (v 45 (v 46 e (v 47 e (v 27 (v 28 e (v 29 e (v 30 e e))) (v 28 e e)))) (v 46 e
      e)))) (v 44 (v 45 e (v 46 e e)) (v 45 (v 46 e e) e))))))) (v 33 e (v 34 e (v 35 e e)))) (v 59 (v 33
      e (v 34 e (v 35 e (v 80 (v 26 (v 44 e (v 45 (v 46 (v 69 e (v 15 e (v 39 e (v 41 e (v 31 e (v 16 e
      e)))))) (v 69 e e)) (v 46 (v 69 e e) e))) (v 44 (v 45 e e) (v 28 (v 30 e (v 31 e (v 16 e (v 18 e
      e)))) (v 30 (v 31 e (v 16 e e)) (v 31 (v 16 e e) (v 16 e e)))))) (v 44 (v 45 e e) e))))) (v 33 e (v
      34 e e)))) (v 58 (v 59 (v 33 e (v 34 (v 36 e (v 37 (v 79 (v 23 e (v 26 e (v 44 e (v 68 (v 47 e (v
      27 e (v 29 e (v 28 e e)))) e)))) (v 23 (v 26 e (v 44 e (v 12 e e))) (v 26 e e))) (v 79 (v 23 e (v
      44 e (v 27 e (v 29 e (v 31 e (v 17 e e)))))) (v 44 e e)))) (v 36 e (v 79 (v 26 e (v 44 (v 45 (v 68
      (v 47 e e) e) e) e)) e)))) (v 33 (v 34 (v 36 (v 79 e (v 81 (v 22 e (v 23 e e)) (v 22 e e))) (v 79 e
      (v 22 e e))) (v 36 (v 79 (v 81 (v 22 e (v 25 e e)) (v 22 e e)) (v 22 e e)) e)) (v 34 (v 36 (v 79 e
      (v 23 (v 25 e e) e)) e) e))) (v 48 (v 33 (v 34 (v 79 e (v 80 (v 26 e (v 22 e e)) (v 26 e e))) (v 79
      (v 80 (v 26 e (v 22 e e)) (v 22 e e)) e)) (v 34 (v 79 (v 80 (v 26 (v 23 e (v 44 e (v 68 (v 69 e e)
      e))) (v 23 e e)) (v 23 e e)) (v 23 (v 80 (v 26 (v 44 e (v 12 e e)) e) e) e)) (v 44 e e))) (v 22 e
      e)))) (v 57 (v 58 (v 59 (v 33 e (v 35 e (v 36 e (v 78 (v 26 e (v 44 (v 67 (v 46 (v 47 e e) e) e)
      e)) e)))) (v 33 (v 35 e (v 36 e e)) (v 35 e e))) (v 48 (v 33 (v 35 (v 78 (v 80 (v 26 e (v 22 e (v
      24 e (v 67 e e)))) (v 26 e (v 22 e e))) (v 80 (v 26 e (v 22 e e)) (v 26 e e))) (v 78 (v 80 (v 26 e
      (v 22 e e)) (v 22 e e)) e)) (v 35 (v 78 (v 80 (v 26 (v 24 e (v 44 e (v 67 (v 69 e e) e))) (v 24 e
      e)) (v 24 e e)) (v 24 e e)) (v 44 e e))) (v 22 e e))) (v 47 (v 48 (v 33 e (v 78 (v 79 (v 25 e e) e)
      e)) (v 22 e e)) (v 22 e e)))) (v 56 (v 57 (v 58 (v 59 (v 34 (v 35 e (v 36 e (v 37 (v 77 (v 23 e (v
      26 e (v 66 (v 46 e (v 47 e (v 31 e (v 27 e (v 28 (v 29 e (v 30 e e)) e))))) (v 46 e e)))) (v 23 e
      (v 26 (v 88 e (v 46 e e)) e))) (v 77 (v 23 e (v 66 (v 46 e e) e)) e)))) (v 35 e (v 36 e (v 77 (v 26
      e (v 66 (v 45 (v 46 e e) e) e)) (v 88 e e))))) (v 34 (v 35 e (v 36 e e)) (v 35 e e))) (v 48 (v 34
      (v 35 e (v 77 (v 80 (v 26 (v 23 e (v 66 (v 46 e (v 69 (v 15 e (v 28 e (v 30 e (v 31 e (v 27 e
      e))))) e)) (v 46 e e))) (v 23 e e)) (v 23 e e)) (v 23 e e))) (v 35 e (v 66 (v 45 (v 46 (v 69 (v 15
      e (v 28 e (v 30 e (v 31 e (v 16 e e))))) e) e) e) e))) (v 77 (v 23 e e) e))) (v 47 (v 48 (v 34 (v
      77 (v 79 (v 25 e (v 26 e (v 23 (v 66 e (v 12 e (v 68 e e))) (v 66 (v 68 (v 36 e e) e) e)))) (v 25 e
      (v 26 e (v 66 (v 12 e e) e)))) (v 79 (v 25 e (v 26 e (v 88 (v 12 e e) e))) (v 25 e e))) (v 77 (v 79
      (v 25 e e) e) e)) (v 77 (v 23 (v 79 (v 25 e (v 66 e e)) e) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 (v
      66 e (v 12 e (v 68 e e))) (v 66 e e)) (v 66 e e)) (v 66 (v 12 e e) e)) (v 66 (v 34 (v 68 (v 58 e e)
      e) e) e)) (v 88 (v 12 e e) e)))) (v 46 (v 47 e (v 77 (v 78 (v 24 e (v 66 (v 67 (v 35 e e) e) e)) e)
      e)) (v 77 (v 78 (v 68 (v 25 e e) e) e) e)))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33 e (v 34 e e)) e)
      e) (v 22 e e)) e) e)) (v 55 (v 56 (v 57 (v 157 (v 59 (v 33 e (v 34 e e)) e) e) (v 22 e e)) (v 22 e
      e)) (v 77 (v 23 e e) e))) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 e (v 34 (v 134 (v 36 e (v 23 (v 123
      (v 26 e e) e) e)) e) e)) (v 22 e e)) (v 22 e e)) e) e) (v 77 (v 23 (v 123 (v 25 e e) e) e) e))) (v
      55 (v 155 (v 57 (v 58 (v 59 (v 33 e (v 133 (v 35 (v 36 e (v 122 (v 24 e e) e)) e) e)) (v 22 e e))
      (v 22 e e)) e) e) (v 77 (v 122 (v 24 e e) e) e))) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34 (v 35
      e (v 36 e (v 121 (v 23 e e) e))) (v 35 e e)) (v 34 (v 35 e e) e)) e) (v 121 (v 23 e e) e)) (v 121
      (v 23 (v 79 (v 25 e e) e) e) e)) e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 0, 4).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 (v 34 e (v 35 e (v 36 e (v 37
      e (v 22 e (v 45 e (v 46 e (v 47 e e)))))))) (v 34 e (v 35 e (v 36 e (v 37 (v 26 e (v 44 e (v 45 (v
      46 e (v 47 e (v 27 (v 28 e (v 29 e (v 30 e e))) (v 28 e e)))) (v 46 e e)))) (v 44 (v 45 (v 46 e (v
      47 e (v 27 e (v 28 (v 29 e (v 30 e e)) e)))) (v 46 e e)) (v 45 (v 46 e e) e))))))) (v 33 (v 34 e (v
      35 e (v 36 e (v 81 (v 22 e (v 45 e e)) e)))) (v 34 e (v 35 e e)))) (v 59 (v 33 (v 34 e (v 35 e (v
      37 (v 80 (v 22 e (v 26 e (v 45 e (v 46 e e)))) (v 22 e (v 26 (v 45 e (v 46 e e)) e))) (v 80 (v 22 e
      (v 45 e e)) e)))) (v 34 e (v 35 e (v 80 (v 26 (v 44 e (v 45 (v 46 e (v 69 e e)) (v 46 (v 69 e e)
      e))) (v 44 (v 45 (v 46 e (v 28 e (v 30 e (v 27 e e)))) (v 28 e (v 30 e (v 31 e (v 16 e e))))) e))
      (v 44 (v 45 (v 46 e e) e) e))))) (v 33 (v 34 e (v 35 e e)) (v 34 e e)))) (v 58 (v 59 (v 33 (v 34 (v
      36 e (v 37 e (v 79 e (v 22 e (v 23 e e))))) (v 36 e (v 37 e (v 79 (v 22 e (v 45 (v 68 e e) e))
      e)))) (v 34 (v 36 (v 37 e (v 79 e (v 23 (v 25 e (v 44 e (v 12 e e))) (v 25 e e)))) (v 37 (v 79 (v
      23 e (v 26 e (v 44 e (v 68 (v 47 e (v 27 e (v 29 e (v 32 e (v 28 e (v 30 e (v 49 (v 51 e e)
      e))))))) e)))) (v 23 e (v 26 e e))) (v 79 (v 23 e (v 44 (v 68 e e) (v 27 e (v 29 e (v 32 e (v 17 e
      e)))))) (v 44 e e)))) (v 36 (v 37 e (v 79 e e)) (v 79 (v 26 e (v 44 (v 45 (v 68 (v 47 (v 37 e (v 27
      (v 29 e (v 32 e (v 17 e (v 19 e e)))) (v 29 (v 32 e (v 17 e e)) (v 32 e (v 17 e e))))) e) e) e) e))
      e)))) (v 33 (v 34 (v 36 (v 79 e (v 81 (v 22 e (v 23 e e)) (v 22 e e))) (v 79 e (v 22 e e))) (v 36
      (v 79 (v 81 (v 22 e (v 25 e e)) (v 22 (v 25 e e) e)) (v 22 e e)) (v 11 e e))) (v 34 (v 36 (v 79 (v
      81 (v 23 e (v 25 e e)) (v 23 e e)) (v 23 (v 25 (v 81 e e) e) e)) e) e))) (v 48 (v 33 (v 34 (v 79 e
      (v 80 (v 26 e (v 22 e e)) (v 26 e e))) (v 79 (v 80 (v 26 e (v 22 e e)) (v 22 (v 26 e e) e)) (v 22 e
      e))) (v 34 (v 79 (v 80 (v 26 e (v 23 e e)) (v 23 e e)) (v 23 (v 80 (v 26 e e) e) e)) (v 44 e e)))
      (v 22 (v 23 e e) e)))) (v 57 (v 58 (v 59 (v 33 (v 35 e (v 36 e (v 37 (v 78 e (v 22 e (v 26 e e)))
      (v 78 (v 22 e (v 67 (v 46 e e) e)) (v 11 e e))))) (v 35 e (v 36 e (v 78 (v 26 e (v 44 (v 67 (v 46 e
      e) e) e)) e)))) (v 33 (v 35 e (v 36 e (v 11 e e))) (v 35 e e))) (v 48 (v 33 (v 35 (v 78 e (v 80 e
      (v 26 (v 22 (v 24 e (v 11 e e)) e) e))) (v 78 (v 80 (v 26 e (v 22 (v 11 e (v 67 e e)) e)) (v 22 (v
      26 (v 11 e (v 67 e e)) e) e)) (v 22 (v 80 (v 26 e e) e) e))) (v 35 (v 78 e (v 24 e e)) (v 44 (v 67
      (v 46 (v 69 e e) e) e) e))) (v 22 (v 78 (v 24 e (v 11 e e)) e) e))) (v 47 (v 48 (v 33 (v 78 e (v 79
      (v 25 e (v 26 e e)) (v 25 e e))) (v 78 (v 79 (v 25 e e) e) e)) (v 22 (v 78 (v 79 (v 25 e e) e) e)
      e)) (v 22 (v 78 (v 79 (v 69 e e) e) e) e)))) (v 56 (v 57 (v 58 (v 59 (v 34 e (v 35 e (v 36 e (v 77
      (v 26 e (v 66 (v 45 (v 46 e e) e) e)) e)))) (v 34 e (v 35 e e))) (v 48 (v 34 e (v 35 e (v 66 (v 45
      (v 46 e e) e) e))) e)) (v 47 (v 48 (v 34 (v 77 (v 79 (v 25 e (v 26 e (v 23 (v 66 e (v 12 e (v 68 e
      e))) (v 66 (v 68 (v 36 e e) e) e)))) (v 25 e (v 26 e (v 66 (v 12 e e) e)))) (v 79 (v 25 e (v 26 e
      (v 88 (v 12 e e) e))) (v 25 e e))) (v 77 (v 79 (v 25 e e) e) e)) (v 77 (v 23 (v 79 (v 25 e (v 66 e
      e)) e) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 (v 66 e (v 12 e (v 68 e e))) (v 66 e e)) (v 66 e e)) (v
      66 e e)) (v 66 (v 34 e e) e)) (v 88 (v 12 e e) e)))) (v 46 (v 47 e (v 77 (v 78 (v 24 e e) e) e)) (v
      77 (v 78 (v 68 (v 25 e e) e) e) e)))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33 (v 34 e (v 35 e e)) (v
      34 e e)) e) e) (v 22 (v 23 e e) e)) e) e)) (v 55 (v 56 (v 57 (v 157 (v 59 (v 33 (v 34 e (v 35 e (v
      22 e e))) (v 34 e e)) e) e) (v 22 (v 23 e e) e)) (v 22 (v 78 (v 24 e (v 11 e e)) e) e)) e)) (v 55
      (v 56 (v 156 (v 58 (v 59 (v 33 (v 34 (v 134 (v 36 e (v 37 e (v 22 e e))) (v 36 e e)) (v 134 (v 36 e
      e) e)) (v 34 (v 134 (v 36 (v 37 e (v 23 (v 123 (v 25 e e) e) e)) (v 23 e e)) e) e)) (v 22 (v 23 (v
      123 e e) e) (v 33 e e))) (v 22 (v 23 (v 123 e e) e) e)) (v 22 e e)) (v 22 e e)) (v 77 (v 23 (v 123
      (v 25 e e) e) e) e))) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 (v 133 (v 35 e (v 36 e (v 22 (v 122 e e)
      e))) (v 35 e e)) (v 133 (v 35 e e) e)) e) (v 22 (v 122 (v 24 e (v 11 e e)) e) e)) (v 22 (v 122 e e)
      e)) e) e)) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34 e (v 35 e e)) (v 34 e e)) e) e) (v 121 (v 23
      (v 79 (v 25 e e) e) e) e)) e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 1, 0).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 (v 34 e (v 35 e (v 36 e (v 37
      e (v 22 e (v 45 e (v 46 e (v 47 e e)))))))) (v 34 (v 35 e (v 36 e (v 37 e (v 23 e (v 44 e (v 46 e
      (v 47 e (v 27 e (v 28 (v 29 e (v 31 e (v 32 e e))) e))))))))) (v 35 e (v 36 e (v 37 e (v 44 (v 45
      (v 46 e (v 47 e (v 27 (v 28 e (v 29 (v 31 e (v 32 e e)) (v 31 e (v 32 e e)))) (v 28 e e)))) (v 46 e
      e)) (v 45 (v 46 e e) e))))))) (v 33 (v 34 (v 35 e (v 36 e (v 81 e (v 22 e (v 23 e e))))) (v 35 e (v
      36 e (v 81 (v 22 e (v 45 (v 46 e e) e)) (v 11 e e))))) (v 34 (v 35 e (v 36 e (v 81 (v 23 e (v 44 (v
      46 e e) e)) e))) (v 35 e e)))) (v 59 (v 33 (v 34 e (v 35 e (v 37 (v 80 e (v 22 e (v 26 e e))) (v 80
      (v 22 e (v 45 e e)) e)))) (v 34 (v 35 e (v 37 (v 80 (v 23 e (v 26 e (v 44 e (v 46 e (v 28 e (v 29 e
      (v 32 e (v 27 e (v 31 e (v 50 (v 51 e (v 19 e e)) e)))))))))) (v 23 e (v 26 e e))) (v 80 (v 23 e (v
      44 e e)) e))) (v 35 (v 37 (v 80 e (v 24 e (v 26 (v 44 e (v 45 e e)) e))) (v 80 e e)) (v 80 (v 26 e
      (v 44 (v 45 (v 46 (v 69 (v 37 e (v 28 (v 29 e (v 32 e (v 16 e (v 19 e e)))) (v 29 e (v 32 (v 16 e
      e) (v 16 e e))))) e) e) e) (v 28 e (v 29 e (v 32 e (v 16 e e)))))) (v 44 e e))))) (v 33 (v 34 (v 35
      e (v 80 (v 81 e (v 22 e e)) e)) (v 35 (v 80 e (v 22 e e)) e)) (v 34 (v 35 e e) e)))) (v 58 (v 59 (v
      33 (v 34 (v 36 e (v 37 e (v 79 (v 22 e (v 23 e (v 68 e (v 47 e e)))) (v 22 e (v 23 (v 12 e (v 90 e
      e)) e))))) (v 36 e (v 37 e (v 79 (v 22 e (v 45 (v 68 (v 47 e e) e) e)) e)))) (v 34 (v 36 e (v 37 e
      (v 79 (v 23 (v 44 e (v 12 e (v 68 e e))) (v 44 (v 68 (v 47 (v 48 e (v 27 e (v 31 e (v 30 e (v 17 e
      e))))) (v 27 e (v 31 e (v 28 e e)))) e) e)) (v 44 (v 12 e e) e)))) (v 36 e (v 79 (v 26 e (v 44 (v
      45 (v 68 (v 47 e e) e) e) e)) e)))) (v 33 (v 34 (v 36 (v 79 e (v 81 e (v 22 (v 23 (v 25 e (v 11 e
      e)) e) e))) (v 79 (v 81 (v 22 e (v 23 e e)) (v 22 (v 23 e e) e)) (v 22 (v 23 (v 81 (v 11 e (v 12 e
      e)) e) e) e))) (v 36 (v 79 e (v 22 (v 25 e e) e)) (v 11 e e))) (v 34 (v 36 (v 79 e (v 23 (v 25 e e)
      e)) (v 44 (v 12 e e) e)) e))) (v 48 (v 33 (v 34 (v 79 e (v 80 (v 26 e (v 22 e (v 12 e e))) (v 26 e
      e))) (v 79 (v 80 (v 26 e (v 22 e e)) (v 22 e e)) e)) (v 34 (v 79 (v 80 (v 26 e (v 23 (v 44 e (v 12
      e e)) e)) (v 23 e e)) (v 23 (v 80 (v 26 e e) e) e)) e)) (v 22 (v 23 (v 79 e (v 11 e e)) (v 11 e e))
      (v 33 e e))))) (v 57 (v 58 (v 59 (v 33 (v 35 e (v 36 e (v 37 e (v 78 (v 22 e (v 67 (v 46 e e) e))
      e)))) (v 35 e (v 36 e (v 78 (v 26 e (v 44 (v 67 (v 46 e e) e) e)) e)))) (v 33 (v 35 e (v 36 e (v 11
      e e))) (v 35 e e))) (v 48 (v 33 (v 35 (v 78 (v 80 (v 26 e (v 22 e (v 24 e (v 67 (v 69 e e) e)))) (v
      26 e (v 22 e e))) (v 80 (v 26 e (v 22 e e)) (v 26 e e))) (v 78 (v 80 (v 26 e (v 22 e e)) (v 22 e
      e)) e)) (v 35 (v 78 (v 80 (v 26 e (v 24 e e)) (v 24 e e)) (v 24 e e)) e)) (v 22 (v 78 (v 24 e (v 11
      e e)) e) e))) (v 47 (v 48 e (v 22 (v 78 (v 79 (v 25 e e) e) e) e)) (v 22 e e)))) (v 56 (v 57 (v 58
      (v 59 (v 34 (v 35 e (v 36 e (v 37 e (v 77 (v 23 e (v 66 (v 46 e e) e)) e)))) (v 35 e (v 36 e (v 77
      (v 26 e (v 66 (v 45 (v 46 e e) e) e)) e)))) (v 34 (v 35 e (v 36 e e)) (v 35 e e))) (v 48 (v 34 (v
      35 e (v 77 (v 80 (v 26 (v 23 e (v 66 e (v 46 e e))) (v 23 e e)) (v 23 e e)) (v 23 e e))) (v 35 (v
      77 (v 80 e (v 24 e e)) (v 24 e e)) (v 66 e e))) (v 77 (v 23 e e) e))) (v 47 (v 48 e (v 77 (v 23 (v
      79 (v 25 e (v 66 (v 12 e e) e)) e) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 e (v 66 (v 12 e e) e)) (v
      66 (v 12 e e) e)) e) e) e))) (v 46 (v 47 e (v 77 (v 78 (v 24 e e) e) e)) e))) (v 55 (v 56 (v 57 (v
      58 (v 158 (v 33 (v 34 (v 35 e (v 36 e (v 22 (v 23 e e) e))) (v 35 e e)) (v 34 (v 35 e e) e)) e) (v
      22 (v 23 e e) e)) (v 22 (v 23 (v 79 (v 25 e (v 11 e e)) e) e) e)) e) e)) (v 55 (v 56 (v 57 (v 157
      (v 59 (v 33 (v 34 e (v 35 e (v 22 e e))) (v 34 (v 35 e (v 23 e e)) (v 24 e e))) (v 22 e e)) (v 22 e
      e)) (v 22 (v 23 e e) e)) (v 22 (v 78 e e) (v 33 e e))) (v 77 (v 23 e e) e))) (v 55 (v 56 (v 156 (v
      58 (v 59 (v 33 (v 34 (v 134 (v 36 e (v 37 e (v 22 e e))) (v 36 e e)) (v 134 (v 36 e e) e)) (v 34 (v
      134 (v 36 e e) e) e)) (v 22 (v 23 (v 123 (v 25 e (v 11 e e)) e) e) e)) (v 22 (v 23 (v 123 (v 80 e
      e) e) e) e)) e) e) e)) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 (v 133 (v 35 e (v 36 e e)) (v 35 e e))
      (v 133 (v 35 e e) e)) e) (v 22 (v 122 (v 24 (v 80 e e) e) e) e)) e) e) e)) (v 154 (v 56 (v 57 (v 58
      (v 59 (v 132 (v 34 (v 35 e (v 36 e e)) (v 35 e e)) (v 34 (v 35 e e) e)) e) (v 121 (v 23 e e) e)) e)
      e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 1, 1).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 (v 34 e (v 35 e (v 36 e (v 37
      e (v 22 e (v 45 (v 46 e (v 47 e (v 48 e (v 27 e (v 28 e e))))) (v 46 (v 47 e (v 48 e (v 28 e (v 29
      (v 30 e (v 31 e (v 32 e e))) (v 30 e e))))) (v 47 e e)))))))) (v 34 (v 35 e (v 36 e (v 37 e (v 23 e
      (v 44 (v 46 e (v 47 e (v 48 e (v 27 e (v 28 (v 29 e (v 30 e e)) e))))) (v 46 e (v 47 e e))))))) (v
      35 e (v 36 e (v 37 e (v 44 (v 45 (v 46 (v 47 e (v 48 e (v 28 (v 29 e (v 30 (v 31 e (v 32 e e)) e))
      (v 29 e (v 30 (v 31 e (v 32 e e)) e))))) (v 47 e e)) (v 46 (v 47 e e) e)) (v 45 (v 46 (v 47 e e) e)
      e))))))) (v 33 (v 34 (v 35 e (v 36 e (v 81 (v 22 e (v 23 e (v 46 e (v 47 e e)))) (v 22 (v 23 e (v
      11 e (v 46 e e))) (v 23 e e))))) (v 35 e (v 36 e (v 81 (v 22 (v 11 e (v 45 (v 46 e (v 47 (v 70 e (v
      41 e (v 43 e (v 27 e (v 17 (v 18 e e) e))))) e)) (v 46 (v 47 e e) e))) (v 45 (v 46 (v 47 e (v 30 e
      (v 32 e (v 28 (v 29 e e) (v 29 e e))))) (v 30 e (v 32 e (v 27 (v 17 e (v 18 e e)) (v 17 e e)))))
      e)) (v 11 (v 45 (v 46 e e) e) e))))) (v 34 (v 35 e (v 36 e (v 81 (v 23 e (v 44 (v 46 e e) e)) e)))
      (v 35 e (v 25 e (v 44 (v 45 (v 46 e e) e) e)))))) (v 59 (v 33 (v 34 e (v 35 (v 37 e (v 80 (v 22 e
      (v 24 e (v 45 e (v 69 (v 48 e (v 28 e (v 29 e (v 31 e (v 30 e (v 32 e (v 16 (v 50 e (v 51 e e))
      e))))))) e)))) (v 22 e (v 24 (v 45 e (v 13 e e)) e)))) (v 37 e (v 80 (v 22 e (v 45 (v 46 e e) e))
      e)))) (v 34 (v 35 (v 37 e (v 80 e (v 23 e (v 24 e e)))) (v 37 e (v 80 (v 23 e (v 44 (v 46 e e) e))
      e))) (v 35 (v 37 (v 80 e (v 24 (v 26 e (v 44 e (v 45 e e))) (v 26 e e))) (v 80 (v 24 e (v 44 (v 45
      (v 69 e (v 39 e (v 40 e (v 42 e (v 19 e (v 21 e (v 16 e e))))))) (v 28 e (v 29 e (v 31 e (v 19 e
      e))))) e)) (v 44 (v 45 e e) e))) (v 80 (v 26 e (v 44 (v 45 (v 46 (v 69 (v 37 e (v 28 e (v 29 (v 31
      e (v 16 e e)) (v 31 (v 16 e e) (v 16 e (v 19 e e)))))) e) e) e) e)) e)))) (v 33 (v 34 (v 35 (v 80 e
      (v 81 e (v 22 (v 23 e e) e))) (v 80 (v 81 (v 22 e (v 23 e e)) (v 22 (v 23 (v 11 e (v 12 e e)) e)
      e)) (v 22 (v 23 e e) e))) (v 35 (v 80 (v 81 (v 22 (v 24 e (v 11 e (v 45 e e))) (v 24 e e)) (v 22 (v
      24 e e) e)) (v 22 (v 24 (v 81 e e) e) e)) (v 11 e e))) (v 34 (v 35 (v 80 e (v 23 e e)) (v 44 (v 12
      e e) e)) e)))) (v 58 (v 59 (v 33 (v 34 (v 36 e (v 37 e (v 79 e (v 22 e (v 23 e e))))) (v 36 e (v 37
      e (v 79 (v 22 e (v 45 (v 68 (v 47 e e) e) e)) e)))) (v 34 (v 36 e (v 37 e (v 79 (v 23 (v 44 e (v 12
      e (v 68 e e))) (v 44 (v 68 (v 47 e e) e) e)) (v 44 (v 12 e e) e)))) (v 36 e e))) (v 33 (v 34 (v 36
      (v 79 e (v 81 e (v 22 (v 23 (v 25 e (v 11 (v 12 e e) e)) e) e))) (v 79 (v 81 (v 22 (v 23 e (v 11 e
      (v 68 e e))) (v 23 (v 12 e (v 68 e e)) (v 27 e (v 30 e (v 32 e (v 17 e e)))))) (v 22 (v 23 (v 11 (v
      12 e (v 68 e e)) (v 12 e e)) e) e)) (v 22 (v 23 (v 81 (v 11 e (v 12 e e)) e) e) e))) (v 36 (v 79 e
      (v 22 (v 25 e e) e)) (v 11 e e))) (v 34 (v 36 (v 79 e (v 23 (v 25 e e) e)) (v 44 (v 12 e e) e))
      e))) (v 48 (v 33 (v 34 e (v 79 (v 80 e e) e)) (v 34 (v 79 (v 80 (v 26 e (v 23 e e)) (v 23 e e)) (v
      23 e e)) e)) (v 22 (v 23 (v 79 (v 80 (v 70 e (v 11 e e)) e) e) (v 11 e e)) (v 33 e e))))) (v 57 (v
      58 (v 59 (v 33 (v 35 e (v 36 e (v 37 e (v 78 (v 22 e (v 67 (v 46 (v 47 e e) e) e)) e)))) (v 35 e (v
      36 e e))) (v 33 (v 35 e (v 36 e (v 11 e e))) (v 35 e e))) (v 48 (v 33 (v 35 (v 78 (v 80 e (v 26 e
      (v 22 e (v 67 (v 13 e e) e)))) (v 80 e (v 26 e e))) (v 78 (v 80 e e) e)) (v 35 (v 78 (v 80 (v 26 e
      (v 24 (v 44 (v 67 e (v 13 e e)) (v 67 e e)) e)) (v 24 (v 26 e e) e)) (v 24 (v 80 e e) e)) e)) (v 22
      (v 78 (v 24 (v 80 (v 70 (v 11 e (v 67 e (v 13 e e))) (v 11 e e)) (v 11 e e)) (v 11 e e)) (v 11 e
      e)) (v 33 (v 67 e e) e)))) (v 47 (v 48 e (v 22 (v 78 (v 79 (v 25 e e) e) e) e)) (v 22 e e)))) (v 56
      (v 57 (v 58 (v 59 (v 34 (v 35 e (v 36 e (v 37 e (v 77 (v 23 e (v 66 (v 46 e e) e)) e)))) (v 35 e (v
      36 e e))) (v 34 (v 35 e (v 36 e e)) (v 35 e e))) (v 48 (v 34 (v 35 (v 77 (v 80 e (v 26 e (v 23 e
      e))) (v 80 e (v 26 (v 23 e e) e))) (v 77 (v 80 (v 26 e (v 23 (v 66 e (v 12 e e)) e)) (v 23 e e)) (v
      23 (v 80 (v 26 e e) e) e))) (v 35 (v 77 (v 80 (v 26 e (v 24 e e)) (v 24 (v 26 e e) e)) (v 24 e e))
      e)) (v 77 (v 23 (v 24 e e) e) e))) (v 47 (v 48 e (v 77 (v 23 (v 79 (v 25 e (v 66 (v 12 e e) e)) e)
      e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 e (v 66 (v 12 e e) e)) e) e) e) e))) (v 46 (v 47 e (v 77 (v 78
      (v 24 (v 69 e e) e) e) e)) e))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33 (v 34 (v 35 e (v 36 e (v 22 (v
      23 e e) e))) (v 35 e e)) (v 34 (v 35 e e) e)) e) (v 22 (v 23 (v 24 e e) e) e)) (v 22 (v 23 (v 79 (v
      25 e (v 11 (v 12 e e) e)) e) e) e)) e) e)) (v 55 (v 56 (v 57 (v 157 (v 59 (v 33 (v 34 e (v 35 (v
      135 (v 37 e (v 22 e e)) e) e)) (v 34 (v 35 (v 135 (v 37 e (v 23 e e)) e) e) (v 24 (v 124 (v 26 e e)
      e) e))) (v 22 (v 23 e e) e)) (v 22 e e)) (v 22 e e)) (v 22 (v 78 e e) e)) (v 77 (v 23 e (v 66 e e))
      e))) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 (v 34 (v 134 (v 36 e (v 37 e (v 22 e e))) (v 36 e e)) (v
      134 (v 36 e e) e)) (v 34 (v 134 (v 36 e e) e) e)) (v 22 (v 23 (v 123 (v 25 e (v 11 e e)) e) e) e))
      (v 22 e e)) e) e) e)) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 (v 133 (v 35 e (v 36 e e)) (v 35 e e))
      (v 133 (v 35 e e) e)) e) (v 22 e e)) e) e) e)) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34 (v 35 e
      (v 36 e e)) (v 35 e e)) (v 34 (v 35 e e) e)) e) (v 121 (v 23 (v 24 e e) e) e)) e) e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 1, 2).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 (v 35 e (v 36 e (v 37
      e (v 23 e (v 44 e (v 46 e (v 47 (v 48 e (v 27 e (v 30 (v 31 (v 32 e (v 17 e e)) (v 32 e e)) (v 31
      (v 32 e (v 17 e e)) (v 32 e e))))) (v 27 e (v 28 (v 29 e (v 32 e (v 19 e e))) e))))))))) (v 35 e (v
      36 e (v 37 e (v 44 (v 45 (v 46 (v 47 e (v 48 e (v 28 (v 29 e (v 30 e e)) (v 29 e (v 30 e e))))) (v
      47 (v 48 e (v 27 (v 30 e (v 31 (v 17 e (v 18 e e)) (v 17 (v 18 (v 21 e e) e) (v 18 (v 21 e e) e))))
      (v 30 (v 31 (v 17 e e) (v 17 e e)) (v 31 (v 17 e e) (v 17 (v 18 (v 21 (v 38 e (v 6 e e)) e) e)
      e))))) e)) (v 46 (v 47 e e) e)) (v 45 (v 46 (v 47 e (v 28 (v 29 e (v 32 e (v 16 e (v 19 e e)))) (v
      29 e (v 32 e (v 16 e e))))) e) e))))))) (v 33 (v 34 e (v 35 e (v 36 (v 81 e (v 22 e (v 25 e e))) (v
      81 (v 22 e (v 45 e e)) e)))) (v 34 (v 35 e (v 36 e (v 81 (v 23 e (v 44 (v 46 e e) e)) e))) (v 35 e
      (v 25 e (v 44 (v 45 (v 46 e e) e) e)))))) (v 59 (v 33 (v 34 e (v 35 e (v 37 e (v 80 (v 22 e (v 45 e
      e)) e)))) (v 34 (v 35 e (v 37 (v 80 e (v 23 e (v 26 e e))) (v 80 (v 23 e (v 44 e e)) e))) (v 35 (v
      37 (v 80 e (v 24 e (v 26 e e))) (v 80 (v 24 e (v 44 (v 45 e e) e)) e)) (v 80 (v 26 e (v 44 (v 45 (v
      46 (v 69 e e) e) e) e)) e)))) (v 33 (v 34 e (v 35 (v 80 e (v 22 e e)) e)) (v 34 (v 35 e e) e)))) (v
      58 (v 59 (v 33 e (v 34 (v 36 e (v 37 e (v 79 (v 23 e (v 44 (v 68 e e) e)) (v 44 e e)))) (v 36 e (v
      79 (v 26 e (v 44 e e)) e)))) (v 33 (v 34 (v 36 (v 79 (v 81 e (v 22 e (v 23 e e))) (v 81 (v 22 e (v
      23 e e)) (v 22 e e))) (v 79 (v 81 e (v 22 e e)) (v 22 e e))) (v 36 (v 79 (v 81 (v 22 e (v 25 e e))
      (v 22 (v 25 e e) e)) (v 22 (v 25 e e) e)) e)) (v 34 (v 36 (v 79 (v 81 (v 23 (v 25 e (v 44 e (v 12 e
      e))) (v 25 e (v 27 e (v 30 e (v 31 e (v 21 e (v 49 e (v 17 e e)))))))) (v 23 (v 25 e e) e)) (v 23
      (v 25 e e) e)) (v 44 e e)) e))) (v 48 (v 33 e (v 34 (v 79 (v 80 (v 26 e (v 23 e e)) (v 23 e e)) e)
      e)) (v 22 e e)))) (v 57 (v 58 (v 59 (v 33 e (v 35 e (v 36 e (v 78 (v 26 e (v 44 e e)) e)))) (v 33
      (v 35 (v 36 e (v 78 (v 81 (v 22 e (v 24 e e)) (v 22 (v 24 e e) e)) (v 22 (v 24 e e) e))) (v 36 (v
      78 (v 81 e (v 22 (v 25 e e) e)) e) e)) (v 35 (v 36 e e) e))) (v 48 (v 33 e (v 35 (v 78 (v 80 (v 26
      e (v 24 e e)) (v 24 (v 26 e e) e)) e) e)) (v 22 (v 78 (v 24 e e) e) e))) (v 47 (v 48 e (v 22 (v 78
      (v 79 (v 25 e e) e) e) e)) (v 22 e e)))) (v 56 (v 57 (v 58 (v 59 (v 34 (v 35 e (v 36 e (v 37 e (v
      77 (v 23 e (v 66 (v 46 e e) e)) (v 88 e e))))) (v 35 e (v 36 e (v 77 (v 26 e (v 66 (v 45 (v 46 (v
      47 e e) e) e) e)) e)))) (v 34 (v 35 e (v 36 (v 77 (v 81 e (v 23 e e)) e) e)) (v 35 (v 36 e e) e)))
      (v 48 (v 34 (v 35 (v 77 e (v 80 e (v 26 (v 23 e e) e))) (v 77 (v 80 (v 26 e (v 23 (v 66 e (v 12 e
      e)) e)) (v 23 (v 26 e e) e)) (v 23 (v 80 (v 26 e e) e) e))) (v 35 (v 77 (v 80 (v 26 e (v 24 e e))
      (v 24 e e)) (v 24 (v 80 e e) e)) e)) (v 77 (v 23 e e) e))) (v 47 (v 48 e (v 77 (v 23 (v 79 (v 25 e
      (v 66 (v 12 e e) e)) e) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 e (v 66 (v 12 e e) e)) e) e) e) e)))
      (v 46 (v 47 (v 48 e (v 77 (v 78 (v 24 e e) e) e)) (v 77 (v 78 (v 24 (v 69 e e) e) e) e)) e))) (v 55
      (v 56 (v 57 (v 58 (v 158 (v 33 (v 34 e (v 35 e (v 22 (v 25 e e) e))) (v 34 (v 35 e e) e)) e) (v 22
      e e)) (v 22 (v 23 (v 79 e e) (v 11 e e)) e)) (v 22 (v 78 (v 24 e e) e) e)) (v 77 (v 23 e e) e))) (v
      55 (v 56 (v 57 (v 157 (v 59 (v 33 (v 34 e (v 35 e e)) (v 34 (v 35 (v 135 (v 37 e (v 23 e e)) e) (v
      23 e e)) (v 24 (v 124 e e) e))) (v 22 e e)) (v 22 e e)) (v 22 e e)) (v 22 e e)) (v 77 (v 23 (v 24 e
      e) e) e))) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 e (v 34 (v 134 (v 36 e e) e) e)) (v 22 (v 23 (v 123
      e e) e) e)) (v 22 e e)) e) e) e)) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 e (v 133 (v 35 e e) e)) (v
      22 (v 122 (v 24 e e) e) e)) (v 22 e e)) e) e) e)) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34 (v 35
      e (v 36 e e)) (v 35 e e)) (v 34 (v 35 e e) e)) (v 121 (v 23 e e) e)) (v 121 (v 23 (v 24 e e) e) e))
      e) e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 1, 3).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 e (v 35 e (v 36 e (v
      37 e (v 44 (v 45 (v 46 e (v 47 (v 48 e (v 27 e (v 30 e (v 17 e e)))) e)) (v 46 (v 47 e (v 28 e (v
      29 (v 32 e (v 16 (v 19 e (v 20 e e)) e)) (v 32 (v 16 (v 19 e e) e) (v 16 (v 19 e e) e))))) e)) (v
      45 (v 46 (v 47 e (v 28 (v 29 e (v 31 e (v 16 e (v 19 (v 21 e e) e)))) (v 29 e (v 31 (v 16 e e) (v
      16 e e))))) e) e))))))) (v 33 (v 34 e (v 35 e (v 36 e (v 81 (v 22 e (v 45 e e)) e)))) (v 34 (v 35 e
      (v 36 e (v 81 (v 23 e (v 44 e e)) e))) (v 35 e (v 25 e (v 44 (v 45 (v 46 e e) e) e)))))) (v 59 (v
      33 e (v 34 e (v 35 (v 37 (v 80 (v 24 e (v 26 e (v 44 e (v 45 e (v 28 e (v 29 e (v 31 e (v 32 e
      e)))))))) (v 24 e (v 26 e e))) (v 80 (v 24 e (v 44 (v 45 e (v 28 e (v 29 e (v 32 e (v 19 e (v 20 e
      e)))))) e)) e)) (v 80 (v 26 e (v 44 (v 45 e e) (v 28 e (v 29 e (v 31 e (v 16 e (v 21 e e)))))))
      e)))) (v 33 (v 34 e (v 35 (v 80 (v 81 e (v 22 e e)) (v 22 e e)) e)) (v 34 (v 35 e e) e)))) (v 58 (v
      59 (v 33 e (v 34 (v 36 e (v 37 e (v 79 (v 23 e (v 44 e e)) e))) (v 36 e (v 79 (v 26 e (v 44 (v 45
      (v 68 (v 47 e e) e) e) e)) e)))) (v 33 (v 34 (v 36 (v 79 e (v 81 e (v 22 e e))) (v 79 e (v 22 e
      e))) (v 36 (v 79 (v 81 e (v 22 (v 25 e e) e)) (v 22 (v 25 e e) e)) e)) (v 34 (v 36 (v 79 (v 81 (v
      23 e (v 25 e e)) (v 23 e e)) (v 23 (v 25 e e) e)) e) e))) (v 48 (v 33 e (v 34 (v 79 (v 80 (v 26 e
      (v 23 e e)) e) (v 23 e e)) e)) (v 22 e e)))) (v 57 (v 58 (v 59 (v 33 e (v 35 (v 36 e (v 37 e (v 78
      (v 24 e (v 44 (v 67 e e) e)) e))) (v 36 e (v 78 (v 26 e (v 44 (v 67 (v 46 (v 47 e e) e) e) e))
      e)))) (v 33 (v 35 (v 36 e (v 78 (v 81 (v 22 e (v 24 e e)) (v 22 (v 24 e e) e)) (v 22 (v 24 e e)
      e))) (v 36 (v 78 e (v 22 (v 25 e e) e)) e)) (v 35 (v 36 e e) e))) (v 48 (v 33 e (v 35 (v 78 (v 80
      (v 26 e (v 24 (v 44 (v 67 e (v 13 e e)) (v 67 e e)) e)) (v 24 (v 26 e e) e)) (v 24 (v 80 (v 26 e e)
      e) e)) e)) (v 22 (v 78 (v 24 e e) e) (v 33 (v 67 e e) e)))) (v 47 (v 48 e (v 22 (v 78 (v 79 (v 25 e
      e) e) e) e)) (v 22 e e)))) (v 56 (v 57 (v 58 (v 59 (v 34 (v 35 e (v 36 e (v 37 (v 77 e (v 23 e (v
      26 e e))) (v 77 (v 23 e (v 66 (v 46 e e) e)) e)))) (v 35 e (v 36 e (v 77 (v 26 e (v 66 (v 45 (v 46
      (v 47 e e) e) e) e)) e)))) (v 34 (v 35 e (v 36 e e)) (v 35 e e))) (v 48 (v 34 (v 35 e (v 77 (v 80
      (v 26 (v 23 e (v 66 e (v 46 e e))) (v 23 e e)) (v 23 e e)) (v 23 e e))) (v 35 (v 77 (v 80 (v 26 (v
      24 e (v 66 e (v 45 e e))) (v 24 e e)) (v 24 e e)) (v 24 e e)) (v 66 e e))) (v 77 (v 23 e e) e))) (v
      47 (v 48 (v 34 (v 77 e (v 79 (v 25 e (v 26 e e)) (v 25 e e))) (v 77 e e)) (v 77 (v 23 (v 79 e e) e)
      e)) (v 77 (v 23 (v 79 e e) e) e))) (v 46 (v 47 (v 48 (v 77 e (v 78 (v 24 e (v 25 e e)) (v 24 e e)))
      (v 77 (v 78 (v 24 e e) e) e)) (v 77 (v 78 (v 24 (v 69 e (v 66 e e)) e) e) e)) (v 77 e e)))) (v 55
      (v 56 (v 57 (v 58 (v 158 (v 33 (v 34 (v 35 e (v 36 e (v 22 e e))) (v 35 e e)) (v 34 (v 35 e e) e))
      e) (v 22 e e)) (v 22 (v 23 (v 79 e e) e) e)) (v 22 (v 78 (v 24 e e) e) e)) e)) (v 55 (v 56 (v 57 (v
      157 (v 59 (v 33 e (v 34 e (v 24 (v 124 (v 26 e e) e) e))) (v 22 e e)) e) (v 22 e e)) (v 22 e e)) (v
      77 (v 23 e e) e))) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 e (v 34 (v 134 (v 36 e e) e) e)) (v 22 (v
      23 (v 123 e e) e) e)) (v 22 e e)) e) e) (v 77 e e))) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 e (v 133
      (v 35 (v 36 e e) e) e)) (v 22 (v 122 (v 24 e e) e) e)) (v 22 e e)) e) e) (v 77 e e))) (v 154 (v 56
      (v 57 (v 58 (v 59 (v 132 (v 34 (v 35 e (v 36 e (v 121 (v 23 e e) e))) (v 35 e e)) (v 34 (v 35 e e)
      e)) e) (v 121 (v 23 e e) e)) (v 121 (v 23 (v 79 e e) e) e)) (v 121 (v 78 (v 24 e e) e) e)) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 1, 4).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 (v 34 e (v 35 e (v 36 e (v 37
      e (v 22 e (v 45 e (v 46 (v 47 e (v 48 e (v 28 (v 29 e (v 30 e e)) (v 29 e (v 30 e e))))) (v 47 (v
      48 e (v 27 (v 30 e (v 31 e (v 32 e e))) (v 30 e (v 31 e (v 32 e e))))) e)))))))) (v 34 e (v 35 e (v
      36 e (v 37 e (v 44 (v 45 (v 46 e (v 47 (v 48 e (v 27 e (v 30 (v 32 e (v 17 e e)) (v 32 e (v 17 e
      e))))) (v 27 e (v 28 e e)))) (v 46 (v 47 e (v 28 e (v 29 e (v 31 (v 16 e e) (v 16 e e))))) e)) (v
      45 (v 46 e e) e))))))) (v 33 (v 34 e (v 35 e (v 36 e (v 81 (v 22 e (v 45 (v 46 e e) e)) (v 11 e
      e))))) (v 34 e (v 35 e (v 25 e (v 44 (v 45 (v 46 e e) e) e)))))) (v 59 (v 33 (v 34 e (v 35 e (v 37
      e (v 80 (v 22 e (v 45 e e)) e)))) (v 34 (v 35 e (v 37 e (v 80 e e))) (v 35 e (v 80 (v 26 e (v 44 (v
      45 (v 46 e e) e) e)) e)))) (v 33 (v 34 e (v 35 e e)) (v 34 (v 35 e e) e)))) (v 58 (v 59 (v 33 (v 34
      e (v 36 e (v 37 e (v 79 (v 22 e (v 45 (v 68 e e) e)) e)))) (v 34 (v 36 e (v 37 e (v 79 (v 23 e (v
      44 e e)) e))) (v 36 e (v 79 (v 26 e (v 44 (v 45 (v 68 (v 47 e e) e) e) e)) e)))) (v 33 (v 34 (v 36
      (v 79 (v 81 e (v 22 e (v 23 e e))) (v 81 (v 22 e (v 23 e e)) (v 22 e e))) (v 79 (v 81 e (v 22 e e))
      (v 22 e e))) (v 36 (v 79 (v 81 (v 22 (v 25 e (v 11 e (v 45 e e))) (v 25 e e)) (v 22 (v 25 e e) e))
      (v 22 (v 25 e e) e)) (v 11 e e))) (v 34 (v 36 (v 79 (v 81 (v 23 e (v 25 e e)) (v 23 e e)) (v 23 (v
      25 e e) e)) e) e))) (v 48 (v 33 (v 34 e (v 79 (v 80 (v 26 e (v 22 e e)) e) e)) (v 34 (v 79 (v 80 (v
      26 e (v 23 e e)) (v 23 e e)) (v 23 e e)) e)) (v 22 (v 23 e e) e)))) (v 57 (v 58 (v 59 (v 33 (v 35 e
      (v 36 e (v 37 e (v 78 (v 22 e (v 67 (v 46 (v 47 e e) e) e)) (v 11 e e))))) (v 35 e (v 36 e (v 78 (v
      26 e (v 44 (v 67 (v 46 (v 47 e e) e) e) e)) e)))) (v 33 (v 35 e (v 36 e (v 11 e e))) (v 35 e e)))
      (v 48 (v 33 (v 35 (v 78 (v 80 (v 26 e (v 22 e (v 24 e (v 67 (v 69 e e) e)))) (v 26 e (v 22 (v 24 e
      (v 11 e e)) e))) (v 80 (v 26 e (v 22 (v 24 e (v 11 e e)) e)) (v 26 e (v 11 e e)))) (v 78 (v 80 (v
      26 e (v 22 e e)) (v 22 e e)) (v 22 e e))) (v 35 (v 78 (v 80 (v 26 e (v 24 e e)) (v 24 e e)) (v 24 e
      e)) e)) (v 22 (v 78 (v 24 e (v 11 e e)) e) e))) (v 47 (v 48 (v 33 (v 78 e (v 79 e (v 25 e e))) (v
      78 (v 79 e e) e)) (v 22 (v 78 (v 79 (v 25 e (v 11 e e)) e) e) e)) (v 22 (v 78 e e) e)))) (v 56 (v
      57 (v 58 (v 59 (v 34 e (v 35 e (v 36 e (v 77 (v 26 e (v 66 (v 45 (v 46 e e) e) e)) e)))) (v 34 e (v
      35 e e))) (v 48 (v 34 (v 35 e (v 77 (v 80 e (v 23 e e)) (v 23 e e))) (v 35 e e)) (v 77 (v 23 e e)
      e))) (v 47 (v 48 (v 34 (v 77 (v 79 e (v 25 e (v 26 e (v 66 e e)))) (v 79 e (v 25 e e))) (v 77 (v 79
      e e) e)) (v 77 (v 23 (v 79 e e) e) e)) (v 77 (v 23 (v 79 e e) e) e))) (v 46 (v 47 e (v 77 (v 78 (v
      24 e e) e) e)) (v 77 (v 78 (v 68 e e) e) e)))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33 (v 34 e (v 35 e
      e)) (v 34 e e)) e) (v 22 (v 23 e e) e)) (v 22 (v 23 (v 79 e e) e) e)) e) e)) (v 55 (v 56 (v 57 (v
      157 (v 59 (v 33 (v 34 e (v 35 (v 135 (v 37 e (v 22 e e)) e) (v 22 e e))) (v 34 (v 35 e e) (v 24 e
      e))) (v 22 e e)) (v 22 e e)) (v 22 e e)) (v 22 (v 78 (v 24 e e) e) e)) (v 77 (v 23 e e) e))) (v 55
      (v 56 (v 156 (v 58 (v 59 (v 33 (v 34 (v 134 (v 36 e (v 37 e (v 22 e e))) (v 36 e e)) (v 134 (v 36
      (v 37 e (v 22 e e)) e) e)) (v 34 (v 134 (v 36 (v 37 e (v 23 (v 123 (v 25 e e) e) e)) e) e) e)) (v
      22 (v 23 (v 123 e e) e) e)) (v 22 e e)) (v 22 e e)) (v 22 e e)) (v 77 (v 23 (v 123 (v 25 e e) e) e)
      e))) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 (v 133 (v 35 e (v 36 e e)) (v 35 e e)) (v 133 (v 35 e e)
      e)) e) (v 22 (v 122 (v 24 (v 80 e e) e) e) e)) (v 22 (v 122 e e) e)) e) e)) (v 154 (v 56 (v 57 (v
      58 (v 59 (v 132 (v 34 e (v 35 e e)) (v 34 e e)) e) (v 121 (v 23 e e) e)) (v 121 (v 23 (v 79 e e) e)
      e)) e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 2, 0).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 (v 35 e (v 36 e (v 37
      e (v 23 e (v 44 e (v 46 e (v 47 e (v 27 e (v 28 (v 30 e (v 31 e (v 32 e e))) e))))))))) (v 35 e (v
      36 e (v 37 e (v 44 (v 45 (v 46 e (v 47 e e)) (v 46 e e)) (v 45 (v 46 e e) e))))))) (v 33 e (v 34 (v
      35 e (v 36 e (v 81 (v 23 e (v 44 e e)) e))) (v 35 e (v 25 e (v 44 (v 45 (v 46 e e) e) e)))))) (v 59
      (v 33 e (v 34 (v 35 e (v 37 (v 80 (v 23 e (v 26 e (v 44 e (v 46 e (v 28 e (v 32 e (v 27 e e)))))))
      (v 23 e (v 26 (v 44 e (v 46 e e)) e))) (v 80 (v 23 e (v 44 e e)) e))) (v 35 e (v 80 (v 26 e (v 44
      (v 45 (v 46 e e) e) (v 28 e (v 32 e (v 30 e (v 16 e e)))))) (v 44 e e))))) (v 33 e (v 34 (v 35 e e)
      e)))) (v 58 (v 59 (v 33 e (v 34 (v 36 e (v 37 e (v 79 (v 23 (v 44 e (v 12 e (v 68 e (v 38 e (v 42 e
      (v 30 e (v 17 e e))))))) (v 44 (v 68 e e) (v 27 (v 31 e (v 30 e (v 17 e (v 18 e e)))) (v 31 (v 30 e
      (v 17 e e)) (v 30 (v 17 e e) (v 17 e e)))))) (v 44 (v 12 e e) e)))) (v 36 e (v 79 (v 26 e (v 44 e
      e)) e)))) (v 33 (v 34 (v 36 (v 79 e (v 81 (v 22 e (v 23 e e)) (v 22 e e))) (v 79 e (v 22 e e))) (v
      36 (v 79 (v 81 (v 22 e (v 25 e e)) (v 22 e e)) (v 22 e e)) e)) (v 34 (v 36 (v 79 (v 81 (v 23 (v 25
      e (v 44 e (v 12 e e))) (v 25 e e)) (v 23 (v 25 e e) e)) (v 23 (v 25 (v 81 e e) e) e)) (v 44 e e))
      e))) (v 48 (v 33 (v 34 (v 79 e (v 80 e (v 26 e e))) (v 79 (v 80 e (v 22 e e)) e)) (v 34 (v 79 (v 80
      (v 26 e (v 23 (v 44 e (v 12 e e)) e)) (v 23 (v 26 (v 44 e (v 12 e e)) e) e)) (v 23 (v 80 (v 26 e e)
      e) e)) e)) (v 22 e e)))) (v 57 (v 58 (v 59 (v 33 e (v 35 e (v 36 e (v 78 (v 26 e (v 44 e e)) e))))
      (v 33 (v 35 e (v 36 e e)) (v 35 e e))) (v 48 (v 33 (v 35 (v 78 (v 80 e (v 26 e (v 22 e e))) (v 80 e
      (v 26 e e))) (v 78 (v 80 e (v 22 e e)) e)) (v 35 (v 78 (v 80 e (v 24 e e)) (v 24 e e)) e)) (v 22 e
      e))) (v 47 (v 48 (v 33 e (v 78 (v 79 (v 25 e e) e) e)) (v 22 e e)) (v 22 e e)))) (v 56 (v 57 (v 58
      (v 59 (v 34 (v 35 e (v 36 e (v 37 (v 77 (v 23 e (v 26 e (v 66 (v 46 e (v 47 e (v 30 e (v 27 (v 28 e
      (v 31 e (v 32 e e))) (v 28 e e))))) (v 46 e e)))) (v 23 (v 26 e (v 88 e (v 12 e e))) (v 26 e e)))
      (v 77 (v 23 e (v 66 (v 46 e e) e)) (v 88 e e))))) (v 35 e (v 36 e (v 77 (v 26 e (v 66 (v 45 (v 46 e
      e) e) e)) e)))) (v 34 (v 35 e (v 36 e e)) (v 35 e e))) (v 48 (v 34 (v 35 e (v 77 (v 80 (v 26 (v 23
      e (v 66 e (v 46 e e))) (v 23 e e)) (v 23 e e)) (v 23 (v 80 (v 26 (v 88 e (v 12 e e)) e) e) e))) (v
      35 (v 77 e (v 24 e e)) (v 66 e e))) (v 77 (v 23 e e) e))) (v 47 (v 48 (v 34 (v 77 (v 79 (v 25 e (v
      26 e (v 23 (v 66 (v 12 e (v 68 (v 36 e (v 37 e (v 27 e (v 30 e (v 31 e (v 17 e e)))))) (v 36 e e)))
      (v 12 e (v 68 (v 36 e e) e))) (v 66 (v 68 (v 36 e e) e) e)))) (v 25 e (v 26 e (v 66 (v 12 (v 90 e
      e) e) e)))) (v 79 (v 25 e (v 26 e (v 88 (v 12 (v 68 e e) e) e))) (v 25 e e))) (v 77 (v 79 (v 25 e
      e) e) e)) (v 77 (v 23 (v 79 (v 25 e (v 66 (v 12 e e) e)) e) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 e
      (v 66 (v 12 e (v 27 e (v 30 e (v 31 e (v 28 e e))))) e)) (v 66 (v 12 e e) e)) e) e) e))) (v 46 (v
      47 e (v 77 (v 78 (v 24 e e) e) e)) (v 77 (v 78 (v 68 (v 25 e e) e) e) e)))) (v 55 (v 56 (v 57 (v 58
      (v 158 (v 33 e (v 34 (v 35 e (v 23 e e)) e)) e) e) (v 22 e e)) (v 22 e e)) (v 77 (v 23 e e) e))) (v
      55 (v 56 (v 57 (v 157 (v 59 (v 33 e (v 34 (v 35 e (v 23 e e)) e)) e) e) (v 22 e e)) (v 22 e e)) (v
      77 (v 23 e e) e))) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 e (v 34 (v 134 (v 36 e e) e) e)) (v 22 e
      e)) (v 22 e e)) e) e) (v 77 (v 23 (v 123 (v 25 e e) e) e) e))) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33
      e (v 133 (v 35 e e) e)) e) (v 22 e e)) e) e) e)) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34 (v 35
      e (v 36 e (v 121 (v 23 (v 26 e e) e) e))) (v 35 e e)) (v 34 (v 35 e e) e)) e) (v 121 (v 23 e e) e))
      (v 121 (v 23 (v 79 (v 25 e e) e) e) e)) e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 2, 1).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 (v 35 e (v 36 e (v 37
      e (v 23 e (v 44 e (v 46 e (v 47 (v 48 e (v 27 e (v 29 (v 30 e (v 32 (v 17 e e) (v 17 e e))) (v 30 e
      e)))) (v 27 e (v 28 (v 30 e (v 31 e (v 18 e e))) e))))))))) (v 35 e (v 36 e (v 37 e (v 44 (v 45 (v
      46 (v 47 e (v 48 e (v 28 (v 29 (v 31 e (v 32 e e)) (v 31 e (v 32 e e))) (v 29 (v 31 e (v 32 e e))
      (v 31 e (v 32 e e)))))) (v 47 (v 48 e (v 27 (v 29 (v 32 e (v 17 e (v 19 e (v 20 e e)))) (v 32 e (v
      17 (v 19 e e) (v 19 e e)))) (v 29 (v 32 (v 17 e e) (v 17 e e)) (v 32 (v 17 e e) (v 17 (v 19 (v 20
      (v 38 e (v 6 e e)) e) e) e))))) e)) (v 46 (v 47 e e) e)) (v 45 (v 46 (v 47 e (v 28 (v 30 e (v 31 e
      (v 16 e (v 18 e e)))) (v 30 e (v 31 e (v 16 e e))))) e) e))))))) (v 33 (v 34 e (v 35 e (v 36 (v 81
      e (v 22 e (v 25 e e))) (v 81 (v 22 e (v 45 e e)) e)))) (v 34 (v 35 e (v 36 e (v 81 (v 23 e (v 44 (v
      46 e e) e)) e))) (v 35 e (v 25 e (v 44 (v 45 (v 46 e e) e) e)))))) (v 59 (v 33 (v 34 e (v 35 e (v
      37 e (v 80 (v 22 e (v 45 e e)) e)))) (v 34 (v 35 e (v 37 (v 80 e (v 23 e (v 26 e e))) (v 80 (v 23 e
      (v 44 e e)) e))) (v 35 (v 37 (v 80 e (v 24 e (v 26 e e))) (v 80 (v 24 e (v 44 (v 45 e e) e)) e)) (v
      80 (v 26 e (v 44 (v 45 (v 46 (v 69 e e) e) e) e)) e)))) (v 33 (v 34 e (v 35 (v 80 e (v 22 e e)) e))
      (v 34 (v 35 e e) e)))) (v 58 (v 59 (v 33 e (v 34 (v 36 e (v 37 e (v 79 (v 23 e (v 44 (v 68 e e) e))
      (v 44 e e)))) (v 36 e (v 79 (v 26 e (v 44 e e)) e)))) (v 33 (v 34 (v 36 (v 79 (v 81 e (v 22 e (v 23
      e e))) (v 81 (v 22 e (v 23 e e)) (v 22 e e))) (v 79 (v 81 e (v 22 e e)) (v 22 e e))) (v 36 (v 79 (v
      81 (v 22 e (v 25 e e)) (v 22 (v 25 e e) e)) (v 22 (v 25 e e) e)) e)) (v 34 (v 36 (v 79 (v 81 (v 23
      (v 25 e (v 44 e (v 12 e e))) (v 25 e (v 27 e (v 29 e (v 32 e (v 19 e (v 49 e (v 17 e e)))))))) (v
      23 (v 25 e e) e)) (v 23 (v 25 e e) e)) (v 44 e e)) e))) (v 48 (v 33 e (v 34 (v 79 (v 80 (v 26 e (v
      23 e e)) (v 23 e e)) e) e)) (v 22 e e)))) (v 57 (v 58 (v 59 (v 33 e (v 35 e (v 36 e (v 78 (v 26 e
      (v 44 e e)) e)))) (v 33 (v 35 (v 36 e (v 78 (v 81 (v 22 e (v 24 e e)) (v 22 (v 24 e e) e)) (v 22 (v
      24 e e) e))) (v 36 (v 78 (v 81 e (v 22 (v 25 e e) e)) e) e)) (v 35 (v 36 e e) e))) (v 48 (v 33 e (v
      35 (v 78 (v 80 (v 26 e (v 24 e e)) (v 24 (v 26 e e) e)) e) e)) (v 22 (v 78 (v 24 e e) e) e))) (v 47
      (v 48 e (v 22 (v 78 (v 79 (v 25 e e) e) e) e)) (v 22 e e)))) (v 56 (v 57 (v 58 (v 59 (v 34 (v 35 e
      (v 36 e (v 37 e (v 77 (v 23 e (v 66 (v 46 e e) e)) (v 88 e e))))) (v 35 e (v 36 e (v 77 (v 26 e (v
      66 (v 45 (v 46 (v 47 e e) e) e) e)) e)))) (v 34 (v 35 e (v 36 (v 77 (v 81 e (v 23 e e)) e) e)) (v
      35 (v 36 e e) e))) (v 48 (v 34 (v 35 (v 77 e (v 80 e (v 26 (v 23 e e) e))) (v 77 (v 80 (v 26 e (v
      23 (v 66 e (v 12 e e)) e)) (v 23 (v 26 e e) e)) (v 23 (v 80 (v 26 e e) e) e))) (v 35 (v 77 (v 80 (v
      26 e (v 24 e e)) (v 24 e e)) (v 24 (v 80 e e) e)) e)) (v 77 (v 23 e e) e))) (v 47 (v 48 e (v 77 (v
      23 (v 79 (v 25 e (v 66 (v 12 e e) e)) e) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 e (v 66 (v 12 e e)
      e)) e) e) e) e))) (v 46 (v 47 (v 48 e (v 77 (v 78 (v 24 e e) e) e)) (v 77 (v 78 (v 24 (v 69 e e) e)
      e) e)) e))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33 (v 34 e (v 35 e (v 22 (v 25 e e) e))) (v 34 (v 35
      e e) e)) e) (v 22 e e)) (v 22 (v 23 (v 79 e e) (v 11 e e)) e)) (v 22 (v 78 (v 24 e e) e) e)) (v 77
      (v 23 e e) e))) (v 55 (v 56 (v 57 (v 157 (v 59 (v 33 (v 34 e (v 35 e e)) (v 34 (v 35 (v 135 (v 37 e
      (v 23 e e)) e) (v 23 e e)) (v 24 (v 124 e e) e))) (v 22 e e)) (v 22 e e)) (v 22 e e)) (v 22 e e))
      (v 77 (v 23 (v 24 e e) e) e))) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 e (v 34 (v 134 (v 36 e e) e)
      e)) (v 22 (v 23 (v 123 e e) e) e)) (v 22 e e)) e) e) e)) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 e (v
      133 (v 35 e e) e)) (v 22 (v 122 (v 24 e e) e) e)) (v 22 e e)) e) e) e)) (v 154 (v 56 (v 57 (v 58 (v
      59 (v 132 (v 34 (v 35 e (v 36 e e)) (v 35 e e)) (v 34 (v 35 e e) e)) (v 121 (v 23 e e) e)) (v 121
      (v 23 (v 24 e e) e) e)) e) e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 2, 2).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 (v 35 e (v 36 e (v 37
      e (v 23 e (v 44 e (v 46 e (v 47 (v 48 e (v 27 e (v 29 (v 30 e (v 31 (v 32 e (v 17 (v 18 e e) e)) (v
      32 e e))) (v 30 e e)))) (v 27 e (v 28 e e))))))))) (v 35 e (v 36 e (v 37 e (v 44 (v 45 (v 46 e (v
      47 e e)) (v 46 (v 47 e e) e)) (v 45 (v 46 (v 47 (v 48 e (v 29 e (v 30 e e))) (v 28 e (v 30 e (v 32
      e (v 16 e e))))) e) e))))))) (v 33 e (v 34 (v 35 e (v 36 (v 81 (v 23 e (v 25 e (v 44 e (v 46 e (v
      29 e (v 31 e (v 27 e (v 30 e e)))))))) (v 23 e (v 25 (v 44 e (v 46 e e)) e))) (v 81 (v 23 e (v 44 e
      e)) e))) (v 35 e (v 25 (v 81 e (v 44 (v 45 (v 46 e e) e) e)) (v 44 (v 45 (v 46 e (v 29 e (v 31 e (v
      27 e (v 19 e e))))) e) e)))))) (v 59 (v 33 e (v 34 (v 35 e (v 37 e (v 80 (v 23 e (v 44 e e)) e)))
      (v 35 e (v 80 (v 26 e (v 44 e e)) e)))) (v 33 e (v 34 (v 35 e e) e)))) (v 58 (v 59 (v 33 e (v 34 (v
      36 (v 37 e (v 79 (v 23 e (v 25 e (v 44 e (v 68 (v 48 e (v 27 e (v 29 e (v 30 (v 31 e (v 32 e e))
      e)))) e)))) (v 23 (v 25 e (v 44 e (v 12 e e))) (v 25 e e)))) (v 37 e (v 79 (v 23 e (v 44 e e)) (v
      44 e e)))) (v 36 (v 37 e (v 79 (v 25 e (v 44 e e)) e)) (v 79 (v 26 e (v 44 e e)) e)))) (v 33 (v 34
      e (v 36 (v 79 e (v 22 e e)) e)) (v 34 (v 36 (v 79 (v 81 (v 23 e (v 25 (v 44 e (v 68 (v 14 e e) e))
      e)) (v 23 e e)) (v 23 (v 25 (v 81 (v 44 e (v 12 e e)) e) e) e)) e) (v 44 (v 45 (v 68 (v 14 e e) e)
      e) e)))) (v 48 (v 33 e (v 34 (v 79 (v 80 (v 26 e (v 23 e e)) e) e) e)) (v 22 e e)))) (v 57 (v 58 (v
      59 (v 33 e (v 35 e (v 36 e (v 78 (v 26 e (v 44 e e)) e)))) (v 33 (v 35 (v 36 (v 78 (v 81 e (v 22 e
      (v 24 e e))) (v 81 e (v 22 e e))) (v 78 (v 81 (v 22 e (v 24 e e)) (v 22 e e)) (v 22 e e))) (v 36 (v
      78 (v 81 e (v 22 e e)) (v 22 e e)) e)) (v 35 (v 36 (v 78 (v 81 e (v 24 e e)) e) e) e))) (v 48 (v 33
      e (v 35 (v 78 (v 80 (v 26 e (v 24 e e)) e) e) e)) (v 22 e e))) (v 47 (v 48 e (v 22 e e)) e))) (v 56
      (v 57 (v 58 (v 59 (v 34 (v 35 e (v 36 e (v 37 e (v 77 (v 23 (v 66 e (v 12 e (v 46 e (v 41 e (v 43 e
      (v 27 e (v 17 e e))))))) (v 66 (v 46 e (v 30 (v 32 e (v 27 e (v 17 e e))) (v 32 (v 27 e (v 17 e e))
      (v 27 (v 17 e (v 18 e e)) (v 17 e e))))) e)) (v 88 (v 12 e e) e))))) (v 35 e (v 36 e (v 77 (v 26 e
      (v 66 (v 45 (v 46 (v 47 e e) e) e) e)) e)))) (v 34 (v 35 (v 36 (v 77 e (v 81 e (v 23 e e))) (v 77 e
      (v 23 e e))) (v 36 (v 77 (v 81 (v 23 (v 25 e (v 66 e (v 12 e e))) (v 25 e e)) (v 23 (v 25 (v 66 e
      (v 12 e e)) e) e)) (v 23 (v 25 (v 81 e e) e) e)) (v 66 e e))) (v 35 (v 36 (v 77 (v 81 e (v 24 e e))
      e) e) e))) (v 48 (v 34 (v 35 (v 77 e (v 80 (v 26 e (v 23 e e)) (v 26 (v 23 e e) e))) (v 77 (v 80 (v
      26 e (v 23 (v 66 e (v 12 e e)) e)) (v 23 (v 26 e e) e)) (v 23 (v 80 (v 26 e e) e) e))) (v 35 (v 77
      (v 80 (v 26 e (v 24 e e)) (v 24 e e)) (v 24 e e)) e)) (v 77 (v 23 e e) e))) (v 47 (v 48 (v 34 (v 77
      (v 79 (v 25 e (v 26 e (v 23 (v 66 (v 12 e (v 68 (v 36 e (v 37 e (v 27 e (v 30 e (v 32 e (v 17 e (v
      18 e e))))))) (v 36 e e))) (v 12 e (v 68 (v 36 e e) e))) (v 66 (v 68 (v 36 e e) e) e)))) (v 25 e (v
      26 e (v 66 (v 12 e e) e)))) (v 79 (v 25 e (v 26 e (v 88 (v 12 (v 68 e e) e) e))) (v 25 e e))) (v 77
      (v 79 (v 25 e e) e) e)) (v 77 (v 23 (v 79 (v 25 (v 70 e (v 66 (v 12 e e) e)) (v 66 (v 12 e (v 27 e
      (v 30 e (v 32 e (v 29 e e))))) e)) e) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 e (v 66 (v 12 e e) e))
      e) e) e) e))) (v 46 (v 47 (v 48 e (v 77 (v 78 (v 24 e e) e) e)) (v 77 (v 78 (v 24 e e) e) e)) (v 77
      (v 78 (v 68 (v 25 e e) e) e) e)))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33 e (v 34 (v 35 e (v 23 e e))
      e)) e) e) (v 22 e e)) (v 22 e e)) (v 77 (v 23 e e) e))) (v 55 (v 56 (v 57 (v 157 (v 59 (v 33 e (v
      34 (v 35 e (v 23 e e)) e)) e) e) (v 22 e e)) (v 22 e e)) (v 77 (v 23 e e) e))) (v 55 (v 56 (v 156
      (v 58 (v 59 (v 33 e (v 34 (v 134 (v 36 (v 37 e (v 23 (v 123 (v 25 e e) e) e)) e) e) e)) (v 22 e e))
      (v 22 e e)) e) e) (v 77 (v 23 (v 123 (v 25 e e) e) e) e))) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 e
      (v 133 (v 35 e e) e)) (v 22 e e)) (v 22 e e)) e) e) e)) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34
      (v 35 e (v 36 e e)) (v 35 e e)) (v 34 (v 35 e e) e)) (v 121 (v 23 (v 24 e e) e) e)) (v 121 (v 23 (v
      24 e e) e) e)) (v 121 (v 23 (v 79 (v 25 e e) e) e) e)) e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 2, 3).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 e (v 35 e (v 36 e (v
      37 e (v 44 (v 45 e (v 46 (v 47 (v 48 e (v 29 e (v 32 e (v 16 e (v 17 e e))))) e) e)) (v 45 (v 46 (v
      47 e (v 28 (v 30 e (v 31 e (v 16 e (v 18 (v 21 e e) e)))) (v 30 e (v 31 (v 16 e e) (v 16 e e)))))
      (v 27 (v 30 e (v 31 e (v 17 e (v 18 e e)))) (v 30 (v 31 e (v 17 e e)) (v 31 e (v 17 e e)))))
      e))))))) (v 33 e (v 34 e (v 35 (v 36 e (v 81 (v 24 e (v 44 e e)) e)) (v 25 e (v 44 (v 45 e e)
      e)))))) (v 59 (v 33 e (v 34 e (v 35 (v 37 (v 80 (v 24 e (v 26 e (v 44 e (v 45 e e)))) (v 24 e (v 26
      e e))) (v 80 (v 24 e (v 44 e e)) e)) (v 80 (v 26 e (v 44 (v 45 e e) e)) e)))) (v 33 e (v 34 e e))))
      (v 58 (v 59 (v 33 e (v 34 (v 36 (v 37 e (v 79 (v 23 e (v 25 e (v 44 e (v 68 e e)))) (v 23 e (v 25 e
      e)))) (v 37 e (v 79 (v 23 e (v 44 e e)) e))) (v 36 (v 37 e (v 79 (v 25 e (v 44 e e)) e)) (v 79 (v
      26 e (v 44 e e)) e)))) (v 33 (v 34 e (v 36 (v 79 e (v 22 e e)) e)) (v 34 (v 36 (v 79 (v 81 (v 23 e
      (v 25 e e)) (v 23 e e)) (v 23 e e)) e) (v 44 e e)))) (v 48 (v 33 e (v 34 (v 79 (v 80 (v 26 e (v 23
      e e)) (v 23 e e)) (v 23 e e)) e)) (v 22 e e)))) (v 57 (v 58 (v 59 (v 33 e (v 35 (v 36 e (v 37 e (v
      78 (v 24 e (v 44 (v 67 (v 47 e e) e) e)) e))) (v 36 (v 37 e (v 78 (v 25 e (v 44 e e)) e)) (v 78 (v
      26 e (v 44 e e)) e)))) (v 33 (v 35 (v 36 (v 78 e (v 81 e (v 22 e e))) (v 78 (v 81 (v 22 e (v 24 e
      e)) (v 22 e e)) (v 22 e e))) (v 36 (v 78 (v 81 (v 22 e (v 25 e e)) (v 22 e e)) (v 22 e e)) e)) (v
      35 (v 36 (v 78 e (v 24 e e)) e) e))) (v 48 (v 33 e (v 35 (v 78 (v 80 (v 26 e (v 24 e e)) (v 24 (v
      26 e e) e)) (v 24 (v 80 (v 26 e e) e) e)) e)) (v 22 e e))) (v 47 (v 48 (v 33 e (v 78 (v 79 (v 25 e
      e) e) e)) (v 22 e e)) (v 22 e e)))) (v 56 (v 57 (v 58 (v 59 (v 34 (v 35 e (v 36 e (v 37 (v 77 (v 23
      e (v 26 e (v 66 (v 46 e (v 47 e (v 30 e (v 31 e (v 27 e (v 28 e e)))))) (v 46 e e)))) (v 23 e (v 26
      e e))) (v 77 (v 23 e (v 66 (v 46 e (v 30 e (v 31 e (v 27 e (v 17 (v 18 e e) e))))) e)) e)))) (v 35
      e (v 36 e (v 77 (v 26 e (v 66 (v 45 (v 46 (v 47 e (v 30 e (v 31 e (v 28 e (v 16 (v 21 e e) e)))))
      e) e) e)) e)))) (v 34 (v 35 e (v 36 (v 77 (v 81 e (v 23 e e)) (v 23 e e)) e)) (v 35 (v 36 e e) e)))
      (v 48 (v 34 (v 35 e (v 77 (v 80 (v 26 (v 23 e (v 66 e (v 46 e e))) (v 23 e e)) (v 23 e e)) (v 23 e
      e))) (v 35 (v 77 (v 80 (v 26 (v 24 e (v 66 e (v 45 e e))) (v 24 e e)) (v 24 e e)) (v 24 e e)) (v 66
      e e))) (v 77 (v 23 e e) e))) (v 47 (v 48 (v 34 (v 77 (v 79 (v 25 e (v 26 e (v 23 (v 66 e (v 12 e (v
      68 e e))) (v 66 (v 68 (v 36 e e) e) e)))) (v 25 e (v 26 e (v 66 (v 12 e e) e)))) (v 79 (v 25 e (v
      26 e (v 88 (v 12 e e) e))) (v 25 e e))) (v 77 (v 79 (v 25 e e) e) e)) (v 77 (v 23 (v 79 (v 25 e (v
      66 e e)) e) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 e (v 66 e e)) (v 66 e e)) e) e) (v 88 (v 12 e e)
      e)))) (v 46 (v 47 (v 48 (v 77 (v 78 (v 24 e (v 25 e (v 26 e (v 66 (v 67 (v 35 e e) e) e)))) (v 24 e
      (v 25 e e))) (v 78 (v 24 e (v 25 e e)) (v 24 e e))) (v 77 (v 78 (v 24 e e) e) e)) (v 77 (v 78 (v 24
      (v 69 e e) e) e) e)) (v 77 (v 78 (v 68 (v 25 e e) e) e) e)))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33
      e (v 34 e (v 24 e e))) e) e) (v 22 e e)) (v 22 e e)) (v 77 (v 23 e e) e))) (v 55 (v 56 (v 57 (v 157
      (v 59 (v 33 e (v 34 e (v 24 e e))) e) e) (v 22 e e)) (v 22 e e)) (v 77 (v 23 e e) e))) (v 55 (v 56
      (v 156 (v 58 (v 59 (v 33 e (v 34 (v 134 (v 36 (v 37 e (v 23 (v 123 e e) e)) e) e) e)) (v 22 e e))
      (v 22 e e)) e) e) (v 77 (v 23 (v 123 (v 25 e e) e) e) e))) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 e
      (v 133 (v 35 (v 36 (v 37 e (v 122 e e)) e) e) e)) (v 22 e e)) (v 22 e e)) e) e) (v 77 (v 122 (v 24
      e e) e) e))) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34 (v 35 e (v 36 e (v 121 (v 23 (v 26 (v 110
      e (v 12 e e)) e) e) e))) (v 35 e e)) (v 34 (v 35 e e) e)) (v 121 (v 23 e e) e)) (v 121 (v 23 e e)
      e)) (v 121 (v 23 (v 79 (v 25 e e) e) e) e)) (v 121 (v 78 (v 24 e e) e) e)) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 2, 4).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 e (v 35 e (v 36 e (v
      37 e (v 44 (v 45 (v 46 e (v 47 (v 48 e (v 27 e (v 29 (v 32 e (v 17 (v 19 e (v 20 e e)) e)) (v 32 (v
      17 (v 19 e e) e) (v 17 (v 19 e e) e))))) e)) (v 46 (v 47 e (v 28 e (v 31 e (v 16 e e)))) e)) (v 45
      (v 46 e (v 27 (v 30 e (v 32 e (v 17 e (v 18 e e)))) (v 30 (v 32 e (v 17 e e)) (v 32 e (v 17 e
      e))))) e))))))) (v 33 e (v 34 e (v 35 e (v 25 e (v 44 (v 45 (v 46 e e) e) e)))))) (v 59 (v 33 e (v
      34 e (v 35 e (v 80 (v 26 e (v 44 (v 45 (v 46 e e) e) e)) e)))) (v 33 e (v 34 e e)))) (v 58 (v 59 (v
      33 e (v 34 (v 36 (v 37 e (v 79 (v 23 e (v 25 e (v 44 e (v 68 (v 48 e (v 27 e (v 32 e (v 29 e (v 30
      e e))))) e)))) (v 23 e (v 25 e e)))) (v 37 e (v 79 (v 23 e (v 44 e (v 27 e (v 32 e (v 30 e (v 17 e
      (v 18 e e))))))) e))) (v 36 (v 37 e (v 79 (v 25 e (v 44 (v 45 (v 68 (v 48 e (v 27 e (v 32 e (v 29 e
      (v 19 e e))))) e) e) e)) e)) (v 79 (v 26 e (v 44 (v 45 e e) e)) e)))) (v 33 (v 34 e (v 36 (v 79 (v
      81 (v 22 e (v 25 (v 45 e (v 68 e e)) e)) (v 22 e e)) (v 22 e e)) e)) (v 34 (v 36 (v 79 (v 81 (v 23
      e (v 25 (v 44 e (v 68 e e)) e)) (v 23 e e)) (v 23 e e)) e) (v 44 (v 45 (v 68 e e) e) e)))) (v 48 (v
      33 (v 34 e (v 79 (v 80 e e) e)) (v 34 (v 79 (v 80 (v 26 e (v 23 e e)) (v 23 e e)) (v 23 e e)) e))
      (v 22 e e)))) (v 57 (v 58 (v 59 (v 33 (v 35 e (v 36 e (v 37 e (v 78 (v 22 e (v 67 (v 46 (v 47 e e)
      e) e)) e)))) (v 35 e (v 36 e (v 78 (v 26 e (v 44 (v 67 (v 46 (v 47 e e) e) e) e)) e)))) (v 33 (v 35
      (v 36 e (v 78 e e)) (v 36 (v 78 (v 81 (v 22 e (v 25 e e)) (v 22 e e)) (v 22 (v 25 e e) e)) e)) (v
      35 (v 36 e e) e))) (v 48 (v 33 (v 35 (v 78 e (v 80 (v 26 e (v 22 e e)) (v 26 e e))) (v 78 (v 80 (v
      26 e (v 22 e e)) e) (v 22 e e))) (v 35 (v 78 (v 80 (v 26 e (v 24 e e)) (v 24 e e)) (v 24 e e)) e))
      (v 22 (v 78 e e) e))) (v 47 (v 48 (v 33 e (v 78 (v 79 (v 25 e e) e) e)) (v 22 (v 78 (v 79 (v 25 e
      e) e) e) e)) (v 22 e e)))) (v 56 (v 57 (v 58 (v 59 (v 34 (v 35 e (v 36 e (v 37 (v 77 e (v 23 e (v
      26 e e))) (v 77 e e)))) (v 35 e (v 36 e (v 77 (v 26 e (v 66 (v 45 (v 46 e e) e) e)) e)))) (v 34 (v
      35 e (v 36 (v 77 e (v 23 e e)) e)) (v 35 e e))) (v 48 (v 34 (v 35 e (v 77 e (v 23 e e))) (v 35 e (v
      66 e e))) (v 77 e e))) (v 47 (v 48 (v 34 (v 77 (v 79 (v 25 e (v 26 e (v 23 (v 66 e (v 12 e (v 68 e
      e))) (v 66 (v 68 (v 36 e e) e) e)))) (v 25 e (v 26 e (v 66 (v 12 e e) e)))) (v 79 (v 25 e (v 26 e
      (v 88 (v 12 e e) e))) (v 25 e e))) (v 77 (v 79 (v 25 e e) e) e)) (v 77 (v 23 (v 79 (v 25 (v 70 e (v
      66 e e)) (v 66 e e)) (v 66 (v 12 e e) e)) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 e (v 66 e e)) e) e)
      e) e))) (v 46 (v 47 (v 48 e (v 77 (v 78 (v 24 e e) e) e)) (v 77 (v 78 (v 24 e e) e) e)) (v 77 (v 78
      (v 68 (v 25 e e) e) e) e)))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33 e (v 34 e e)) e) e) (v 22 e e))
      (v 22 (v 78 e e) e)) (v 77 e e))) (v 55 (v 56 (v 57 (v 157 (v 59 (v 33 e (v 34 e e)) e) e) (v 22 e
      e)) (v 22 (v 78 e e) e)) (v 77 e e))) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 e (v 34 (v 134 (v 36 (v
      37 e (v 23 (v 123 e e) e)) e) e) e)) (v 22 e e)) (v 22 e e)) e) (v 22 e e)) (v 77 (v 23 (v 123 (v
      25 e e) e) e) e))) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 (v 133 (v 35 e (v 36 e (v 22 e e))) (v 35 e
      e)) (v 133 (v 35 e e) e)) (v 22 (v 122 (v 24 e e) e) e)) (v 22 (v 122 (v 24 e e) e) e)) (v 22 e e))
      e) e)) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34 (v 35 e (v 36 e (v 121 (v 23 e e) e))) (v 35 e
      e)) (v 34 (v 35 e e) e)) (v 121 (v 23 e e) e)) (v 121 (v 23 e e) e)) (v 121 (v 23 (v 79 (v 25 e e)
      e) e) e)) e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 3, 0).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 e (v 35 e (v 36 e (v
      37 (v 26 e (v 44 e (v 45 (v 46 e (v 47 e (v 27 (v 28 e (v 29 e (v 31 e (v 32 e e)))) (v 28 e e))))
      (v 46 e e)))) (v 44 (v 45 e (v 46 e e)) (v 45 (v 46 e e) e))))))) (v 33 e (v 34 e (v 35 e e)))) (v
      59 (v 33 e (v 34 e (v 35 e (v 80 (v 26 (v 44 e (v 45 (v 46 (v 69 e (v 15 e (v 39 e (v 43 e (v 29 e
      (v 16 e e)))))) (v 69 e e)) (v 46 (v 69 e e) e))) (v 44 (v 45 e e) (v 28 (v 32 e (v 29 e (v 16 e (v
      19 e e)))) (v 32 (v 29 e (v 16 e e)) (v 29 (v 16 e e) (v 16 e e)))))) (v 44 (v 45 e e) e))))) (v 33
      e (v 34 e e)))) (v 58 (v 59 (v 33 e (v 34 (v 36 e (v 37 (v 79 (v 23 e (v 26 e (v 44 e (v 68 (v 47 e
      (v 27 e (v 31 e (v 28 e e)))) e)))) (v 23 (v 26 e (v 44 e (v 12 e e))) (v 26 e e))) (v 79 (v 23 e
      (v 44 e (v 27 e (v 31 e (v 29 e (v 17 e e)))))) (v 44 e e)))) (v 36 e (v 79 (v 26 e (v 44 (v 45 (v
      68 (v 47 e e) e) e) e)) e)))) (v 33 (v 34 (v 36 (v 79 e (v 81 (v 22 e (v 23 e e)) (v 22 e e))) (v
      79 e (v 22 e e))) (v 36 (v 79 (v 81 (v 22 e (v 25 e e)) (v 22 e e)) (v 22 e e)) e)) (v 34 (v 36 (v
      79 e (v 23 (v 25 e e) e)) e) e))) (v 48 (v 33 (v 34 (v 79 e (v 80 (v 26 e (v 22 e e)) (v 26 e e)))
      (v 79 (v 80 (v 26 e (v 22 e e)) (v 22 e e)) e)) (v 34 (v 79 (v 80 (v 26 (v 23 e (v 44 e (v 68 (v 69
      e e) e))) (v 23 e e)) (v 23 e e)) (v 23 (v 80 (v 26 (v 44 e (v 12 e e)) e) e) e)) (v 44 e e))) (v
      22 e e)))) (v 57 (v 58 (v 59 (v 33 e (v 35 e (v 36 e (v 78 (v 26 e (v 44 (v 67 (v 46 (v 47 e e) e)
      e) e)) e)))) (v 33 (v 35 e (v 36 e e)) (v 35 e e))) (v 48 (v 33 (v 35 (v 78 (v 80 (v 26 e (v 22 e
      (v 24 e (v 67 e e)))) (v 26 e (v 22 e e))) (v 80 (v 26 e (v 22 e e)) (v 26 e e))) (v 78 (v 80 (v 26
      e (v 22 e e)) (v 22 e e)) e)) (v 35 (v 78 (v 80 (v 26 (v 24 e (v 44 e (v 67 (v 69 e e) e))) (v 24 e
      e)) (v 24 e e)) (v 24 e e)) (v 44 e e))) (v 22 e e))) (v 47 (v 48 (v 33 e (v 78 (v 79 (v 25 e e) e)
      e)) (v 22 e e)) (v 22 e e)))) (v 56 (v 57 (v 58 (v 59 (v 34 (v 35 e (v 36 e (v 37 (v 77 (v 23 e (v
      26 e (v 66 (v 46 e (v 47 e (v 29 e (v 27 e (v 28 (v 31 e (v 32 e e)) e))))) (v 46 e e)))) (v 23 e
      (v 26 (v 88 e (v 46 e e)) e))) (v 77 (v 23 e (v 66 (v 46 e e) e)) e)))) (v 35 e (v 36 e (v 77 (v 26
      e (v 66 (v 45 (v 46 e e) e) e)) (v 88 e e))))) (v 34 (v 35 e (v 36 e e)) (v 35 e e))) (v 48 (v 34
      (v 35 e (v 77 (v 80 (v 26 (v 23 e (v 66 (v 46 e (v 69 (v 15 e (v 28 e (v 29 e (v 32 e (v 27 e
      e))))) e)) (v 46 e e))) (v 23 e e)) (v 23 e e)) (v 23 e e))) (v 35 e (v 66 (v 45 (v 46 (v 69 (v 15
      e (v 28 e (v 29 e (v 32 e (v 16 e e))))) e) e) e) e))) (v 77 (v 23 e e) e))) (v 47 (v 48 (v 34 (v
      77 (v 79 (v 25 e (v 26 e (v 23 (v 66 e (v 12 e (v 68 e e))) (v 66 (v 68 (v 36 e e) e) e)))) (v 25 e
      (v 26 e (v 66 (v 12 e e) e)))) (v 79 (v 25 e (v 26 e (v 88 (v 12 e e) e))) (v 25 e e))) (v 77 (v 79
      (v 25 e e) e) e)) (v 77 (v 23 (v 79 (v 25 e (v 66 e e)) e) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 (v
      66 e (v 12 e (v 68 e e))) (v 66 e e)) (v 66 e e)) (v 66 (v 12 e e) e)) (v 66 (v 34 (v 68 (v 58 e e)
      e) e) e)) (v 88 (v 12 e e) e)))) (v 46 (v 47 e (v 77 (v 78 (v 24 e (v 66 (v 67 (v 35 e e) e) e)) e)
      e)) (v 77 (v 78 (v 68 (v 25 e e) e) e) e)))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33 e (v 34 e e)) e)
      e) (v 22 e e)) e) e)) (v 55 (v 56 (v 57 (v 157 (v 59 (v 33 e (v 34 e e)) e) e) (v 22 e e)) (v 22 e
      e)) (v 77 (v 23 e e) e))) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 e (v 34 (v 134 (v 36 e (v 23 (v 123
      (v 26 e e) e) e)) e) e)) (v 22 e e)) (v 22 e e)) e) e) (v 77 (v 23 (v 123 (v 25 e e) e) e) e))) (v
      55 (v 155 (v 57 (v 58 (v 59 (v 33 e (v 133 (v 35 (v 36 e (v 122 (v 24 e e) e)) e) e)) (v 22 e e))
      (v 22 e e)) e) e) (v 77 (v 122 (v 24 e e) e) e))) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34 (v 35
      e (v 36 e (v 121 (v 23 e e) e))) (v 35 e e)) (v 34 (v 35 e e) e)) e) (v 121 (v 23 e e) e)) (v 121
      (v 23 (v 79 (v 25 e e) e) e) e)) e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 3, 1).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 e (v 35 e (v 36 e (v
      37 e (v 44 (v 45 (v 46 e (v 47 (v 48 e (v 27 e (v 32 e (v 17 e e)))) e)) (v 46 (v 47 e (v 28 e (v
      30 (v 31 e (v 16 (v 18 e (v 21 e e)) e)) (v 31 (v 16 (v 18 e e) e) (v 16 (v 18 e e) e))))) e)) (v
      45 (v 46 (v 47 e (v 28 (v 29 e (v 31 e (v 16 e (v 19 e e)))) (v 29 (v 31 e (v 16 e e)) (v 31 e (v
      16 e e))))) e) e))))))) (v 33 (v 34 e (v 35 e (v 36 e (v 81 (v 22 e (v 45 e e)) e)))) (v 34 (v 35 e
      (v 36 e (v 81 (v 23 e (v 44 e e)) e))) (v 35 e (v 25 e (v 44 (v 45 (v 46 e e) e) e)))))) (v 59 (v
      33 e (v 34 e (v 35 (v 37 (v 80 (v 24 e (v 26 e (v 44 e (v 45 e (v 28 e (v 31 e (v 29 e (v 30 e
      e)))))))) (v 24 e (v 26 e e))) (v 80 (v 24 e (v 44 (v 45 e (v 28 e (v 31 e (v 30 e (v 18 e e)))))
      e)) e)) (v 80 (v 26 e (v 44 (v 45 e e) (v 28 e (v 31 e (v 29 e (v 16 e (v 19 e e))))))) e)))) (v 33
      (v 34 e (v 35 (v 80 (v 81 e (v 22 e e)) (v 22 e e)) e)) (v 34 (v 35 e e) e)))) (v 58 (v 59 (v 33 e
      (v 34 (v 36 e (v 37 e (v 79 (v 23 e (v 44 e e)) e))) (v 36 e (v 79 (v 26 e (v 44 (v 45 (v 68 (v 47
      e e) e) e) e)) e)))) (v 33 (v 34 (v 36 (v 79 e (v 81 e (v 22 e e))) (v 79 e (v 22 e e))) (v 36 (v
      79 (v 81 e (v 22 (v 25 e e) e)) (v 22 (v 25 e e) e)) e)) (v 34 (v 36 (v 79 (v 81 (v 23 e (v 25 e
      e)) (v 23 e e)) (v 23 (v 25 e e) e)) e) e))) (v 48 (v 33 e (v 34 (v 79 (v 80 (v 26 e (v 23 e e)) e)
      (v 23 e e)) e)) (v 22 e e)))) (v 57 (v 58 (v 59 (v 33 e (v 35 (v 36 e (v 37 e (v 78 (v 24 e (v 44
      (v 67 e e) e)) e))) (v 36 e (v 78 (v 26 e (v 44 (v 67 (v 46 (v 47 e e) e) e) e)) e)))) (v 33 (v 35
      (v 36 e (v 78 (v 81 (v 22 e (v 24 e e)) (v 22 (v 24 e e) e)) (v 22 (v 24 e e) e))) (v 36 (v 78 e (v
      22 (v 25 e e) e)) e)) (v 35 (v 36 e e) e))) (v 48 (v 33 e (v 35 (v 78 (v 80 (v 26 e (v 24 (v 44 (v
      67 e (v 13 e e)) (v 67 e e)) e)) (v 24 (v 26 e e) e)) (v 24 (v 80 (v 26 e e) e) e)) e)) (v 22 (v 78
      (v 24 e e) e) (v 33 (v 67 e e) e)))) (v 47 (v 48 e (v 22 (v 78 (v 79 (v 25 e e) e) e) e)) (v 22 e
      e)))) (v 56 (v 57 (v 58 (v 59 (v 34 (v 35 e (v 36 e (v 37 (v 77 e (v 23 e (v 26 e e))) (v 77 (v 23
      e (v 66 (v 46 e e) e)) e)))) (v 35 e (v 36 e (v 77 (v 26 e (v 66 (v 45 (v 46 (v 47 e e) e) e) e))
      e)))) (v 34 (v 35 e (v 36 e e)) (v 35 e e))) (v 48 (v 34 (v 35 e (v 77 (v 80 (v 26 (v 23 e (v 66 e
      (v 46 e e))) (v 23 e e)) (v 23 e e)) (v 23 e e))) (v 35 (v 77 (v 80 (v 26 (v 24 e (v 66 e (v 45 e
      e))) (v 24 e e)) (v 24 e e)) (v 24 e e)) (v 66 e e))) (v 77 (v 23 e e) e))) (v 47 (v 48 (v 34 (v 77
      e (v 79 (v 25 e (v 26 e e)) (v 25 e e))) (v 77 e e)) (v 77 (v 23 (v 79 e e) e) e)) (v 77 (v 23 (v
      79 e e) e) e))) (v 46 (v 47 (v 48 (v 77 e (v 78 (v 24 e (v 25 e e)) (v 24 e e))) (v 77 (v 78 (v 24
      e e) e) e)) (v 77 (v 78 (v 24 (v 69 e (v 66 e e)) e) e) e)) (v 77 e e)))) (v 55 (v 56 (v 57 (v 58
      (v 158 (v 33 (v 34 (v 35 e (v 36 e (v 22 e e))) (v 35 e e)) (v 34 (v 35 e e) e)) e) (v 22 e e)) (v
      22 (v 23 (v 79 e e) e) e)) (v 22 (v 78 (v 24 e e) e) e)) e)) (v 55 (v 56 (v 57 (v 157 (v 59 (v 33 e
      (v 34 e (v 24 (v 124 (v 26 e e) e) e))) (v 22 e e)) e) (v 22 e e)) (v 22 e e)) (v 77 (v 23 e e)
      e))) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 e (v 34 (v 134 (v 36 e e) e) e)) (v 22 (v 23 (v 123 e e)
      e) e)) (v 22 e e)) e) e) (v 77 e e))) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 e (v 133 (v 35 (v 36 e
      e) e) e)) (v 22 (v 122 (v 24 e e) e) e)) (v 22 e e)) e) e) (v 77 e e))) (v 154 (v 56 (v 57 (v 58 (v
      59 (v 132 (v 34 (v 35 e (v 36 e (v 121 (v 23 e e) e))) (v 35 e e)) (v 34 (v 35 e e) e)) e) (v 121
      (v 23 e e) e)) (v 121 (v 23 (v 79 e e) e) e)) (v 121 (v 78 (v 24 e e) e) e)) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 3, 2).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 e (v 35 e (v 36 e (v
      37 e (v 44 (v 45 e (v 46 (v 47 (v 48 e (v 30 e (v 31 e (v 16 e (v 17 e e))))) e) e)) (v 45 (v 46 (v
      47 e (v 28 (v 29 e (v 32 e (v 16 e (v 19 e e)))) (v 29 (v 32 e (v 16 e e)) (v 32 e (v 16 e e)))))
      (v 27 (v 29 e (v 32 e (v 17 e (v 19 (v 20 e e) e)))) (v 29 e (v 32 (v 17 e e) (v 17 e e)))))
      e))))))) (v 33 e (v 34 e (v 35 (v 36 e (v 81 (v 24 e (v 44 e e)) e)) (v 25 e (v 44 (v 45 e e)
      e)))))) (v 59 (v 33 e (v 34 e (v 35 (v 37 (v 80 (v 24 e (v 26 e (v 44 e (v 45 e e)))) (v 24 e (v 26
      e e))) (v 80 (v 24 e (v 44 e e)) e)) (v 80 (v 26 e (v 44 (v 45 e e) e)) e)))) (v 33 e (v 34 e e))))
      (v 58 (v 59 (v 33 e (v 34 (v 36 (v 37 e (v 79 (v 23 e (v 25 e (v 44 e (v 68 e e)))) (v 23 e (v 25 e
      e)))) (v 37 e (v 79 (v 23 e (v 44 e e)) e))) (v 36 (v 37 e (v 79 (v 25 e (v 44 e e)) e)) (v 79 (v
      26 e (v 44 e e)) e)))) (v 33 (v 34 e (v 36 (v 79 e (v 22 e e)) e)) (v 34 (v 36 (v 79 (v 81 (v 23 e
      (v 25 e e)) (v 23 e e)) (v 23 e e)) e) (v 44 e e)))) (v 48 (v 33 e (v 34 (v 79 (v 80 (v 26 e (v 23
      e e)) (v 23 e e)) (v 23 e e)) e)) (v 22 e e)))) (v 57 (v 58 (v 59 (v 33 e (v 35 (v 36 e (v 37 e (v
      78 (v 24 e (v 44 (v 67 (v 47 e e) e) e)) e))) (v 36 (v 37 e (v 78 (v 25 e (v 44 e e)) e)) (v 78 (v
      26 e (v 44 e e)) e)))) (v 33 (v 35 (v 36 (v 78 e (v 81 e (v 22 e e))) (v 78 (v 81 (v 22 e (v 24 e
      e)) (v 22 e e)) (v 22 e e))) (v 36 (v 78 (v 81 (v 22 e (v 25 e e)) (v 22 e e)) (v 22 e e)) e)) (v
      35 (v 36 (v 78 e (v 24 e e)) e) e))) (v 48 (v 33 e (v 35 (v 78 (v 80 (v 26 e (v 24 e e)) (v 24 (v
      26 e e) e)) (v 24 (v 80 (v 26 e e) e) e)) e)) (v 22 e e))) (v 47 (v 48 (v 33 e (v 78 (v 79 (v 25 e
      e) e) e)) (v 22 e e)) (v 22 e e)))) (v 56 (v 57 (v 58 (v 59 (v 34 (v 35 e (v 36 e (v 37 (v 77 (v 23
      e (v 26 e (v 66 (v 46 e (v 47 e (v 29 e (v 32 e (v 27 e (v 28 e e)))))) (v 46 e e)))) (v 23 e (v 26
      e e))) (v 77 (v 23 e (v 66 (v 46 e (v 29 e (v 32 e (v 27 e (v 17 (v 20 e e) e))))) e)) e)))) (v 35
      e (v 36 e (v 77 (v 26 e (v 66 (v 45 (v 46 (v 47 e (v 29 e (v 32 e (v 28 e (v 16 (v 19 e e) e)))))
      e) e) e)) e)))) (v 34 (v 35 e (v 36 (v 77 (v 81 e (v 23 e e)) (v 23 e e)) e)) (v 35 (v 36 e e) e)))
      (v 48 (v 34 (v 35 e (v 77 (v 80 (v 26 (v 23 e (v 66 e (v 46 e e))) (v 23 e e)) (v 23 e e)) (v 23 e
      e))) (v 35 (v 77 (v 80 (v 26 (v 24 e (v 66 e (v 45 e e))) (v 24 e e)) (v 24 e e)) (v 24 e e)) (v 66
      e e))) (v 77 (v 23 e e) e))) (v 47 (v 48 (v 34 (v 77 (v 79 (v 25 e (v 26 e (v 23 (v 66 e (v 12 e (v
      68 e e))) (v 66 (v 68 (v 36 e e) e) e)))) (v 25 e (v 26 e (v 66 (v 12 e e) e)))) (v 79 (v 25 e (v
      26 e (v 88 (v 12 e e) e))) (v 25 e e))) (v 77 (v 79 (v 25 e e) e) e)) (v 77 (v 23 (v 79 (v 25 e (v
      66 e e)) e) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 e (v 66 e e)) (v 66 e e)) e) e) (v 88 (v 12 e e)
      e)))) (v 46 (v 47 (v 48 (v 77 (v 78 (v 24 e (v 25 e (v 26 e (v 66 (v 67 (v 35 e e) e) e)))) (v 24 e
      (v 25 e e))) (v 78 (v 24 e (v 25 e e)) (v 24 e e))) (v 77 (v 78 (v 24 e e) e) e)) (v 77 (v 78 (v 24
      (v 69 e e) e) e) e)) (v 77 (v 78 (v 68 (v 25 e e) e) e) e)))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33
      e (v 34 e (v 24 e e))) e) e) (v 22 e e)) (v 22 e e)) (v 77 (v 23 e e) e))) (v 55 (v 56 (v 57 (v 157
      (v 59 (v 33 e (v 34 e (v 24 e e))) e) e) (v 22 e e)) (v 22 e e)) (v 77 (v 23 e e) e))) (v 55 (v 56
      (v 156 (v 58 (v 59 (v 33 e (v 34 (v 134 (v 36 (v 37 e (v 23 (v 123 e e) e)) e) e) e)) (v 22 e e))
      (v 22 e e)) e) e) (v 77 (v 23 (v 123 (v 25 e e) e) e) e))) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 e
      (v 133 (v 35 (v 36 (v 37 e (v 122 e e)) e) e) e)) (v 22 e e)) (v 22 e e)) e) e) (v 77 (v 122 (v 24
      e e) e) e))) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34 (v 35 e (v 36 e (v 121 (v 23 (v 26 (v 110
      e (v 12 e e)) e) e) e))) (v 35 e e)) (v 34 (v 35 e e) e)) (v 121 (v 23 e e) e)) (v 121 (v 23 e e)
      e)) (v 121 (v 23 (v 79 (v 25 e e) e) e) e)) (v 121 (v 78 (v 24 e e) e) e)) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 3, 3).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 e (v 35 e (v 36 e (v
      37 (v 26 e (v 44 e (v 45 (v 46 e (v 47 e (v 27 e (v 28 e e)))) (v 46 (v 47 e (v 28 e (v 29 e (v 30
      (v 31 e (v 32 (v 16 (v 19 e e) e) e)) e)))) e)))) (v 44 (v 45 e (v 46 e e)) (v 45 (v 46 e (v 27 e
      (v 29 e (v 31 e (v 17 e e))))) (v 29 e (v 30 e e))))))))) (v 33 e (v 34 e (v 35 e (v 25 e (v 44 (v
      45 e e) e)))))) (v 59 (v 33 e (v 34 e (v 35 (v 37 (v 80 (v 24 e (v 26 e (v 44 e (v 45 e (v 28 e (v
      29 (v 30 e (v 31 e (v 32 e e))) (v 30 e e))))))) (v 24 e (v 26 (v 44 e (v 45 e e)) e))) (v 80 (v 24
      e (v 44 e e)) e)) (v 80 (v 26 e (v 44 (v 45 e e) e)) (v 44 e e))))) (v 33 e (v 34 e e)))) (v 58 (v
      59 (v 33 e (v 34 e (v 36 e (v 79 (v 26 e (v 44 (v 45 e e) e)) e)))) (v 33 e (v 34 e e))) (v 48 (v
      33 e (v 34 e e)) (v 22 e e)))) (v 57 (v 58 (v 59 (v 33 e (v 35 (v 36 e (v 37 (v 78 (v 24 e (v 26 e
      (v 44 e (v 67 (v 47 e (v 30 e (v 32 e (v 28 e (v 29 e e))))) e)))) (v 24 (v 26 e (v 44 e (v 89 (v
      13 e e) e))) (v 26 e e))) (v 78 (v 24 e (v 44 (v 67 (v 47 e (v 30 e (v 32 e (v 28 e (v 18 e e)))))
      e) e)) (v 44 (v 89 (v 13 e e) e) e)))) (v 36 e (v 78 (v 26 e (v 44 (v 67 (v 46 (v 47 e e) e) e) e))
      e)))) (v 33 (v 35 (v 36 (v 78 e (v 81 (v 22 e (v 24 e e)) (v 22 e e))) (v 78 e (v 22 e e))) (v 36
      (v 78 (v 81 (v 22 e (v 25 e e)) (v 22 e e)) (v 22 e e)) e)) (v 35 (v 36 (v 78 e (v 24 e e)) e) e)))
      (v 48 (v 33 e (v 35 (v 78 (v 80 (v 26 e (v 24 (v 44 (v 67 e (v 13 e e)) (v 67 e e)) e)) (v 24 (v 26
      (v 44 e (v 67 e e)) e) e)) (v 24 (v 80 (v 26 e e) e) e)) e)) (v 22 e (v 33 e e)))) (v 47 (v 48 (v
      33 e (v 78 (v 79 (v 25 e e) e) e)) (v 22 e e)) (v 22 e e)))) (v 56 (v 57 (v 58 (v 59 (v 34 e (v 35
      e (v 36 e (v 77 (v 26 (v 66 e (v 45 (v 46 (v 47 e (v 15 e (v 40 e (v 42 e (v 28 e (v 16 e e))))))
      (v 47 e e)) (v 46 (v 47 e e) e))) (v 66 (v 45 (v 46 (v 47 e (v 29 (v 31 e (v 28 e (v 16 e e))) (v
      31 (v 28 e (v 16 e e)) (v 28 (v 16 e (v 19 e e)) (v 16 e e))))) e) e) e)) (v 88 (v 45 (v 46 (v 47 e
      e) e) e) e))))) (v 34 e (v 35 e e))) (v 48 (v 34 e (v 35 (v 77 (v 80 (v 26 (v 24 e (v 66 (v 45 e (v
      69 (v 15 e (v 28 e (v 29 e (v 31 e (v 30 e e))))) e)) (v 45 e e))) (v 24 e e)) (v 24 e e)) (v 24 e
      e)) (v 66 (v 45 (v 46 (v 69 (v 15 e (v 28 e (v 29 e (v 31 e (v 16 e (v 19 e e)))))) e) e) e) e)))
      (v 77 (v 23 e e) e))) (v 47 (v 48 (v 34 (v 77 (v 79 (v 25 e (v 26 e (v 23 e (v 66 (v 68 e e) e))))
      (v 25 e (v 26 e e))) (v 79 (v 25 e (v 26 (v 23 e (v 88 e e)) e)) (v 25 e (v 88 e e)))) (v 77 (v 79
      (v 25 e (v 26 e e)) e) (v 79 (v 25 e e) e))) (v 77 (v 23 e e) e)) (v 77 (v 23 e (v 66 (v 34 (v 68 e
      e) e) e)) e))) (v 46 (v 47 (v 48 (v 77 (v 78 (v 24 e (v 25 e (v 26 e (v 66 (v 67 (v 35 e e) e)
      e)))) (v 24 (v 25 e (v 26 e (v 66 (v 89 e e) e))) (v 25 e e))) (v 78 (v 24 e (v 25 e (v 88 e e)))
      (v 24 (v 25 e (v 88 e e)) e))) (v 77 (v 78 (v 24 e e) e) e)) (v 77 (v 78 (v 24 (v 69 (v 26 (v 66 (v
      67 e (v 13 e (v 58 e e))) (v 67 e (v 13 e e))) (v 66 (v 67 e e) e)) (v 66 (v 67 e e) e)) (v 66 (v
      67 (v 35 (v 58 e e) e) e) e)) (v 66 (v 89 (v 13 e e) e) e)) (v 88 (v 67 e e) e))) (v 77 (v 78 (v 68
      (v 25 e e) e) e) e)))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33 e (v 34 e e)) e) e) (v 22 e e)) (v 22 e
      e)) e)) (v 55 (v 56 (v 57 (v 157 (v 59 (v 33 e (v 34 e (v 24 e e))) e) e) (v 22 e e)) (v 22 e e))
      (v 77 (v 23 e e) e))) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 e (v 34 (v 134 (v 36 e (v 23 e e)) e)
      e)) (v 22 e e)) (v 22 e e)) e) e) (v 77 (v 23 (v 123 (v 25 e e) e) e) e))) (v 55 (v 155 (v 57 (v 58
      (v 59 (v 33 e (v 133 (v 35 (v 36 e (v 122 (v 24 (v 26 e e) e) e)) e) e)) (v 22 e e)) (v 22 e e)) e)
      e) (v 77 (v 122 (v 24 (v 25 e e) e) e) e))) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34 e (v 35 e
      e)) (v 34 e e)) e) (v 121 (v 23 e e) e)) (v 121 (v 23 (v 79 e e) e) e)) (v 121 (v 78 (v 24 e e) e)
      e)) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 3, 4).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 e (v 35 e (v 36 e (v
      37 (v 26 e (v 44 e (v 45 (v 46 e (v 47 e (v 27 (v 28 e (v 29 e (v 32 e (v 19 e e)))) (v 28 e e))))
      (v 46 (v 47 e (v 28 e (v 29 e (v 30 (v 31 (v 16 e e) (v 16 e e)) e)))) e)))) (v 44 (v 45 e (v 46 (v
      47 e (v 28 (v 30 (v 31 e (v 16 e (v 18 e (v 21 e e)))) (v 31 e (v 16 (v 18 e e) (v 18 e e)))) (v 30
      (v 31 (v 16 e e) (v 16 e e)) (v 31 (v 16 e e) (v 16 (v 18 (v 21 (v 5 e e) e) e) e))))) (v 27 (v 30
      (v 31 e (v 32 e e)) (v 31 e (v 32 e e))) (v 30 (v 31 e (v 32 e e)) (v 31 e (v 32 e e)))))) (v 45 (v
      46 e (v 27 (v 29 e (v 32 e (v 17 e (v 19 e e)))) (v 29 e (v 32 e (v 17 e e))))) e))))))) (v 33 e (v
      34 e (v 35 e (v 25 e (v 44 (v 45 e e) e)))))) (v 59 (v 33 e (v 34 e (v 35 e (v 80 (v 26 e (v 44 (v
      45 e e) e)) (v 44 e e))))) (v 33 e (v 34 e e)))) (v 58 (v 59 (v 33 (v 34 e (v 36 e (v 37 e (v 79 (v
      22 e (v 45 e e)) e)))) (v 34 (v 36 (v 37 e (v 79 e (v 23 e (v 25 e e)))) (v 37 (v 79 e (v 23 e (v
      26 e e))) (v 79 e e))) (v 36 (v 37 e (v 79 (v 25 e (v 44 (v 45 (v 68 e e) e) e)) e)) (v 79 (v 26 e
      (v 44 (v 45 (v 68 e e) e) e)) e)))) (v 33 (v 34 e (v 36 (v 79 (v 81 (v 22 e (v 25 e e)) (v 22 e e))
      (v 22 e e)) e)) (v 34 (v 36 (v 79 e (v 23 e e)) e) e))) (v 48 (v 33 (v 34 e (v 79 (v 80 e e) e)) (v
      34 (v 79 e (v 23 e e)) e)) (v 22 e e)))) (v 57 (v 58 (v 59 (v 33 (v 35 (v 36 e (v 37 e (v 78 e (v
      22 e (v 24 e e))))) (v 36 e (v 37 e (v 78 (v 22 e (v 67 (v 46 (v 47 e e) e) e)) e)))) (v 35 (v 36 e
      (v 37 e (v 78 e e))) (v 36 e (v 78 (v 26 e (v 44 (v 67 (v 46 (v 47 e e) e) e) e)) e)))) (v 33 (v 35
      (v 36 e (v 78 e (v 22 (v 24 e e) e))) (v 36 (v 78 (v 81 (v 22 e (v 25 e e)) (v 22 e e)) (v 22 (v 25
      e e) e)) e)) (v 35 (v 36 e e) e))) (v 48 (v 33 (v 35 (v 78 (v 80 (v 26 e (v 22 e (v 24 e (v 67 (v
      69 e e) e)))) (v 26 e (v 22 e e))) (v 80 (v 26 e (v 22 e e)) (v 26 e (v 11 e e)))) (v 78 (v 80 (v
      26 e (v 22 e e)) (v 22 e e)) (v 22 e e))) (v 35 (v 78 (v 80 (v 26 (v 24 e (v 44 e (v 67 (v 69 e e)
      e))) (v 24 e (v 28 e (v 30 e (v 31 e (v 18 e (v 16 e e))))))) (v 24 e e)) (v 24 (v 80 e e) e)) (v
      44 e e))) (v 22 (v 78 e e) e))) (v 47 (v 48 (v 33 (v 78 e (v 79 (v 25 e (v 26 e e)) (v 25 e e))) (v
      78 (v 79 (v 25 e e) e) e)) (v 22 (v 78 (v 79 (v 25 e e) e) e) e)) (v 22 e e)))) (v 56 (v 57 (v 58
      (v 59 (v 34 e (v 35 e (v 36 e (v 77 (v 26 e (v 66 (v 45 (v 46 e e) e) e)) (v 88 e e))))) (v 34 e (v
      35 e e))) (v 48 (v 34 e (v 35 e (v 66 (v 45 (v 46 e e) e) e))) e)) (v 47 (v 48 (v 34 (v 77 (v 79 (v
      25 e (v 26 e (v 23 e (v 66 (v 68 (v 36 e e) e) e)))) (v 25 e (v 26 e e))) (v 79 (v 25 e (v 26 e e))
      (v 25 e (v 88 (v 12 e e) e)))) (v 77 (v 79 (v 25 e (v 26 e e)) e) (v 79 e e))) (v 77 (v 23 e e) e))
      (v 77 (v 23 e (v 66 (v 34 e e) e)) e))) (v 46 (v 47 (v 48 (v 77 (v 78 (v 24 e (v 25 e (v 26 e (v 66
      (v 67 e e) e)))) (v 24 e (v 25 e e))) (v 78 (v 24 e (v 25 e e)) (v 24 e e))) (v 77 (v 78 (v 24 e e)
      e) e)) (v 77 (v 78 (v 24 e (v 66 e e)) e) e)) (v 77 (v 78 (v 68 (v 25 e e) e) e) e)))) (v 55 (v 56
      (v 57 (v 58 (v 158 (v 33 e (v 34 e e)) e) e) (v 22 e e)) (v 22 (v 78 e e) e)) e)) (v 55 (v 56 (v 57
      (v 157 (v 59 (v 33 e (v 34 e e)) e) e) (v 22 e e)) (v 22 (v 78 e e) e)) e)) (v 55 (v 56 (v 156 (v
      58 (v 59 (v 33 (v 34 e (v 134 (v 36 e e) e)) (v 34 (v 134 (v 36 (v 37 e (v 23 e e)) (v 23 e e)) e)
      (v 123 e e))) (v 22 e e)) (v 22 e e)) (v 22 e e)) (v 22 e e)) (v 77 (v 23 (v 123 (v 25 e e) e) e)
      e))) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 (v 133 (v 35 (v 36 e (v 37 e (v 22 (v 122 (v 24 e e) e)
      e))) (v 36 e e)) (v 35 (v 36 e e) e)) (v 133 (v 35 (v 36 e e) e) e)) (v 22 (v 122 (v 24 e e) e) e))
      (v 22 (v 122 (v 24 (v 80 (v 26 e (v 11 e e)) e) e) e) e)) (v 22 e e)) e) (v 77 (v 122 (v 24 e e) e)
      e))) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34 e (v 35 e e)) (v 34 e e)) e) e) (v 121 (v 23 (v 79
      e e) e) e)) (v 121 (v 78 (v 24 e e) e) e)) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 4, 0).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 (v 34 e (v 35 e (v 36 e (v 37
      e (v 22 e (v 45 e (v 46 e (v 47 e e)))))))) (v 34 e (v 35 e (v 36 e (v 37 (v 26 e (v 44 e (v 45 (v
      46 e (v 47 e (v 27 (v 28 e (v 30 e (v 31 e (v 32 e e)))) (v 28 e e)))) (v 46 e e)))) (v 44 (v 45 (v
      46 e (v 47 e (v 27 e (v 28 (v 30 (v 31 e (v 32 e e)) (v 31 e (v 32 e e))) e)))) (v 46 e e)) (v 45
      (v 46 e e) e))))))) (v 33 (v 34 e (v 35 e (v 36 e (v 81 (v 22 e (v 45 e e)) e)))) (v 34 e (v 35 e
      e)))) (v 59 (v 33 (v 34 e (v 35 e (v 37 (v 80 (v 22 e (v 26 e (v 45 e (v 46 e e)))) (v 22 e (v 26
      (v 45 e (v 46 e e)) e))) (v 80 (v 22 e (v 45 e e)) e)))) (v 34 e (v 35 e (v 80 (v 26 (v 44 e (v 45
      (v 46 e (v 69 e e)) (v 46 (v 69 e e) e))) (v 44 (v 45 (v 46 e (v 28 e (v 32 e (v 27 e e)))) (v 28 e
      (v 32 e (v 29 e (v 16 e e))))) e)) (v 44 (v 45 (v 46 e e) e) e))))) (v 33 (v 34 e (v 35 e e)) (v 34
      e e)))) (v 58 (v 59 (v 33 (v 34 (v 36 e (v 37 e (v 79 e (v 22 e (v 23 e e))))) (v 36 e (v 37 e (v
      79 (v 22 e (v 45 (v 68 e e) e)) e)))) (v 34 (v 36 (v 37 e (v 79 e (v 23 (v 25 e (v 44 e (v 12 e
      e))) (v 25 e e)))) (v 37 (v 79 (v 23 e (v 26 e (v 44 e (v 68 (v 47 e (v 27 e (v 30 e (v 31 e (v 28
      e (v 32 e (v 49 (v 18 e e) e))))))) e)))) (v 23 e (v 26 e e))) (v 79 (v 23 e (v 44 (v 68 e e) (v 27
      e (v 30 e (v 31 e (v 17 e e)))))) (v 44 e e)))) (v 36 (v 37 e (v 79 e e)) (v 79 (v 26 e (v 44 (v 45
      (v 68 (v 47 (v 37 e (v 27 (v 30 e (v 31 e (v 17 e (v 18 e e)))) (v 30 e (v 31 (v 17 e e) (v 17 e
      e))))) e) e) e) e)) e)))) (v 33 (v 34 (v 36 (v 79 e (v 81 (v 22 e (v 23 e e)) (v 22 e e))) (v 79 e
      (v 22 e e))) (v 36 (v 79 (v 81 (v 22 e (v 25 e e)) (v 22 (v 25 e e) e)) (v 22 e e)) (v 11 e e))) (v
      34 (v 36 (v 79 (v 81 (v 23 e (v 25 e e)) (v 23 e e)) (v 23 (v 25 (v 81 e e) e) e)) e) e))) (v 48 (v
      33 (v 34 (v 79 e (v 80 (v 26 e (v 22 e e)) (v 26 e e))) (v 79 (v 80 (v 26 e (v 22 e e)) (v 22 (v 26
      e e) e)) (v 22 e e))) (v 34 (v 79 (v 80 (v 26 e (v 23 e e)) (v 23 e e)) (v 23 (v 80 (v 26 e e) e)
      e)) (v 44 e e))) (v 22 (v 23 e e) e)))) (v 57 (v 58 (v 59 (v 33 (v 35 e (v 36 e (v 37 (v 78 e (v 22
      e (v 26 e e))) (v 78 (v 22 e (v 67 (v 46 e e) e)) (v 11 e e))))) (v 35 e (v 36 e (v 78 (v 26 e (v
      44 (v 67 (v 46 e e) e) e)) e)))) (v 33 (v 35 e (v 36 e (v 11 e e))) (v 35 e e))) (v 48 (v 33 (v 35
      (v 78 e (v 80 e (v 26 (v 22 (v 24 e (v 11 e e)) e) e))) (v 78 (v 80 (v 26 e (v 22 (v 11 e (v 67 e
      e)) e)) (v 22 (v 26 (v 11 e (v 67 e e)) e) e)) (v 22 (v 80 (v 26 e e) e) e))) (v 35 (v 78 e (v 24 e
      e)) (v 44 (v 67 (v 46 (v 69 e e) e) e) e))) (v 22 (v 78 (v 24 e (v 11 e e)) e) e))) (v 47 (v 48 (v
      33 (v 78 e (v 79 (v 25 e (v 26 e e)) (v 25 e e))) (v 78 (v 79 (v 25 e e) e) e)) (v 22 (v 78 (v 79
      (v 25 e e) e) e) e)) (v 22 (v 78 (v 79 (v 69 e e) e) e) e)))) (v 56 (v 57 (v 58 (v 59 (v 34 e (v 35
      e (v 36 e (v 77 (v 26 e (v 66 (v 45 (v 46 e e) e) e)) e)))) (v 34 e (v 35 e e))) (v 48 (v 34 e (v
      35 e (v 66 (v 45 (v 46 e e) e) e))) e)) (v 47 (v 48 (v 34 (v 77 (v 79 (v 25 e (v 26 e (v 23 (v 66 e
      (v 12 e (v 68 e e))) (v 66 (v 68 (v 36 e e) e) e)))) (v 25 e (v 26 e (v 66 (v 12 e e) e)))) (v 79
      (v 25 e (v 26 e (v 88 (v 12 e e) e))) (v 25 e e))) (v 77 (v 79 (v 25 e e) e) e)) (v 77 (v 23 (v 79
      (v 25 e (v 66 e e)) e) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 (v 66 e (v 12 e (v 68 e e))) (v 66 e
      e)) (v 66 e e)) (v 66 e e)) (v 66 (v 34 e e) e)) (v 88 (v 12 e e) e)))) (v 46 (v 47 e (v 77 (v 78
      (v 24 e e) e) e)) (v 77 (v 78 (v 68 (v 25 e e) e) e) e)))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33 (v
      34 e (v 35 e e)) (v 34 e e)) e) e) (v 22 (v 23 e e) e)) e) e)) (v 55 (v 56 (v 57 (v 157 (v 59 (v 33
      (v 34 e (v 35 e (v 22 e e))) (v 34 e e)) e) e) (v 22 (v 23 e e) e)) (v 22 (v 78 (v 24 e (v 11 e e))
      e) e)) e)) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 (v 34 (v 134 (v 36 e (v 37 e (v 22 e e))) (v 36 e
      e)) (v 134 (v 36 e e) e)) (v 34 (v 134 (v 36 (v 37 e (v 23 (v 123 (v 25 e e) e) e)) (v 23 e e)) e)
      e)) (v 22 (v 23 (v 123 e e) e) (v 33 e e))) (v 22 (v 23 (v 123 e e) e) e)) (v 22 e e)) (v 22 e e))
      (v 77 (v 23 (v 123 (v 25 e e) e) e) e))) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 (v 133 (v 35 e (v 36
      e (v 22 (v 122 e e) e))) (v 35 e e)) (v 133 (v 35 e e) e)) e) (v 22 (v 122 (v 24 e (v 11 e e)) e)
      e)) (v 22 (v 122 e e) e)) e) e)) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34 e (v 35 e e)) (v 34 e
      e)) e) e) (v 121 (v 23 (v 79 (v 25 e e) e) e) e)) e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 4, 1).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 (v 34 e (v 35 e (v 36 e (v 37
      e (v 22 e (v 45 e (v 46 (v 47 e (v 48 e (v 28 (v 29 e (v 31 e (v 32 e e))) (v 29 e (v 31 e (v 32 e
      e)))))) (v 47 (v 48 e (v 27 (v 29 e (v 30 e e)) (v 29 e (v 30 e e)))) e)))))))) (v 34 e (v 35 e (v
      36 e (v 37 e (v 44 (v 45 (v 46 e (v 47 (v 48 e (v 27 e (v 30 e (v 32 (v 17 e e) (v 17 e e))))) (v
      27 e (v 28 e e)))) (v 46 (v 47 e (v 28 e (v 29 (v 31 e (v 16 e e)) (v 31 e (v 16 e e))))) e)) (v 45
      (v 46 e e) e))))))) (v 33 (v 34 e (v 35 e (v 36 e (v 81 (v 22 e (v 45 (v 46 e e) e)) (v 11 e e)))))
      (v 34 e (v 35 e (v 25 e (v 44 (v 45 (v 46 e e) e) e)))))) (v 59 (v 33 (v 34 e (v 35 e (v 37 e (v 80
      (v 22 e (v 45 e e)) e)))) (v 34 (v 35 e (v 37 e (v 80 e e))) (v 35 e (v 80 (v 26 e (v 44 (v 45 (v
      46 e e) e) e)) e)))) (v 33 (v 34 e (v 35 e e)) (v 34 (v 35 e e) e)))) (v 58 (v 59 (v 33 (v 34 e (v
      36 e (v 37 e (v 79 (v 22 e (v 45 (v 68 e e) e)) e)))) (v 34 (v 36 e (v 37 e (v 79 (v 23 e (v 44 e
      e)) e))) (v 36 e (v 79 (v 26 e (v 44 (v 45 (v 68 (v 47 e e) e) e) e)) e)))) (v 33 (v 34 (v 36 (v 79
      (v 81 e (v 22 e (v 23 e e))) (v 81 (v 22 e (v 23 e e)) (v 22 e e))) (v 79 (v 81 e (v 22 e e)) (v 22
      e e))) (v 36 (v 79 (v 81 (v 22 (v 25 e (v 11 e (v 45 e e))) (v 25 e e)) (v 22 (v 25 e e) e)) (v 22
      (v 25 e e) e)) (v 11 e e))) (v 34 (v 36 (v 79 (v 81 (v 23 e (v 25 e e)) (v 23 e e)) (v 23 (v 25 e
      e) e)) e) e))) (v 48 (v 33 (v 34 e (v 79 (v 80 (v 26 e (v 22 e e)) e) e)) (v 34 (v 79 (v 80 (v 26 e
      (v 23 e e)) (v 23 e e)) (v 23 e e)) e)) (v 22 (v 23 e e) e)))) (v 57 (v 58 (v 59 (v 33 (v 35 e (v
      36 e (v 37 e (v 78 (v 22 e (v 67 (v 46 (v 47 e e) e) e)) (v 11 e e))))) (v 35 e (v 36 e (v 78 (v 26
      e (v 44 (v 67 (v 46 (v 47 e e) e) e) e)) e)))) (v 33 (v 35 e (v 36 e (v 11 e e))) (v 35 e e))) (v
      48 (v 33 (v 35 (v 78 (v 80 (v 26 e (v 22 e (v 24 e (v 67 (v 69 e e) e)))) (v 26 e (v 22 (v 24 e (v
      11 e e)) e))) (v 80 (v 26 e (v 22 (v 24 e (v 11 e e)) e)) (v 26 e (v 11 e e)))) (v 78 (v 80 (v 26 e
      (v 22 e e)) (v 22 e e)) (v 22 e e))) (v 35 (v 78 (v 80 (v 26 e (v 24 e e)) (v 24 e e)) (v 24 e e))
      e)) (v 22 (v 78 (v 24 e (v 11 e e)) e) e))) (v 47 (v 48 (v 33 (v 78 e (v 79 e (v 25 e e))) (v 78 (v
      79 e e) e)) (v 22 (v 78 (v 79 (v 25 e (v 11 e e)) e) e) e)) (v 22 (v 78 e e) e)))) (v 56 (v 57 (v
      58 (v 59 (v 34 e (v 35 e (v 36 e (v 77 (v 26 e (v 66 (v 45 (v 46 e e) e) e)) e)))) (v 34 e (v 35 e
      e))) (v 48 (v 34 (v 35 e (v 77 (v 80 e (v 23 e e)) (v 23 e e))) (v 35 e e)) (v 77 (v 23 e e) e)))
      (v 47 (v 48 (v 34 (v 77 (v 79 e (v 25 e (v 26 e (v 66 e e)))) (v 79 e (v 25 e e))) (v 77 (v 79 e e)
      e)) (v 77 (v 23 (v 79 e e) e) e)) (v 77 (v 23 (v 79 e e) e) e))) (v 46 (v 47 e (v 77 (v 78 (v 24 e
      e) e) e)) (v 77 (v 78 (v 68 e e) e) e)))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33 (v 34 e (v 35 e e))
      (v 34 e e)) e) (v 22 (v 23 e e) e)) (v 22 (v 23 (v 79 e e) e) e)) e) e)) (v 55 (v 56 (v 57 (v 157
      (v 59 (v 33 (v 34 e (v 35 (v 135 (v 37 e (v 22 e e)) e) (v 22 e e))) (v 34 (v 35 e e) (v 24 e e)))
      (v 22 e e)) (v 22 e e)) (v 22 e e)) (v 22 (v 78 (v 24 e e) e) e)) (v 77 (v 23 e e) e))) (v 55 (v 56
      (v 156 (v 58 (v 59 (v 33 (v 34 (v 134 (v 36 e (v 37 e (v 22 e e))) (v 36 e e)) (v 134 (v 36 (v 37 e
      (v 22 e e)) e) e)) (v 34 (v 134 (v 36 (v 37 e (v 23 (v 123 (v 25 e e) e) e)) e) e) e)) (v 22 (v 23
      (v 123 e e) e) e)) (v 22 e e)) (v 22 e e)) (v 22 e e)) (v 77 (v 23 (v 123 (v 25 e e) e) e) e))) (v
      55 (v 155 (v 57 (v 58 (v 59 (v 33 (v 133 (v 35 e (v 36 e e)) (v 35 e e)) (v 133 (v 35 e e) e)) e)
      (v 22 (v 122 (v 24 (v 80 e e) e) e) e)) (v 22 (v 122 e e) e)) e) e)) (v 154 (v 56 (v 57 (v 58 (v 59
      (v 132 (v 34 e (v 35 e e)) (v 34 e e)) e) (v 121 (v 23 e e) e)) (v 121 (v 23 (v 79 e e) e) e)) e)
      e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 4, 2).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 e (v 35 e (v 36 e (v
      37 e (v 44 (v 45 (v 46 e (v 47 (v 48 e (v 27 e (v 30 (v 31 e (v 17 (v 18 e (v 21 e e)) e)) (v 31 (v
      17 (v 18 e e) e) (v 17 (v 18 e e) e))))) e)) (v 46 (v 47 e (v 28 e (v 29 e (v 16 e e)))) e)) (v 45
      (v 46 e (v 27 (v 30 e (v 32 e (v 17 e (v 18 (v 20 e e) e)))) (v 30 e (v 32 (v 17 e e) (v 17 e
      e))))) e))))))) (v 33 e (v 34 e (v 35 e (v 25 e (v 44 (v 45 (v 46 e e) e) e)))))) (v 59 (v 33 e (v
      34 e (v 35 e (v 80 (v 26 e (v 44 (v 45 (v 46 e e) e) e)) e)))) (v 33 e (v 34 e e)))) (v 58 (v 59 (v
      33 e (v 34 (v 36 (v 37 e (v 79 (v 23 e (v 25 e (v 44 e (v 68 (v 48 e (v 27 e (v 30 e (v 31 e (v 32
      e e))))) e)))) (v 23 e (v 25 e e)))) (v 37 e (v 79 (v 23 e (v 44 e (v 27 e (v 30 e (v 32 e (v 17 e
      (v 20 e e))))))) e))) (v 36 (v 37 e (v 79 (v 25 e (v 44 (v 45 (v 68 (v 48 e (v 27 e (v 30 e (v 31 e
      (v 18 e (v 21 e e)))))) e) e) e)) e)) (v 79 (v 26 e (v 44 (v 45 e e) e)) e)))) (v 33 (v 34 e (v 36
      (v 79 (v 81 (v 22 e (v 25 (v 45 e (v 68 e e)) e)) (v 22 e e)) (v 22 e e)) e)) (v 34 (v 36 (v 79 (v
      81 (v 23 e (v 25 (v 44 e (v 68 e e)) e)) (v 23 e e)) (v 23 e e)) e) (v 44 (v 45 (v 68 e e) e) e))))
      (v 48 (v 33 (v 34 e (v 79 (v 80 e e) e)) (v 34 (v 79 (v 80 (v 26 e (v 23 e e)) (v 23 e e)) (v 23 e
      e)) e)) (v 22 e e)))) (v 57 (v 58 (v 59 (v 33 (v 35 e (v 36 e (v 37 e (v 78 (v 22 e (v 67 (v 46 (v
      47 e e) e) e)) e)))) (v 35 e (v 36 e (v 78 (v 26 e (v 44 (v 67 (v 46 (v 47 e e) e) e) e)) e)))) (v
      33 (v 35 (v 36 e (v 78 e e)) (v 36 (v 78 (v 81 (v 22 e (v 25 e e)) (v 22 e e)) (v 22 (v 25 e e) e))
      e)) (v 35 (v 36 e e) e))) (v 48 (v 33 (v 35 (v 78 e (v 80 (v 26 e (v 22 e e)) (v 26 e e))) (v 78 (v
      80 (v 26 e (v 22 e e)) e) (v 22 e e))) (v 35 (v 78 (v 80 (v 26 e (v 24 e e)) (v 24 e e)) (v 24 e
      e)) e)) (v 22 (v 78 e e) e))) (v 47 (v 48 (v 33 e (v 78 (v 79 (v 25 e e) e) e)) (v 22 (v 78 (v 79
      (v 25 e e) e) e) e)) (v 22 e e)))) (v 56 (v 57 (v 58 (v 59 (v 34 (v 35 e (v 36 e (v 37 (v 77 e (v
      23 e (v 26 e e))) (v 77 e e)))) (v 35 e (v 36 e (v 77 (v 26 e (v 66 (v 45 (v 46 e e) e) e)) e))))
      (v 34 (v 35 e (v 36 (v 77 e (v 23 e e)) e)) (v 35 e e))) (v 48 (v 34 (v 35 e (v 77 e (v 23 e e)))
      (v 35 e (v 66 e e))) (v 77 e e))) (v 47 (v 48 (v 34 (v 77 (v 79 (v 25 e (v 26 e (v 23 (v 66 e (v 12
      e (v 68 e e))) (v 66 (v 68 (v 36 e e) e) e)))) (v 25 e (v 26 e (v 66 (v 12 e e) e)))) (v 79 (v 25 e
      (v 26 e (v 88 (v 12 e e) e))) (v 25 e e))) (v 77 (v 79 (v 25 e e) e) e)) (v 77 (v 23 (v 79 (v 25 (v
      70 e (v 66 e e)) (v 66 e e)) (v 66 (v 12 e e) e)) e) e)) (v 77 (v 23 (v 79 (v 69 (v 26 e (v 66 e
      e)) e) e) e) e))) (v 46 (v 47 (v 48 e (v 77 (v 78 (v 24 e e) e) e)) (v 77 (v 78 (v 24 e e) e) e))
      (v 77 (v 78 (v 68 (v 25 e e) e) e) e)))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33 e (v 34 e e)) e) e)
      (v 22 e e)) (v 22 (v 78 e e) e)) (v 77 e e))) (v 55 (v 56 (v 57 (v 157 (v 59 (v 33 e (v 34 e e)) e)
      e) (v 22 e e)) (v 22 (v 78 e e) e)) (v 77 e e))) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 e (v 34 (v
      134 (v 36 (v 37 e (v 23 (v 123 e e) e)) e) e) e)) (v 22 e e)) (v 22 e e)) e) (v 22 e e)) (v 77 (v
      23 (v 123 (v 25 e e) e) e) e))) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 (v 133 (v 35 e (v 36 e (v 22 e
      e))) (v 35 e e)) (v 133 (v 35 e e) e)) (v 22 (v 122 (v 24 e e) e) e)) (v 22 (v 122 (v 24 e e) e)
      e)) (v 22 e e)) e) e)) (v 154 (v 56 (v 57 (v 58 (v 59 (v 132 (v 34 (v 35 e (v 36 e (v 121 (v 23 e
      e) e))) (v 35 e e)) (v 34 (v 35 e e) e)) (v 121 (v 23 e e) e)) (v 121 (v 23 e e) e)) (v 121 (v 23
      (v 79 (v 25 e e) e) e) e)) e) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 4, 3).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 e (v 34 e (v 35 e (v 36 e (v
      37 (v 26 e (v 44 e (v 45 (v 46 e (v 47 e (v 27 (v 28 e (v 30 e (v 31 e (v 18 e e)))) (v 28 e e))))
      (v 46 (v 47 e (v 28 e (v 29 (v 31 e (v 32 (v 16 e e) e)) (v 31 e (v 32 (v 16 e e) e))))) e)))) (v
      44 (v 45 e (v 46 (v 47 e (v 28 (v 29 e (v 32 (v 16 e (v 19 e e)) (v 16 (v 19 (v 20 e e) e) (v 19 (v
      20 e e) e)))) (v 29 (v 32 (v 16 e e) (v 16 e e)) (v 32 (v 16 e e) (v 16 (v 19 (v 20 (v 5 e e) e) e)
      e))))) (v 27 (v 29 e (v 30 e e)) (v 29 e (v 30 e e))))) (v 45 (v 46 e (v 27 (v 30 e (v 31 e (v 17 e
      (v 18 e e)))) (v 30 e (v 31 e (v 17 e e))))) e))))))) (v 33 e (v 34 e (v 35 e (v 25 e (v 44 (v 45 e
      e) e)))))) (v 59 (v 33 e (v 34 e (v 35 e (v 80 (v 26 e (v 44 (v 45 e e) e)) (v 44 e e))))) (v 33 e
      (v 34 e e)))) (v 58 (v 59 (v 33 (v 34 e (v 36 e (v 37 e (v 79 (v 22 e (v 45 e e)) e)))) (v 34 (v 36
      (v 37 e (v 79 e (v 23 e (v 25 e e)))) (v 37 (v 79 e (v 23 e (v 26 e e))) (v 79 e e))) (v 36 (v 37 e
      (v 79 (v 25 e (v 44 (v 45 (v 68 e e) e) e)) e)) (v 79 (v 26 e (v 44 (v 45 (v 68 e e) e) e)) e))))
      (v 33 (v 34 e (v 36 (v 79 (v 81 (v 22 e (v 25 e e)) (v 22 e e)) (v 22 e e)) e)) (v 34 (v 36 (v 79 e
      (v 23 e e)) e) e))) (v 48 (v 33 (v 34 e (v 79 (v 80 e e) e)) (v 34 (v 79 e (v 23 e e)) e)) (v 22 e
      e)))) (v 57 (v 58 (v 59 (v 33 (v 35 (v 36 e (v 37 e (v 78 e (v 22 e (v 24 e e))))) (v 36 e (v 37 e
      (v 78 (v 22 e (v 67 (v 46 (v 47 e e) e) e)) e)))) (v 35 (v 36 e (v 37 e (v 78 e e))) (v 36 e (v 78
      (v 26 e (v 44 (v 67 (v 46 (v 47 e e) e) e) e)) e)))) (v 33 (v 35 (v 36 e (v 78 e (v 22 (v 24 e e)
      e))) (v 36 (v 78 (v 81 (v 22 e (v 25 e e)) (v 22 e e)) (v 22 (v 25 e e) e)) e)) (v 35 (v 36 e e)
      e))) (v 48 (v 33 (v 35 (v 78 (v 80 (v 26 e (v 22 e (v 24 e (v 67 (v 69 e e) e)))) (v 26 e (v 22 e
      e))) (v 80 (v 26 e (v 22 e e)) (v 26 e (v 11 e e)))) (v 78 (v 80 (v 26 e (v 22 e e)) (v 22 e e)) (v
      22 e e))) (v 35 (v 78 (v 80 (v 26 (v 24 e (v 44 e (v 67 (v 69 e e) e))) (v 24 e (v 28 e (v 29 e (v
      32 e (v 20 e (v 16 e e))))))) (v 24 e e)) (v 24 (v 80 e e) e)) (v 44 e e))) (v 22 (v 78 e e) e)))
      (v 47 (v 48 (v 33 (v 78 e (v 79 (v 25 e (v 26 e e)) (v 25 e e))) (v 78 (v 79 (v 25 e e) e) e)) (v
      22 (v 78 (v 79 (v 25 e e) e) e) e)) (v 22 e e)))) (v 56 (v 57 (v 58 (v 59 (v 34 e (v 35 e (v 36 e
      (v 77 (v 26 e (v 66 (v 45 (v 46 e e) e) e)) (v 88 e e))))) (v 34 e (v 35 e e))) (v 48 (v 34 e (v 35
      e (v 66 (v 45 (v 46 e e) e) e))) e)) (v 47 (v 48 (v 34 (v 77 (v 79 (v 25 e (v 26 e (v 23 e (v 66 (v
      68 (v 36 e e) e) e)))) (v 25 e (v 26 e e))) (v 79 (v 25 e (v 26 e e)) (v 25 e (v 88 (v 12 e e)
      e)))) (v 77 (v 79 (v 25 e (v 26 e e)) e) (v 79 e e))) (v 77 (v 23 e e) e)) (v 77 (v 23 e (v 66 (v
      34 e e) e)) e))) (v 46 (v 47 (v 48 (v 77 (v 78 (v 24 e (v 25 e (v 26 e (v 66 (v 67 e e) e)))) (v 24
      e (v 25 e e))) (v 78 (v 24 e (v 25 e e)) (v 24 e e))) (v 77 (v 78 (v 24 e e) e) e)) (v 77 (v 78 (v
      24 e (v 66 e e)) e) e)) (v 77 (v 78 (v 68 (v 25 e e) e) e) e)))) (v 55 (v 56 (v 57 (v 58 (v 158 (v
      33 e (v 34 e e)) e) e) (v 22 e e)) (v 22 (v 78 e e) e)) e)) (v 55 (v 56 (v 57 (v 157 (v 59 (v 33 e
      (v 34 e e)) e) e) (v 22 e e)) (v 22 (v 78 e e) e)) e)) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 (v 34 e
      (v 134 (v 36 e e) e)) (v 34 (v 134 (v 36 (v 37 e (v 23 e e)) (v 23 e e)) e) (v 123 e e))) (v 22 e
      e)) (v 22 e e)) (v 22 e e)) (v 22 e e)) (v 77 (v 23 (v 123 (v 25 e e) e) e) e))) (v 55 (v 155 (v 57
      (v 58 (v 59 (v 33 (v 133 (v 35 (v 36 e (v 37 e (v 22 (v 122 (v 24 e e) e) e))) (v 36 e e)) (v 35 (v
      36 e e) e)) (v 133 (v 35 (v 36 e e) e) e)) (v 22 (v 122 (v 24 e e) e) e)) (v 22 (v 122 (v 24 (v 80
      (v 26 e (v 11 e e)) e) e) e) e)) (v 22 e e)) e) (v 77 (v 122 (v 24 e e) e) e))) (v 154 (v 56 (v 57
      (v 58 (v 59 (v 132 (v 34 e (v 35 e e)) (v 34 e e)) e) e) (v 121 (v 23 (v 79 e e) e) e)) (v 121 (v
      78 (v 24 e e) e) e)) e)), ?_⟩
    decide +kernel
  · -- Anchor positions (0, 4, 4).
    refine ⟨
      (v 99 (v 100 (v 101 (v 102 (v 103 (v 55 (v 56 (v 57 (v 58 (v 59 (v 33 (v 34 e (v 35 e (v 36 e (v 37
      e (v 22 e (v 45 e (v 46 e (v 47 (v 48 e (v 27 e (v 29 e (v 30 (v 31 e (v 32 e e)) e)))) (v 27 e (v
      28 e e)))))))))) (v 34 e (v 35 e (v 36 e (v 37 (v 26 e (v 44 (v 45 e (v 46 e (v 47 e (v 27 (v 28 e
      (v 29 e (v 30 e e))) (v 28 e e))))) (v 45 e (v 46 e e)))) (v 44 (v 45 e (v 46 e (v 27 (v 29 (v 30 e
      (v 31 e (v 32 e e))) (v 30 e e)) (v 29 (v 30 e (v 31 e (v 32 e e))) (v 30 e e))))) (v 45 e e)))))))
      (v 33 (v 34 e (v 35 e (v 36 e (v 81 (v 22 e (v 45 e e)) e)))) (v 34 e (v 35 e (v 25 e (v 44 (v 45 e
      e) e)))))) (v 59 (v 33 (v 34 e (v 35 e (v 37 (v 80 e (v 22 e (v 26 e e))) (v 80 (v 22 e (v 45 e e))
      e)))) (v 34 e (v 35 e (v 80 (v 26 (v 44 e (v 45 e (v 46 e e))) (v 44 (v 45 e e) e)) (v 44 (v 45 e
      e) e))))) (v 33 (v 34 e (v 35 e e)) (v 34 e e)))) (v 58 (v 59 (v 33 (v 34 e (v 36 (v 37 e (v 79 (v
      22 e (v 25 e (v 45 e (v 68 (v 48 e (v 27 e (v 30 e (v 32 e (v 29 e (v 31 e (v 49 e (v 17 (v 52 e e)
      e)))))))) e)))) (v 22 e (v 25 (v 45 e (v 90 e e)) e)))) (v 37 e (v 79 (v 22 e (v 45 e e)) e)))) (v
      34 (v 36 (v 37 e (v 79 e (v 23 e (v 25 (v 44 e (v 90 e e)) e)))) (v 37 e (v 79 e e))) (v 36 (v 37
      (v 79 e (v 25 e (v 26 e e))) (v 79 (v 25 e (v 44 (v 45 (v 68 (v 48 e (v 27 e (v 30 e (v 32 e (v 18
      e e))))) (v 38 e (v 41 e (v 43 e (v 18 e (v 20 e (v 60 e (v 17 e e)))))))) e) e)) (v 44 (v 45 (v 90
      e e) e) e))) (v 79 (v 26 e (v 44 (v 45 (v 68 (v 47 (v 37 e (v 27 e (v 30 (v 32 e (v 17 e e)) (v 32
      (v 17 e e) (v 17 e (v 18 e e)))))) e) e) e) e)) e)))) (v 33 (v 34 e (v 36 (v 79 (v 81 (v 22 e (v 25
      (v 45 e (v 68 e e)) e)) (v 22 e e)) (v 22 (v 25 (v 81 e e) e) e)) e)) (v 34 (v 36 (v 79 e (v 23 e
      e)) e) (v 44 (v 45 (v 68 e e) e) e)))) (v 48 (v 33 (v 34 e (v 79 (v 80 (v 26 e (v 22 e e)) (v 22 e
      e)) (v 22 e e))) (v 34 (v 79 e (v 23 e e)) (v 44 e e))) (v 22 e e)))) (v 57 (v 58 (v 59 (v 33 (v 35
      e (v 36 e (v 37 (v 78 (v 22 e (v 26 e (v 67 e (v 46 e e)))) (v 22 (v 26 e (v 11 e (v 89 (v 46 e e)
      e))) (v 26 e e))) (v 78 (v 22 (v 11 e (v 67 (v 46 e (v 47 e e)) (v 46 (v 47 e (v 40 e (v 42 e (v 28
      e (v 16 (v 19 e e) e))))) e))) (v 67 (v 46 (v 47 e (v 29 e (v 31 e (v 28 (v 16 e (v 19 e e)) (v 16
      e e))))) (v 29 e (v 31 e (v 27 (v 30 e e) (v 30 e e))))) e)) (v 11 (v 89 e e) e))))) (v 35 e (v 36
      e (v 78 (v 26 e (v 44 (v 67 (v 46 (v 47 e e) e) e) e)) e)))) (v 33 (v 35 e (v 36 e (v 11 e e))) (v
      35 e e))) (v 48 (v 33 (v 35 (v 78 e (v 80 e (v 26 (v 22 (v 24 e (v 11 (v 89 e e) e)) e) e))) (v 78
      (v 80 (v 26 (v 22 e (v 67 e (v 46 (v 69 e e) e))) (v 22 (v 11 e (v 67 (v 46 e e) e)) (v 28 e (v 29
      e (v 31 e (v 16 e e)))))) (v 22 (v 26 (v 11 e (v 67 e e)) e) e)) (v 22 (v 80 (v 26 (v 11 (v 89 e (v
      46 (v 69 e e) e)) (v 89 (v 46 (v 69 e e) e) e)) e) e) e))) (v 35 (v 78 e (v 24 e e)) (v 44 (v 67 (v
      46 (v 69 e e) e) e) e))) (v 22 (v 78 (v 24 e (v 11 e e)) e) e))) (v 47 (v 48 (v 33 (v 78 (v 79 (v
      25 e (v 26 e (v 22 e (v 67 (v 68 (v 36 e e) e) e)))) (v 25 e (v 26 e e))) (v 79 (v 25 e (v 26 e (v
      11 e e))) (v 25 e e))) (v 78 (v 79 (v 25 e (v 26 e e)) (v 25 e e)) e)) (v 22 (v 78 (v 79 (v 25 (v
      70 e (v 11 e e)) (v 11 e e)) (v 11 e e)) e) e)) (v 22 (v 78 (v 79 (v 69 (v 26 e (v 11 e e)) e) e)
      (v 11 e e)) (v 33 e e))))) (v 56 (v 57 (v 58 (v 59 (v 34 e (v 35 e (v 36 e (v 77 (v 26 e (v 66 (v
      45 e e) e)) e)))) (v 34 e (v 35 e e))) (v 48 (v 34 e (v 35 e (v 66 (v 45 e e) e))) e)) (v 47 (v 48
      (v 34 (v 77 (v 79 (v 25 e (v 26 e (v 23 e (v 66 (v 68 e e) e)))) (v 25 e (v 26 e e))) (v 79 (v 25 e
      (v 26 e e)) (v 25 e e))) (v 77 (v 79 (v 25 e (v 26 e e)) (v 25 e e)) e)) (v 77 (v 23 e e) e)) (v 77
      (v 23 e (v 66 e e)) e))) (v 46 (v 47 e (v 77 (v 78 (v 24 e e) e) e)) (v 77 (v 78 (v 68 (v 25 e e)
      e) e) e)))) (v 55 (v 56 (v 57 (v 58 (v 158 (v 33 (v 34 e (v 35 e e)) (v 34 e e)) e) e) (v 22 e e))
      e) e)) (v 55 (v 56 (v 57 (v 157 (v 59 (v 33 (v 34 e (v 35 e (v 22 e e))) (v 34 e e)) e) e) (v 22 e
      e)) (v 22 (v 78 (v 24 e (v 11 e e)) e) e)) e)) (v 55 (v 56 (v 156 (v 58 (v 59 (v 33 (v 34 e (v 134
      (v 36 (v 37 e (v 22 e e)) e) e)) (v 34 (v 134 (v 36 (v 37 e (v 23 e e)) e) e) (v 123 (v 25 (v 26 e
      e) e) e))) (v 22 (v 23 e e) e)) (v 22 e e)) (v 22 e e)) (v 22 (v 78 e e) e)) (v 77 (v 23 (v 123 (v
      25 (v 26 e (v 66 e e)) e) e) e) e))) (v 55 (v 155 (v 57 (v 58 (v 59 (v 33 (v 133 (v 35 e (v 36 e (v
      22 (v 122 (v 26 e e) e) e))) (v 35 e e)) (v 133 (v 35 e e) e)) e) (v 22 (v 122 (v 24 e (v 11 (v 111
      (v 35 e e) e) e)) e) e)) (v 22 (v 122 (v 79 (v 25 e e) e) e) e)) e) e)) (v 154 (v 56 (v 57 (v 58 (v
      59 (v 132 (v 34 e (v 35 e e)) (v 34 e e)) e) e) (v 121 (v 23 (v 79 e e) e) e)) e) e)), ?_⟩
    decide +kernel
set_option maxHeartbeats 1600000 in
/-- Numeric consequence of the five class sizes summing to 22. Each pair
of side counts is bounded by the corresponding class sizes less one. -/
lemma capacity_bound (n : Fin 5 → ℕ) (positive : ∀ i,1 ≤ n i)
    (total : (∑ i,n i)=22) (b c : Fin 5)
    (lp rp lq rq lr rr : ℕ)
    (hp : lp<n 2 ∧ rp<n 3) (hq : lq<n (b+2) ∧ rq<n (b+3))
    (hr : lr<n (c+2) ∧ rr<n (c+3)) :
  let fee (t a : Fin 5) (l r : ℕ) := if t=a ∨ t=a+1 then l else if t=a+2 then 0 else r
  let same (t b : Fin 5) := if b≠0 ∧ (((0:Fin 5)=t+2 ∨ (0:Fin 5)=t+4) ↔ (b=t+2 ∨ b=t+4)) then 1 else 0
  let ded (t a : Fin 5) (h : ℕ) := if t=a+2 then h else 0
  ∃ t : Fin 5, n t*n (t+1)+fee t 0 lp rp+fee t b lq rq+fee t c lr rr+(same t b+same t c) ≤
    25+max (ded t 0 (lp*rp)) (max (ded t b (lq*rq)) (ded t c (lr*rr))) := by
  intro fee same ded
  let leaf (b c : Fin 5) (lo hi : Fin 11 → ℕ) :=
    let total := lo 0+lo 1+lo 2+lo 3+lo 4
    let cap (i : Fin 5) := min (hi (Fin.ofNat 11 i.val)) (22+lo (Fin.ofNat 11 i.val)-total)
    let l (a : Fin 5) (i : Fin 11) := min (hi i) (cap (a+2)-1)
    let r (a : Fin 5) (i : Fin 11) := min (hi i) (cap (a+3)-1)
    decide (22 < total ∨ hi 0+hi 1+hi 2+hi 3+hi 4 < 22 ∨
      ∃ t : Fin 5, cap t*cap (t+1)+fee t 0 (l 0 5) (r 0 6)+fee t b (l b 7) (r b 8)+
        fee t c (l c 9) (r c 10)+(same t b+same t c) ≤
        25+max (ded t 0 (lo 5*lo 6)) (max (ded t b (lo 7*lo 8)) (ded t c (lo 9*lo 10))))
  let audit (b c : Fin 5) (tr : BinaryTree ℕ) := BinaryTree.rec
    (motive:=fun _ => (Fin 11 → ℕ) → (Fin 11 → ℕ) → Bool)
    (leaf b c) (fun s _ _ l r lo hi =>
      l lo (Function.update hi (Fin.ofNat 11 s) (s/11)) &&
      r (Function.update lo (Fin.ofNat 11 s) (s/11+1)) hi) tr
  let initLo (i : Fin 11) := if i.val<5 then 1 else 0
  let initHi (i : Fin 11) := if i.val<5 then 18 else 17
  obtain ⟨tr,test⟩ : ∃ tr, audit b c tr initLo initHi=true := by
    exact all_subdivisions b c
  let x : Fin 11 → ℕ := ![n 0,n 1,n 2,n 3,n 4,lp,rp,lq,rq,lr,rr]
  have sum : n 0+n 1+n 2+n 3+n 4=22 := by simpa only [Fin.sum_univ_five] using total
  have pos0 := positive 0; have pos1 := positive 1; have pos2 := positive 2
  have pos3 := positive 3; have pos4 := positive 4
  have maxN (i) : n i ≤ 18 := by
    fin_cases i
    · change n 0 ≤ 18; omega
    · change n 1 ≤ 18; omega
    · change n 2 ≤ 18; omega
    · change n 3 ≤ 18; omega
    · change n 4 ≤ 18; omega
  have initLow (i) : initLo i ≤ x i := by fin_cases i <;> simp [initLo,x,positive]
  have initHigh (i) : x i ≤ initHi i := by
    have u := maxN (b+2); have v := maxN (b+3)
    have w := maxN (c+2); have y := maxN (c+3)
    fin_cases i
    · change n 0 ≤ 18; exact maxN _
    · change n 1 ≤ 18; exact maxN _
    · change n 2 ≤ 18; exact maxN _
    · change n 3 ≤ 18; exact maxN _
    · change n 4 ≤ 18; exact maxN _
    · change lp ≤ 17; omega
    · change rp ≤ 17; omega
    · change lq ≤ 17; omega
    · change rq ≤ 17; omega
    · change lr ≤ 17; omega
    · change rr ≤ 17; omega
  apply interval_audit (leaf b c) x _ _ tr initLo initHi initLow initHigh test
  intro lo hi low high accepted
  let tot := lo 0+lo 1+lo 2+lo 3+lo 4
  let cap (i : Fin 5) := min (hi (Fin.ofNat 11 i.val)) (22+lo (Fin.ofNat 11 i.val)-tot)
  have compare (i : Fin 5) : n i ≤ cap i := by
    have l0 : lo 0 ≤ n 0 := low 0; have l1 : lo 1 ≤ n 1 := low 1
    have l2 : lo 2 ≤ n 2 := low 2; have l3 : lo 3 ≤ n 3 := low 3
    have l4 : lo 4 ≤ n 4 := low 4
    have ix (j : Fin 5) : x (Fin.ofNat 11 j.val)=n j := by fin_cases j <;> rfl
    apply le_min (by simpa only [ix] using high (Fin.ofNat 11 i.val))
    fin_cases i
    · change n 0 ≤ 22+lo 0-(lo 0+lo 1+lo 2+lo 3+lo 4); omega
    · change n 1 ≤ 22+lo 1-(lo 0+lo 1+lo 2+lo 3+lo 4); omega
    · change n 2 ≤ 22+lo 2-(lo 0+lo 1+lo 2+lo 3+lo 4); omega
    · change n 3 ≤ 22+lo 3-(lo 0+lo 1+lo 2+lo 3+lo 4); omega
    · change n 4 ≤ 22+lo 4-(lo 0+lo 1+lo 2+lo 3+lo 4); omega
  have lowTotal : tot≤22 := calc
    _ ≤ n 0+n 1+n 2+n 3+n 4 := by
      dsimp only [tot]
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (low 0) (low 1))
        (low 2)) (low 3)) (low 4)
    _ = 22 := sum
  have highTotal : 22 ≤ hi 0+hi 1+hi 2+hi 3+hi 4 := by
    rw [←sum]
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (high 0) (high 1))
      (high 2)) (high 3)) (high 4)
  dsimp only [leaf] at accepted
  rw [decide_eq_true_eq] at accepted
  rcases accepted with h|h|⟨t,ht⟩
  · exact ((not_lt_of_ge lowTotal) h).elim
  · exact ((not_lt_of_ge highTotal) h).elim
  refine ⟨t,?_⟩
  have mono (a : Fin 5) {j k J K : ℕ} (u : j ≤ J) (v : k ≤ K) : fee t a j k ≤ fee t a J K := by
    dsimp only [fee]; split_ifs <;> omega
  have small {v : ℕ} {j : Fin 11} {k : Fin 5} (u : v ≤ hi j) (h : v<n k) : v ≤ min (hi j) (cap k-1) :=
    le_min u (by have e := compare k; omega)
  have dmono (a : Fin 5) {u v : ℕ} (h : u ≤ v) : ded t a u ≤ ded t a v := by
    dsimp only [ded]; split_ifs <;> omega
  have x1 := mono 0 (small (j:=5) (high 5 : lp ≤ hi 5) hp.1) (small (j:=6) (high 6 : rp ≤ hi 6) hp.2)
  have x2 := mono b (small (j:=7) (high 7 : lq ≤ hi 7) hq.1) (small (j:=8) (high 8 : rq ≤ hi 8) hq.2)
  have x3 := mono c (small (j:=9) (high 9 : lr ≤ hi 9) hr.1) (small (j:=10) (high 10 : rr ≤ hi 10) hr.2)
  have x0 := Nat.mul_le_mul (compare t) (compare (t+1))
  have dm := max_le_max (dmono 0 (Nat.mul_le_mul (low 5 : _≤lp) (low 6 : _≤rp)))
    (max_le_max (dmono b (Nat.mul_le_mul (low 7 : _≤lq) (low 8 : _≤rq)))
      (dmono c (Nat.mul_le_mul (low 9 : _≤lr) (low 10 : _≤rr))))
  change cap t*cap (t+1)+_+_+_+_ ≤ _ at ht
  exact (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add x0 x1) x2) x3) _).trans
    (ht.trans (Nat.add_le_add_left dm _))

set_option maxHeartbeats 2000000 in
/-- Bound a cut by the five ordinary class sizes and the two side neighborhoods
of each exceptional vertex. The class at index t and its successor form the
only monochromatic ordinary boundary. -/
lemma layer_cut (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (O : Finset (Fin 25)) (g : Fin 25 → Fin 5) (z : Fin 3 → Fin 25)
    (a : Fin 3 → Fin 5) (inj : Function.Injective z)
    (out : ∀ u,z u ∉ O) (cover : ∀ i,i∉O → ∃ u,z u=i)
    (coreMap : ∀ i ∈ O,∀ j ∈ O,G.Adj i j → g j=g i+1 ∨ g i=g j+1)
    (side : ∀ u i,i∈O → G.Adj (z u) i → g i=a u ∨ g i=a u+2 ∨ g i=a u+3)
    (special : ∀ u v,G.Adj (z u) (z v) → (u=0 ∧ (v=1 ∨ v=2)) ∨ (v=0 ∧ (u=1 ∨ u=2)))
    (separate : ∀ u v,G.Adj (z u) (z v) → a u≠a v)
    (t : Fin 5) :
    let A (k : Fin 5) := O.filter (fun i => g i=k)
    let N (u : Fin 3) (k : Fin 5) := (A (a u+k)).filter (G.Adj (z u))
    let fee (u : Fin 3) := if t=a u ∨ t=a u+1 then (N u 2).card else
      if t=a u+2 then 0 else (N u 3).card
    let same (u : Fin 3) := if a u≠a 0 ∧ ((a 0=t+2 ∨ a 0=t+4) ↔ (a u=t+2 ∨ a u=t+4)) then 1 else 0
    let missing (u : Fin 3) := if t=a u+2 then (N u 2).card*(N u 3).card else 0
    (A t).card*(A (t+1)).card+fee 0+fee 1+fee 2+(same 1+same 2) ≤
      25+max (missing 0) (max (missing 1) (missing 2)) →
    ∃ f : Fin 25 → Bool, (∑ i,∑ j, if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 50 := by
  classical
  intro A N fee same missing bound
  let white (k : Fin 5) := decide (k=t+2 ∨ k=t+4)
  let owner (i : Fin 25) : Fin 3 := if i=z 0 then 0 else if i=z 1 then 1 else 2
  have own (u : Fin 3) : owner (z u)=u := by fin_cases u <;> simp [owner,inj.eq_iff]
  let f (i : Fin 25) := if i∈O then white (g i) else !(white (a (owner i)))
  have fc {i} (hi : i∈O) : f i=white (g i) := if_pos hi
  have fz (u) : f (z u) = !(white (a u)) := by simp [f,out u,own]
  let W (u : Fin 3) := if t=a u ∨ t=a u+1 then N u 2 else if t=a u+2 then ∅ else N u 3
  have wc (u) : (W u).card=fee u := by
    dsimp only [fee,W]
    split_ifs <;> simp
  have ordinaryRule : ∀ k u v : Fin 5, (v=u+1 ∨ u=v+1) →
      (decide (u=k+2 ∨ u=k+4) = decide (v=k+2 ∨ v=k+4)) →
      (u=k ∧ v=k+1) ∨ (v=k ∧ u=k+1) := by decide +kernel
  have sideRule : ∀ k a c : Fin 5, (c=a ∨ c=a+2 ∨ c=a+3) →
      decide (c=k+2 ∨ c=k+4) ≠ decide (a=k+2 ∨ a=k+4) →
      (if k=a ∨ k=a+1 then c=a+2 else if k=a+2 then False else c=a+3) := by decide +kernel
  have whenSide {u i} (hi : i∈O) (h : G.Adj (z u) i) (eq : f (z u)=f i) : i∈W u := by
    have different : white (g i)≠white (a u) := by
      rw [fz,fc hi] at eq
      intro e
      rw [e] at eq
      cases hs : white (a u) <;> simp [hs] at eq
    have rule := sideRule t (a u) (g i) (side u i hi h) different
    by_cases l : t=a u ∨ t=a u+1
    · simp only [l,if_true] at rule
      simp [W,l,N,A,hi,h,rule]
    by_cases r : t=a u+2
    · simp [r] at rule
    · simp only [l,r,if_false] at rule
      simp [W,l,r,N,A,hi,h,rule]
  let rect (U V : Finset (Fin 25)) (i j : Fin 25) : ℕ :=
    if i∈U then if j∈V then 1 else 0 else 0
  have rectSum (U V : Finset (Fin 25)) : (∑ i,∑ j,rect U V i j)=U.card*V.card := by
    simp only [rect]
    simp_rw [← Finset.ite_sum_zero]
    simp
  let block (i j : Fin 25) := if G.Adj i j then rect (A t) (A (t+1)) i j else 0
  let pair (i j : Fin 25) := rect {z 0} {z 1} i j * same 1 + rect {z 0} {z 2} i j * same 2
  let loss (i j : Fin 25) := block i j + (∑ u, rect {z u} (W u) i j) + pair i j
  have between {i j} (hi : i∈O) (hj : j∈O) (h : G.Adj i j) (hl : g i=t ∧ g j=t+1) :
      1 ≤ loss i j := by
    have b : block i j=1 := by simp [block,rect,A,h,hi,hj,hl.1,hl.2]
    dsimp only [loss]; omega
  have incident {u i} (hi : i∈O) (h : G.Adj (z u) i) (eq : f (z u)=f i) : 1≤loss (z u) i := by
    have one : rect {z u} (W u) (z u) i=1 := by simp [rect,whenSide hi h eq]
    have le := Finset.single_le_sum (s:=univ) (f:=fun v : Fin 3 => rect {z v} (W v) (z u) i)
      (fun _ _ => Nat.zero_le _) (mem_univ u)
    dsimp only [loss]; omega
  have zz (u : Fin 3) (leaf : u=1 ∨ u=2) (adj : G.Adj (z 0) (z u))
      (eq : f (z 0)=f (z u)) : 1≤loss (z 0) (z u) := by
    have he : white (a 0)=white (a u) := by simpa only [fz,Bool.not_not] using congrArg Bool.not eq
    have eqv : (a 0=t+2 ∨ a 0=t+4) ↔ (a u=t+2 ∨ a u=t+4) := by
      simpa only [white,decide_eq_decide] using he
    have h : same u=1 := by simp [same,(separate 0 u adj).symm,eqv]
    have b : 1≤pair (z 0) (z u) := by
      rcases leaf with rfl|rfl <;> simp [pair,rect,h,inj.eq_iff]
    dsimp only [loss]; omega
  have charge (i j : Fin 25) :
      (if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ loss i j+loss j i := by
    split_ifs with h
    · obtain ⟨ij,eq⟩ := h
      by_cases hi : i∈O
      · by_cases hj : j∈O
        · have rule := ordinaryRule t (g i) (g j) (coreMap i hi j hj ij) (by simpa only [fc hi,fc hj] using eq)
          rcases rule with l|l
          · have e := between hi hj ij l; omega
          · have e := between hj hi ij.symm l; omega
        · obtain ⟨u,rfl⟩ := cover j hj
          have e := incident hi ij.symm eq.symm; omega
      · obtain ⟨u,rfl⟩ := cover i hi
        by_cases hj : j∈O
        · have e := incident hj ij eq; omega
        · obtain ⟨v,rfl⟩ := cover j hj
          rcases special u v ij with ⟨rfl,leaf⟩|⟨rfl,leaf⟩
          · have e := zz v leaf ij eq; omega
          · have e := zz u leaf ij.symm eq.symm; omega
    · exact Nat.zero_le _
  let B := ∑ i,∑ j,block i j
  have cap (u : Fin 3) : B+missing u ≤ (A t).card*(A (t+1)).card := by
    by_cases pos : t=a u+2
    · have shift : t+1=a u+3 := by rw [pos]; abel
      have cell (i j : Fin 25) :
          block i j + rect (N u 2) (N u 3) i j ≤ rect (A t) (A (t+1)) i j := by
        by_cases a1 : i∈N u 2
        · by_cases a2 : j∈N u 3
          · have hi := mem_filter.mp a1
            have hj := mem_filter.mp a2
            have no : ¬G.Adj i j := fun ij => tri _ (is3Clique_triple_iff.mpr ⟨hi.2,hj.2,ij⟩)
            have left : i∈A t := pos ▸ hi.1
            have right : j∈A (t+1) := shift ▸ hj.1
            simp [block,no,rect,a1,a2,left,right]
          · simp only [rect,a2,if_false,ite_self,add_zero]
            dsimp only [block,rect]; split_ifs <;> omega
        · simp only [rect,a1,if_false,add_zero]
          dsimp only [block,rect]; split_ifs <;> omega
      have total := sum_le_sum (s:=univ) (fun i _ => sum_le_sum (s:=univ) (fun j _ => cell i j))
      simpa only [B,sum_add_distrib,rectSum,missing,pos,if_true] using total
    · have cell (i j : Fin 25) : block i j ≤ rect (A t) (A (t+1)) i j := by
        dsimp only [block]; split_ifs <;> omega
      have total := sum_le_sum (s:=univ) (fun i _ => sum_le_sum (s:=univ) (fun j _ => cell i j))
      simpa only [B,missing,pos,if_false,add_zero,rectSum] using total
  have maxCap : B+max (missing 0) (max (missing 1) (missing 2)) ≤ (A t).card*(A (t+1)).card := by
    have a := cap 0; have b := cap 1; have c := cap 2; omega
  have sumPair : (∑ i,∑ j,pair i j)=same 1+same 2 := by simp only [pair,sum_add_distrib,←sum_mul,rectSum,card_singleton,one_mul]
  have count : (∑ i,∑ j,loss i j)=B+fee 0+fee 1+fee 2+(same 1+same 2) := by
    simp only [loss,Fin.sum_univ_three,sum_add_distrib,rectSum,sumPair,card_singleton,one_mul,wc,B]
    omega
  have transpose : (∑ i,∑ j,loss j i)=∑ i,∑ j,loss i j := sum_comm
  have h := sum_le_sum (s:=univ) (fun i _ => sum_le_sum (s:=univ) (fun j _ => charge i j))
  simp only [sum_add_distrib,transpose,count] at h
  exact ⟨f,by omega⟩

/-- The two-neighbor classification on the pentagon, restricted to the
complement of the vertices with a unique cycle neighbor. -/
lemma pentagon_profiles {V : Type*} (G : SimpleGraph V) (tri : G.CliqueFree 3)
    (v : Fin 5 → V) (cycle : ∀ i, G.Adj (v i) (v (i+1)))
    (dom : ∀ x, ∃ i, G.Adj x (v i)) :
    ∃ g : V → Fin 5, (∀ x, ¬(∃! j, G.Adj x (v j)) → ∀ i,
      G.Adj x (v i) ↔ (i=g x+1 ∨ g x=i+1)) ∧ ∀ x, ¬(∃! i, G.Adj x (v i)) →
      ∀ y, ¬(∃! i, G.Adj y (v i)) →
        G.Adj x y → g y=g x+1 ∨ g x=g y+1 := by
  classical
  let S (x : V) := univ.filter (fun i : Fin 5 => G.Adj x (v i))
  have mem (x : V) (i : Fin 5) : i ∈ S x ↔ G.Adj x (v i) := by simp [S]
  have classify : ∀ T : Finset (Fin 5), 2 ≤ T.card → (∀ i ∈ T, i+1 ∉ T) →
      ∃ a : Fin 5, ∀ i, i ∈ T ↔ (i=a+1 ∨ a=i+1) := by decide +kernel
  have common : ∀ a b : Fin 5, ¬(b=a+1 ∨ a=b+1) →
      ∃ i, (i=a+1 ∨ a=i+1) ∧ (i=b+1 ∨ b=i+1) := by decide +kernel
  have label (x : V) : ∃ a : Fin 5, ∀ i, ¬(∃! j, G.Adj x (v j)) →
      (i ∈ S x ↔ (i=a+1 ∨ a=i+1)) := by
    by_cases single : ∃! i, G.Adj x (v i)
    · exact ⟨0, fun _ h => (h single).elim⟩
    · obtain ⟨i,hi⟩ := dom x
      have pos : 0 < (S x).card := Finset.card_pos.mpr ⟨i,(mem x i).mpr hi⟩
      have two : 2 ≤ (S x).card := by
        by_contra! small
        obtain ⟨j,hj⟩ := Finset.card_eq_one.mp (show (S x).card = 1 by omega)
        apply single
        have eq (k : Fin 5) : G.Adj x (v k) ↔ k = j := by rw [← mem,hj,mem_singleton]
        exact ⟨j,(eq j).mpr rfl,fun k hk => (eq k).mp hk⟩
      obtain ⟨a,ha⟩ := classify (S x) two
        (fun j hj hk => tri _ (is3Clique_triple_iff.mpr
          ⟨(mem x j).mp hj,(mem x _).mp hk,cycle j⟩))
      exact ⟨a,fun i _ => ha i⟩
  choose g hg using label
  refine ⟨g,fun x hx i => (mem x i).symm.trans (hg x i hx),fun x hx y hy xy => ?_⟩
  by_contra hn
  obtain ⟨i,hi,hj⟩ := common _ _ hn
  exact tri _ (is3Clique_triple_iff.mpr
    ⟨xy,(mem x i).mp ((hg x i hx).mpr hi),(mem y i).mp ((hg y i hy).mpr hj)⟩)


set_option maxHeartbeats 1600000 in
/-- Order the exceptions so that the last two are nonadjacent. The first
can be incident with both exceptional edges. -/
lemma cut_of_ordered_triple (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (v : Fin 5 → Fin 25) (cycle : ∀ i,G.Adj (v i) (v (i+1))) (dom : ∀ x,∃ i,G.Adj x (v i))
    (p q r : Fin 25) (pq : p≠q) (rp : r≠p) (rq : r≠q)
    (noQ : ¬G.Adj r q)
    (exceptions : ∀ x, (∃! k,G.Adj x (v k)) ↔ x=p ∨ x=q ∨ x=r) :
    ∃ f : Fin 25 → Bool, (∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 50 := by
  classical
  let z : Fin 3 → Fin 25 := ![p,q,r]
  have inj : Function.Injective z := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [z,pq,pq.symm,rp,rp.symm,rq,rq.symm]
  have ex (u : Fin 3) : ∃! k,G.Adj (z u) (v k) := (exceptions _).mpr (by fin_cases u <;> simp [z])
  choose a ha hu using ex
  let V (k : Fin 5) := v (k+a 0)
  let A (u : Fin 3) := a u-a 0
  have A0 : A 0=0 := sub_self _
  have separate (u w : Fin 3) (h : G.Adj (z u) (z w)) : A u≠A w := by
    intro e
    have eq : a u = a w := by
      simpa only [A,sub_add_cancel] using congrArg (fun k : Fin 5 => k+a 0) e
    exact tri _ (is3Clique_triple_iff.mpr ⟨h,ha u,by simpa only [eq] using ha w⟩)
  have unique (u : Fin 3) (k : Fin 5) : G.Adj (z u) (V k) ↔ k=A u := by
    constructor
    · intro h
      exact eq_sub_iff_add_eq.mpr (hu u (k+a 0) h)
    · rintro rfl
      simpa only [V,A,sub_add_cancel] using ha u
  have cyc (k : Fin 5) : G.Adj (V k) (V (k+1)) := by
    simpa only [V,add_right_comm] using cycle (k+a 0)
  have hits (x) : ∃ i,G.Adj x (V i) := by
    obtain ⟨k,h⟩ := dom x
    exact ⟨k-a 0,by simpa only [V,sub_add_cancel] using h⟩
  let X := ({p,q,r} : Finset (Fin 25))
  let O := Xᶜ
  have out (u) : z u ∉ O := by fin_cases u <;> simp [z,O,X]
  have cover (i) (h : i∉O) : ∃ u,z u=i := by
    have h' : i=p ∨ i=q ∨ i=r := by
      have mem : i∈X := by simpa only [O,mem_compl,not_not] using h
      simpa [X] using mem
    rcases h' with h|h|h
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,h.symm⟩
  have reg {x} (hx : x∈O) : ¬∃! i,G.Adj x (V i) := by
    rintro ⟨i,hi,only⟩
    have old : ∃! k,G.Adj x (v k) := by
      refine ⟨i+a 0,hi,fun k hk => ?_⟩
      have kEq := only (k-a 0) (by simpa only [V,sub_add_cancel] using hk)
      exact (sub_eq_iff_eq_add.mp kEq)
    have mem := (exceptions x).mp old
    exact (mem_compl.mp hx) (by simpa [X] using mem)
  have prev (k : Fin 5) : G.Adj (V k) (V (k+4)) := by
    have eq : k+4+1=k := by omega
    simpa only [eq] using (cyc (k+4)).symm
  have cycleIn (k : Fin 5) : V k ∈ O := by
    by_contra h
    obtain ⟨u,eu⟩ := cover _ h
    have x := (unique u (k+1)).mp (eu ▸ cyc k)
    have y := (unique u (k+4)).mp (eu ▸ prev k)
    omega
  obtain ⟨g,prof,maps⟩ := pentagon_profiles G tri V cyc hits
  have fixed (k : Fin 5) : g (V k)=k := by
    have h := (prof _ (reg (cycleIn k)) _).mp (cyc k)
    have j := (prof _ (reg (cycleIn k)) _).mp (prev k)
    omega
  let C (k : Fin 5) := O.filter (fun i => g i=k)
  let N (u : Fin 3) (k : Fin 5) := (C (A u+k)).filter (G.Adj (z u))
  let n (k) := (C k).card
  have head (k : Fin 5) : V k ∈ C k := mem_filter.mpr ⟨cycleIn k,fixed k⟩
  have pos (k) : 1 ≤ n k := card_pos.mpr ⟨_,head k⟩
  have total : (∑ k,n k)=22 := calc
    _ = O.card := by
      simpa [n,C] using Finset.sum_card_fiberwise_eq_card_filter O univ g
    _ = 22 := by
      change Xᶜ.card=22
      rw [Finset.card_compl]
      simp [X,pq,rp.symm,rq.symm]
  have strict (u : Fin 3) (k : Fin 5) (nz : k≠0) : (N u k).card<n (A u+k) := by
    apply card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨filter_subset _ _,?_⟩
    intro eq
    have mem : V (A u+k)∈N u k := eq ▸ head _
    have ea := (unique u _).mp (mem_filter.mp mem).2
    exact nz (by omega)
  have pairBound (u : Fin 3) : (N u 2).card<n (A u+2) ∧ (N u 3).card<n (A u+3) :=
    ⟨strict u 2 (by decide),strict u 3 (by decide)⟩
  have adjSides (u i) (hi : i∈O) (zi : G.Adj (z u) i) : g i=A u ∨ g i=A u+2 ∨ g i=A u+3 := by
    have no : ¬(A u=g i+1 ∨ g i=A u+1) := fun h => tri _ (is3Clique_triple_iff.mpr
      ⟨zi,(unique u _).mpr rfl,(prof i (reg hi) _).mpr h⟩)
    omega
  have special (u w : Fin 3) (h : G.Adj (z u) (z w)) :
      (u=0 ∧ (w=1 ∨ w=2)) ∨ (w=0 ∧ (u=1 ∨ u=2)) := by
    have nq : ¬G.Adj q r := fun e => noQ e.symm
    fin_cases u <;> fin_cases w <;> first | decide | exact (G.loopless.irrefl _ h).elim | exact (noQ h).elim | exact (nq h).elim
  obtain ⟨t,ht⟩ := capacity_bound n pos total (A 1) (A 2)
    (N 0 2).card (N 0 3).card (N 1 2).card (N 1 3).card (N 2 2).card (N 2 3).card
    (by simpa only [A0,zero_add] using pairBound 0) (pairBound 1) (pairBound 2)
  apply layer_cut G tri O g z A inj out cover (fun i hi j hj => maps i (reg hi) j (reg hj))
    adjSides special separate t
  change n t*n (t+1)+_+_+_+_ ≤ _
  dsimp only at ht
  simpa only [N,C,A0,zero_add] using ht

lemma edge_sum {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ i, ∑ j, if G.Adj i j then 1 else 0) = 2*G.edgeFinset.card := by
  classical
  rw [←G.sum_degrees_eq_twice_card_edges]
  apply sum_congr rfl
  intro i _
  simp [←G.card_neighborFinset_eq_degree,G.neighborFinset_eq_filter,Finset.sum_boole]

private lemma cut_set (G : SimpleGraph (Fin 25)) (f : Fin 25 → Bool)
    (small : (∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 50) :
    ∃ S : Finset (Fin 25),
      (G.edgeFinset.filter (fun e => ∀ x ∈ e,∀ y ∈ e,(x ∈ S ↔ y ∈ S))).card ≤ 25 := by
  classical
  let S := univ.filter (fun i => f i=true)
  let M : SimpleGraph (Fin 25) := {
    Adj := fun i j => G.Adj i j ∧ f i=f j
    symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
    loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩ }
  have count : (∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0)=2*M.edgeFinset.card := edge_sum M
  have eq : G.edgeFinset.filter (fun e => ∀ x ∈ e,∀ y ∈ e,(x ∈ S ↔ y ∈ S))=M.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | h i j =>
      rw [mem_filter,OMA.R_Erdos23_erdos_23_variants_n5_R1.same_mk,mem_edgeFinset,mem_edgeFinset]
      change (_ ∧ _) ↔ G.Adj i j ∧ f i=f j
      cases a : f i <;> cases b : f j <;> simp [S,a,b]
  exact ⟨S,eq ▸ (by omega : M.edgeFinset.card ≤ 25)⟩

/-- In a triangle-free graph any three distinct vertices have a nonadjacent pair.
Permuting the exceptions puts that pair at the ends of the possible path. -/
lemma cut_of_three_exceptions (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (v : Fin 5 → Fin 25) (cycle : ∀ i,G.Adj (v i) (v (i+1))) (dom : ∀ x,∃ i,G.Adj x (v i))
    (p q r : Fin 25) (pq : p≠q) (rp : r≠p) (rq : r≠q)
    (exceptions : ∀ x, (∃! k,G.Adj x (v k)) ↔ x=p ∨ x=q ∨ x=r) :
    ∃ f : Fin 25 → Bool, (∑ i,∑ j,if G.Adj i j ∧ f i=f j then (1:ℕ) else 0) ≤ 50 := by
  by_cases qr : G.Adj r q
  · by_cases pr : G.Adj r p
    · have miss : ¬G.Adj p q := fun adj => tri _ (is3Clique_triple_iff.mpr ⟨pr,qr,adj⟩)
      apply cut_of_ordered_triple G tri v cycle dom r q p rq rp.symm pq miss
      intro x
      rw [exceptions]; tauto
    · apply cut_of_ordered_triple G tri v cycle dom q p r pq.symm rq rp pr
      intro x
      rw [exceptions]; tauto
  · exact cut_of_ordered_triple G tri v cycle dom p q r pq rp rq qr exceptions

/-- A bipartite spanning subgraph of the requested size, independently of
the maximality, degree and density restrictions on the registered step. -/
lemma bipartize_three_exceptions (G : SimpleGraph (Fin 25)) (tri : G.CliqueFree 3)
    (v : Fin 5 → Fin 25) (cycle : ∀ i,G.Adj (v i) (v (i+1))) (dom : ∀ x,∃ i,G.Adj x (v i))
    (p q r : Fin 25) (pq : p≠q) (rp : r≠p) (rq : r≠q)
    (exceptions : ∀ x, (∃! k,G.Adj x (v k)) ↔ x=p ∨ x=q ∨ x=r) :
    ∃ H : SimpleGraph (Fin 25), H ≤ G ∧ H.IsBipartite ∧ (G.edgeFinset \ H.edgeFinset).card ≤ 25 := by
  obtain ⟨f,hf⟩ := cut_of_three_exceptions G tri v cycle dom p q r pq rp rq exceptions
  obtain ⟨S,small⟩ := cut_set G f hf
  obtain ⟨H,sub,bip,eq⟩ := OMA.R_Erdos23_erdos_23_variants_n5_R1.cut_graph
    (fun S e => ∀ x ∈ e,∀ y ∈ e,(x ∈ S ↔ y ∈ S))
    OMA.R_Erdos23_erdos_23_variants_n5_R1.same_mk G S
  refine ⟨H,sub,bip,?_⟩
  apply le_trans (le_of_eq eq)
  convert! small using 1
  congr 1
  ext e
  simp only [mem_filter,mem_edgeFinset]

/-- The residual maximal graphs with no dominating pentagon. -/
def H1 : Prop :=
  ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj], G.CliqueFree 3 →
    (∀ H : SimpleGraph (Fin 25), G ≤ H → H.CliqueFree 3 → H = G) →
    (∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z) →
    93 ≤ G.edgeFinset.card → G.edgeFinset.card ≤ 123 → (∀ v, G.degree v ≤ 12) →
    (∀ v, 25 < (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e,
      (x ∈ G.neighborFinset v ↔ y ∈ G.neighborFinset v))).card) →
    (∀ u v, G.Adj u v → (G.edgeFinset.filter
      (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card + 51
        < G.edgeFinset.card) →
    (¬∃ v : Fin 5 → Fin 25, (∀ i,G.Adj (v i) (v (i+1))) ∧ (∀ x,∃ i,G.Adj x (v i))) →
    ∃ S : Finset (Fin 25),
      (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 25

/-- A dominating pentagon exists, but every dominating pentagon has a number of
exceptional vertices different from three. -/
def H2 : Prop :=
  ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj], G.CliqueFree 3 →
    (∀ H : SimpleGraph (Fin 25), G ≤ H → H.CliqueFree 3 → H = G) →
    (∀ x y, x ≠ y → ¬ G.Adj x y → ∃ z, G.Adj x z ∧ G.Adj y z) →
    93 ≤ G.edgeFinset.card → G.edgeFinset.card ≤ 123 → (∀ v, G.degree v ≤ 12) →
    (∀ v, 25 < (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e,
      (x ∈ G.neighborFinset v ↔ y ∈ G.neighborFinset v))).card) →
    (∀ u v, G.Adj u v → (G.edgeFinset.filter
      (fun e => ∀ x ∈ e, x ∈ G.neighborFinset u ∪ G.neighborFinset v)).card + 51
        < G.edgeFinset.card) →
    (∃ v : Fin 5 → Fin 25, (∀ i,G.Adj (v i) (v (i+1))) ∧ (∀ x,∃ i,G.Adj x (v i))) →
    (∀ v : Fin 5 → Fin 25, (∀ i,G.Adj (v i) (v (i+1))) → (∀ x,∃ i,G.Adj x (v i)) →
      ∀ p q r, p≠q → r≠p → r≠q →
      ¬∀ x, (∃! k,G.Adj x (v k)) ↔ x=p ∨ x=q ∨ x=r) →
    ∃ S : Finset (Fin 25),
      (G.edgeFinset.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, (x ∈ S ↔ y ∈ S))).card ≤ 25

section
set_option maxHeartbeats 2000000 in
theorem main : H1 → H2 → OMA.R_Erdos23_erdos_23_variants_n5_R1_H2_R1.H1 := by
  classical
  intro none other G dec tri maximal diameter lo hi degree neighborhoods edges
  by_cases pentagon : ∃ v : Fin 5 → Fin 25, (∀ i,G.Adj (v i) (v (i+1))) ∧ (∀ x,∃ i,G.Adj x (v i))
  · by_cases configuration : ∃ (v : Fin 5 → Fin 25) (p q r : Fin 25),
        (∀ i,G.Adj (v i) (v (i+1))) ∧ (∀ x,∃ i,G.Adj x (v i)) ∧ p≠q ∧ r≠p ∧ r≠q ∧
        (∀ x, (∃! k,G.Adj x (v k)) ↔ x=p ∨ x=q ∨ x=r)
    · obtain ⟨v,p,q,r,cycle,dom,pq,rp,rq,ex⟩ := configuration
      obtain ⟨f,hf⟩ := cut_of_three_exceptions G tri v cycle dom p q r pq rp rq ex
      obtain ⟨S,small⟩ := cut_set G f hf
      refine ⟨S,?_⟩
      convert! small using 1 <;> congr 1 <;> ext e <;> simp only [mem_filter,mem_edgeFinset]
    · apply other G tri maximal diameter lo hi degree neighborhoods edges pentagon
      intro v cycle dom p q r pq rp rq ex
      exact configuration ⟨v,p,q,r,cycle,dom,pq,rp,rq,ex⟩
  · exact none G tri maximal diameter lo hi degree neighborhoods edges pentagon
end

end OMA.R_Erdos23_erdos_23_variants_n5_R1_H2_R1_H1_R3
