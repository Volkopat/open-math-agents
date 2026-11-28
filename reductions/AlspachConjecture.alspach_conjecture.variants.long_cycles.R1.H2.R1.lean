import OMAReductions.R_AlspachConjecture_alspach_conjecture_variants_long_cycles_R1
import Mathlib

/-! The mixed-length case first occurs at order nine, where its length
multiset is forced. At higher orders, separate lists according to whether
the number of cycles exceeds the Hamiltonian count by one or by more. -/
open AlspachConjecture SimpleGraph
namespace LongCycleSmallOrders

theorem m9_exists :
    ∃ C : Multiset (Cycle (completeGraph (Fin 9))),
      IsCycleDecomposition (completeGraph (Fin 9)) C ∧ lengths C = 8 ::ₘ Multiset.replicate 4 7 := by
  let c0 : Cycle (completeGraph (Fin 9)) := {
    base := 0
    walk :=
      Walk.cons (by decide : (completeGraph (Fin 9)).Adj 0 1)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 1 2)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 2 3)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 3 4)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 4 5)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 5 6)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 6 7)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 7 0) (Walk.nil))))))))
    isCycle := by
      rw [Walk.isCycle_def, Walk.isTrail_def]
      exact ⟨by decide, by simp, by decide⟩
  }
  let c1 : Cycle (completeGraph (Fin 9)) := {
    base := 0
    walk :=
      Walk.cons (by decide : (completeGraph (Fin 9)).Adj 0 2)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 2 4)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 4 1)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 1 3)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 3 5)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 5 8)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 8 0) (Walk.nil)))))))
    isCycle := by
      rw [Walk.isCycle_def, Walk.isTrail_def]
      exact ⟨by decide, by simp, by decide⟩
  }
  let c2 : Cycle (completeGraph (Fin 9)) := {
    base := 0
    walk :=
      Walk.cons (by decide : (completeGraph (Fin 9)).Adj 0 3)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 3 6)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 6 8)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 8 1)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 1 7)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 7 4)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 4 0) (Walk.nil)))))))
    isCycle := by
      rw [Walk.isCycle_def, Walk.isTrail_def]
      exact ⟨by decide, by simp, by decide⟩
  }
  let c3 : Cycle (completeGraph (Fin 9)) := {
    base := 0
    walk :=
      Walk.cons (by decide : (completeGraph (Fin 9)).Adj 0 5)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 5 2)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 2 7)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 7 8)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 8 4)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 4 6)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 6 0) (Walk.nil)))))))
    isCycle := by
      rw [Walk.isCycle_def, Walk.isTrail_def]
      exact ⟨by decide, by simp, by decide⟩
  }
  let c4 : Cycle (completeGraph (Fin 9)) := {
    base := 1
    walk :=
      Walk.cons (by decide : (completeGraph (Fin 9)).Adj 1 5)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 5 7)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 7 3)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 3 8)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 8 2)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 2 6)
        (Walk.cons (by decide : (completeGraph (Fin 9)).Adj 6 1) (Walk.nil)))))))
    isCycle := by
      rw [Walk.isCycle_def, Walk.isTrail_def]
      exact ⟨by decide, by simp, by decide⟩
  }
  let family : Multiset (Cycle (completeGraph (Fin 9))) := {c0, c1, c2, c3, c4}
  refine ⟨family, ?_, ?_⟩
  · intro e he
    induction e using Sym2.ind with
    | h a b =>
      fin_cases a <;> fin_cases b <;>
        first | (simp [completeGraph_eq_top] at he <;> contradiction)
              | (dsimp only [family, c0, c1, c2, c3, c4]; decide)
  · dsimp only [family, c0, c1, c2, c3, c4]
    decide

theorem lower_bound (m : Multiset ℕ) (c : ℕ) (bounds : ∀ x ∈ m, c ≤ x) :
    c * m.card ≤ m.sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    have ha := bounds a (Multiset.mem_cons_self _ _)
    have hm := ih (fun x hx ↦ bounds x (Multiset.mem_cons_of_mem hx))
    simp only [Multiset.card_cons,Multiset.sum_cons,Nat.mul_succ]
    omega

theorem upper_bound (m : Multiset ℕ) (c : ℕ) (bounds : ∀ x ∈ m, x ≤ c) :
    m.sum ≤ c * m.card := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    have ha := bounds a (Multiset.mem_cons_self _ _)
    have hm := ih (fun x hx ↦ bounds x (Multiset.mem_cons_of_mem hx))
    simp only [Multiset.card_cons,Multiset.sum_cons,Nat.mul_succ]
    omega

theorem erase_total {m : Multiset ℕ} {x : ℕ} (hx : x ∈ m) :
    x + (m.erase x).sum = m.sum ∧ (m.erase x).card + 1 = m.card := by
  constructor
  · simpa only [Multiset.sum_cons] using congrArg Multiset.sum (Multiset.cons_erase hx)
  · simpa only [Multiset.card_cons] using congrArg Multiset.card (Multiset.cons_erase hx)

theorem replicate_of_upper {m : Multiset ℕ} {c : ℕ} (bounds : ∀ x ∈ m, x ≤ c)
    (eq : m.sum = c * m.card) : m = Multiset.replicate m.card c := by
  apply Multiset.eq_replicate_card.mpr
  intro x hx
  obtain ⟨sumErase,cardErase⟩ := erase_total hx
  have rest := upper_bound (m.erase x) c (fun y hy ↦ bounds y (Multiset.mem_of_mem_erase hy))
  rw [← cardErase,Nat.mul_succ] at eq
  have := bounds x hx
  omega

theorem replicate_of_lower {m : Multiset ℕ} {c : ℕ} (bounds : ∀ x ∈ m, c ≤ x)
    (eq : m.sum = c * m.card) : m = Multiset.replicate m.card c := by
  apply Multiset.eq_replicate_card.mpr
  intro x hx
  obtain ⟨sumErase,cardErase⟩ := erase_total hx
  have rest := lower_bound (m.erase x) c (fun y hy ↦ bounds y (Multiset.mem_of_mem_erase hy))
  rw [← cardErase,Nat.mul_succ] at eq
  have := bounds x hx
  omega

theorem list_nine (m : Multiset ℕ) (bounds : ∀ x ∈ m, 7 ≤ x ∧ x ≤ 9) (sum : m.sum = 36) :
    m = Multiset.replicate 4 9 ∨ m = 8 ::ₘ Multiset.replicate 4 7 := by
  have lo := lower_bound m 7 (fun x hx ↦ (bounds x hx).1)
  have hi := upper_bound m 9 (fun x hx ↦ (bounds x hx).2)
  have cases : m.card = 4 ∨ m.card = 5 := by omega
  rcases cases with four | five
  · left
    have all := replicate_of_upper (fun x hx ↦ (bounds x hx).2) (by omega)
    rwa [four] at all
  · right
    have has : ∃ x ∈ m, 7 < x := by
      by_contra! none
      have := upper_bound m 7 none
      omega
    obtain ⟨x,hx,hgt⟩ := has
    obtain ⟨s,c⟩ := erase_total hx
    have rest (y : ℕ) (hy : y ∈ m.erase x) : 7 ≤ y :=
      (bounds y (Multiset.mem_of_mem_erase hy)).1
    have restLower := lower_bound (m.erase x) 7 rest
    have eight : x = 8 := by omega
    have eq := replicate_of_lower rest (by omega)
    calc
      m = x ::ₘ m.erase x := (Multiset.cons_erase hx).symm
      _ = 8 ::ₘ Multiset.replicate 4 7 := by rw [eq,show (m.erase x).card = 4 by omega,eight]

theorem choose_odd (n : ℕ) (hn : Odd n) : n.choose 2 = n * (n/2) := by
  obtain ⟨k,hk⟩ := hn
  have part : n-1 = 2*k := by omega
  have half : n/2 = k := by omega
  rw [Nat.choose_two_right,part,half,show n*(2*k) = (n*k)*2 by ring]
  omega

end LongCycleSmallOrders

namespace OMA.R_AlspachConjecture_alspach_conjecture_variants_long_cycles_R1_H2_R1
open LongCycleSmallOrders

/-- Long-cycle lists whose cardinality exceeds the Hamiltonian count by one. -/
def H1 : Prop := ∀ n : ℕ, Odd n → 11 ≤ n → ∀ m : Multiset ℕ, m.card = n/2+1 →
  (∀ x ∈ m, (n+5)/2 ≤ x ∧ x ≤ n) → m.sum = n.choose 2 →
  ∃ C : Multiset (Cycle (completeGraph (Fin n))),
    IsCycleDecomposition (completeGraph (Fin n)) C ∧ lengths C = m

/-- Long-cycle lists with at least two more cycles than the Hamiltonian count. -/
def H2 : Prop := ∀ n : ℕ, Odd n → 13 ≤ n → ∀ m : Multiset ℕ, n/2+2 ≤ m.card →
  (∀ x ∈ m, (n+5)/2 ≤ x ∧ x ≤ n) → m.sum = n.choose 2 →
  ∃ C : Multiset (Cycle (completeGraph (Fin n))),
    IsCycleDecomposition (completeGraph (Fin n)) C ∧ lengths C = m

theorem main : H1 → H2 → OMA.R_AlspachConjecture_alspach_conjecture_variants_long_cycles_R1.H2 := by
  intro one other n hn ge5 m bounds mixed sum
  have below := lower_bound m ((n+5)/2) (fun x hx ↦ (bounds x hx).1)
  have above := upper_bound m n (fun x hx ↦ (bounds x hx).2)
  rw [sum,choose_odd n hn] at above
  have minCard : n/2 ≤ m.card := Nat.le_of_mul_le_mul_left above (by omega)
  have extra : n/2 < m.card := by
    by_contra! hnextra
    have eq : m.card = n/2 := le_antisymm hnextra minCard
    have rep := replicate_of_upper (fun x hx ↦ (bounds x hx).2)
      (by rw [sum,choose_odd n hn,eq])
    obtain ⟨x,hx,hlt⟩ := mixed
    rw [rep] at hx
    have : x = n := (Multiset.mem_replicate.mp hx).2
    omega
  by_cases le9 : n ≤ 9
  · have cases : n=5 ∨ n=7 ∨ n=9 := by
      obtain ⟨k,hk⟩ := hn
      omega
    rcases cases with rfl | rfl | rfl
    · change 5*m.card ≤ m.sum at below
      change 2 < m.card at extra
      rw [show (5 : ℕ).choose 2 = 10 by decide] at sum
      omega
    · change 6*m.card ≤ m.sum at below
      change 3 < m.card at extra
      rw [show (7 : ℕ).choose 2 = 21 by decide] at sum
      omega
    · rcases list_nine m bounds sum with same | exceptional
      · have z : m.card = 4 := by rw [same,Multiset.card_replicate]
        omega
      · obtain ⟨C,hC,lengthC⟩ := m9_exists
        exact ⟨C,hC,lengthC.trans exceptional.symm⟩
  have ge11 : 11 ≤ n := by
    obtain ⟨k,hk⟩ := hn
    omega
  by_cases oneExtra : m.card = n/2+1
  · exact one n hn ge11 m oneExtra bounds sum
  have twoExtra : n/2+2 ≤ m.card := by omega
  have ge13 : 13 ≤ n := by
    by_contra! le12
    have eq11 : n=11 := by
      obtain ⟨k,hk⟩ := hn
      omega
    subst n
    change 8*m.card ≤ m.sum at below
    change 7 ≤ m.card at twoExtra
    rw [show (11 : ℕ).choose 2 = 55 by decide] at sum
    omega
  exact other n hn ge13 m twoExtra bounds sum

end OMA.R_AlspachConjecture_alspach_conjecture_variants_long_cycles_R1_H2_R1
