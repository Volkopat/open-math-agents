import FormalConjectures.ErdosProblems.«848»
/-! The three regimes and endpoint convention follow MacchaCat/erdos848,
commit 99b8d9bf40fdd090a2a117328c5707ca21ec748e (Apache-2.0).
The finite colouring, finite analytic interval estimates, and asymptotic analytic
estimate respectively establish the three independent size bounds below. -/
namespace OMA.R_Erdos848_erdos_848_R3
open Erdos848

def H1 : Prop := ∀ N : ℕ, N ≤ 986746 → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
  (∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a*b+1)) → A.card ≤ (N+18)/25

def H2 : Prop := ∀ N : ℕ, 986747 ≤ N → N ≤ 160000000 → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
  (∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a*b+1)) → A.card ≤ (N+18)/25

def H3 : Prop := ∀ N : ℕ, 160000000 ≤ N → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
  (∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a*b+1)) → A.card ≤ (N+18)/25

lemma countSeven (N : ℕ) : (A₇ N).card = (N+17)/25 := by
  induction N with
  | zero => rfl
  | succ n ih =>
    unfold A₇ at ih ⊢
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), ih]; omega
    · rw [ih]; omega

theorem main : H1 → H2 → H3 → type_of% @Erdos848.erdos_848 := by
  intro small middle large N A sub adm
  have incl : A ⊆ Finset.Icc 1 (N-1) := by
    intro x hx
    have lt := Finset.mem_range.mp (sub hx)
    have nz : x ≠ 0 := by
      rintro rfl
      exact adm 0 hx 0 hx (by simp)
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [countSeven]
  have h : A.card ≤ ((N-1)+18)/25 := by
    by_cases lo : N-1 ≤ 986746
    · exact small _ lo A incl adm
    by_cases mid : N-1 ≤ 160000000
    · exact middle _ (by omega) mid A incl adm
    · exact large _ (by omega) A incl adm
  omega
end OMA.R_Erdos848_erdos_848_R3
