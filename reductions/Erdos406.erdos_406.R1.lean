import FormalConjectures.ErdosProblems.«406»
import Mathlib

/- Two classes of exponents can be classified completely: sparse ternary
exponents m, and repunits with 2*m+1 a power of three. -/
namespace OMA.R_Erdos406_erdos_406_R1

def H1 : Prop := ∀ m : ℕ, (((Nat.digits 3 m).filter (fun d => d != 0)).length ≤ 6 ∨ ∃ j : ℕ, 2*m+1 = 3^j) →
  Nat.digits 3 (4^m) ⊆ [0,1] → m=0 ∨ m=1 ∨ m=4

def H2 : Prop := {m : ℕ | (6 < ((Nat.digits 3 m).filter (fun d => d != 0)).length ∧ ∀ j : ℕ, 2*m+1 ≠ 3^j) ∧
  Nat.digits 3 (4^m) ⊆ [0,1]}.Finite

lemma fourth_power_of_digits (k : ℕ) (hg : Nat.digits 3 (2^k) ⊆ [0,1]) :
    ∃ m : ℕ, 2^k=4^m := by
  by_cases he : k%2 = 0
  · refine ⟨k/2, ?_⟩
    have eq : k = 2*(k/2) := by omega
    calc
      2^k = 2^(2*(k/2)) := congrArg (fun n : ℕ => 2^n) eq
      _ = 4^(k/2) := by rw [pow_mul]; rfl
  have eq : k = 2*(k/2)+1 := by omega
  have form : 2^k = 4^(k/2)*2 := by
    calc
      2^k = 2^(2*(k/2)+1) := congrArg (fun n : ℕ => 2^n) eq
      _ = 4^(k/2)*2 := by rw [pow_succ, pow_mul]; rfl
  have hfour : 4 ≡ 1 [MOD 3] := by decide
  have modtwo : 2^k % 3 = 2 := by
    rw [form]
    have h := (hfour.pow (k/2)).mul (Nat.ModEq.refl 2)
    have normalized : 4^(k/2)*2 ≡ 2 [MOD 3] := by simpa only [one_pow, one_mul] using h
    exact normalized
  have mem : 2^k % 3 ∈ Nat.digits 3 (2^k) := by
    rw [Nat.digits_def' (by decide : 1 < 3) (by positivity)]
    exact List.mem_cons_self
  rw [modtwo] at mem
  have bad := hg mem
  simp at bad

theorem main : H1 → H2 → type_of% @Erdos406.erdos_406 := by
  intro sparse dense
  let D := {m : ℕ | (6 < ((Nat.digits 3 m).filter (fun d => d != 0)).length ∧ ∀ j : ℕ, 2*m+1 ≠ 3^j) ∧
    Nat.digits 3 (4^m) ⊆ [0,1]}
  have fd : D.Finite := dense
  have img := fd.image (fun m : ℕ => 4^m)
  apply (((img.insert 256).insert 4).insert 1).subset
  rintro y ⟨⟨k, hk⟩, hg⟩
  obtain ⟨m, hpow⟩ := fourth_power_of_digits k (hk ▸ hg)
  have hy : y = 4^m := hk.trans hpow
  rw [hy] at hg ⊢
  by_cases h : ((Nat.digits 3 m).filter (fun d => d != 0)).length ≤ 6 ∨ ∃ j : ℕ, 2*m+1 = 3^j
  · rcases sparse m h hg with rfl | rfl | rfl <;> norm_num
  · apply Set.mem_insert_of_mem
    apply Set.mem_insert_of_mem
    apply Set.mem_insert_of_mem
    simp only [not_or, not_le, not_exists] at h
    exact ⟨m, ⟨h, hg⟩, rfl⟩

end OMA.R_Erdos406_erdos_406_R1
