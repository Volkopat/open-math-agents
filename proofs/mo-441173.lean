import OMAStatements.S_mo_441173
import Mathlib
/-!
Shortening of @caa1982's proof #28292, retaining the halting-dependent pair swap.
Standard many-one reducibility and computable-predicate conversion APIs replace
manual Boolean representations. Source: Numa Grinberg, MathOverflow 441173.
-/

open OMA.S_mo_441173

open Nat.Partrec

/-- `K n`: the program with code `n` halts on input `0`. -/
def KH (n : ℕ) : Prop := ((Denumerable.ofNat Code n).eval 0).Dom

lemma KH_not : ¬ ComputablePred KH := by
  intro hK
  apply ComputablePred.halting_problem 0
  exact ComputablePred.computable_of_manyOneReducible
    ⟨Encodable.encode, Computable.encode, fun c => by simp [KH]⟩ hK

/-- Swap `2m` and `2m+1` exactly when `KH m` holds; an involution. -/
noncomputable def sw (n : ℕ) : ℕ := by
  classical
  exact if KH (n / 2) then (if n % 2 = 0 then n + 1 else n - 1) else n

lemma sw_even_pos (m : ℕ) (h : KH m) : sw (2 * m) = 2 * m + 1 := by
  unfold sw
  have h1 : 2 * m / 2 = m := by omega
  have h2 : 2 * m % 2 = 0 := by omega
  simp only [h1, h2, h, if_true]

lemma sw_even_neg (m : ℕ) (h : ¬ KH m) : sw (2 * m) = 2 * m := by
  unfold sw
  have h1 : 2 * m / 2 = m := by omega
  simp only [h1, h, if_false]

lemma sw_odd_pos (m : ℕ) (h : KH m) : sw (2 * m + 1) = 2 * m := by
  unfold sw
  have h1 : (2 * m + 1) / 2 = m := by omega
  have h2 : (2 * m + 1) % 2 = 1 := by omega
  simp only [h1, h2, h, if_true, one_ne_zero, if_false]
  omega

lemma sw_odd_neg (m : ℕ) (h : ¬ KH m) : sw (2 * m + 1) = 2 * m + 1 := by
  unfold sw
  have h1 : (2 * m + 1) / 2 = m := by omega
  simp only [h1, h, if_false]

lemma sw_sw (n : ℕ) : sw (sw n) = n := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m ∨ n = 2 * m + 1 := ⟨n / 2, by omega⟩
  · by_cases h : KH m
    · rw [sw_even_pos m h, sw_odd_pos m h]
    · rw [sw_even_neg m h, sw_even_neg m h]
  · by_cases h : KH m
    · rw [sw_odd_pos m h, sw_even_pos m h]
    · rw [sw_odd_neg m h, sw_odd_neg m h]

theorem OMA.solution : type_of% @OMA.S_mo_441173.main := by
  refine ⟨sw, ?_, ?_⟩
  · have : (fun x => sw (sw x)) = id := funext sw_sw
    rw [this]
    exact Computable.id
  · intro hc
    have : (fun x => sw (sw (sw x))) = sw := funext fun x => by rw [sw_sw]
    rw [this] at hc
    apply KH_not
    have h2 : Computable fun m : ℕ => 2 * m :=
      Primrec.nat_mul.to_comp.comp (Computable.const 2) Computable.id
    have h3 : Computable fun m : ℕ => 2 * m + 1 := Computable.succ.comp h2
    have hd : Computable fun m : ℕ => decide (sw (2 * m) = 2 * m + 1) :=
      Primrec.eq.decide.to_comp.comp (hc.comp h2) h3
    have hp : ComputablePred fun m : ℕ => sw (2 * m) = 2 * m + 1 :=
      hd.computablePred
    refine ComputablePred.of_eq hp (fun m => ?_)
    by_cases h : KH m
    · simp [h, sw_even_pos m h]
    · simp [h, sw_even_neg m h]
