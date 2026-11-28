import OMAStatements.S_oeis_a308190
import Mathlib.Data.Nat.Prime.Basic

/-!
For a composite input above five, the smallest prime divisor and its
cofactor have sum at least five and strictly less than the input.
A prime above five instead moves to the next even integer and then
below the original prime. Strong induction applies to these two cases.
-/

namespace OMA.S_oeis_a308190

private theorem composite_drop (n : ℕ) (hn : 5 < n) (hp : ¬n.Prime) :
    5 ≤ f n ∧ f n < n := by
  let p := n.minFac
  let q := n / p
  have h2 : 2 ≤ p := (Nat.minFac_prime (by omega : n ≠ 1)).two_le
  have hpq : p ≤ q := Nat.minFac_le_div (by omega) hp
  have hprod : q*p=n := Nat.div_mul_cancel (Nat.minFac_dvd n)
  have h3 : 3 ≤ q := by
    by_contra h
    have hq : q = 2 := by omega
    have hp' : p = 2 := by omega
    rw [hq, hp'] at hprod
    omega
  have hsum : q+p<n := by
    by_cases h : p=2
    · rw [h] at hprod ⊢
      omega
    · have hlt : 2 < p := by omega
      calc
        q+p ≤ q+q := Nat.add_le_add_left hpq q
        _ = q*2 := by omega
        _ < q*p := Nat.mul_lt_mul_of_pos_left hlt (by omega)
        _ = n := hprod
  unfold f
  rw [if_neg (by omega)]
  change 5 ≤ q+p ∧ q+p<n
  exact ⟨by omega, hsum⟩

private theorem prime_drop (n : ℕ) (hn : 5 < n) (hp : n.Prime) :
    5 ≤ f (f n) ∧ f (f n) < n := by
  have he : f n = n+1 := by
    unfold f
    rw [if_neg (by omega), hp.minFac_eq, Nat.div_self (by omega)]
    omega
  have hodd : n%2=1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hf : (n+1).minFac=2 := (Nat.minFac_eq_two_iff _).2 (by omega)
  rw [he]
  unfold f
  rw [if_neg (by omega), hf]
  omega

end OMA.S_oeis_a308190

open OMA.S_oeis_a308190 in
theorem OMA.solution : type_of% @OMA.S_oeis_a308190.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases he : n=5
    · exact ⟨0, he⟩
    · by_cases hp : n.Prime
      · obtain ⟨hlo, hhi⟩ := prime_drop n (by omega) hp
        obtain ⟨k, hk⟩ := ih _ hhi hlo
        refine ⟨k+2, ?_⟩
        rw [Function.iterate_add_apply]
        exact hk
      · obtain ⟨hlo, hhi⟩ := composite_drop n (by omega) hp
        obtain ⟨k, hk⟩ := ih _ hhi hlo
        exact ⟨k+1, (Function.iterate_succ_apply f k n).trans hk⟩
