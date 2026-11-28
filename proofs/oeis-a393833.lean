import OMAStatements.S_oeis_a393833
import Mathlib

open OMA.S_oeis_a393833

theorem OMA.solution : type_of% @OMA.S_oeis_a393833.main := by
  intro n hn
  let _ : NeZero n := ⟨by omega⟩
  obtain ⟨p, _, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := n) (a := 1) isUnit_one 0
  have hc : p ≡ 1 [MOD n] :=
    (ZMod.natCast_eq_natCast_iff p 1 n).mp (by simpa using hmod)
  let e := 2*n+1
  refine ⟨p^e, pow_pos hp.pos _, ?_, ?_⟩
  · simp [Nat.divisors_prime_pow hp, e]
  · unfold residues
    let l := (p^e).properDivisors.sort
    change l.map (fun d => d % n) = (l.map (fun d => d % n)).reverse
    have hr : l.map (fun d => d % n) = l.map (fun _ => 1 % n) := by
      apply List.map_congr_left
      intro d hd
      have hm : d ∈ (p^e).properDivisors := (Finset.mem_sort _).mp hd
      obtain ⟨j, _, rfl⟩ := (Nat.mem_properDivisors_prime_pow hp e).mp hm
      simpa [Nat.ModEq] using hc.pow j
    have hrep (s : List ℕ) :
        s.map (fun _ => (1 : ℕ) % n) = List.replicate s.length (1 % n) := by
      induction s with
      | nil => rfl
      | cons d s ih => simp [ih, List.replicate_succ]
    rw [hr, hrep, List.reverse_replicate]