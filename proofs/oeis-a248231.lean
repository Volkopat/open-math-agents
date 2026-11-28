import OMAStatements.S_oeis_a248231
import Mathlib.Tactic

open OMA.S_oeis_a248231

namespace ZetaTailProof

noncomputable def bound (c i : ℕ) : ℝ := 1/(2*(i : ℝ)*(i+1)+c)^2

lemma upper_step (i : ℕ) (hi : 0 < i) : term i < bound 1 i - bound 1 (i+1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  apply sub_pos.mp
  unfold term bound
  push_cast
  field_simp
  ring_nf
  positivity

lemma lower_step (i : ℕ) : bound 2 i - bound 2 (i+1) ≤ term i := by
  apply sub_nonneg.mp
  unfold term bound
  push_cast
  field_simp
  ring_nf
  positivity

lemma bound_summable (c k : ℕ) (hc : 1 ≤ c) :
    Summable (fun j : ℕ => bound c (k+j)) := by
  have p := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1<2))
  apply Summable.of_nonneg_of_le (f := fun j : ℕ => 1/((j : ℝ)+1)^2)
  · intro j
    unfold bound
    positivity
  · intro j
    unfold bound
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
    have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
    have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
    gcongr
    nlinarith [sq_nonneg ((k : ℝ)+j)]
  · simpa using p

lemma telescope (c k : ℕ) (hc : 1 ≤ c) :
    HasSum (fun j : ℕ => bound c (k+j) - bound c (k+j+1)) (bound c k) := by
  let f (j : ℕ) := bound c (k+j)
  have hf : Summable f := bound_summable c k hc
  have hg := (summable_nat_add_iff 1).mpr hf
  have total := hf.hasSum.sub hg.hasSum
  have he := hf.tsum_eq_zero_add
  have val : (∑' j, f j) - (∑' j, f (j+1)) = f 0 := by linarith
  rw [val] at total
  simpa [f, Nat.add_assoc] using total

lemma tail_bounds (k : ℕ) (hk : 0<k) : bound 2 k ≤ tail k ∧ tail k < bound 1 k := by
  have u := telescope 1 k (by decide)
  have l := telescope 2 k (by decide)
  have ts := (summable_nat_add_iff (k+1)).mpr
    (Real.summable_one_div_nat_pow.mpr (by decide : 1<5))
  have ht : Summable (fun j : ℕ => term (k+j)) := by
    simpa [term, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, add_comm, add_left_comm,
      add_assoc] using ts
  constructor
  · rw [← l.tsum_eq, tail]
    exact l.summable.tsum_le_tsum (fun j => lower_step (k+j)) ht
  · rw [← u.tsum_eq, tail]
    exact Summable.tsum_lt_tsum (fun j => (upper_step (k+j) (by omega)).le)
      (i := 0) (upper_step (k+0) (by omega)) ht u.summable

lemma cutoff (n k : ℕ) (hn : 1<n) : proposal n ≤ k ↔ n^2 ≤ 2*k*(k+1)+1 := by
  have hsub : 4 ≤ 2*n^2 := by
    have := Nat.pow_le_pow_left (show 2 ≤ n by omega) 2
    omega
  have h : proposal n ≤ k ↔ Nat.sqrt (2*n^2-4) < 2*k+1 := by unfold proposal; omega
  rw [h, Nat.sqrt_lt, show (2*k+1)*(2*k+1) = 2*(2*k*(k+1))+1 by ring]
  have gap : n^2 ≠ 2*k*(k+1)+2 := by
    have parity (v : ℕ) : ∃ u, v=2*u ∨ v=2*u+1 := ⟨v/2, by omega⟩
    intro he
    obtain ⟨u, rfl | rfl⟩ := parity n <;> obtain ⟨v, rfl | rfl⟩ := parity k <;>
      ring_nf at he <;> omega
  omega

lemma good (n k : ℕ) (hn : 1<n) (hk : 0<k) :
    tail k < 1/(n : ℝ)^4 ↔ n^2 ≤ 2*k*(k+1)+1 := by
  obtain ⟨hl, hu⟩ := tail_bounds k hk
  rw [show (n : ℝ)^4 = ((n : ℝ)^2)^2 by ring]
  constructor
  · intro h
    by_contra! hh
    have ha : 2*(k : ℝ)*(k+1)+2 ≤ (n : ℝ)^2 := by
      exact_mod_cast (show 2*k*(k+1)+2 ≤ n^2 by omega)
    have hi : 1/((n : ℝ)^2)^2 ≤ bound 2 k := by
      unfold bound
      apply one_div_le_one_div_of_le (by positivity)
      norm_num
      gcongr
    linarith
  · intro h
    have ha : (n : ℝ)^2 ≤ 2*(k : ℝ)*(k+1)+1 := by exact_mod_cast h
    apply lt_of_lt_of_le hu
    unfold bound
    apply one_div_le_one_div_of_le (by positivity)
    norm_num
    gcongr

end ZetaTailProof

open ZetaTailProof

theorem OMA.solution : type_of% @OMA.S_oeis_a248231.main := by
  intro n hn
  have hp : 0 < proposal n := by
    by_contra! hz
    have h := (cutoff n 0 hn).mp hz
    have h2 := Nat.pow_le_pow_left (show 2 ≤ n by omega) 2
    omega
  exact ⟨⟨hp, (good n _ hn hp).mpr ((cutoff n _ hn).mp le_rfl)⟩,
    fun k hk => (cutoff n k hn).mpr ((good n k hn hk.1).mp hk.2)⟩
