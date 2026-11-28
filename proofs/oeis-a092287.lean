import OMAStatements.S_oeis_a092287

namespace OMA.S_oeis_a092287

open Finset


/-- The entry's ten listed terms a(0..9) = f(n, n). -/
theorem listed_terms : (List.range 10).map (fun n => f n n) =
    [1, 1, 2, 6, 96, 480, 414720, 2903040, 5945425920, 4334215495680] := by
  decide +kernel

variable {p : ℕ} [hp : Fact p.Prime]

lemma pv_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℕ) (hg : ∀ i ∈ s, g i ≠ 0) :
    padicValNat p (∏ i ∈ s, g i) = ∑ i ∈ s, padicValNat p (g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 : g a ≠ 0 := hg a (mem_insert_self a s)
    have h2 : ∀ i ∈ s, g i ≠ 0 := fun i hi => hg i (mem_insert_of_mem hi)
    rw [prod_insert ha, sum_insert ha, padicValNat.mul h1 (prod_ne_zero_iff.mpr h2), ih h2]

lemma pv_le (x : ℕ) (hx : x ≠ 0) : padicValNat p x ≤ x := by
  have h1 : p ^ padicValNat p x ≤ x := Nat.le_of_dvd (Nat.pos_of_ne_zero hx) pow_padicValNat_dvd
  have h2 : padicValNat p x < p ^ padicValNat p x := Nat.lt_pow_self hp.out.one_lt
  omega

/-- v_p(x) is the number of i in [1, N] with p^i | x, once N >= v_p(x). -/
lemma pv_eq_card (x N : ℕ) (hx : x ≠ 0) (hN : padicValNat p x ≤ N) :
    padicValNat p x = ((Icc 1 N).filter (fun i => p ^ i ∣ x)).card := by
  have h : (Icc 1 N).filter (fun i => p ^ i ∣ x) = Icc 1 (padicValNat p x) := by
    ext i
    simp only [mem_filter, mem_Icc]
    rw [padicValNat_dvd_iff_le hx]
    omega
  rw [h, Nat.card_Icc]
  omega

/-- The number of multiples of d in [1, n] is n / d. -/
lemma card_multiples (n d : ℕ) : ((Icc 1 n).filter (fun j => d ∣ j)).card = n / d := by
  have h : Icc 1 n = Ioc 0 n := by
    ext x; simp only [mem_Icc, mem_Ioc]; omega
  rw [h]
  exact Nat.Ioc_filter_dvd_card_eq_div n d

/-- The conjecture of the entry. -/
theorem conjecture (n m : ℕ) :
    padicValNat p (f n m) = ∑ i ∈ Icc 1 n, (n / p ^ i) * (m / p ^ i) := by
  have hg : ∀ j ∈ Icc 1 n, ∀ k ∈ Icc 1 m, Nat.gcd j k ≠ 0 := by
    intro j hj k _
    exact Nat.pos_iff_ne_zero.mp (Nat.gcd_pos_of_pos_left k (by simp at hj; omega))
  rw [f, pv_prod _ _ (fun j hj => prod_ne_zero_iff.mpr (hg j hj))]
  rw [sum_congr rfl (fun j hj => pv_prod _ _ (hg j hj))]
  -- each valuation counts the i <= n with p^i dividing both j and k
  have hcount : ∀ j ∈ Icc 1 n, ∀ k ∈ Icc 1 m, padicValNat p (Nat.gcd j k) =
      ∑ i ∈ Icc 1 n, (if p ^ i ∣ j then 1 else 0) * (if p ^ i ∣ k then 1 else 0) := by
    intro j hj k hk
    have hj' : j ≤ n := (mem_Icc.mp hj).2
    have hle : padicValNat p (Nat.gcd j k) ≤ n :=
      le_trans (pv_le _ (hg j hj k hk))
        (le_trans (Nat.le_of_dvd (by simp at hj; omega) (Nat.gcd_dvd_left j k)) hj')
    rw [pv_eq_card _ n (hg j hj k hk) hle, card_filter]
    refine sum_congr rfl (fun i _ => ?_)
    by_cases h1 : p ^ i ∣ j <;> by_cases h2 : p ^ i ∣ k <;> simp [h1, h2, Nat.dvd_gcd_iff]
  rw [sum_congr rfl (fun j hj => sum_congr rfl (fun k hk => hcount j hj k hk))]
  have hmult : ∀ (N d : ℕ), ∑ x ∈ Icc 1 N, (if d ∣ x then 1 else 0) = N / d := by
    intro N d
    rw [← card_filter, card_multiples]
  calc ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 m, ∑ i ∈ Icc 1 n,
        (if p ^ i ∣ j then 1 else 0) * (if p ^ i ∣ k then 1 else 0)
      = ∑ j ∈ Icc 1 n, ∑ i ∈ Icc 1 n, ∑ k ∈ Icc 1 m,
        (if p ^ i ∣ j then 1 else 0) * (if p ^ i ∣ k then 1 else 0) :=
        sum_congr rfl (fun j _ => sum_comm)
    _ = ∑ i ∈ Icc 1 n, ∑ j ∈ Icc 1 n, ∑ k ∈ Icc 1 m,
        (if p ^ i ∣ j then 1 else 0) * (if p ^ i ∣ k then 1 else 0) := sum_comm
    _ = ∑ i ∈ Icc 1 n, (∑ j ∈ Icc 1 n, (if p ^ i ∣ j then 1 else 0)) *
        (∑ k ∈ Icc 1 m, (if p ^ i ∣ k then 1 else 0)) :=
        sum_congr rfl (fun i _ => (sum_mul_sum _ _ _ _).symm)
    _ = ∑ i ∈ Icc 1 n, (n / p ^ i) * (m / p ^ i) := by
        refine sum_congr rfl (fun i _ => ?_)
        rw [hmult, hmult]

end OMA.S_oeis_a092287

theorem OMA.solution : type_of% @OMA.S_oeis_a092287.main := by
  refine ⟨fun p hp n => ?_, fun p hp n m => ?_⟩
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [OMA.S_oeis_a092287.conjecture (p := p) n n]
    simp only [sq]
  · haveI : Fact p.Prime := ⟨hp⟩
    exact OMA.S_oeis_a092287.conjecture (p := p) n m
