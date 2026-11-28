import OMAStatements.S_oeis_a330733

-- Problem: A330733: Triangle read by rows in which row n is the complete rhythm of n (see Comments for precise definition).
-- Upstream: formal-conjectures statements/oeis-a330733.lean:0 (declaration OMA.S_oeis_a330733.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: write H(n) = A002033(n-1), so H(1) = 1 and H(n) = Sum of H(i) over the proper
-- divisors i of n (n >= 2). Diagonal: for f | n the n-th term of the repeated rhythm of f is its
-- f-th term, so R(n,n) = 1 + Sum_{f | n, 1 < f < n} R(f,f) = H(1) + Sum H(f) = H(n) by strong
-- induction. Prime column: by strong induction on n >= 2, for every 1 <= j <= n with
-- j = p mod n one has R(n,j) = H(n/p) if p | n and 0 otherwise (the terms of the repeats keep
-- the residue of j); for n = p*m, m >= 2, the divisors f = p*e of n correspond to the proper
-- divisors e of m. H is never 0 because H(1) = 1 is a summand of every H(n), n >= 2.

namespace K03A330733

open OMA.S_oeis_a330733

theorem R_eq (n j : ℕ) : R n j = (if j = n then 1 else 0) +
    ∑ f ∈ (Nat.properDivisors n).erase 1, R f ((j - 1) % f + 1) := by
  rw [R]
  exact congrArg (fun s => (if j = n then 1 else 0) + s)
    (Finset.sum_attach ((Nat.properDivisors n).erase 1) (fun f => R f ((j - 1) % f + 1)))

theorem A_zero : A002033 0 = 1 := by
  rw [A002033]

theorem A_succ (m : ℕ) :
    A002033 (m + 1) = ∑ i ∈ Nat.properDivisors (m + 2), A002033 (i - 1) := by
  rw [A002033]
  exact Finset.sum_attach (Nat.properDivisors (m + 2)) (fun i => A002033 (i - 1))

theorem H_rec (n : ℕ) (hn : 2 ≤ n) :
    A002033 (n - 1) = ∑ i ∈ Nat.properDivisors n, A002033 (i - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega]
  exact A_succ m

theorem A_one_sub : A002033 (1 - 1) = 1 := by
  rw [Nat.sub_self, A_zero]

theorem A_pos (m : ℕ) : 1 ≤ A002033 m := by
  cases m with
  | zero =>
    have h := A_zero
    omega
  | succ m =>
    rw [A_succ]
    have h1 : (1 : ℕ) ∈ Nat.properDivisors (m + 2) :=
      Nat.mem_properDivisors.mpr ⟨one_dvd _, by omega⟩
    have h2 : A002033 (1 - 1) ≤ ∑ i ∈ Nat.properDivisors (m + 2), A002033 (i - 1) :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (A002033 (i - 1))) h1
    have h3 := A_one_sub
    omega

theorem mod_last (n f : ℕ) (hn : 1 ≤ n) (hf : f ∣ n) : (n - 1) % f + 1 = f := by
  obtain ⟨c, hc⟩ := hf
  have hf0 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, Nat.zero_mul] at hc
      omega
    · omega
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [Nat.mul_zero] at hc
    omega
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have e0 : f * (c' + 1) = f * c' + f := by ring
  have e1 : n - 1 = (f - 1) + f * c' := by omega
  rw [e1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show f - 1 < f by omega)]
  omega

theorem diag : ∀ n : ℕ, 1 ≤ n → R n n = A002033 (n - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rw [R_eq, if_pos rfl]
    have hs : ∑ f ∈ (Nat.properDivisors n).erase 1, R f ((n - 1) % f + 1) =
        ∑ f ∈ (Nat.properDivisors n).erase 1, A002033 (f - 1) := by
      apply Finset.sum_congr rfl
      intro f hf
      have hf1 := Nat.mem_properDivisors.mp (Finset.mem_of_mem_erase hf)
      have hf0 : 1 ≤ f := by
        rcases Nat.eq_zero_or_pos f with h0 | h0
        · have h := hf1.1
          rw [h0, Nat.zero_dvd] at h
          omega
        · omega
      rw [mod_last n f hn hf1.1]
      exact ih f hf1.2 hf0
    rw [hs]
    by_cases h1 : n = 1
    · subst h1
      have hs1 : ∑ f ∈ (Nat.properDivisors 1).erase 1, A002033 (f - 1) = 0 := by
        rw [Nat.properDivisors_one, Finset.erase_empty, Finset.sum_empty]
      have h3 := A_one_sub
      omega
    · have h1mem : (1 : ℕ) ∈ Nat.properDivisors n :=
        Nat.mem_properDivisors.mpr ⟨one_dvd n, by omega⟩
      have e : A002033 (1 - 1) + ∑ i ∈ (Nat.properDivisors n).erase 1, A002033 (i - 1) =
          ∑ i ∈ Nat.properDivisors n, A002033 (i - 1) :=
        Finset.add_sum_erase (Nat.properDivisors n) (fun i => A002033 (i - 1)) h1mem
      have h3 := A_one_sub
      rw [H_rec n (by omega)]
      omega

theorem col (p : ℕ) (hp : p.Prime) : ∀ n : ℕ, 2 ≤ n → ∀ j : ℕ, 1 ≤ j → j ≤ n →
    j % n = p % n → R n j = if p ∣ n then A002033 (n / p - 1) else 0 := by
  have hp2 : 2 ≤ p := hp.two_le
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn j hj1 hjn hjp
    rw [R_eq]
    have hs : ∑ f ∈ (Nat.properDivisors n).erase 1, R f ((j - 1) % f + 1) =
        ∑ f ∈ (Nat.properDivisors n).erase 1, (if p ∣ f then A002033 (f / p - 1) else 0) := by
      apply Finset.sum_congr rfl
      intro f hf
      have hf2 : f ≠ 1 := Finset.ne_of_mem_erase hf
      have hf1 := Nat.mem_properDivisors.mp (Finset.mem_of_mem_erase hf)
      have hfd : f ∣ n := hf1.1
      have hf0 : f ≠ 0 := by
        rintro rfl
        rw [Nat.zero_dvd] at hfd
        omega
      have hlt := Nat.mod_lt (j - 1) (show 0 < f by omega)
      apply ih f hf1.2 (by omega) ((j - 1) % f + 1) (by omega) (by omega)
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.sub_add_cancel hj1,
        ← Nat.mod_mod_of_dvd j hfd, hjp, Nat.mod_mod_of_dvd p hfd]
    rw [hs]
    have hjeq : j = n → n = p := by
      intro h
      rw [h, Nat.mod_self] at hjp
      rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hjp.symm) with h1 | h1
      · omega
      · exact h1
    by_cases hpn : p ∣ n
    · obtain ⟨m, rfl⟩ := hpn
      rw [if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m (show 0 < p by omega)]
      by_cases hm1 : m = 1
      · subst hm1
        have hj : j = p * 1 := by
          have h0 : j % p = 0 := by
            rw [Nat.mul_one] at hjp
            rw [hjp, Nat.mod_self]
          have hle := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero h0)
          omega
        have hPD : (Nat.properDivisors (p * 1)).erase 1 = ∅ := by
          rw [Nat.mul_one, Nat.Prime.properDivisors hp, Finset.erase_singleton]
        have hs0 : ∑ f ∈ (Nat.properDivisors (p * 1)).erase 1,
            (if p ∣ f then A002033 (f / p - 1) else 0) = 0 := by
          rw [hPD, Finset.sum_empty]
        have hA := A_one_sub
        rw [if_pos hj]
        omega
      · have hm0 : m ≠ 0 := by
          rintro rfl
          rw [Nat.mul_zero] at hn
          omega
        have hm2 : 2 ≤ m := by omega
        have hjne : ¬(j = p * m) := by
          intro h
          have h2 := hjeq h
          have h3 : p * m = p * 1 := by
            rw [Nat.mul_one]
            exact h2
          exact hm1 (Nat.eq_of_mul_eq_mul_left (show 0 < p by omega) h3)
        rw [if_neg hjne, Nat.zero_add, H_rec m hm2]
        have hinj : Set.InjOn (fun e => p * e) (Nat.properDivisors m) := by
          intro a _ b _ hab
          exact Nat.eq_of_mul_eq_mul_left (show 0 < p by omega) hab
        have himg : (Nat.properDivisors m).image (fun e => p * e) ⊆
            (Nat.properDivisors (p * m)).erase 1 := by
          intro f hf
          rw [Finset.mem_image] at hf
          obtain ⟨e, he, rfl⟩ := hf
          have he1 := Nat.mem_properDivisors.mp he
          have he0 : e ≠ 0 := by
            rintro rfl
            have h := he1.1
            rw [Nat.zero_dvd] at h
            omega
          rw [Finset.mem_erase, Nat.mem_properDivisors]
          refine ⟨?_, Nat.mul_dvd_mul_left p he1.1, Nat.mul_lt_mul_of_pos_left he1.2 (by omega)⟩
          intro h
          have h' : 2 * 1 ≤ p * e := Nat.mul_le_mul hp2 (by omega)
          omega
        have hzero : ∀ f ∈ (Nat.properDivisors (p * m)).erase 1,
            f ∉ (Nat.properDivisors m).image (fun e => p * e) →
              (if p ∣ f then A002033 (f / p - 1) else 0) = 0 := by
          intro f hf hfi
          have hf1 := Nat.mem_properDivisors.mp (Finset.mem_of_mem_erase hf)
          rw [if_neg]
          rintro ⟨e, rfl⟩
          apply hfi
          rw [Finset.mem_image]
          refine ⟨e, ?_, rfl⟩
          rw [Nat.mem_properDivisors]
          exact ⟨(Nat.mul_dvd_mul_iff_left (show 0 < p by omega)).mp hf1.1,
            Nat.lt_of_mul_lt_mul_left hf1.2⟩
        rw [← Finset.sum_subset himg hzero, Finset.sum_image hinj]
        apply Finset.sum_congr rfl
        intro e _
        show (if p ∣ p * e then A002033 (p * e / p - 1) else 0) = A002033 (e - 1)
        rw [if_pos (dvd_mul_right p e), Nat.mul_div_cancel_left e (show 0 < p by omega)]
    · have hjne : ¬(j = n) := by
        intro h
        have h2 := hjeq h
        rw [h2] at hpn
        exact hpn (dvd_refl p)
      rw [if_neg hjne, if_neg hpn, Nat.zero_add]
      apply Finset.sum_eq_zero
      intro f hf
      have hfd := (Nat.mem_properDivisors.mp (Finset.mem_of_mem_erase hf)).1
      rw [if_neg]
      intro hpf
      exact hpn (Nat.dvd_trans hpf hfd)

end K03A330733

open OMA.S_oeis_a330733 K03A330733 in
theorem OMA.solution : type_of% @OMA.S_oeis_a330733.main := by
  refine ⟨diag, fun m => Nat.one_le_iff_ne_zero.mp (A_pos m), fun p hp => ⟨?_, ?_⟩⟩
  · intro n hpn hnd
    have h2 := hp.two_le
    have h := col p hp n (by omega) p (by omega) hpn rfl
    rw [if_neg hnd] at h
    exact h
  · intro m hm
    have h2 := hp.two_le
    have hle : p ≤ m * p := Nat.le_mul_of_pos_left p hm
    have h := col p hp (m * p) (by omega) p (by omega) hle rfl
    rw [if_pos (dvd_mul_left p m), Nat.mul_div_cancel m (show 0 < p by omega)] at h
    exact h
