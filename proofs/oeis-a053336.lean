import OMAStatements.S_oeis_a053336
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

namespace OMA.P_oeis_a053336

open OMA.S_oeis_a053336

private lemma ofDigits_append_singleton (l : List ℕ) (c : ℕ) :
    Nat.ofDigits 10 (l ++ [c]) = Nat.ofDigits 10 l + c * 10 ^ l.length := by
  induction l with
  | nil => simp [Nat.ofDigits]
  | cons a t ih =>
    simp only [List.cons_append, Nat.ofDigits, List.length_cons, ih, pow_succ]
    ring

private lemma ofDigits_digits_append (m c : ℕ) (hc1 : 1 ≤ c) (hc9 : c < 10) :
    Nat.digits 10 (m + c * 10 ^ (Nat.digits 10 m).length) = Nat.digits 10 m ++ [c] := by
  have hval : m + c * 10 ^ (Nat.digits 10 m).length = Nat.ofDigits 10 (Nat.digits 10 m ++ [c]) := by
    rw [ofDigits_append_singleton, Nat.ofDigits_digits]
  rw [hval]
  apply Nat.digits_ofDigits 10 (by omega)
  · intro d hd
    rw [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | rfl
    · exact Nat.digits_lt_base (by omega) hd
    · exact hc9
  · intro hne
    rw [List.getLast_append_singleton]
    omega

private lemma existsUnique_two_digits (d₀ d₁ : ℕ) (hd₀ : 1 ≤ d₀) (hd₀' : d₀ < 10)
    (hd₁ : 1 ≤ d₁) (hd₁' : d₁ < 10) (hpar : d₀ % 2 ≠ d₁ % 2) :
    ∀ n : ℕ, 1 ≤ n →
      ∃! m : ℕ, (Nat.digits 10 m).length = n ∧
        (∀ d ∈ Nat.digits 10 m, d = d₀ ∨ d = d₁) ∧ 2 ^ n ∣ m := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      -- Base case n = 1
      have hex : ∃ c, (c = d₀ ∨ c = d₁) ∧ 2 ∣ c := by
        by_cases h0 : d₀ % 2 = 0
        · exact ⟨d₀, Or.inl rfl, Nat.dvd_of_mod_eq_zero h0⟩
        · exact ⟨d₁, Or.inr rfl, Nat.dvd_of_mod_eq_zero (by omega)⟩
      rcases hex with ⟨c, hc, hc2⟩
      have hc_lo : 1 ≤ c := by rcases hc with rfl | rfl <;> omega
      have hc_hi : c < 10 := by rcases hc with rfl | rfl <;> omega
      refine ⟨c, ?_, ?_⟩
      · have hdig : Nat.digits 10 c = [c] := Nat.digits_of_lt 10 c (by omega) hc_hi
        refine ⟨by simp [hdig], ?_, by simpa using hc2⟩
        intro d hd; rw [hdig, List.mem_singleton] at hd; subst hd; exact hc
      · intro m ⟨hlen, hmem, hdvd⟩
        cases hL : Nat.digits 10 m with
        | nil => rw [hL] at hlen; simp at hlen
        | cons a t =>
          rw [hL] at hlen
          have ht : t = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
          subst ht
          have hm : m = a := by
            have := Nat.ofDigits_digits 10 m
            rw [hL] at this
            simpa [Nat.ofDigits] using this.symm
          have ha : a = d₀ ∨ a = d₁ := hmem a (by simp [hL])
          have ha2 : 2 ∣ a := by rw [← hm]; simpa using hdvd
          rw [hm]
          rcases hc with rfl | rfl <;> rcases ha with rfl | rfl <;> omega
    | succ k' =>
      -- Inductive step from k' + 1 to k' + 2
      set n' : ℕ := k' + 1
      obtain ⟨m₀, ⟨hlen₀, hmem₀, hdvd₀⟩, huniq₀⟩ := ih (by omega)
      obtain ⟨q, hq⟩ := hdvd₀
      have h5odd : (5 ^ n') % 2 = 1 := by
        have : Odd (5 ^ n') := Odd.pow ⟨2, rfl⟩
        exact Nat.odd_iff.mp this
      have hex_c : ∃ c, (c = d₀ ∨ c = d₁) ∧ (q + c * 5 ^ n') % 2 = 0 := by
        by_cases h0 : (q + d₀ * 5 ^ n') % 2 = 0
        · exact ⟨d₀, Or.inl rfl, h0⟩
        · refine ⟨d₁, Or.inr rfl, ?_⟩
          have h1 : (q + d₀ * 5 ^ n') % 2 = (q % 2 + d₀ % 2) % 2 := by
            simp [Nat.add_mod, Nat.mul_mod, h5odd]
          have h2 : (q + d₁ * 5 ^ n') % 2 = (q % 2 + d₁ % 2) % 2 := by
            simp [Nat.add_mod, Nat.mul_mod, h5odd]
          omega
      rcases hex_c with ⟨c, hc, hceven⟩
      have hc_lo : 1 ≤ c := by rcases hc with rfl | rfl <;> omega
      have hc_hi : c < 10 := by rcases hc with rfl | rfl <;> omega
      set m₁ : ℕ := m₀ + c * 10 ^ n'
      refine ⟨m₁, ?_, ?_⟩
      · have hdig : Nat.digits 10 m₁ = Nat.digits 10 m₀ ++ [c] := by
          dsimp only [m₁]
          rw [← hlen₀]
          exact ofDigits_digits_append m₀ c hc_lo hc_hi
        refine ⟨by simp [hdig, hlen₀, n'], ?_, ?_⟩
        · intro d hd
          rw [hdig, List.mem_append, List.mem_singleton] at hd
          rcases hd with hd | rfl
          · exact hmem₀ d hd
          · exact hc
        · have h10 : 10 ^ n' = 2 ^ n' * 5 ^ n' := by
            rw [← mul_pow]; norm_num
          have hfac : m₁ = 2 ^ n' * (q + c * 5 ^ n') := by
            dsimp only [m₁]
            rw [hq, h10]; ring
          obtain ⟨r, hr⟩ := Nat.dvd_of_mod_eq_zero hceven
          refine ⟨r, ?_⟩
          rw [hfac, hr, pow_succ]; ring
      · intro m ⟨hlen, hmem, hdvd⟩
        have hne : Nat.digits 10 m ≠ [] := by
          intro h; rw [h] at hlen; simp at hlen
        set L' := (Nat.digits 10 m).dropLast
        set c' := (Nat.digits 10 m).getLast hne
        have hsplit : Nat.digits 10 m = L' ++ [c'] := (List.dropLast_append_getLast hne).symm
        have hL'_len : L'.length = n' := by
          have := congr_arg List.length hsplit
          simp only [List.length_append, List.length_singleton] at this
          omega
        have hL'_mem : ∀ d ∈ L', d = d₀ ∨ d = d₁ := by
          intro d hd
          exact hmem d (by rw [hsplit]; exact List.mem_append_left _ hd)
        have hc'_mem : c' = d₀ ∨ c' = d₁ :=
          hmem c' (by rw [hsplit]; exact List.mem_append_right _ (List.mem_singleton_self _))
        have hL'_dig : Nat.digits 10 (Nat.ofDigits 10 L') = L' := by
          apply Nat.digits_ofDigits 10 (by omega)
          · intro d hd
            rcases hL'_mem d hd with rfl | rfl <;> omega
          · intro hL'ne
            have hlast := hL'_mem (L'.getLast hL'ne) (List.getLast_mem hL'ne)
            rcases hlast with h | h <;> omega
        have hm_eq : m = Nat.ofDigits 10 L' + c' * 10 ^ n' := by
          have := Nat.ofDigits_digits 10 m
          rw [hsplit, ofDigits_append_singleton, hL'_len] at this
          exact this.symm
        have hprev_dvd : 2 ^ n' ∣ Nat.ofDigits 10 L' := by
          have h1 : 2 ^ n' ∣ m := (pow_dvd_pow 2 (by omega : n' ≤ n' + 1)).trans hdvd
          have h2 : 2 ^ n' ∣ c' * 10 ^ n' := by
            have h10 : 10 ^ n' = 2 ^ n' * 5 ^ n' := by rw [← mul_pow]; norm_num
            rw [h10]; exact ⟨c' * 5 ^ n', by ring⟩
          rw [hm_eq] at h1
          exact (Nat.dvd_add_left h2).mp h1
        have hprev_eq : Nat.ofDigits 10 L' = m₀ :=
          huniq₀ (Nat.ofDigits 10 L') ⟨by rw [hL'_dig]; exact hL'_len,
            fun d hd => hL'_mem d (by rwa [hL'_dig] at hd), hprev_dvd⟩
        have hc'_eq : c' = c := by
          have h10 : 10 ^ n' = 2 ^ n' * 5 ^ n' := by rw [← mul_pow]; norm_num
          have hfac : m = 2 ^ n' * (q + c' * 5 ^ n') := by
            rw [hm_eq, hprev_eq, hq, h10]; ring
          have h2dvd : 2 ∣ (q + c' * 5 ^ n') := by
            rw [hfac, pow_succ] at hdvd
            exact (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ n')).mp hdvd
          have hmod' : (q + c' * 5 ^ n') % 2 = 0 := Nat.mod_eq_zero_of_dvd h2dvd
          have h1 : (q + c * 5 ^ n') % 2 = (q % 2 + c % 2) % 2 := by
            simp [Nat.add_mod, Nat.mul_mod, h5odd]
          have h2 : (q + c' * 5 ^ n') % 2 = (q % 2 + c' % 2) % 2 := by
            simp [Nat.add_mod, Nat.mul_mod, h5odd]
          rcases hc with rfl | rfl <;> rcases hc'_mem with rfl | rfl <;> omega
        rw [hm_eq, hprev_eq, hc'_eq]

private lemma ofDigits_add_complement (l : List ℕ) (hl : ∀ d ∈ l, d ≤ 9) :
    Nat.ofDigits 10 l + Nat.ofDigits 10 (l.map (fun d => 9 - d)) + 1 = 10 ^ l.length := by
  induction l with
  | nil => simp [Nat.ofDigits]
  | cons a t ih =>
    have ha : a ≤ 9 := hl a (List.mem_cons_self ..)
    have ht : ∀ d ∈ t, d ≤ 9 := fun d hd => hl d (List.mem_cons_of_mem _ hd)
    have ih' := ih ht
    simp only [List.map_cons, Nat.ofDigits, List.length_cons, pow_succ, Nat.cast_id]
    omega

private lemma prove_a053336 :
    ∀ n : ℕ, 1 ≤ n →
      (∃! m, IsA053336 n m) ∧
      (∃! m, IsA035014 n m) ∧
      (∀ m₁ m₂, IsA053336 n m₁ → IsA035014 n m₂ → m₁ = 10 ^ n - m₂) := by
  intro n hn
  have hu1 : ∃! m, IsA053336 n m :=
    existsUnique_two_digits 5 6 (by omega) (by omega) (by omega) (by omega) (by omega) n hn
  have hu2 : ∃! m, IsA035014 n m :=
    existsUnique_two_digits 3 4 (by omega) (by omega) (by omega) (by omega) (by omega) n hn
  refine ⟨hu1, hu2, ?_⟩
  intro m₁ m₂ hm₁ hm₂
  rcases hm₂ with ⟨hlen₂, hmem₂, hdvd₂⟩
  -- Write the digits of m₂ as d₀ :: rest, with d₀ = 4 (since 2 ∣ m₂)
  cases hL : Nat.digits 10 m₂ with
  | nil => rw [hL] at hlen₂; simp at hlen₂; omega
  | cons d₀ rest =>
    have hd₀_mem : d₀ = 3 ∨ d₀ = 4 := hmem₂ d₀ (by simp [hL])
    have hd₀_even : 2 ∣ d₀ := by
      have hm2_even : 2 ∣ m₂ := (pow_dvd_pow 2 hn).trans hdvd₂
      have hm2_eq : m₂ = d₀ + 10 * Nat.ofDigits 10 rest := by
        have := Nat.ofDigits_digits 10 m₂
        rw [hL] at this
        simpa [Nat.ofDigits] using this.symm
      omega
    have hd₀ : d₀ = 4 := by rcases hd₀_mem with rfl | rfl <;> omega
    subst hd₀
    let L₁ : List ℕ := 6 :: rest.map (fun d => 9 - d)
    have hrest_mem : ∀ d ∈ rest, d = 3 ∨ d = 4 := fun d hd =>
      hmem₂ d (by rw [hL]; exact List.mem_cons_of_mem _ hd)
    have hsum : m₂ + Nat.ofDigits 10 L₁ = 10 ^ n := by
      have hm2_eq : m₂ = 4 + 10 * Nat.ofDigits 10 rest := by
        have := Nat.ofDigits_digits 10 m₂
        rw [hL] at this
        simpa [Nat.ofDigits] using this.symm
      have hL1_eq : Nat.ofDigits 10 L₁ = 6 + 10 * Nat.ofDigits 10 (rest.map (fun d => 9 - d)) := by
        simp [L₁, Nat.ofDigits]
      have hcomp := ofDigits_add_complement rest (fun d hd => by rcases hrest_mem d hd with rfl | rfl <;> omega)
      have hlen_rest : rest.length + 1 = n := by
        rw [hL, List.length_cons] at hlen₂; exact hlen₂
      rw [hm2_eq, hL1_eq, ← hlen_rest, pow_succ]
      omega
    have hL₁_mem : ∀ d ∈ L₁, d = 5 ∨ d = 6 := by
      intro d hd
      simp only [L₁, List.mem_cons, List.mem_map] at hd
      rcases hd with rfl | ⟨x, hx, rfl⟩
      · exact Or.inr rfl
      · rcases hrest_mem x hx with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl rfl
    have hL₁_dig : Nat.digits 10 (Nat.ofDigits 10 L₁) = L₁ := by
      apply Nat.digits_ofDigits 10 (by omega)
      · intro d hd; rcases hL₁_mem d hd with rfl | rfl <;> omega
      · intro hne
        have hlast := hL₁_mem (L₁.getLast hne) (List.getLast_mem hne)
        rcases hlast with h | h <;> omega
    have hL₁_len : L₁.length = n := by
      rw [hL, List.length_cons] at hlen₂
      simpa [L₁] using hlen₂
    have hcand : IsA053336 n (10 ^ n - m₂) := by
      have hsub_eq : 10 ^ n - m₂ = Nat.ofDigits 10 L₁ := by omega
      rw [hsub_eq]
      refine ⟨by rw [hL₁_dig]; exact hL₁_len, fun d hd => hL₁_mem d (by rwa [hL₁_dig] at hd), ?_⟩
      have h10_dvd : 2 ^ n ∣ 10 ^ n := by
        have h10 : 10 ^ n = 2 ^ n * 5 ^ n := by rw [← mul_pow]; norm_num
        rw [h10]; exact dvd_mul_right _ _
      rw [← hsum] at h10_dvd
      exact (Nat.dvd_add_right hdvd₂).mp h10_dvd
    exact hu1.unique hm₁ hcand

end OMA.P_oeis_a053336

theorem OMA.solution : type_of% @OMA.S_oeis_a053336.main :=
  OMA.P_oeis_a053336.prove_a053336
