import OMAStatements.S_oeis_a274010
import Mathlib

-- Problem: A274010: Boris Stechkin function: a(n) is the number of m with 2 <= m <= n and
-- floor(n(m-1)/m) divisible by m-1.
-- Upstream: formal-conjectures statements/oeis-a274010.lean:0 (declaration OMA.S_oeis_a274010.main)
-- Credit: @rorcores (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof.  Fix m = d + 1 >= 2 and write n = m q + r with 0 <= r < m.  Then
--   floor(n d / m) = q d            if r = 0,
--   floor(n d / m) = q d + (r - 1)  if r >= 1   (because r d = (r - 1) m + (m - r)).
-- Since 0 <= r - 1 < d, the number d divides floor(n d / m) exactly when r = 0 or r = 1, that is
-- exactly when m divides n or m divides n - 1.  So a(n) counts the divisors m >= 2 of n together
-- with the divisors m >= 2 of n - 1.  No m >= 2 divides both n and n - 1, hence
--   a(n) = (tau(n) - 1) + (tau(n - 1) - 1).

namespace OMA.A274010

theorem key (n d : ℕ) (_hd : 1 ≤ d) : d ∣ n * d / (d + 1) ↔ n % (d + 1) ≤ 1 := by
  have hdiv := Nat.div_add_mod n (d + 1)
  have hlt := Nat.mod_lt n (Nat.succ_pos d)
  generalize n / (d + 1) = q at hdiv
  generalize n % (d + 1) = r at hdiv hlt
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · have hn : n = (d + 1) * q := by omega
    have e : n * d / (d + 1) = q * d := by
      rw [hn, Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.succ_pos d)]
    rw [e]
    constructor
    · intro _
      omega
    · intro _
      exact Dvd.intro_left q rfl
  · obtain ⟨r', hr'⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hn : n = (d + 1) * q + r' + 1 := by omega
    have hr'd : r' < d := by omega
    have e : n * d / (d + 1) = q * d + r' := by
      apply Nat.div_eq_of_lt_le
      · rw [hn]
        nlinarith
      · rw [hn]
        nlinarith
    rw [e]
    constructor
    · intro h
      have h1 : d ∣ r' := (Nat.dvd_add_right (Dvd.intro_left q rfl)).1 h
      have h2 : r' = 0 := Nat.eq_zero_of_dvd_of_lt h1 hr'd
      omega
    · intro h
      have h2 : r' = 0 := by omega
      rw [h2, Nat.add_zero]
      exact Dvd.intro_left q rfl

theorem mem_iff (n m : ℕ) (hn : 2 ≤ n) :
    (2 ≤ m ∧ m ≤ n) ∧ (m - 1) ∣ n * (m - 1) / m ↔
      (m ≠ 1 ∧ m ∣ n) ∨ (m ≠ 1 ∧ m ∣ n - 1) := by
  constructor
  · rintro ⟨⟨h2, hmn⟩, hdvd⟩
    obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩
    have hdvd' : d ∣ n * d / (d + 1) := by simpa using hdvd
    have hk := (key n d (by omega)).1 hdvd'
    rcases Nat.eq_zero_or_pos (n % (d + 1)) with h0 | h1
    · left
      exact ⟨by omega, Nat.dvd_of_mod_eq_zero h0⟩
    · right
      have h1' : n % (d + 1) = 1 := by omega
      refine ⟨by omega, ?_⟩
      have h3 : (d + 1) ∣ n - n % (d + 1) := Nat.dvd_sub_mod n
      rw [h1'] at h3
      exact h3
  · rintro (⟨hne, hdvd⟩ | ⟨hne, hdvd⟩)
    · have hpos : 0 < m := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hle : m ≤ n := Nat.le_of_dvd (by omega) hdvd
      refine ⟨⟨by omega, hle⟩, ?_⟩
      obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩
      have h4 : n % (d + 1) ≤ 1 := by
        rw [Nat.mod_eq_zero_of_dvd hdvd]
        omega
      have h5 := (key n d (by omega)).2 h4
      simpa using h5
    · have hpos : 0 < m := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hle : m ≤ n - 1 := Nat.le_of_dvd (by omega) hdvd
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := ⟨m - 1, by omega⟩
      have h4 : n % (d + 1) ≤ 1 := by
        obtain ⟨c, hc⟩ := hdvd
        have hn' : n = (d + 1) * c + 1 := by omega
        rw [hn', Nat.mul_add_mod]
        exact Nat.mod_le _ _
      have h5 := (key n d (by omega)).2 h4
      simpa using h5

end OMA.A274010

theorem OMA.solution : type_of% @OMA.S_oeis_a274010.main := by
  intro n hn
  unfold OMA.S_oeis_a274010.a
  have hset : (Finset.Icc 2 n).filter (fun m => (m - 1) ∣ n * (m - 1) / m)
      = (n.divisors.erase 1) ∪ ((n - 1).divisors.erase 1) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_erase,
      Nat.mem_divisors]
    rw [OMA.A274010.mem_iff n m hn]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · left
        exact ⟨h1, h2, by omega⟩
      · right
        exact ⟨h1, h2, by omega⟩
    · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩)
      · left
        exact ⟨h1, h2⟩
      · right
        exact ⟨h1, h2⟩
  have hdisj : Disjoint (n.divisors.erase 1) ((n - 1).divisors.erase 1) := by
    rw [Finset.disjoint_left]
    intro m h1 h2
    simp only [Finset.mem_erase, Nat.mem_divisors] at h1 h2
    have hd1 : m ∣ n - (n - 1) := Nat.dvd_sub h1.2.1 h2.2.1
    have h3 : n - (n - 1) = 1 := by omega
    rw [h3] at hd1
    exact h1.1 (Nat.dvd_one.1 hd1)
  have hm1 : 1 ∈ n.divisors := by
    rw [Nat.mem_divisors]
    exact ⟨one_dvd n, by omega⟩
  have hm2 : 1 ∈ (n - 1).divisors := by
    rw [Nat.mem_divisors]
    exact ⟨one_dvd (n - 1), by omega⟩
  have hc1 : 1 ≤ n.divisors.card := Finset.card_pos.2 ⟨1, hm1⟩
  have hc2 : 1 ≤ (n - 1).divisors.card := Finset.card_pos.2 ⟨1, hm2⟩
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hm1,
    Finset.card_erase_of_mem hm2]
  push_cast [Nat.cast_sub hc1, Nat.cast_sub hc2]
  ring
