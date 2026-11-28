import OMAStatements.S_oeis_a231635

-- Reduction oeis-a231635.R1 of A231635
-- Credit: @yuka30240

namespace OMA.R_oeis_a231635_R1

/-- Split off all pairs whose smaller summand divides the sum. For every
other pair, divide the sum and both summands by their common gcd. -/
lemma partition_iff (P : ℕ → Prop) {n : ℕ} (hn : 0 < n) :
    (∃ x y : ℕ, 0 < x ∧ x ≤ y ∧ x + y = n ∧ P (Nat.lcm x y)) ↔
    (∃ d : ℕ, d ∣ n ∧ d < n ∧ P (n - d)) ∨
    (∃ m : ℕ, m ∣ n ∧ ∃ k : ℕ, 2 ≤ k ∧ 2 * k ≤ m ∧ k.Coprime m ∧
      P (n / m * k * (m - k))) := by
  constructor
  · rintro ⟨x, y, hx, hxy, hsum, hp⟩
    obtain ⟨g, a, b, hg, hc, rfl, rfl⟩ :=
      Nat.exists_coprime' (Nat.gcd_pos_of_pos_left y hx)
    have ha := Nat.pos_of_mul_pos_right hx
    have hab := Nat.le_of_mul_le_mul_right hxy hg
    have hn' : n = (a + b) * g := by rwa [Nat.add_mul, eq_comm]
    rw [Nat.lcm_mul_right, hc.lcm_eq_mul] at hp
    by_cases hunit : a = 1
    · subst a
      simp only [Nat.one_mul] at hsum hp hxy
      exact Or.inl ⟨g, ⟨1 + b, by rw [hn', Nat.mul_comm]⟩,
        by omega, by simpa [← hsum] using hp⟩
    · right
      refine ⟨a + b, ⟨g, hn'⟩, a, by omega, by omega, by simpa using hc, ?_⟩
      rw [hn', Nat.mul_div_cancel_left g (by omega), Nat.add_sub_cancel_left]
      simpa only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hp
  · rintro (⟨d, hd, hlt, hp⟩ | ⟨m, hm, k, hk, hkm, hc, hp⟩)
    · have hdiv : d ∣ n - d := Nat.dvd_sub hd (dvd_refl _)
      exact ⟨d, n - d, Nat.pos_of_dvd_of_pos hd hn, Nat.le_of_dvd (by omega) hdiv,
        by omega, by rwa [Nat.lcm_eq_right hdiv]⟩
    · have hmpos : 0 < m := by omega
      have hg := Nat.div_pos (Nat.le_of_dvd hn hm) hmpos
      have hsub : k + (m - k) = m := by omega
      refine ⟨n / m * k, n / m * (m - k), Nat.mul_pos hg (by omega),
        Nat.mul_le_mul_left _ (by omega), ?_, ?_⟩
      · rw [← Nat.mul_add, hsub, Nat.div_mul_cancel hm]
      · rw [Nat.lcm_mul_left, ((Nat.coprime_sub_self_right (by omega)).2 hc).lcm_eq_mul,
          ← Nat.mul_assoc]
        exact hp

-- Each step treats one polynomial on the remaining inputs.
def H1 : Prop :=
  ∀ n : ℕ, 100 < n → (∀ d : ℕ, d ∣ n → d < n → ¬ Nat.Prime ((n - d) + 1)) →
    ∃ m : ℕ, m ∣ n ∧ ∃ k : ℕ, 2 ≤ k ∧ 2 * k ≤ m ∧ k.Coprime m ∧
      Nat.Prime (n / m * k * (m - k) + 1)

def H2 : Prop :=
  ∀ n : ℕ, 100 < n → (∀ d : ℕ, d ∣ n → d < n → ¬ Nat.Prime ((n - d) - 1)) →
    ∃ m : ℕ, m ∣ n ∧ ∃ k : ℕ, 2 ≤ k ∧ 2 * k ≤ m ∧ k.Coprime m ∧
      Nat.Prime (n / m * k * (m - k) - 1)

def H3 : Prop :=
  ∀ n : ℕ, 100 < n → (∀ d : ℕ, d ∣ n → d < n → ¬ Nat.Prime ((n - d) ^ 2 + (n - d) + 1)) →
    ∃ m : ℕ, m ∣ n ∧ ∃ k : ℕ, 2 ≤ k ∧ 2 * k ≤ m ∧ k.Coprime m ∧
      let t := n / m * k * (m - k)
      Nat.Prime (t ^ 2 + t + 1)

def H4 : Prop :=
  ∀ n : ℕ, 100 < n → (∀ d : ℕ, d ∣ n → d < n → ¬ Nat.Prime ((n - d) ^ 2 + 1)) →
    ∃ m : ℕ, m ∣ n ∧ ∃ k : ℕ, 2 ≤ k ∧ 2 * k ≤ m ∧ k.Coprime m ∧
      let t := n / m * k * (m - k)
      Nat.Prime (t ^ 2 + 1)

/-- A bounded divisibility test for the four finite kernel checks. -/
lemma prime_trial (p : ℕ) : Nat.Prime p ↔
    2 ≤ p ∧ ∀ d : Fin (p.sqrt + 1), 2 ≤ d.val → p % d.val ≠ 0 := by
  rw [Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun d hd hmod => h d hd (by omega) (Nat.dvd_of_mod_eq_zero hmod)⟩
  · rintro ⟨hp, h⟩
    exact ⟨hp, fun d hd hs hdiv => h ⟨d, by omega⟩ hd (Nat.mod_eq_zero_of_dvd hdiv)⟩

lemma cover (P : ℕ → Prop) (A : ℕ → Prop)
    (small : ∀ n : Fin 101, A n.val → ∃ x : Fin (n.val / 2 + 1),
      0 < x.val ∧ P (Nat.lcm x.val (n.val - x.val)))
    (large : ∀ n : ℕ, 100 < n → (∀ d : ℕ, d ∣ n → d < n → ¬ P (n - d)) →
      ∃ m : ℕ, m ∣ n ∧ ∃ k : ℕ, 2 ≤ k ∧ 2 * k ≤ m ∧ k.Coprime m ∧
        P (n / m * k * (m - k))) {n : ℕ} (hn : 0 < n) (ha : A n) :
    ∃ x y : ℕ, 0 < x ∧ x ≤ y ∧ x + y = n ∧ P (Nat.lcm x y) := by
  by_cases hs : n ≤ 100
  · obtain ⟨x, hx, hp⟩ := small ⟨n, by omega⟩ ha
    have hbound : x.val < n / 2 + 1 := x.isLt
    exact ⟨x.val, n - x.val, hx, by omega, by omega, hp⟩
  · apply (partition_iff P hn).2
    by_cases hd : ∃ d : ℕ, d ∣ n ∧ d < n ∧ P (n - d)
    · exact Or.inl hd
    · exact Or.inr (large n (by omega) (fun d hdvd hlt hp => hd ⟨d, hdvd, hlt, hp⟩))

lemma positive_pair {P : ℕ → Prop} {n : ℕ}
    (h : ∃ x y : ℕ, 0 < x ∧ x ≤ y ∧ x + y = n ∧ P (Nat.lcm x y)) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ P (Nat.lcm x y) := by
  obtain ⟨x, y, hx, hxy, hs, hp⟩ := h
  exact ⟨x, y, hx, lt_of_lt_of_le hx hxy, hs, hp⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a231635.main := by
  intro h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    apply cover (fun t => Nat.Prime (t + 1)) (fun s => 1 < s) _ h1 (by omega) hn
    simp only [prime_trial]
    decide +kernel
  · intro n hn
    apply positive_pair (P := fun t => Nat.Prime (t - 1))
    apply cover (fun t => Nat.Prime (t - 1)) (fun s => 3 < s) _ h2 (by omega) hn
    simp only [prime_trial]
    decide +kernel
  · intro n hn
    apply positive_pair (P := fun t => Nat.Prime (t ^ 2 + t + 1))
    apply cover (fun t => Nat.Prime (t ^ 2 + t + 1)) (fun s => 2 ≤ s) _ h3 (by omega) hn
    simp only [prime_trial]
    decide +kernel
  · intro n hn hten
    apply positive_pair (P := fun t => Nat.Prime (t ^ 2 + 1))
    apply cover (fun t => Nat.Prime (t ^ 2 + 1)) (fun s => 1 < s ∧ s ≠ 10) _ h4 (by omega) ⟨hn, hten⟩
    simp only [prime_trial]
    decide +kernel

end OMA.R_oeis_a231635_R1
