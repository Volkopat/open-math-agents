import FormalConjectures.ErdosProblems.«376»

/-! Shorter proof of `Erdos376.erdos_376.variants.prime`. -/

private def G (p n : ℕ) : Prop := ∀ k : ℕ, 2 * (n % p ^ k) < p ^ k

private lemma G_small {p c : ℕ} (h : 2 * c < p) : G p c := fun k => by
  cases k with
  | zero => simp [Nat.mod_one]
  | succ k =>
    have : p ≤ p ^ (k + 1) := Nat.le_self_pow (Nat.succ_ne_zero k) p
    rw [Nat.mod_eq_of_lt (by omega)]; omega

private lemma G_append {p a d : ℕ} (hd : 2 * d < p) (h : G p a) : G p (p * a + d) := fun k => by
  cases k with
  | zero => simp [Nat.mod_one]
  | succ k =>
    have h1 : (p * a + d) % p ^ (k + 1) = d + p * (a % p ^ k) := by
      rw [pow_succ', Nat.mod_mul, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega),
        Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), add_zero]
    have := Nat.mul_le_mul_left p (h k)
    rw [h1, pow_succ']; nlinarith

private lemma step {p h X Y u V : ℕ} (hp : p = 2 * h + 1) (hX : 0 < X) (h1 : 2 * u ≤ 2 * V + Y)
    (h2 : 2 * V ≤ 2 * u + p * X) (hXY : X ≤ Y) :
    ∃ d, 2 * d < p ∧ 2 * (u + d * X) ≤ 2 * V + Y ∧ 2 * V ≤ 2 * (u + d * X) + X := by
  subst hp
  by_cases hc : h ≤ (2 * V + Y - 2 * u) / (2 * X)
  · have := (Nat.le_div_iff_mul_le (by omega)).1 hc
    have : h * (2 * X) = 2 * (h * X) := by ring
    exact ⟨h, by omega, by omega, by nlinarith⟩
  · set q := (2 * V + Y - 2 * u) / (2 * X)
    have h3 : q * (2 * X) ≤ 2 * V + Y - 2 * u := Nat.div_mul_le_self _ _
    have h4 : 2 * V + Y - 2 * u < q * (2 * X) + 2 * X := Nat.lt_div_mul_add (by omega)
    have h5 : q * (2 * X) = 2 * (q * X) := by ring
    exact ⟨q, by omega, by omega, by omega⟩

private lemma descent {p q : ℕ} (hp : Odd p) (hq : Odd q) :
    ∀ m i j a b : ℕ, i + j = m → G p a → G q b →
      2 * (a * p ^ i) ≤ 2 * (b * q ^ j) + q ^ j →
      2 * (b * q ^ j) ≤ 2 * (a * p ^ i) + p ^ i →
      q ^ j ≤ q * p ^ i → p ^ i ≤ p * q ^ j →
      ∃ n, G p n ∧ G q n ∧ a * p ^ i ≤ n ∧ b * q ^ j ≤ n := by
  obtain ⟨hh, hph⟩ := hp; obtain ⟨kk, hqk⟩ := hq
  have ppos : 0 < p := by omega
  have qpos : 0 < q := by omega
  intro m; induction m with
  | zero =>
    intro i j a b hij ha hb h1 h2 _ _
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ j = 0 := by omega
    simp only [pow_zero, mul_one] at h1 h2 ⊢
    exact ⟨a, ha, (by omega : a = b) ▸ hb, le_rfl, by omega⟩
  | succ m ih =>
    intro i j a b hij ha hb h1 h2 h3 h4
    by_cases hc : ∃ i', i = i' + 1 ∧ q ^ j ≤ q * p ^ i'
    · obtain ⟨i', rfl, hc⟩ := hc
      have e1 : p ^ (i' + 1) = p * p ^ i' := pow_succ' p i'
      have hXY : p ^ i' ≤ q ^ j := Nat.le_of_mul_le_mul_left (e1 ▸ h4) ppos
      obtain ⟨d, hd, s1, s2⟩ := step hph (Nat.pow_pos ppos) h1 (e1 ▸ h2) hXY
      have e2 : (p * a + d) * p ^ i' = a * p ^ (i' + 1) + d * p ^ i' := by rw [e1]; ring
      obtain ⟨n, hn1, hn2, hn3, hn4⟩ := ih i' j (p * a + d) b (by omega) (G_append hd ha) hb
        (e2 ▸ s1) (e2 ▸ s2) hc (hXY.trans (Nat.le_mul_of_pos_left _ ppos))
      exact ⟨n, hn1, hn2, by omega, hn4⟩
    · have hj : ∃ j', j = j' + 1 ∧ p ^ i ≤ p * q ^ j' := by
        cases j with
        | zero => exact absurd ⟨m, by omega, by rw [pow_zero]; exact Nat.mul_pos qpos (Nat.pow_pos ppos)⟩ hc
        | succ j' =>
          refine ⟨j', rfl, ?_⟩
          cases i with
          | zero => rw [pow_zero]; exact Nat.mul_pos ppos (Nat.pow_pos qpos)
          | succ i' =>
            have hlt : q * p ^ i' < q ^ (j' + 1) := by by_contra hcon; exact hc ⟨i', rfl, by omega⟩
            rw [pow_succ' q j'] at hlt
            rw [pow_succ' p i']
            exact Nat.mul_le_mul_left p (Nat.lt_of_mul_lt_mul_left hlt).le
      obtain ⟨j', rfl, hc'⟩ := hj
      have e1 : q ^ (j' + 1) = q * q ^ j' := pow_succ' q j'
      have hXY : q ^ j' ≤ p ^ i := Nat.le_of_mul_le_mul_left (e1 ▸ h3) qpos
      obtain ⟨d, hd, s1, s2⟩ := step hqk (Nat.pow_pos qpos) h2 (e1 ▸ h1) hXY
      have e2 : (q * b + d) * q ^ j' = b * q ^ (j' + 1) + d * q ^ j' := by rw [e1]; ring
      obtain ⟨n, hn1, hn2, hn3, hn4⟩ := ih i j' a (q * b + d) (by omega) ha (G_append hd hb)
        (e2 ▸ s2) (e2 ▸ s1) (hXY.trans (Nat.le_mul_of_pos_left _ qpos)) hc'
      exact ⟨n, hn1, hn2, hn3, by omega⟩

private lemma core {p q : ℕ} (hp : Odd p) (hq : Odd q) (hp3 : 3 ≤ p) (hq5 : 5 ≤ q) (N : ℕ) :
    ∃ n, N ≤ n ∧ G p n ∧ G q n := by
  classical
  have hyN : N < q ^ N := Nat.lt_pow_self (by omega)
  have hex : ∃ i, q ^ N ≤ p ^ i := ⟨q ^ N, (Nat.lt_pow_self (by omega)).le⟩
  have hi := Nat.find_spec hex
  have hmin : ∀ i', i' < Nat.find hex → ¬ q ^ N ≤ p ^ i' := fun _ => Nat.find_min hex
  generalize Nat.find hex = i at hi hmin
  have h4 : p ^ i ≤ p * q ^ N := by
    cases i with
    | zero => rw [pow_zero]; exact Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
    | succ i' => have := hmin i' (Nat.lt_succ_self i'); rw [pow_succ' p i']; exact Nat.mul_le_mul_left p (by omega)
  have h3 : q ^ N ≤ q * p ^ i := hi.trans (Nat.le_mul_of_pos_left _ (by omega))
  by_cases hA : 2 * q ^ N ≤ p ^ i
  · obtain ⟨n, hn1, hn2, _, hn4⟩ := descent hp hq (i + N) i N 0 1 rfl
      (G_small (by omega)) (G_small (by omega)) (by omega) (by omega) h3 h4
    exact ⟨n, by omega, hn1, hn2⟩
  · by_cases hB : 2 * p ^ i ≤ 3 * q ^ N
    · obtain ⟨n, hn1, hn2, hn3, _⟩ := descent hp hq (i + N) i N 1 1 rfl
        (G_small (by omega)) (G_small (by omega)) (by omega) (by omega) h3 h4
      exact ⟨n, by omega, hn1, hn2⟩
    · obtain ⟨n, hn1, hn2, hn3, _⟩ := descent hp hq (i + N) i N 1 2 rfl
        (G_small (by omega)) (G_small (by omega)) (by omega) (by omega) h3 h4
      exact ⟨n, by omega, hn1, hn2⟩

theorem OMA.solution : type_of% @Erdos376.erdos_376.variants.prime := by
  intro p q h₁ h₂ h₃ h₄
  have hp3 : 3 ≤ p := by obtain ⟨k, hk⟩ := h₂; have := h₁.two_le; omega
  have hq3 : 3 ≤ q := by obtain ⟨k, hk⟩ := h₄; have := h₃.two_le; omega
  have hndvd {r n : ℕ} (hr : r.Prime) (h : G r n) : ¬ r ∣ n.centralBinom := by
    have key := Nat.Prime.emultiplicity_choose' (p := r) (n := n) (k := n)
      (b := Nat.log r (n + n) + 1) hr (Nat.lt_succ_self _)
    have he : Finset.filter (fun i => r ^ i ≤ n % r ^ i + n % r ^ i)
        (Finset.Ico 1 (Nat.log r (n + n) + 1)) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun i _ hi => by have := h i; omega
    rw [he, Finset.card_empty] at key
    rw [Nat.centralBinom_eq_two_mul_choose, two_mul, ← emultiplicity_eq_zero]
    exact key.trans Nat.cast_zero
  refine Set.infinite_of_not_bddAbove fun ⟨B, hB⟩ => ?_
  have hsub : ∃ n, B + 1 ≤ n ∧ G p n ∧ G q n := by
    by_cases hq5 : 5 ≤ q
    · exact core h₂ h₄ hp3 hq5 (B + 1)
    · by_cases hp5 : 5 ≤ p
      · obtain ⟨n, hn, h1, h2⟩ := core h₄ h₂ hq3 hp5 (B + 1); exact ⟨n, hn, h2, h1⟩
      · obtain ⟨rfl⟩ : p = q := by obtain ⟨k, hk⟩ := h₂; obtain ⟨l, hl⟩ := h₄; omega
        have : B + 1 < p ^ (B + 1) := Nat.lt_pow_self (by omega)
        have h3 : p ^ (B + 1) ≤ p * p ^ (B + 1) := Nat.le_mul_of_pos_left _ (by omega)
        obtain ⟨n, hn1, hn2, hn3, _⟩ := descent h₂ h₂ (B + 1 + (B + 1)) (B + 1) (B + 1) 1 1 rfl
          (G_small (by omega)) (G_small (by omega)) (by omega) (by omega) h3 h3
        exact ⟨n, by omega, hn1, hn2⟩
  obtain ⟨n, hn, h1, h2⟩ := hsub
  have := hB (show n.centralBinom.Coprime (p * q) from Nat.Coprime.mul_right
    ((Nat.Prime.coprime_iff_not_dvd h₁).2 (hndvd h₁ h1)).symm
    ((Nat.Prime.coprime_iff_not_dvd h₃).2 (hndvd h₃ h2)).symm)
  omega
