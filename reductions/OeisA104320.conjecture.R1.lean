import FormalConjectures.OEIS.«104320»

/-!
# Zeros in the ternary expansion of `2 ^ n`: a verified prefix and the open tail

Sloane's conjecture says that `2 ^ n` has a ternary digit `0` for every `n > 15`. The ternary
digit of `2 ^ n` at position `j` depends only on `n` modulo `2 * 3 ^ j`, because
`2 ^ (2 * 3 ^ j) ≡ 1` modulo `3 ^ (j + 1)`. So the exponents whose lowest digits avoid `0` can be
lifted one digit at a time, as in Robert I. Saye, On Two Conjectures Concerning the Ternary
Digits of Powers of Two, J. Integer Sequences 25 (2022). The lemma `checkedPrefix` runs this
lift in the Lean kernel for all `n < 2 * 3 ^ 15`: the only such `n` with no ternary digit `0`
are `0, 1, 2, 3, 4, 15`. A leading zero is not a digit, so a zero found by the lift is only
counted when the number is long enough to have that position.

The shape of the kernel computation follows the merged reduction of
`OeisA259667.conjecture_2` by @marcusbuffett, which lifts the exponents with no ternary digit `2`.

* `H1` is the conjecture on the finite range `2 * 3 ^ 15 ≤ n ≤ 2 * 3 ^ 45`. The upper end is the
  bound used in that merged reduction for Saye's published computation.
* `H2` is the open tail `n > 2 * 3 ^ 45`.
-/

namespace TernaryZero

/-- With no digit `0`, every position below the length of `x` holds a nonzero digit. -/
private lemma nz (j : ℕ) : ∀ x : ℕ, 0 ∉ Nat.digits 3 x → 3 ^ j ≤ x → x / 3 ^ j % 3 ≠ 0 := by
  induction j with
  | zero =>
    intro x h hx
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
    rw [Nat.digits_def' (by decide) hx0, List.mem_cons, not_or] at h
    rw [pow_zero, Nat.div_one]
    exact fun h0 => h.1 h0.symm
  | succ j ih =>
    intro x h hx
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
    rw [Nat.digits_def' (by decide) hx0, List.mem_cons, not_or] at h
    have hx3 : 3 ^ j ≤ x / 3 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      simpa [pow_succ] using hx
    have := ih (x / 3) h.2 hx3
    rwa [Nat.div_div_eq_div_mul, ← pow_succ'] at this

/-- The digit at position `p` is unchanged by reduction modulo a higher power of `3`. -/
private lemma digMod (x p K : ℕ) (hp : p < K) : x % 3 ^ K / 3 ^ p % 3 = x / 3 ^ p % 3 := by
  obtain ⟨d, rfl⟩ : ∃ d, K = p + (d + 1) := ⟨K - p - 1, by omega⟩
  rw [pow_add, Nat.mod_mul_right_div_self, pow_succ,
    Nat.mod_mod_of_dvd _ (dvd_mul_left 3 (3 ^ d))]

/-- `2 ^ (2 * 3 ^ l) ≡ 1` modulo `3 ^ (l + 1)`. -/
private lemma per (l : ℕ) : 2 ^ (2 * 3 ^ l) ≡ 1 [MOD 3 ^ (l + 1)] := by
  induction l with
  | zero => decide
  | succ l ih =>
    have h1 : 1 ≤ 2 ^ (2 * 3 ^ l) := Nat.one_le_two_pow
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' h1).mp ih.symm
    have ha : 2 ^ (2 * 3 ^ l) = 1 + 3 ^ (l + 1) * c := by omega
    have e : 2 ^ (2 * 3 ^ (l + 1)) =
        1 + 3 ^ (l + 1 + 1) * (c + 3 * 3 ^ l * c ^ 2 + 3 * (3 ^ l) ^ 2 * c ^ 3) := by
      rw [show 2 * 3 ^ (l + 1) = 2 * 3 ^ l * 3 by ring, pow_mul, ha]
      ring
    rw [e]
    exact (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right (3 ^ (l + 1 + 1)) _)).add_left 1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
/-- The verified prefix: the exponents below `2 * 3 ^ 15` with no ternary digit `0`. -/
private lemma checkedPrefix (n : ℕ) (hn : n < 2 * 3 ^ 15) (h : 0 ∉ Nat.digits 3 (2 ^ n)) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 15 := by
  let M : ℕ := 3 ^ 80
  let rz : ℕ → ℕ → Bool := Nat.rec (fun _ => false)
    (fun _ next x => decide (x ≠ 0 ∧ x % 3 = 0) || next (x / 3))
  have rzs (s x : ℕ) (hr : rz s x = true) :
      ∃ j, j < s ∧ x / 3 ^ j ≠ 0 ∧ x / 3 ^ j % 3 = 0 := by
    induction s generalizing x with
    | zero =>
      change false = true at hr
      cases hr
    | succ s ih =>
      change (decide (x ≠ 0 ∧ x % 3 = 0) || rz s (x / 3)) = true at hr
      rcases Bool.or_eq_true_iff.mp hr with h1 | h2
      · have := of_decide_eq_true h1
        exact ⟨0, by omega, by simpa using this.1, by simpa using this.2⟩
      · obtain ⟨j, hj, a, b⟩ := ih _ h2
        refine ⟨j + 1, by omega, ?_, ?_⟩
        · rwa [pow_succ', ← Nat.div_div_eq_div_mul]
        · rwa [pow_succ', ← Nat.div_div_eq_div_mul]
  let exc : ℕ → Bool := fun i => decide (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 15)
  let scan : ℕ → ℕ → ℕ → ℕ → ℕ → Bool := Nat.rec
    (fun q idx v _ => exc idx || rz 48 (v / q))
    (fun _ next q idx v u =>
      if (v / q) % 3 = 0 then decide (v / q ≠ 0) || exc idx
      else [0, 1, 2].all (fun i =>
        next (q * 3) (idx + 2 * q * i) ((v * u ^ i) % M) (u ^ 3 % M)))
  have sound (dep lev idx v u t : ℕ) (bound : lev + dep ≤ 30)
      (hv : v = 2 ^ idx % M) (hu : u = 2 ^ (2 * 3 ^ lev) % M)
      (ht : t < 3 ^ dep) (good : 0 ∉ Nat.digits 3 (2 ^ (idx + 2 * 3 ^ lev * t)))
      (ok : scan dep (3 ^ lev) idx v u = true) :
      exc (idx + 2 * 3 ^ lev * t) = true := by
    induction dep generalizing lev idx v u t with
    | zero =>
      have t0 : t = 0 := by simpa using ht
      subst t0
      simp only [Nat.mul_zero, Nat.add_zero] at good ⊢
      change (exc idx || rz 48 (v / 3 ^ lev)) = true at ok
      rcases Bool.or_eq_true_iff.mp ok with h1 | h2
      · exact h1
      · exfalso
        obtain ⟨j, hj, hne, hz⟩ := rzs 48 _ h2
        rw [Nat.div_div_eq_div_mul, ← pow_add] at hne hz
        have hle : 3 ^ (lev + j) ≤ 2 ^ idx := by
          have h3 : 3 ^ (lev + j) ≤ v := by
            by_contra hlt
            exact hne (Nat.div_eq_of_lt (by omega))
          exact h3.trans (hv ▸ Nat.mod_le _ _)
        have hd := digMod (2 ^ idx) (lev + j) 80 (by omega)
        rw [← hv, hz] at hd
        exact nz _ _ good hle hd.symm
    | succ dep ih =>
      have hpow : 2 ^ (idx + 2 * 3 ^ lev * t) ≡ 2 ^ idx [MOD 3 ^ (lev + 1)] := by
        have := ((per lev).pow t).mul_left (2 ^ idx)
        simpa [pow_add, pow_mul] using this
      change (if (v / 3 ^ lev) % 3 = 0 then decide (v / 3 ^ lev ≠ 0) || exc idx
        else [0, 1, 2].all (fun i =>
          scan dep (3 ^ lev * 3) (idx + 2 * 3 ^ lev * i) ((v * u ^ i) % M) (u ^ 3 % M))) = true
        at ok
      by_cases hd : (v / 3 ^ lev) % 3 = 0
      · rw [if_pos hd] at ok
        have hdig : 2 ^ (idx + 2 * 3 ^ lev * t) / 3 ^ lev % 3 = 0 := by
          have e1 : 2 ^ (idx + 2 * 3 ^ lev * t) / 3 ^ lev % 3
              = 2 ^ (idx + 2 * 3 ^ lev * t) % 3 ^ (lev + 1) / 3 ^ lev := by
            rw [pow_succ, Nat.mod_mul_right_div_self]
          have e2 : 2 ^ idx / 3 ^ lev % 3 = 2 ^ idx % 3 ^ (lev + 1) / 3 ^ lev := by
            rw [pow_succ, Nat.mod_mul_right_div_self]
          have e3 := digMod (2 ^ idx) lev 80 (by omega)
          rw [← hv, hd] at e3
          rw [e1, hpow, ← e2, ← e3]
        have key : 3 ^ lev ≤ 2 ^ (idx + 2 * 3 ^ lev * t) → False :=
          fun hle => nz _ _ good hle hdig
        rcases Bool.or_eq_true_iff.mp ok with h1 | h2
        · exfalso
          apply key
          have hne : v / 3 ^ lev ≠ 0 := of_decide_eq_true h1
          have h3 : 3 ^ lev ≤ v := by
            by_contra hlt
            exact hne (Nat.div_eq_of_lt (by omega))
          calc 3 ^ lev ≤ v := h3
            _ ≤ 2 ^ idx := hv ▸ Nat.mod_le _ _
            _ ≤ 2 ^ (idx + 2 * 3 ^ lev * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
        · rcases Nat.eq_zero_or_pos t with rfl | htpos
          · simpa using h2
          · exfalso
            apply key
            calc 3 ^ lev ≤ 4 ^ lev := Nat.pow_le_pow_left (by norm_num) lev
              _ ≤ 4 ^ 3 ^ lev := Nat.pow_le_pow_right (by norm_num) (Nat.lt_pow_self (by norm_num)).le
              _ = 2 ^ (2 * 3 ^ lev) := by rw [pow_mul]; norm_num
              _ ≤ 2 ^ (idx + 2 * 3 ^ lev * t) :=
                Nat.pow_le_pow_right (by norm_num)
                  ((Nat.le_mul_of_pos_right _ htpos).trans (Nat.le_add_left _ _))
      · rw [if_neg hd] at ok
        simp only [List.all_eq_true] at ok
        have imem : t % 3 ∈ ([0, 1, 2] : List ℕ) := by
          have : t % 3 < 3 := Nat.mod_lt _ (by norm_num)
          simp
          omega
        have next := ok (t % 3) imem
        have idxEq : idx + 2 * 3 ^ lev * t
            = (idx + 2 * 3 ^ lev * (t % 3)) + 2 * 3 ^ (lev + 1) * (t / 3) := by
          rw [pow_succ]
          linear_combination (2 * 3 ^ lev) * (Nat.mod_add_div t 3).symm
        have vi : (v * u ^ (t % 3)) % M = 2 ^ (idx + 2 * 3 ^ lev * (t % 3)) % M := by
          rw [hv, hu, pow_add, pow_mul 2 (2 * 3 ^ lev) (t % 3)]
          exact (Nat.mod_modEq _ _).mul ((Nat.mod_modEq _ _).pow _)
        have ui : u ^ 3 % M = 2 ^ (2 * 3 ^ (lev + 1)) % M := by
          rw [hu, show 2 * 3 ^ (lev + 1) = 2 * 3 ^ lev * 3 by ring, pow_mul 2 (2 * 3 ^ lev) 3]
          exact (Nat.mod_modEq _ _).pow 3
        have ht1 : t / 3 < 3 ^ dep := by
          rw [pow_succ] at ht
          omega
        rw [idxEq] at good ⊢
        exact ih (lev + 1) _ _ _ (t / 3) (by omega) vi ui ht1 good
          (by rw [pow_succ 3 lev]; exact next)
  have all : scan 15 1 0 1 4 = true ∧ scan 15 1 1 2 4 = true := by
    dsimp only [scan, rz, exc, M]
    decide +kernel
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have hsplit : n = n % 2 + 2 * 3 ^ 0 * (n / 2) := by omega
  have ht : n / 2 < 3 ^ 15 := by omega
  rw [hsplit] at h
  have res : exc (n % 2 + 2 * 3 ^ 0 * (n / 2)) = true := by
    rcases hmod with h0 | h1
    · rw [h0] at h ⊢
      exact sound 15 0 0 1 4 (n / 2) (by decide) (by decide) (by decide) ht h all.1
    · rw [h1] at h ⊢
      exact sound 15 0 1 2 4 (n / 2) (by decide) (by decide) (by decide) ht h all.2
  rw [← hsplit] at res
  exact of_decide_eq_true res

end TernaryZero

namespace OMA.R_OeisA104320_conjecture_R1

/-- The conjecture on the finite range `2 * 3 ^ 15 ≤ n ≤ 2 * 3 ^ 45`. -/
def H1 : Prop := ∀ n : ℕ, 2 * 3 ^ 15 ≤ n → n ≤ 2 * 3 ^ 45 → 0 < OeisA104320.a n

/-- The open tail: `2 ^ n` has a ternary digit `0` for every `n > 2 * 3 ^ 45`. -/
def H2 : Prop := ∀ n : ℕ, 2 * 3 ^ 45 < n → 0 < OeisA104320.a n

theorem main : H1 → H2 → type_of% @OeisA104320.conjecture := by
  intro h1 h2 n hn
  by_cases hlt : n < 2 * 3 ^ 15
  · by_contra hz
    have hc : OeisA104320.a n = 0 := by omega
    have h0 : 0 ∉ Nat.digits 3 (2 ^ n) := List.count_eq_zero.mp hc
    have := TernaryZero.checkedPrefix n hlt h0
    omega
  · by_cases hle : n ≤ 2 * 3 ^ 45
    · exact h1 n (by omega) hle
    · exact h2 n (by omega)

end OMA.R_OeisA104320_conjecture_R1
