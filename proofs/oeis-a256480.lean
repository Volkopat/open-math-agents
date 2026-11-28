import OMAStatements.S_oeis_a256480

namespace OMA.S_oeis_a256480

/-- The repunit with i digits. -/
def R : ℕ → ℕ
  | 0 => 0
  | i + 1 => 10 * R i + 1



theorem ofDigits_replicate (d k : ℕ) : Nat.ofDigits 10 (List.replicate k d) = d * R k := by
  induction k with
  | zero => simp [R]
  | succ k ih =>
    rw [List.replicate_succ', Nat.ofDigits_append, ih, List.length_replicate]
    simp only [Nat.ofDigits_cons, Nat.ofDigits_nil, R]
    have h : 10 ^ k * (d + 10 * 0) = d * 10 ^ k := by ring
    rw [h]
    have hR : ∀ j, 9 * R j + 1 = 10 ^ j := by
      intro j
      induction j with
      | zero => simp [R]
      | succ j ihj => rw [R, pow_succ]; omega
    have := hR k
    nlinarith [this]

theorem prep_eq (n d k : ℕ) : prep n d k = d * R k * 10 ^ (Nat.digits 10 n).length + n := by
  unfold prep
  rw [Nat.ofDigits_append, Nat.ofDigits_digits, ofDigits_replicate]
  ring

def n0 : ℕ :=
  100259397339064294179584070876334750061911275910953649364205338689746815564846640916475011507401

def Cs : List ℕ := [3, 7, 11, 13, 17, 31, 37, 41, 61, 73, 101, 137, 211, 241, 271, 2161, 3541,
  9091, 9901, 27961, 1676321, 2906161, 4188901, 5070721, 5882353, 39526741, 99990001]

theorem digits_n0 : (Nat.digits 10 n0).length = 96 := by
  rw [Nat.length_digits 10 n0 (by norm_num) (by decide)]
  have : Nat.log 10 n0 = 95 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by decide +kernel) (by decide +kernel)
  rw [this]

theorem R_add (i L : ℕ) : R (i + L) = 10 ^ L * R i + R L := by
  induction L with
  | zero => simp [R]
  | succ L ih =>
    rw [show i + (L + 1) = (i + L) + 1 by ring, R, ih, R, pow_succ]
    ring

set_option maxRecDepth 100000 in
theorem period_facts : ∀ C ∈ Cs, 10 ^ 240 % C = 1 ∧ R 240 % C = 0 ∧ 1 < C ∧ C < n0 := by
  decide +kernel

/-- The number for digit d and length k, as arithmetic. -/
def F (d k : ℕ) : ℕ := d * R k * 10 ^ 96 + n0

theorem periodic (d k C : ℕ) (hC : C ∈ Cs) : F d (k + 240) % C = F d k % C := by
  obtain ⟨h1, h2, h3, -⟩ := period_facts C hC
  have h10 : 10 ^ 240 ≡ 1 [MOD C] := by
    unfold Nat.ModEq
    rw [h1]
    exact (Nat.mod_eq_of_lt h3).symm
  have hR : R 240 ≡ 0 [MOD C] := by
    unfold Nat.ModEq
    rw [h2, Nat.zero_mod]
  have e : F d (k + 240) = d * (10 ^ 240 * R k + R 240) * 10 ^ 96 + n0 := by
    unfold F
    rw [R_add]
  have key : d * (10 ^ 240 * R k + R 240) * 10 ^ 96 + n0 ≡ d * (1 * R k + 0) * 10 ^ 96 + n0
      [MOD C] :=
    ((((h10.mul_right _).add hR).mul_left _).mul_right _).add_right _
  have back : d * (1 * R k + 0) * 10 ^ 96 + n0 = F d k := by
    unfold F
    ring
  rw [e]
  unfold Nat.ModEq at key
  rw [key, back]

set_option maxRecDepth 100000 in
/-- The kernel checks the first period for all nine digits. -/
theorem base : ∀ i < 240, ∀ d ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9], ∃ C ∈ Cs, F d (i + 1) % C = 0 := by
  decide +kernel

theorem cover (d : ℕ) (hd : d ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9]) (k : ℕ) (hk : 1 ≤ k) :
    ∃ C ∈ Cs, F d k % C = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h : k ≤ 240
    · have := base (k - 1) (by omega) d hd
      rwa [show k - 1 + 1 = k by omega] at this
    · obtain ⟨C, hC, h0⟩ := ih (k - 240) (by omega) (by omega)
      refine ⟨C, hC, ?_⟩
      have := periodic d (k - 240) C hC
      rw [show k - 240 + 240 = k by omega] at this
      rw [this, h0]

/-- a(n0) = 0. -/
theorem zero_term : ZeroTerm n0 := by
  intro d hd1 hd9 k hk hp
  rw [prep_eq, digits_n0] at hp
  have hmem : d ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  obtain ⟨C, hC, h0⟩ := cover d hmem k hk
  obtain ⟨-, -, hC1, hC2⟩ := period_facts C hC
  have hdvd : C ∣ d * R k * 10 ^ 96 + n0 := Nat.dvd_of_mod_eq_zero h0
  have hlt : C < d * R k * 10 ^ 96 + n0 := by omega
  rcases hp.eq_one_or_self_of_dvd C hdvd with h | h <;> omega

/-- The conjecture "if n is odd and not a multiple of 5 then a(n) is nonzero" is false. -/
theorem disproof : ¬ ∀ n : ℕ, n % 2 = 1 → n % 5 ≠ 0 → ¬ ZeroTerm n := by
  intro h
  exact h n0 (by decide) (by decide) zero_term

end OMA.S_oeis_a256480

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a256480.main) :=
  OMA.S_oeis_a256480.disproof
