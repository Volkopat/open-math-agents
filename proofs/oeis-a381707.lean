import OMAStatements.S_oeis_a381707
import Mathlib

namespace OMA.A381707Proof

open OMA.S_oeis_a381707

/-! ## The Collatz side -/

theorem T_odd {v : ℕ} (h : v % 2 = 1) : T v = (3 * v + 1) / 2 := by
  unfold T
  rw [if_pos h]

theorem T_even {v : ℕ} (h : v % 2 = 0) : T v = v / 2 := by
  unfold T
  rw [if_neg (show ¬(v % 2 = 1) by omega)]

/-- After `j ≤ n` rises: `2^j (T^[j] x + 1) = 3^j (x + 1)`. -/
theorem rises (n x : ℕ) (h : ∀ j < n, T^[j] x % 2 = 1) :
    ∀ j ≤ n, 2 ^ j * (T^[j] x + 1) = 3 ^ j * (x + 1) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hodd := h j (by omega)
    have ih' := ih (by omega)
    rw [Function.iterate_succ_apply', T_odd hodd]
    generalize T^[j] x = v at hodd ih' ⊢
    have e : 2 * ((3 * v + 1) / 2 + 1) = 3 * (v + 1) := by omega
    generalize (3 * v + 1) / 2 = w at e ⊢
    calc 2 ^ (j + 1) * (w + 1) = 2 ^ j * (2 * (w + 1)) := by ring
      _ = 2 ^ j * (3 * (v + 1)) := by rw [e]
      _ = 3 * (2 ^ j * (v + 1)) := by ring
      _ = 3 ^ (j + 1) * (x + 1) := by rw [ih']; ring

theorem ge_of_rel {j v x : ℕ} (h : 2 ^ j * (v + 1) = 3 ^ j * (x + 1)) : x ≤ v := by
  have h1 : 2 ^ j ≤ 3 ^ j := Nat.pow_le_pow_left (by norm_num) j
  have h2 : 2 ^ j * (x + 1) ≤ 2 ^ j * (v + 1) := by
    rw [h]
    exact Nat.mul_le_mul h1 le_rfl
  have h3 := Nat.le_of_mul_le_mul_left h2 (by positivity)
  omega

theorem two_pow_succ_le_three_pow {n : ℕ} (hn : 2 ≤ n) : 2 ^ (n + 1) ≤ 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ 2 (k + 1), pow_succ 3 k]
    omega

theorem three_pow_mod_four (n : ℕ) : 3 ^ n % 4 = if n % 2 = 0 then 1 else 3 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    split_ifs <;> omega

theorem mod_aux {x P t r : ℕ} (hP : 0 < P) (ht : x + 1 = P * t) (hr : t % 4 = r) (hr1 : 1 ≤ r) :
    x % (4 * P) + 1 = P * r := by
  have hr4 : r < 4 := by omega
  obtain ⟨q, rfl⟩ : ∃ q, t = 4 * q + r := ⟨t / 4, by omega⟩
  have e1 : P * (4 * q + r) = 4 * P * q + P * r := by ring
  have e2 : 0 < P * r := Nat.mul_pos hP hr1
  have e3 : P * r ≤ P * 3 := Nat.mul_le_mul le_rfl (by omega)
  have hx : x = (P * r - 1) + 4 * P * q := by omega
  rw [hx, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show P * r - 1 < 4 * P by omega)]
  omega

/-- The residue of any start of a unimodal glide with `n ≥ 2` rises. -/
theorem residue {n x : ℕ} (hn : 2 ≤ n) (hx : UnimodalGlide n x) :
    x % 2 ^ (n + 2) + 1 = 2 ^ n * (if n % 2 = 0 then 1 else 3) := by
  obtain ⟨hr, m, hf, hlt, hge⟩ := hx
  have key := rises n x hr n le_rfl
  have hlow := ge_of_rel key
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.add_zero] at hlt
    omega
  have hven : T^[n] x % 2 = 0 := hf n le_rfl (by omega)
  have hstep : T^[n + 1] x = T^[n] x / 2 := by
    rw [Function.iterate_succ_apply', T_even hven]
  have hP : 0 < 2 ^ n := by positivity
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [hstep] at hlt
    have h3 : 2 * 2 ^ n ≤ 3 ^ n := by
      have := two_pow_succ_le_three_pow hn
      rw [pow_succ] at this
      omega
    generalize T^[n] x = v at key hven hlt
    generalize 2 ^ n = P at key h3 hP
    generalize 3 ^ n = Q at key h3
    have hv : v + 2 ≤ 2 * x := by omega
    have h5 : 2 * P * (x + 1) ≤ Q * (x + 1) := Nat.mul_le_mul h3 le_rfl
    have h6 : P * (v + 2) ≤ P * (2 * x) := Nat.mul_le_mul le_rfl hv
    nlinarith
  have hv2 : T^[n] x / 2 % 2 = 0 := by
    have := hf (n + 1) (by omega) (by omega)
    rwa [hstep] at this
  have hv4 : T^[n] x % 4 = 0 := by omega
  have hcop : Nat.Coprime (2 ^ n) (3 ^ n) := Nat.Coprime.pow n n (by norm_num)
  have hdvd : 2 ^ n ∣ x + 1 := hcop.dvd_of_dvd_mul_left (Dvd.intro _ key)
  obtain ⟨t, ht⟩ := hdvd
  have hvt : T^[n] x + 1 = 3 ^ n * t := by
    have h' : 2 ^ n * (T^[n] x + 1) = 2 ^ n * (3 ^ n * t) := by
      rw [key, ht]
      ring
    exact Nat.eq_of_mul_eq_mul_left hP h'
  have h3t : 3 ^ n * t % 4 = 1 := by omega
  have ht4 : t % 4 = if n % 2 = 0 then 1 else 3 := by
    rw [Nat.mul_mod, three_pow_mod_four] at h3t
    split_ifs at h3t ⊢ <;> omega
  have hpow : 2 ^ (n + 2) = 4 * 2 ^ n := by
    rw [pow_add]
    ring
  rw [hpow]
  split_ifs at ht4 ⊢
  · exact mod_aux hP ht ht4 (by norm_num)
  · exact mod_aux hP ht ht4 (by norm_num)

/-- For every `n ≥ 1` some `x` starts a unimodal glide with exactly `n` increases. -/
theorem nonempty_glide (n : ℕ) (hn : 1 ≤ n) : ∃ x, UnimodalGlide n x := by
  have hcop : Nat.Coprime (3 ^ n) (2 ^ (n + 1)) := Nat.Coprime.pow n (n + 1) (by norm_num)
  have hP : 0 < 2 ^ n := by positivity
  have h1 : 1 < 2 ^ (n + 1) := by
    rw [pow_succ]
    omega
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, Nat.mul_zero, Nat.zero_mod] at ht
      omega
    · exact h
  obtain ⟨c, hc⟩ : ∃ c, 3 ^ n * t = 2 ^ (n + 1) * c + 1 := by
    refine ⟨3 ^ n * t / 2 ^ (n + 1), ?_⟩
    have := Nat.div_add_mod (3 ^ n * t) (2 ^ (n + 1))
    rw [ht] at this
    exact this.symm
  obtain ⟨x, hx⟩ : ∃ x, x + 1 = 2 ^ n * t :=
    ⟨2 ^ n * t - 1, by have := Nat.mul_pos hP ht0; omega⟩
  have hrise : ∀ j ≤ n, T^[j] x + 1 = 3 ^ j * 2 ^ (n - j) * t := by
    intro j
    induction j with
    | zero => intro _; simp [hx]
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      obtain ⟨d, hd1, hd2⟩ : ∃ d, n - j = d + 1 ∧ n - (j + 1) = d := ⟨n - (j + 1), by omega, rfl⟩
      rw [hd1, pow_succ] at ih'
      rw [hd2, Function.iterate_succ_apply']
      have e1 : 3 ^ j * (2 ^ d * 2) * t = 2 * (3 ^ j * 2 ^ d * t) := by ring
      have e2 : 3 ^ (j + 1) * 2 ^ d * t = 3 * (3 ^ j * 2 ^ d * t) := by ring
      rw [e1] at ih'
      rw [e2]
      generalize 3 ^ j * 2 ^ d * t = w at ih' ⊢
      generalize T^[j] x = v at ih' ⊢
      have hodd : v % 2 = 1 := by omega
      rw [T_odd hodd]
      omega
  have hodd : ∀ j < n, T^[j] x % 2 = 1 := by
    intro j hj
    have h1 := hrise j hj.le
    obtain ⟨d, hd⟩ : ∃ d, n - j = d + 1 := ⟨n - j - 1, by omega⟩
    rw [hd, pow_succ] at h1
    have e : 3 ^ j * (2 ^ d * 2) * t = 2 * (3 ^ j * 2 ^ d * t) := by ring
    rw [e] at h1
    omega
  have hlow : ∀ j ≤ n, x ≤ T^[j] x := by
    intro j hj
    have h1 := hrise j hj
    have h2 : 2 ^ j * 2 ^ (n - j) = 2 ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hj]
    have h3 : 2 ^ j ≤ 3 ^ j := Nat.pow_le_pow_left (by norm_num) j
    have h4 : 2 ^ j * 2 ^ (n - j) * t ≤ 3 ^ j * 2 ^ (n - j) * t :=
      Nat.mul_le_mul (Nat.mul_le_mul h3 le_rfl) le_rfl
    rw [h2] at h4
    omega
  have hv : T^[n] x = 2 ^ (n + 1) * c := by
    have h1 := hrise n le_rfl
    rw [Nat.sub_self, pow_zero, Nat.mul_one, hc] at h1
    omega
  have hfall : ∀ i ≤ n + 1, T^[n + i] x = 2 ^ (n + 1 - i) * c := by
    intro i
    induction i with
    | zero => intro _; simpa using hv
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      obtain ⟨d, hd1, hd2⟩ : ∃ d, n + 1 - i = d + 1 ∧ n + 1 - (i + 1) = d :=
        ⟨n + 1 - (i + 1), by omega, rfl⟩
      rw [hd1, pow_succ] at ih'
      rw [hd2, show n + (i + 1) = n + i + 1 by omega, Function.iterate_succ_apply', ih']
      have e : 2 ^ d * 2 * c = 2 * (2 ^ d * c) := by ring
      rw [e]
      generalize 2 ^ d * c = w
      rw [T_even (show 2 * w % 2 = 0 by omega)]
      omega
  have hcx : c < x := by
    by_contra hcon
    have hP2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hQ : 3 ^ n ≤ 2 ^ n * 2 ^ n := by
      rw [← mul_pow]
      exact Nat.pow_le_pow_left (by norm_num) n
    rw [pow_succ] at hc
    generalize 2 ^ n = P at hP2 hQ hc hx
    generalize 3 ^ n = Q at hQ hc
    have h1 : Q * t ≤ P * P * t := Nat.mul_le_mul hQ le_rfl
    have h2 : P * P * 1 ≤ P * P * t := Nat.mul_le_mul le_rfl ht0
    have h3 : 2 * P ≤ P * P := Nat.mul_le_mul hP2 le_rfl
    have h4 : 2 * P * (x + 1) ≤ 2 * P * (c + 1) := Nat.mul_le_mul le_rfl (by omega)
    rw [hx] at h4
    nlinarith
  have hlast : T^[n + (n + 1)] x < x := by
    rw [hfall (n + 1) le_rfl, Nat.sub_self, pow_zero, Nat.one_mul]
    exact hcx
  have hex : ∃ i, T^[n + i] x < x := ⟨n + 1, hlast⟩
  refine ⟨x, ?_⟩
  unfold UnimodalGlide
  refine ⟨hodd, Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · intro j hj1 hj2
    have hm : Nat.find hex ≤ n + 1 := Nat.find_min' hex hlast
    obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
    rw [hfall i (by omega)]
    obtain ⟨d, hd⟩ : ∃ d, n + 1 - i = d + 1 := ⟨n - i, by omega⟩
    rw [hd, pow_succ]
    have e : 2 ^ d * 2 * c = 2 * (2 ^ d * c) := by ring
    rw [e]
    omega
  · intro j hj
    rcases Nat.lt_or_ge j n with h | h
    · exact hlow j h.le
    · obtain ⟨i, rfl⟩ : ∃ i, j = n + i := ⟨j - n, by omega⟩
      have := Nat.find_min hex (show i < Nat.find hex by omega)
      omega

theorem a_mem (n : ℕ) (hn : 1 ≤ n) : UnimodalGlide n (A381707 n) := by
  obtain ⟨x, hx⟩ := nonempty_glide n hn
  exact Nat.sInf_mem (s := {x : ℕ | UnimodalGlide n x}) ⟨x, hx⟩

theorem glide_one_five : UnimodalGlide 1 5 := by
  unfold UnimodalGlide
  refine ⟨?_, 1, ?_, ?_, ?_⟩
  · intro j hj
    obtain rfl : j = 0 := by omega
    decide
  · intro j hj1 hj2
    obtain rfl : j = 1 := by omega
    decide
  · decide
  · intro j hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · decide
    · decide

theorem not_glide_small (x : ℕ) (hx : x < 5) : ¬UnimodalGlide 1 x := by
  rintro ⟨hr, m, hf, hlt, hge⟩
  have h0 := hr 0 (by norm_num)
  rw [Function.iterate_zero_apply] at h0
  rcases (show x = 1 ∨ x = 3 by omega) with rfl | rfl
  · rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with rfl | rfl | hm
    · exact absurd hlt (by decide)
    · exact absurd hlt (by decide)
    · exact absurd (hf 2 (by omega) (by omega)) (by decide)
  · rcases (show m = 0 ∨ 1 ≤ m by omega) with rfl | hm
    · exact absurd hlt (by decide)
    · exact absurd (hf 1 le_rfl (by omega)) (by decide)

theorem a_one : A381707 1 = 5 := by
  unfold A381707
  apply le_antisymm
  · exact Nat.sInf_le glide_one_five
  · by_contra h
    have hmem : sInf {x : ℕ | UnimodalGlide 1 x} ∈ {x : ℕ | UnimodalGlide 1 x} :=
      Nat.sInf_mem ⟨5, glide_one_five⟩
    exact not_glide_small _ (by omega) hmem

/-! ## The Rule 641 side -/

def step641 (f : ℤ × ℤ → Bool) (p : ℤ × ℤ) : Bool :=
  Nat.testBit 641 (2 * onNeighbours f p + (f p).toNat)

theorem stage_succ (k : ℕ) : stage (k + 1) = step641 (stage k) := rfl

def cfg1 (p : ℤ × ℤ) : Bool :=
  decide (2 ≤ p.1 ∨ p.1 ≤ -2 ∨ 2 ≤ p.2 ∨ p.2 ≤ -2 ∨ (p.1 ≠ 0 ∧ p.2 ≠ 0))

def cfgE (p : ℤ × ℤ) : Bool :=
  decide (2 ≤ p.1 ∨ p.1 ≤ -2 ∨ 2 ≤ p.2 ∨ p.2 ≤ -2 ∨ (p.1 = 0 ∧ p.2 = 0))

def cfgZ (p : ℤ × ℤ) : Bool :=
  decide (2 ≤ p.1 ∨ p.1 ≤ -2 ∨ 2 ≤ p.2 ∨ p.2 ≤ -2)

theorem cfg1_mk (a b : ℤ) :
    cfg1 (a, b) = decide (2 ≤ a ∨ a ≤ -2 ∨ 2 ≤ b ∨ b ≤ -2 ∨ (a ≠ 0 ∧ b ≠ 0)) := rfl

theorem cfgE_mk (a b : ℤ) :
    cfgE (a, b) = decide (2 ≤ a ∨ a ≤ -2 ∨ 2 ≤ b ∨ b ≤ -2 ∨ (a = 0 ∧ b = 0)) := rfl

theorem cfgZ_mk (a b : ℤ) : cfgZ (a, b) = decide (2 ≤ a ∨ a ≤ -2 ∨ 2 ≤ b ∨ b ≤ -2) := rfl

theorem or5 {A B C D E : Prop} (h : A ∨ B ∨ C ∨ D) : A ∨ B ∨ C ∨ D ∨ E := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem cfg1_out (a b : ℤ) (h : 2 ≤ a ∨ a ≤ -2 ∨ 2 ≤ b ∨ b ≤ -2) : cfg1 (a, b) = true := by
  rw [cfg1_mk]
  exact decide_eq_true (or5 h)

theorem cfgE_out (a b : ℤ) (h : 2 ≤ a ∨ a ≤ -2 ∨ 2 ≤ b ∨ b ≤ -2) : cfgE (a, b) = true := by
  rw [cfgE_mk]
  exact decide_eq_true (or5 h)

theorem cfgZ_out (a b : ℤ) (h : 2 ≤ a ∨ a ≤ -2 ∨ 2 ≤ b ∨ b ≤ -2) : cfgZ (a, b) = true := by
  rw [cfgZ_mk]
  exact decide_eq_true h

theorem inB (a b : ℤ) (h : ¬(2 ≤ a ∨ a ≤ -2 ∨ 2 ≤ b ∨ b ≤ -2)) :
    (a = -1 ∨ a = 0 ∨ a = 1) ∧ (b = -1 ∨ b = 0 ∨ b = 1) := by
  omega

/-- A cell outside the 3x3 box whose outside-the-box neighbours are all ON stays ON: it has at least 3 ON
neighbours, and indices 7 and 9 are set bits of 641. -/
theorem step_out (f : ℤ × ℤ → Bool)
    (hf : ∀ a b : ℤ, (2 ≤ a ∨ a ≤ -2 ∨ 2 ≤ b ∨ b ≤ -2) → f (a, b) = true)
    (a b : ℤ) (h : 2 ≤ a ∨ a ≤ -2 ∨ 2 ≤ b ∨ b ≤ -2) : step641 f (a, b) = true := by
  dsimp only [step641, onNeighbours]
  rw [hf a b h]
  rcases h with h | h | h | h
  · rw [hf (a + 1) b (by omega), hf a (b + 1) (by omega), hf a (b - 1) (by omega)]
    cases f (a - 1, b) <;> decide
  · rw [hf (a - 1) b (by omega), hf a (b + 1) (by omega), hf a (b - 1) (by omega)]
    cases f (a + 1, b) <;> decide
  · rw [hf (a + 1) b (by omega), hf (a - 1) b (by omega), hf a (b + 1) (by omega)]
    cases f (a, b - 1) <;> decide
  · rw [hf (a + 1) b (by omega), hf (a - 1) b (by omega), hf a (b - 1) (by omega)]
    cases f (a, b + 1) <;> decide

theorem stage0_off (a b : ℤ) (h : a ≠ 0 ∨ b ≠ 0) : stage 0 (a, b) = false := by
  show decide ((a, b) = ((0 : ℤ), (0 : ℤ))) = false
  apply decide_eq_false
  intro hab
  rw [Prod.mk.injEq] at hab
  omega

theorem step0_eq (a b : ℤ) : step641 (stage 0) (a, b) = cfg1 (a, b) := by
  by_cases h : 2 ≤ a ∨ a ≤ -2 ∨ 2 ≤ b ∨ b ≤ -2
  · rw [cfg1_out a b h]
    dsimp only [step641, onNeighbours]
    rw [stage0_off a b (by omega), stage0_off (a + 1) b (by omega), stage0_off (a - 1) b (by omega),
      stage0_off a (b + 1) (by omega), stage0_off a (b - 1) (by omega)]
    decide
  · rcases inB a b h with ⟨rfl | rfl | rfl, rfl | rfl | rfl⟩ <;> decide

theorem step1_eq (a b : ℤ) : step641 cfg1 (a, b) = cfgE (a, b) := by
  by_cases h : 2 ≤ a ∨ a ≤ -2 ∨ 2 ≤ b ∨ b ≤ -2
  · rw [cfgE_out a b h, step_out cfg1 cfg1_out a b h]
  · rcases inB a b h with ⟨rfl | rfl | rfl, rfl | rfl | rfl⟩ <;> decide

theorem stepE_eq (a b : ℤ) : step641 cfgE (a, b) = cfgZ (a, b) := by
  by_cases h : 2 ≤ a ∨ a ≤ -2 ∨ 2 ≤ b ∨ b ≤ -2
  · rw [cfgZ_out a b h, step_out cfgE cfgE_out a b h]
  · rcases inB a b h with ⟨rfl | rfl | rfl, rfl | rfl | rfl⟩ <;> decide

theorem stepZ_eq (a b : ℤ) : step641 cfgZ (a, b) = cfgE (a, b) := by
  by_cases h : 2 ≤ a ∨ a ≤ -2 ∨ 2 ≤ b ∨ b ≤ -2
  · rw [cfgE_out a b h, step_out cfgZ cfgZ_out a b h]
  · rcases inB a b h with ⟨rfl | rfl | rfl, rfl | rfl | rfl⟩ <;> decide

theorem stage_one : stage 1 = cfg1 := by
  show step641 (stage 0) = cfg1
  funext p
  obtain ⟨a, b⟩ := p
  exact step0_eq a b

theorem stage_two : stage 2 = cfgE := by
  show step641 (stage 1) = cfgE
  rw [stage_one]
  funext p
  obtain ⟨a, b⟩ := p
  exact step1_eq a b

/-- From stage 2 on, the stages alternate: origin plus the outside of the box at even stages, the outside of the
box only at odd stages. -/
theorem stage_even_odd (k : ℕ) (hk : 2 ≤ k) : stage k = if k % 2 = 0 then cfgE else cfgZ := by
  induction k, hk using Nat.le_induction with
  | base => rw [stage_two, if_pos (show 2 % 2 = 0 by norm_num)]
  | succ k hk ih =>
    rw [stage_succ, ih]
    by_cases h : k % 2 = 0
    · rw [if_pos h, if_neg (show ¬((k + 1) % 2 = 0) by omega)]
      funext p
      obtain ⟨a, b⟩ := p
      exact stepE_eq a b
    · rw [if_neg h, if_pos (show (k + 1) % 2 = 0 by omega)]
      funext p
      obtain ⟨a, b⟩ := p
      exact stepZ_eq a b

def tailSum (k : ℕ) : ℕ := ∑ i ∈ Finset.range (k + 1), if 2 ≤ i then 2 ^ (k - i) else 0

theorem tailSum_succ (k : ℕ) : tailSum (k + 1) = 2 * tailSum k + (if 2 ≤ k + 1 then 1 else 0) := by
  unfold tailSum
  rw [Finset.sum_range_succ _ (k + 1), Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < k + 1 := Finset.mem_range.mp hi
    obtain ⟨d, hd1, hd2⟩ : ∃ d, k + 1 - i = d + 1 ∧ k - i = d := ⟨k - i, by omega, rfl⟩
    rw [hd1, hd2, pow_succ]
    split_ifs <;> ring
  · simp

theorem tailSum_closed (k : ℕ) (hk : 1 ≤ k) : tailSum k + 1 = 2 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => simp [tailSum, Finset.sum_range_succ]
  | succ k hk ih =>
    rw [tailSum_succ, if_pos (show 2 ≤ k + 1 by omega)]
    obtain ⟨d, hd1, hd2⟩ : ∃ d, k + 1 - 1 = d + 1 ∧ k - 1 = d := ⟨k - 1, by omega, rfl⟩
    rw [hd1, pow_succ]
    rw [hd2] at ih
    omega

theorem cfgE_term (k i : ℕ) : (if cfgE ((i : ℤ), 0) = true then 2 ^ (k - i) else 0) =
    (if 2 ≤ i then 2 ^ (k - i) else 0) + (if i = 0 then 2 ^ k else 0) := by
  rcases Nat.lt_or_ge i 2 with h | h
  · rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · have hS : cfgE (((0 : ℕ) : ℤ), 0) = true := by decide
      rw [if_pos hS]
      simp
    · have hS : cfgE (((1 : ℕ) : ℤ), 0) = false := by decide
      rw [hS]
      simp
  · have hS : cfgE ((i : ℤ), 0) = true := by
      rw [cfgE_mk]
      exact decide_eq_true (Or.inl (by omega))
    rw [if_pos hS, if_pos h, if_neg (show i ≠ 0 by omega), Nat.add_zero]

theorem cfgZ_term (k i : ℕ) : (if cfgZ ((i : ℤ), 0) = true then 2 ^ (k - i) else 0) =
    (if 2 ≤ i then 2 ^ (k - i) else 0) := by
  by_cases h : 2 ≤ i
  · have hS : cfgZ ((i : ℤ), 0) = true := by
      rw [cfgZ_mk]
      exact decide_eq_true (Or.inl (by omega))
    rw [if_pos hS, if_pos h]
  · have hS : cfgZ ((i : ℤ), 0) = false := by
      rw [cfgZ_mk]
      exact decide_eq_false (by omega)
    rw [hS, if_neg h]
    simp

theorem A283507_ge2 (k : ℕ) (hk : 2 ≤ k) :
    A283507 k = tailSum k + (if k % 2 = 0 then 2 ^ k else 0) := by
  unfold A283507
  rw [stage_even_odd k hk]
  by_cases he : k % 2 = 0
  · rw [if_pos he, if_pos he]
    simp only [cfgE_term, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', if_pos (show (0 : ℕ) ∈ Finset.range (k + 1) by simp)]
    rfl
  · rw [if_neg he, if_neg he, Nat.add_zero]
    simp only [cfgZ_term]
    rfl

theorem A283507_value (n : ℕ) (hn : 1 ≤ n) :
    A283507 (n + 1) + 1 = 2 ^ n * (if n % 2 = 0 then 1 else 3) := by
  rw [A283507_ge2 (n + 1) (by omega)]
  have hQ := tailSum_closed (n + 1) (by omega)
  rw [Nat.add_sub_cancel] at hQ
  rw [pow_succ]
  split_ifs <;> omega

end OMA.A381707Proof

open OMA.S_oeis_a381707 OMA.A381707Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a381707.main := by
  intro n hn
  have hA := A283507_value n hn
  have hR : A381707 n % 2 ^ (n + 2) + 1 = 2 ^ n * (if n % 2 = 0 then 1 else 3) := by
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      rw [a_one]
      decide
    · exact residue h (a_mem n hn)
  have := hR.trans hA.symm
  omega
