import OMAStatements.S_mo_455844

section Helpers

open OMA.S_mo_455844

private lemma blue_zero : blue 0 = 0 := by
  simp [blue]

private lemma blue_bit (b : Bool) (n : ℕ) :
    blue (Nat.bit b n) = blue n ^^^ Nat.bit b (blue n) := by
  unfold blue
  rw [Nat.binaryRec_eq _ _ (Or.inl (by simp)), Nat.bit_val]

private lemma blue_xor (a b : ℕ) : blue (a ^^^ b) = blue a ^^^ blue b := by
  induction a using Nat.binaryRec generalizing b with
  | zero => simp [blue_zero]
  | bit ba a ih =>
    induction b using Nat.binaryRec with
    | zero => simp [blue_zero]
    | bit bb b =>
      rw [Nat.xor_bit, blue_bit, ih b, blue_bit, blue_bit, ← Nat.xor_bit]
      ac_rfl

private lemma blue_blue (n : ℕ) : blue (blue n) = n := by
  induction n using Nat.binaryRec with
  | zero => simp [blue_zero]
  | bit b n ih =>
    rw [blue_bit, blue_xor, ih, blue_bit, ih, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

private lemma blue_lt_two_pow : ∀ k n : ℕ, n < 2 ^ k → blue n < 2 ^ k := by
  intro k
  induction k with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by omega
    simp [blue_zero]
  | succ k ih =>
    intro n hn
    rw [← Nat.bit_bodd_div2 n] at hn ⊢
    rw [Nat.bit_lt_two_pow_succ_iff] at hn
    rw [blue_bit]
    have h1 : blue n.div2 < 2 ^ k := ih n.div2 hn
    have h2 : Nat.bit n.bodd (blue n.div2) < 2 ^ (k + 1) :=
      Nat.bit_lt_two_pow_succ_iff.mpr h1
    have h1' : blue n.div2 < 2 ^ (k + 1) :=
      lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))
    exact Nat.bitwise_lt_two_pow h1' h2

private lemma blue_ge_two_pow {k n : ℕ} (h : 2 ^ k ≤ n) : 2 ^ k ≤ blue n := by
  by_contra hlt
  push Not at hlt
  have hbb := blue_lt_two_pow k (blue n) hlt
  rw [blue_blue] at hbb
  omega

private lemma two_pow_xor_eq_add : ∀ k y : ℕ, y < 2 ^ k → 2 ^ k ^^^ y = 2 ^ k + y := by
  intro k
  induction k with
  | zero =>
    intro y hy
    obtain rfl : y = 0 := by omega
    simp
  | succ k ih =>
    intro y hy
    rw [← Nat.bit_bodd_div2 y] at hy ⊢
    rw [Nat.bit_lt_two_pow_succ_iff] at hy
    have hpow : 2 ^ (k + 1) = Nat.bit false (2 ^ k) := by
      rw [Nat.bit_val, Nat.pow_succ]; simp [Nat.mul_comm]
    rw [hpow, Nat.xor_bit]
    simp only [Bool.false_bne]
    rw [ih y.div2 hy]
    simp only [Nat.bit_val, Bool.toNat_false, Nat.add_zero]
    omega

private lemma high_bit_xor_lt {k x y : ℕ} (hx1 : 2 ^ k ≤ x) (hx2 : x < 2 ^ (k + 1))
    (hy1 : 2 ^ k ≤ y) (hy2 : y < 2 ^ (k + 1)) : x ^^^ y < 2 ^ k := by
  have hx' : x - 2 ^ k < 2 ^ k := by rw [Nat.pow_succ] at hx2; omega
  have hy' : y - 2 ^ k < 2 ^ k := by rw [Nat.pow_succ] at hy2; omega
  have hx : x = 2 ^ k ^^^ (x - 2 ^ k) := by
    rw [two_pow_xor_eq_add k _ hx']; omega
  have hy : y = 2 ^ k ^^^ (y - 2 ^ k) := by
    rw [two_pow_xor_eq_add k _ hy']; omega
  rw [hx, hy, Nat.xor_comm (2 ^ k) (x - 2 ^ k), Nat.xor_assoc,
    ← Nat.xor_assoc (2 ^ k) (2 ^ k), Nat.xor_self, Nat.zero_xor]
  exact Nat.bitwise_lt_two_pow hx' hy'

private lemma two_pow_sub_one_xor (k : ℕ) :
    (2 ^ k - 1) ^^^ (2 * (2 ^ k - 1) + 1) = 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hpow : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hm : 2 ^ (k + 1) - 1 = Nat.bit true (2 ^ k - 1) := by
      rw [Nat.bit_val, Nat.pow_succ]; simp; omega
    have hm2 : 2 * (2 ^ (k + 1) - 1) + 1 = Nat.bit true (2 ^ (k + 1) - 1) := by
      rw [Nat.bit_val]; simp
    rw [hm2, hm, Nat.xor_bit]
    simp only [bne_self_eq_false]
    rw [Nat.bit_val true (2 ^ k - 1)]
    simp only [Bool.toNat_true]
    rw [ih, Nat.bit_val, Nat.pow_succ]
    simp [Nat.mul_comm]

private lemma leadingPower_bounds {n : ℕ} (hn : 1 < n) :
    2 ≤ leadingPower n ∧ leadingPower n ≤ n ∧ n < 2 * leadingPower n ∧ 1 ≤ n.log2 := by
  have hn0 : n ≠ 0 := by omega
  have hle : leadingPower n ≤ n := Nat.log2_self_le hn0
  have hlt : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  have hlt2 : n < 2 * leadingPower n := by
    simpa [leadingPower, Nat.pow_succ, Nat.mul_comm] using hlt
  have hlog : 1 ≤ n.log2 := by
    by_contra h0
    have hlog0 : n.log2 = 0 := by omega
    rw [hlog0] at hlt
    omega
  have h2 : 2 ≤ leadingPower n := by
    calc 2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ n.log2 := Nat.pow_le_pow_right (by omega) hlog
  exact ⟨h2, hle, hlt2, hlog⟩

private lemma leadingPower_eq_of_bounds {n k : ℕ} (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1)) :
    leadingPower n = 2 ^ k := by
  have hn0 : n ≠ 0 := by
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  have hlog : n.log2 = k := (Nat.log2_eq_iff hn0).mpr ⟨h1, h2⟩
  simp [leadingPower, hlog]

private lemma g_sub_lt {n : ℕ} (hn : 1 < n) : g n - leadingPower n < leadingPower n := by
  obtain ⟨_, hle, hlt2, hlog⟩ := leadingPower_bounds hn
  set k := n.log2
  set m := k - 1
  have hk : k = m + 1 := by omega
  have hf : leadingPower n = 2 ^ (m + 1) := by simp [leadingPower, k, hk]
  have hpowm : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hfm1_ge : 2 ^ m ≤ leadingPower n - 1 := by
    rw [hf, Nat.pow_succ]; omega
  have hfm1_lt : leadingPower n - 1 < 2 ^ (m + 1) := by
    rw [hf]; omega
  have hb_ge : 2 ^ m ≤ blue (leadingPower n - 1) := blue_ge_two_pow hfm1_ge
  have hb_lt : blue (leadingPower n - 1) < 2 ^ (m + 1) := blue_lt_two_pow (m + 1) _ hfm1_lt
  have hdiv_ge : 2 ^ m ≤ n / 2 := by
    rw [hf, Nat.pow_succ, Nat.mul_comm] at hle
    omega
  have hdiv_lt : n / 2 < 2 ^ (m + 1) := by
    rw [hf, Nat.pow_succ] at hlt2
    omega
  have hxor : blue (leadingPower n - 1) ^^^ (n / 2) < 2 ^ m :=
    high_bit_xor_lt hb_ge hb_lt hdiv_ge hdiv_lt
  have hg : g n = 2 * (blue (leadingPower n - 1) ^^^ (n / 2)) + 1 - n % 2 + leadingPower n := rfl
  rw [hg, Nat.add_sub_cancel]
  rw [hf, Nat.pow_succ] at hxor ⊢
  omega

private lemma part_one {n : ℕ} (hn : 1 < n) :
    blue n = blue (g n - leadingPower n) + leadingPower n := by
  obtain ⟨_, hle, _, _⟩ := leadingPower_bounds hn
  set f := leadingPower n
  have hsub_lt : g n - f < f := g_sub_lt hn
  have hgsub_eq : g n - f = Nat.bit (!n.bodd) (blue (f - 1) ^^^ (n / 2)) := by
    have hg : g n = 2 * (blue (f - 1) ^^^ (n / 2)) + 1 - n % 2 + f := rfl
    rw [hg, Nat.add_sub_cancel]
    have hmod : n % 2 = n.bodd.toNat := Nat.mod_two_of_bodd n
    rw [hmod, Nat.bit_val]
    cases n.bodd <;> simp
  have hblue_sub : blue (g n - f) = f ^^^ blue n := by
    rw [hgsub_eq, blue_bit, blue_xor, blue_blue]
    set Y := blue (n / 2)
    have hbit1 : Nat.bit (!n.bodd) ((f - 1) ^^^ Y) =
        Nat.bit false (f - 1) ^^^ Nat.bit (!n.bodd) Y := by
      rw [Nat.xor_bit]; simp
    have hbit2 : Nat.bit (!n.bodd) Y = 1 ^^^ Nat.bit n.bodd Y := by
      have h1 : (1 : ℕ) = Nat.bit true 0 := rfl
      rw [h1, Nat.xor_bit, Nat.zero_xor]
      cases n.bodd <;> rfl
    rw [hbit1, hbit2]
    have hff : (f - 1) ^^^ (Nat.bit false (f - 1) ^^^ 1) = f := by
      have hbf : Nat.bit false (f - 1) ^^^ 1 = 2 * (f - 1) + 1 := by
        have h1 : (1 : ℕ) = Nat.bit true 0 := rfl
        rw [h1, Nat.xor_bit, Nat.xor_zero, Nat.bit_val]
        simp
      rw [hbf]
      exact two_pow_sub_one_xor n.log2
    have hbn : Y ^^^ Nat.bit n.bodd Y = blue n := by
      have hY : Y = blue n.div2 := by simp [Y, Nat.div2_val]
      rw [hY, ← blue_bit n.bodd n.div2, Nat.bit_bodd_div2]
    have hrearr : ((f - 1) ^^^ Y) ^^^ (Nat.bit false (f - 1) ^^^ (1 ^^^ Nat.bit n.bodd Y)) =
        ((f - 1) ^^^ (Nat.bit false (f - 1) ^^^ 1)) ^^^ (Y ^^^ Nat.bit n.bodd Y) := by
      ac_rfl
    rw [hrearr, hff, hbn]
  have hblt : blue (g n - f) < f := blue_lt_two_pow n.log2 (g n - f) hsub_lt
  have hbn_xor : blue n = f ^^^ blue (g n - f) := by
    rw [hblue_sub, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  rw [hbn_xor]
  change 2 ^ n.log2 ^^^ blue (g n - f) = blue (g n - f) + 2 ^ n.log2
  rw [two_pow_xor_eq_add n.log2 _ hblt, Nat.add_comm]

end Helpers

theorem OMA.solution : type_of% @OMA.S_mo_455844.main := by
  intro n hn
  refine ⟨part_one hn, ?_⟩
  set f := OMA.S_mo_455844.leadingPower n
  obtain ⟨hf2, hle, hlt2, _⟩ := leadingPower_bounds hn
  have hnf_lt : n - f < f := by omega
  have hbnf_lt : OMA.S_mo_455844.blue (n - f) < f := blue_lt_two_pow n.log2 (n - f) hnf_lt
  set u := OMA.S_mo_455844.blue (n - f) + f
  have hu1 : 1 < u := by omega
  have huf_ge : 2 ^ n.log2 ≤ u := by simp [u, f, OMA.S_mo_455844.leadingPower]
  have huf_lt : u < 2 ^ (n.log2 + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
    change u < 2 * f
    omega
  have hlu : OMA.S_mo_455844.leadingPower u = f := leadingPower_eq_of_bounds huf_ge huf_lt
  have hp1_u : OMA.S_mo_455844.blue u =
      OMA.S_mo_455844.blue (OMA.S_mo_455844.g u - f) + f := by
    simpa [hlu] using part_one hu1
  have hgu_sub_lt : OMA.S_mo_455844.g u - f < f := by
    simpa [hlu] using g_sub_lt hu1
  have hbgu_sub_lt : OMA.S_mo_455844.blue (OMA.S_mo_455844.g u - f) < f :=
    blue_lt_two_pow n.log2 _ hgu_sub_lt
  have hbu_xor : OMA.S_mo_455844.blue u = f ^^^ OMA.S_mo_455844.blue (OMA.S_mo_455844.g u - f) := by
    rw [hp1_u, Nat.add_comm]
    change 2 ^ n.log2 + OMA.S_mo_455844.blue (OMA.S_mo_455844.g u - f) =
      2 ^ n.log2 ^^^ OMA.S_mo_455844.blue (OMA.S_mo_455844.g u - f)
    exact (two_pow_xor_eq_add n.log2 _ hbgu_sub_lt).symm
  have hbgu_sub_eq : OMA.S_mo_455844.blue (OMA.S_mo_455844.g u - f) =
      f ^^^ OMA.S_mo_455844.blue u := by
    rw [hbu_xor, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have hgu_ge : f ≤ OMA.S_mo_455844.g u := by
    change f ≤ 2 * (OMA.S_mo_455844.blue (OMA.S_mo_455844.leadingPower u - 1) ^^^ (u / 2)) + 1 - u % 2 + OMA.S_mo_455844.leadingPower u
    rw [hlu]
    omega
  have hgu_eq : OMA.S_mo_455844.g u = f ^^^ (OMA.S_mo_455844.g u - f) := by
    change OMA.S_mo_455844.g u = 2 ^ n.log2 ^^^ (OMA.S_mo_455844.g u - f)
    rw [two_pow_xor_eq_add n.log2 _ hgu_sub_lt]
    change OMA.S_mo_455844.g u = f + (OMA.S_mo_455844.g u - f)
    omega
  have hu_eq : u = f ^^^ OMA.S_mo_455844.blue (n - f) := by
    change u = 2 ^ n.log2 ^^^ OMA.S_mo_455844.blue (n - f)
    rw [two_pow_xor_eq_add n.log2 _ hbnf_lt]
    simp [u, f, OMA.S_mo_455844.leadingPower, Nat.add_comm]
  have hn_eq : n = f ^^^ (n - f) := by
    change n = 2 ^ n.log2 ^^^ (n - f)
    rw [two_pow_xor_eq_add n.log2 _ hnf_lt]
    change n = f + (n - f)
    omega
  have hbu_eq2 : OMA.S_mo_455844.blue u = OMA.S_mo_455844.blue f ^^^ (n - f) := by
    rw [hu_eq, blue_xor, blue_blue]
  have hnf_xor : n - f = f ^^^ n := by
    conv_rhs => rw [hn_eq]
    rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have hbgu : OMA.S_mo_455844.blue (OMA.S_mo_455844.g u) = n := by
    rw [hgu_eq, blue_xor, hbgu_sub_eq, hbu_eq2, hnf_xor]
    simp only [← Nat.xor_assoc]
    rw [Nat.xor_assoc (OMA.S_mo_455844.blue f), Nat.xor_comm f (OMA.S_mo_455844.blue f),
      ← Nat.xor_assoc (OMA.S_mo_455844.blue f), Nat.xor_self, Nat.zero_xor,
      Nat.xor_self, Nat.zero_xor]
  calc OMA.S_mo_455844.blue n
      = OMA.S_mo_455844.blue (OMA.S_mo_455844.blue (OMA.S_mo_455844.g u)) := by rw [hbgu]
    _ = OMA.S_mo_455844.g u := blue_blue _
