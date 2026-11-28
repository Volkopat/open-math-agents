import OMAReductions.R_Erdos980_erdos_980_R1

/-!
# Reduction of Elliott's tail estimate to simultaneous l-th power residue bounds

For every prime `l`:
1. Elementary pointwise bound `n_l(p) * (n_l(p) - 1) < p`, hence `n_l(p) ≤ 2 √x`.
2. Existence of an order-`l` multiplicative character `χ_p : ZMod p → ℂ` for `p ≡ 1 (mod l)`.
3. Complex second-moment exceptional-set bound: at most `x^(1/3)` primes `p < ⌈x⌉` with
   `p ≡ 1 (mod l)` have `n_l(p) > (log x)^8`.
4. Layer decomposition reducing `OMA.R_Erdos980_erdos_980_R1.H2` to the uniform sieve upper bound
   `SievePatternBound l`.
-/

namespace Erdos980H2

open Erdos980 Finset Filter Asymptotics
open scoped Classical Topology BigOperators

/-- Uniform upper bound for simultaneous `l`-th power residue patterns through
logarithmically many prescribed primes. -/
def SievePatternBound (l : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ j₀ : ℕ, ∀ᶠ x : ℝ in atTop, ∀ j : ℕ, j₀ ≤ j →
    (2 : ℝ) ^ j ≤ (Real.log x) ^ 10 →
    (((Nat.primesBelow ⌈x⌉₊).filter (fun p => p % l = 1 ∧
      ∀ i < j, ∃ y : ZMod p, y ^ l = (Nat.nth Nat.Prime i : ZMod p))).card : ℝ) *
      (Real.log x / x) ≤ C / (2 : ℝ) ^ j

section Pointwise

lemma smaller_lth_power {l p b : ℕ} (hl : l ≠ 0) (hb : b < leastNonresidue l p) :
    ∃ y : ZMod p, y ^ l = (b : ZMod p) := by
  by_cases h0 : b = 0
  · exact ⟨0, by simp [h0, hl]⟩
  by_contra h
  exact (not_le_of_gt hb) (Nat.sInf_le (s := {n : ℕ | 0 < n ∧ ¬∃ y : ZMod p, y ^ l = (n : ZMod p)})
    ⟨Nat.pos_of_ne_zero h0, h⟩)

/-- Uniform elementary bound for any prime `l`: `n_l(p) * (n_l(p) - 1) < p`. -/
theorem pointwise_l {l p : ℕ} (hl : l.Prime) (hp : p.Prime) :
    let a := leastNonresidue l p
    a * (a - 1) < p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let a := leastNonresidue l p
  by_cases ha : a = 0
  · change a * (a - 1) < p; simp [ha, hp.pos]
  let S := {v : ℕ | 0 < v ∧ ¬∃ y : ZMod p, y ^ l = (v : ZMod p)}
  have non : S.Nonempty := by
    by_contra empty
    have hs := Set.not_nonempty_iff_eq_empty.mp empty
    exact ha (by change sInf S = 0; simp [hs])
  have haS : a ∈ S := Nat.sInf_mem non
  obtain ⟨apos, notPow⟩ := haS
  have ap : a < p := by
    have noMod : ¬∃ y : ZMod p, y ^ l = ((a % p : ℕ) : ZMod p) := by rwa [ZMod.natCast_mod]
    have nz : a % p ≠ 0 := fun h => noMod ⟨0, by simp [h, hl.ne_zero]⟩
    exact (Nat.sInf_le (s := S) ⟨Nat.pos_of_ne_zero nz, noMod⟩).trans_lt (Nat.mod_lt _ hp.pos)
  change a * (a - 1) < p
  by_contra! h
  let q := (p - 1) / a + 1
  have qa : q < a := by
    have divlt : (p - 1) / a < a - 1 := (Nat.div_lt_iff_lt_mul apos).mpr (by
      rw [Nat.mul_comm]; omega)
    dsimp [q]; omega
  have qp : 0 < q ∧ q < p := ⟨Nat.succ_pos _, qa.trans ap⟩
  let r := a * q - p
  have recomb : a * q = p + r ∧ r < a := by
    have er := Nat.mod_add_div (p - 1) a
    have rem := Nat.mod_lt (p - 1) apos
    have eq : a * q = a * ((p - 1) / a) + a := by dsimp [q]; ring
    dsimp [r]; omega
  obtain ⟨u, hu⟩ := smaller_lth_power hl.ne_zero qa
  obtain ⟨v, hv⟩ := smaller_lth_power hl.ne_zero recomb.2
  have qu : (q : ZMod p) ≠ 0 := by
    intro e
    have hz := (ZMod.natCast_eq_zero_iff _ _).mp e
    exact (not_le_of_gt qp.2) (Nat.le_of_dvd qp.1 hz)
  have prod : (a : ZMod p) * q = (r : ZMod p) := by
    have eq := congrArg (fun n : ℕ => (n : ZMod p)) recomb.1
    simpa using eq
  apply notPow
  exact ⟨v / u, by rw [div_pow, hv, hu, div_eq_iff qu, prod]⟩

theorem rootBound_l {l p : ℕ} (hl : l.Prime) (hp : p.Prime) {x : ℝ} (px : (p : ℝ) ≤ x) :
    (leastNonresidue l p : ℝ) ≤ 2 * Real.sqrt x := by
  let a := leastNonresidue l p
  have ht : a * (a - 1) < p := pointwise_l hl hp
  have hsq : a ^ 2 ≤ 4 * p := by
    cases h : a with
    | zero => simp
    | succ n =>
      rw [h, Nat.succ_sub_one] at ht
      nlinarith [hp.pos]
  have sqR : (a : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by exact_mod_cast hsq
  have sx := Real.sq_sqrt (show 0 ≤ x from (Nat.cast_nonneg p).trans px)
  change (a : ℝ) ≤ 2 * Real.sqrt x
  nlinarith [Real.sqrt_nonneg x, sq_nonneg ((a : ℝ) - 2 * Real.sqrt x)]

end Pointwise

section OrderLChar

/-- Existence of a nontrivial multiplicative character `ZMod p → ℂ` of order dividing `l`
for any primes `l, p` with `p % l = 1`. -/
lemma exists_order_l_char {l p : ℕ} (hl : l.Prime) (hp : p.Prime) (hpl : p % l = 1) :
    ∃ χ : MulChar (ZMod p) ℂ,
      (∀ x : ZMod p, χ (x ^ l) = if x = 0 then 0 else 1) ∧
      (∀ x : ZMod p, ‖χ x‖ ≤ 1) ∧
      (letI : NeZero p := ⟨hp.ne_zero⟩; ∑ x : ZMod p, χ x = 0) := by
  have : Fact p.Prime := ⟨hp⟩
  have hl_dvd : l ∣ Fintype.card (ZMod p)ˣ := by
    rw [ZMod.card_units p]
    exact (Nat.modEq_iff_dvd' hp.one_lt.le).mp
      (by rw [Nat.ModEq, hpl, Nat.mod_eq_of_lt hl.one_lt])
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord_g : orderOf g = Fintype.card (ZMod p)ˣ :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).trans Nat.card_eq_fintype_card
  have hord_pos : 0 < orderOf g := by rw [hord_g]; exact Fintype.card_pos
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (l : ℂ))
  have hζ_ne0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hζ_norm : ‖ζ‖ = 1 := by
    dsimp [ζ]
    rw [show 2 * (Real.pi : ℂ) * Complex.I / (l : ℂ) = (((2 * Real.pi / (l : ℝ)) : ℝ) : ℂ) * Complex.I
      by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hζ_pow : ζ ^ l = 1 := by
    dsimp [ζ]
    rw [← Complex.exp_nat_mul]
    have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
    have : (l : ℂ) * (2 * Real.pi * Complex.I / (l : ℂ)) = 2 * Real.pi * Complex.I := by
      field_simp [hl0]
    rw [this, Complex.exp_two_pi_mul_I]
  have hζ_ne_one : ζ ≠ 1 := by
    dsimp [ζ]
    intro h1
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h2piI : (2 : ℂ) * Real.pi * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) hpi) Complex.I_ne_zero
    have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
    have hnl : (n : ℂ) * (l : ℂ) = 1 := by
      have h2 : (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * (l : ℂ)) =
          (2 * (Real.pi : ℂ) * Complex.I) * 1 := by
        calc (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℂ) * (l : ℂ))
            = ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) * (l : ℂ) := by ring
          _ = (2 * (Real.pi : ℂ) * Complex.I / (l : ℂ)) * (l : ℂ) := by rw [← hn]
          _ = (2 * (Real.pi : ℂ) * Complex.I) * 1 := by field_simp [hl0]
      exact mul_left_cancel₀ h2piI h2
    have hnl_int : (n : ℤ) * (l : ℤ) = 1 := by exact_mod_cast hnl
    have hdvd : (l : ℤ) ∣ 1 := ⟨n, by linarith⟩
    have := Int.le_of_dvd one_pos hdvd
    have := hl.two_le
    omega
  have hζ_ord : ζ ^ orderOf g = 1 := by
    rw [hord_g]
    obtain ⟨m, hm⟩ := hl_dvd
    rw [hm, pow_mul, hζ_pow, one_pow]
  have hex_nat : ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u := by
    intro u
    obtain ⟨z, hz⟩ := hg u
    refine ⟨(z % (orderOf g : ℤ)).toNat, ?_⟩
    have hnn : 0 ≤ z % (orderOf g : ℤ) := Int.emod_nonneg z (by omega)
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
    have hmod : g ^ (z % (orderOf g : ℤ)) = g ^ z := zpow_mod_orderOf g z
    rw [hmod]
    exact hz
  let idx : (ZMod p)ˣ → ℕ := fun u => Classical.choose (hex_nat u)
  have hidx_spec : ∀ u : (ZMod p)ˣ, g ^ idx u = u := fun u => Classical.choose_spec (hex_nat u)
  have hpow_eq : ∀ {a b : ℕ}, g ^ a = g ^ b → ζ ^ a = ζ ^ b := by
    intro a b hab
    have hmod : a ≡ b [MOD orderOf g] := pow_eq_pow_iff_modEq.mp hab
    have ha : ζ ^ a = ζ ^ (a % orderOf g) := by
      conv_lhs => rw [← Nat.div_add_mod a (orderOf g), pow_add, pow_mul, hζ_ord, one_pow, one_mul]
    have hb : ζ ^ b = ζ ^ (b % orderOf g) := by
      conv_lhs => rw [← Nat.div_add_mod b (orderOf g), pow_add, pow_mul, hζ_ord, one_pow, one_mul]
    rw [ha, hb, hmod]
  let φ : (ZMod p)ˣ →* ℂˣ :=
    { toFun := fun u => Units.mk0 (ζ ^ idx u) (pow_ne_zero _ hζ_ne0)
      map_one' := by
        apply Units.ext
        simpa using hpow_eq (hidx_spec 1 |>.trans (pow_zero g).symm)
      map_mul' := fun u v => by
        apply Units.ext
        have h := hpow_eq (show g ^ idx (u * v) = g ^ (idx u + idx v) by
          rw [pow_add, hidx_spec, hidx_spec, hidx_spec])
        simpa [pow_add] using h }
  let χ : MulChar (ZMod p) ℂ := MulChar.ofUnitHom φ
  have hχ_unit : ∀ u : (ZMod p)ˣ, χ (u : ZMod p) = ζ ^ idx u := fun u => by
    simp [χ, φ]
  have hχ_g : χ (g : ZMod p) = ζ := by
    rw [hχ_unit]
    simpa using hpow_eq (show g ^ idx g = g ^ 1 by rw [pow_one, hidx_spec])
  have hχ_zero : χ 0 = 0 := χ.map_nonunit not_isUnit_zero
  refine ⟨χ, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x = 0
    · simp [hx, hl.ne_zero, hχ_zero]
    · simp only [hx, ↓reduceIte]
      let u : (ZMod p)ˣ := Units.mk0 x hx
      change χ ((u : ZMod p) ^ l) = 1
      rw [map_pow, hχ_unit, ← pow_mul, mul_comm, pow_mul, hζ_pow, one_pow]
  · intro x
    by_cases hx : x = 0
    · simp [hx, hχ_zero]
    · let u : (ZMod p)ˣ := Units.mk0 x hx
      change ‖χ (u : ZMod p)‖ ≤ 1
      rw [hχ_unit, norm_pow, hζ_norm, one_pow]
  · have hshift : χ (g : ZMod p) * ∑ x : ZMod p, χ x = ∑ x : ZMod p, χ x := by
      rw [mul_sum]
      refine Fintype.sum_equiv (Equiv.mulLeft₀ (g : ZMod p) g.ne_zero) _ _ fun x => ?_
      simp [Equiv.mulLeft₀_apply]
    have hsub : (χ (g : ZMod p) - 1) * ∑ x : ZMod p, χ x = 0 := by
      rw [sub_mul, one_mul, hshift, sub_self]
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd (sub_eq_zero.mp h) (by rw [hχ_g]; exact hζ_ne_one)
    · exact h

noncomputable def chiL (l p : ℕ) : MulChar (ZMod p) ℂ :=
  if h : l.Prime ∧ p.Prime ∧ p % l = 1 then
    Classical.choose (exists_order_l_char h.1 h.2.1 h.2.2)
  else 1

lemma chiL_pow {l p : ℕ} (hl : l.Prime) (hp : p.Prime) (hpl : p % l = 1) (x : ZMod p) :
    chiL l p (x ^ l) = if x = 0 then 0 else 1 := by
  have h : l.Prime ∧ p.Prime ∧ p % l = 1 := ⟨hl, hp, hpl⟩
  simp only [chiL, dif_pos h]
  exact (Classical.choose_spec (exists_order_l_char hl hp hpl)).1 x

lemma chiL_norm_le_one {l p : ℕ} (hl : l.Prime) (hp : p.Prime) (hpl : p % l = 1) (x : ZMod p) :
    ‖chiL l p x‖ ≤ 1 := by
  have h : l.Prime ∧ p.Prime ∧ p % l = 1 := ⟨hl, hp, hpl⟩
  simp only [chiL, dif_pos h]
  exact (Classical.choose_spec (exists_order_l_char hl hp hpl)).2.1 x

lemma chiL_sum_zero {l p : ℕ} (hl : l.Prime) (hp : p.Prime) (hpl : p % l = 1) [NeZero p] :
    ∑ x : ZMod p, chiL l p x = 0 := by
  have h : l.Prime ∧ p.Prime ∧ p % l = 1 := ⟨hl, hp, hpl⟩
  simp only [chiL, dif_pos h]
  simpa using (Classical.choose_spec (exists_order_l_char hl hp hpl)).2.2

end OrderLChar

section Exceptional

/-- Complex second-moment inequality: a finite family of bounded complex vectors cannot
all equal `1` on a large set `S ⊆ range N` if all pairwise correlations are at most `M`. -/
theorem moment_complex {α : Type*} [DecidableEq α] (P : Finset α) (S : Finset ℕ) (N : ℕ)
    (f : α → ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M) (hS : S ⊆ range N)
    (h1 : ∀ p ∈ P, ∀ m ∈ S, f p m = 1)
    (hd : ∀ p ∈ P, ∑ m ∈ range N, ‖f p m‖ ^ 2 ≤ N)
    (hc : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → ‖∑ m ∈ range N, f p m * star (f q m)‖ ≤ M) :
    (S.card : ℝ) * (P.card : ℝ) ^ 2 ≤ (P.card : ℝ) * (N : ℝ) + (P.card : ℝ) ^ 2 * M := by
  let T (m : ℕ) : ℂ := ∑ p ∈ P, f p m
  have full : (∑ m ∈ S, ‖T m‖ ^ 2) = (S.card : ℝ) * (P.card : ℝ) ^ 2 := by
    have on (m) (hm : m ∈ S) : ‖T m‖ ^ 2 = (P.card : ℝ) ^ 2 := by
      have hTm : T m = (P.card : ℂ) := by
        simp [T, sum_congr rfl (fun p hp => h1 p hp m hm)]
      rw [hTm, Complex.norm_natCast]
    rw [sum_congr rfl on, sum_const, nsmul_eq_mul]
  have lb : (S.card : ℝ) * (P.card : ℝ) ^ 2 ≤ ∑ m ∈ range N, ‖T m‖ ^ 2 := by
    rw [← full]
    exact sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => sq_nonneg _)
  have norm_sq_eq (z : ℂ) : (‖z‖ ^ 2 : ℝ) = (z * star z).re := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have expan : (∑ m ∈ range N, ‖T m‖ ^ 2) =
      ∑ p ∈ P, ∑ q ∈ P, (∑ m ∈ range N, f p m * star (f q m)).re := by
    calc (∑ m ∈ range N, ‖T m‖ ^ 2)
        = ∑ m ∈ range N, (T m * star (T m)).re := by
            refine sum_congr rfl fun m _ => norm_sq_eq (T m)
      _ = ∑ m ∈ range N, (∑ p ∈ P, ∑ q ∈ P, f p m * star (f q m)).re := by
            refine sum_congr rfl fun m _ => congrArg Complex.re ?_
            simp_rw [T, star_sum, sum_mul, mul_sum]
      _ = ∑ m ∈ range N, ∑ p ∈ P, ∑ q ∈ P, (f p m * star (f q m)).re := by
            refine sum_congr rfl fun m _ => by
              rw [Complex.re_sum]
              exact sum_congr rfl fun p _ => Complex.re_sum _ _
      _ = ∑ p ∈ P, ∑ q ∈ P, ∑ m ∈ range N, (f p m * star (f q m)).re := by
            rw [sum_comm]
            refine sum_congr rfl fun p _ => sum_comm
      _ = ∑ p ∈ P, ∑ q ∈ P, (∑ m ∈ range N, f p m * star (f q m)).re := by
            refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => (Complex.re_sum _ _).symm
  rw [expan] at lb
  have lineBound (p) (hp : p ∈ P) :
      (∑ q ∈ P, (∑ m ∈ range N, f p m * star (f q m)).re) ≤ (N : ℝ) + (P.card : ℝ) * M := by
    have hdiag : (∑ m ∈ range N, f p m * star (f p m)).re ≤ (N : ℝ) := by
      have heq : (∑ m ∈ range N, f p m * star (f p m)).re = ∑ m ∈ range N, ‖f p m‖ ^ 2 := by
        rw [Complex.re_sum]
        refine sum_congr rfl fun m _ => (norm_sq_eq (f p m)).symm
      rw [heq]
      exact hd p hp
    have hoff : (∑ q ∈ P.erase p, (∑ m ∈ range N, f p m * star (f q m)).re) ≤ (P.card : ℝ) * M := by
      calc (∑ q ∈ P.erase p, (∑ m ∈ range N, f p m * star (f q m)).re)
          ≤ ∑ q ∈ P.erase p, M := sum_le_sum fun q hq =>
              (Complex.re_le_norm _).trans (hc p hp q (mem_erase.mp hq).2 (mem_erase.mp hq).1.symm)
        _ = ((P.erase p).card : ℝ) * M := by rw [sum_const, nsmul_eq_mul]
        _ ≤ (P.card : ℝ) * M := mul_le_mul_of_nonneg_right
              (by exact_mod_cast card_le_card (erase_subset p P)) hM
    have ee := sum_erase_add (s := P) (fun q => (∑ m ∈ range N, f p m * star (f q m)).re) hp
    linarith
  have top : (∑ p ∈ P, ∑ q ∈ P, (∑ m ∈ range N, f p m * star (f q m)).re) ≤
      (P.card : ℝ) * ((N : ℝ) + (P.card : ℝ) * M) := by
    calc _ ≤ ∑ _p ∈ P, ((N : ℝ) + (P.card : ℝ) * M) := sum_le_sum lineBound
      _ = (P.card : ℝ) * ((N : ℝ) + (P.card : ℝ) * M) := by rw [sum_const, nsmul_eq_mul]
  nlinarith only [lb, top]

/-- A bounded, zero-average periodic complex sequence has partial sums bounded in norm by its period. -/
theorem interval_bound_complex (f : ℕ → ℂ) {L : ℕ} (hL : 0 < L)
    (per : Function.Periodic f L) (cancel : ∑ i ∈ range L, f i = 0)
    (hh : ∀ i, ‖f i‖ ≤ 1) (N : ℕ) : ‖∑ i ∈ range N, f i‖ ≤ (L : ℝ) := by
  have block (k : ℕ) : ∑ i ∈ range (k * L), f i = 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, sum_range_add, ih, zero_add]
      convert cancel using 2 with i
      rw [Nat.add_comm]
      exact (per.nat_mul k) i
  have decomp : N = (N / L) * L + N % L := by
    simpa only [Nat.mul_comm] using (Nat.div_add_mod N L).symm
  conv_lhs => rw [decomp, sum_range_add, block, zero_add]
  calc ‖∑ i ∈ range (N % L), f ((N / L) * L + i)‖
      ≤ ∑ i ∈ range (N % L), ‖f ((N / L) * L + i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range (N % L), (1 : ℝ) := sum_le_sum fun i _ => hh _
    _ = ((N % L : ℕ) : ℝ) := by simp
    _ ≤ (L : ℝ) := by exact_mod_cast (Nat.mod_lt N hL).le

/-- Lifting a function on `ZMod L` to `range L` preserves its sum. -/
lemma sum_mod_complex {L : ℕ} [NeZero L] (g : ZMod L → ℂ) :
    ∑ i ∈ range L, g i = ∑ a : ZMod L, g a := by
  rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => g i)]
  have agree (i : Fin L) : (i.val : ZMod L) = ZMod.finEquiv L i := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
    exact ZMod.natCast_zmod_val (ZMod.finEquiv (k + 1) i)
  simp_rw [agree]
  exact (ZMod.finEquiv L).toEquiv.sum_comp g

lemma correlation_complex {l p q : ℕ} (hl : l.Prime) (hp : p.Prime) (hq : q.Prime)
    (hpl : p % l = 1) (hql : q % l = 1) (hne : p ≠ q) (N : ℕ) :
    ‖∑ m ∈ range N, chiL l p (m : ZMod p) * star (chiL l q (m : ZMod q))‖ ≤ ((p * q : ℕ) : ℝ) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  have : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hcop : p.Coprime q :=
    hp.coprime_iff_not_dvd.mpr fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  let e := ZMod.chineseRemainder hcop
  let F (u : ZMod p × ZMod q) : ℂ := chiL l p u.1 * star (chiL l q u.2)
  let G (z : ZMod (p * q)) : ℂ := F (e z)
  have heq (m : ℕ) : chiL l p (m : ZMod p) * star (chiL l q (m : ZMod q)) = G (m : ZMod (p * q)) := by
    simp [G, F, e]
  have periodic : Function.Periodic (fun m : ℕ => G (m : ZMod (p * q))) (p * q) := by
    intro m
    simp only [Nat.cast_add, ZMod.natCast_self, add_zero]
  have cancel : ∑ m ∈ range (p * q), G (m : ZMod (p * q)) = 0 := by
    rw [sum_mod_complex, show (∑ z : ZMod (p * q), G z) = ∑ u : ZMod p × ZMod q, F u from
      e.toEquiv.sum_comp F]
    simp only [F, Fintype.sum_prod_type, ← mul_sum, ← sum_mul, chiL_sum_zero hl hp hpl, zero_mul]
  simp_rw [heq]
  apply interval_bound_complex _ (Nat.mul_pos hp.pos hq.pos) periodic cancel _ N
  intro m
  rw [← heq, norm_mul, norm_star]
  exact mul_le_one₀ (chiL_norm_le_one hl hp hpl _) (norm_nonneg _) (chiL_norm_le_one hl hq hql _)

private def products (y k : ℕ) : Finset ℕ :=
  ((Nat.primesLE y).powersetCard k).image (fun t => ∏ q ∈ t, q)

lemma card_products (y k : ℕ) : (products y k).card = (Nat.primeCounting y).choose k := by
  have contains {s t : Finset ℕ} (ps : s ⊆ Nat.primesLE y) (pt : t ⊆ Nat.primesLE y)
      (he : (∏ q ∈ s, q) = ∏ q ∈ t, q) : s ⊆ t := by
    intro a ha
    have ap := (Nat.mem_primesLE.mp (ps ha)).2
    have hd := Finset.dvd_prod_of_mem (fun x : ℕ => x) ha
    rw [he] at hd
    obtain ⟨b, hb, hab⟩ := (ap.prime.dvd_finsetProd_iff id).mp hd
    have bp := (Nat.mem_primesLE.mp (pt hb)).2
    exact (Nat.prime_dvd_prime_iff_eq ap bp).mp hab ▸ hb
  unfold products
  rw [card_image_of_injOn, card_powersetCard, Nat.primesLE_card_eq_primeCounting]
  intro s hs t ht he
  exact Subset.antisymm (contains (mem_powersetCard.mp hs).1 (mem_powersetCard.mp ht).1 he)
    (contains (mem_powersetCard.mp ht).1 (mem_powersetCard.mp hs).1 he.symm)

lemma products_size (y k : ℕ) : products y k ⊆ range (y ^ k + 1) := by
  intro m hm
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hm
  obtain ⟨hs, hk⟩ := mem_powersetCard.mp ht
  have h := t.prod_le_pow_card id y (fun q hq => (Nat.mem_primesLE.mp (hs hq)).1)
  simpa [hk] using h

lemma products_one_l {l y k p : ℕ} (hl : l.Prime) (hp : p.Prime) (hpl : p % l = 1)
    (hy : y < leastNonresidue l p) {m : ℕ} (hm : m ∈ products y k) :
    chiL l p (m : ZMod p) = 1 := by
  have cap := pointwise_l hl hp
  let a := leastNonresidue l p
  change a * (a - 1) < p at cap
  have yp : y < p := by
    by_cases ha : 2 ≤ a
    · have h := Nat.le_mul_of_pos_right a (show 0 < a - 1 by omega)
      omega
    · have := hp.two_le
      omega
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hm
  obtain ⟨hs, _⟩ := mem_powersetCard.mp ht
  rw [Nat.cast_prod, map_prod]
  apply prod_eq_one
  intro q hq
  obtain ⟨hsmall, hprime⟩ := Nat.mem_primesLE.mp (hs hq)
  have hpos := hprime.pos
  have nz : (q : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff q p).mp hz
    have := Nat.le_of_dvd hpos hd
    omega
  obtain ⟨z, hz⟩ := smaller_lth_power hl.ne_zero (hsmall.trans_lt hy)
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, zero_pow hl.ne_zero] at hz
    exact nz hz.symm
  rw [← hz, chiL_pow hl hp hpl z, if_neg hz0]

private lemma choose_lower {n k : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (h : (k : ℝ) * b + k ≤ n) : b ^ k ≤ (n.choose k : ℝ) := by
  have hk : k ≤ n := by exact_mod_cast (show (k : ℝ) ≤ n by nlinarith)
  refine le_trans ?_ (Nat.pow_le_choose (α := ℝ) k n)
  apply (le_div_iff₀ (show (0 : ℝ) < k.factorial by exact_mod_cast k.factorial_pos)).mpr
  have fac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  calc
    b ^ k * (k.factorial : ℝ) ≤ b ^ k * (k : ℝ) ^ k := by gcongr
    _ = (b * k) ^ k := (mul_pow ..).symm
    _ ≤ _ := by
      gcongr
      rw [Nat.cast_sub (by omega : k ≤ n + 1)]
      push_cast
      linarith

private lemma many_primes {t lv : ℝ} (ht : 2 ≤ t) (hlv : 100 ≤ lv)
    (eq : Real.log t = lv) (htl : 1000 * lv ≤ t) :
    t ^ 8 / (32 * lv) ≤ (Nat.primeCounting ⌊t ^ 8⌋₊ : ℝ) := by
  have positive : 0 < t := by linarith
  have L : Real.log (t ^ 8) = 8 * lv := by rw [Real.log_pow, eq]; norm_num
  have t8 : t ≤ t ^ 8 := by simpa using (pow_le_pow_right₀ (by linarith : 1 ≤ t) (by decide : 1 ≤ 8))
  have logbound : Real.log (t ^ 8 + 2) ≤ 1 + 8 * lv := by
    calc
      _ ≤ Real.log (2 * t ^ 8) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + 8 * lv := by rw [Real.log_mul (by norm_num) (by positivity), L]
      _ ≤ _ := by linarith [Real.log_two_lt_d9]
  have numerator : t ^ 8 / 4 ≤ (t ^ 8 - 1) * Real.log 2 - Real.log (t ^ 8 + 2) := by
    have := mul_nonneg (show 0 ≤ t ^ 8 - 1 by linarith)
      (show 0 ≤ Real.log 2 - 1 / 2 by linarith [Real.log_two_gt_d9])
    nlinarith
  have bound := Chebyshev.pi_ge' (show 1 < t ^ 8 by linarith)
  rw [L] at bound
  apply le_trans _ bound
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right numerator (show 0 ≤ 32 * lv by linarith)]

lemma smooth_numeric : ∀ᶠ x : ℝ in atTop, ∃ y k : ℕ,
    (y : ℝ) ≤ (Real.log x) ^ 8 ∧ ((y ^ k + 1 : ℕ) : ℝ) ≤ 2 * x ^ ((7 : ℝ) / 3) ∧
    4 * x ^ 2 ≤ ((Nat.primeCounting y).choose k : ℝ) := by
  have little := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).bound
    (by norm_num : (0 : ℝ) < 1 / 1000)
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1000,
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 100,
    Real.tendsto_log_atTop.eventually little, eventually_ge_atTop (2 : ℝ)] with x ht hlv small hx
  let t := Real.log x
  let lv := Real.log t
  change 1000 ≤ t at ht
  change 100 ≤ lv at hlv
  change ‖lv‖ ≤ 1 / 1000 * ‖t ^ (1 : ℝ)‖ at small
  rw [Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
    abs_of_nonneg (by linarith)] at small
  have htl : 1000 * lv ≤ t := by linarith
  have lt0 : 0 < lv := by linarith
  have tt0 : 0 < t := by linarith
  have xp : 0 < x := by linarith
  let y := ⌊t ^ 8⌋₊
  let k := ⌊7 * t / (24 * lv)⌋₊
  let b := t ^ 7 / 32
  have hku : (k : ℝ) * (24 * lv) ≤ 7 * t :=
    (le_div_iff₀ (by positivity)).mp (Nat.floor_le (by positivity))
  have hkl : 7 * t < ((k : ℝ) + 1) * (24 * lv) :=
    (div_lt_iff₀ (by positivity)).mp (Nat.lt_floor_add_one _)
  have price := many_primes (by linarith : 2 ≤ t) hlv (rfl : Real.log t = lv) htl
  change t ^ 8 / (32 * lv) ≤ (Nat.primeCounting y : ℝ) at price
  have t7 : 32 ≤ t ^ 7 := by
    have := pow_le_pow_right₀ (by linarith : 1 ≤ t) (by decide : 1 ≤ 7)
    simp only [pow_one] at this
    linarith
  have hchoice : b ^ k ≤ ((Nat.primeCounting y).choose k : ℝ) := by
    apply choose_lower (by dsimp [b]; positivity)
    apply le_trans _ price
    apply (le_div_iff₀ (by positivity)).mpr
    dsimp [b]
    have a := mul_le_mul_of_nonneg_right hku (show 0 ≤ t ^ 7 by positivity)
    have c := mul_nonneg (show 0 ≤ (k : ℝ) * lv by positivity) (show 0 ≤ t ^ 7 - 32 by linarith)
    nlinarith only [a, c, show 0 ≤ t ^ 8 by positivity]
  have lbLog : (139 / 20 : ℝ) * lv ≤ Real.log b := by
    have log32 : Real.log 32 = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]; norm_num
    rw [show Real.log b = 7 * lv - Real.log 32 by
      dsimp [b, lv]; rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]; norm_num, log32]
    linarith [Real.log_two_lt_d9]
  have lo : 4 * x ^ 2 ≤ b ^ k := by
    apply (Real.log_le_log_iff (by positivity) (by dsimp [b]; positivity)).mp
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
    have log4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [log4]
    change 2 * Real.log 2 + 2 * t ≤ (k : ℝ) * Real.log b
    nlinarith only [hkl, htl, ht, Real.log_two_lt_d9,
      mul_le_mul_of_nonneg_left lbLog (show 0 ≤ (k : ℝ) by positivity)]
  have yupper : (y : ℝ) ≤ t ^ 8 := Nat.floor_le (by positivity)
  refine ⟨y, k, yupper, ?_, lo.trans hchoice⟩
  have size : (t ^ 8) ^ k ≤ x ^ ((7 : ℝ) / 3) := by
    rw [Real.rpow_def_of_pos xp]
    apply (Real.log_le_iff_le_exp (by positivity)).mp
    rw [Real.log_pow, Real.log_pow]
    change (k : ℝ) * (8 * lv) ≤ t * (7 / 3)
    linarith
  have one : 1 ≤ x ^ ((7 : ℝ) / 3) := Real.one_le_rpow (by linarith) (by norm_num)
  push_cast
  have le' := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ y) yupper k
  linarith

/-- For every prime `l`, at most `x^(1/3)` primes `p < ⌈x⌉` with `p % l = 1` have
`leastNonresidue l p > (log x)^8`. -/
theorem exceptional_l {l : ℕ} (hl : l.Prime) :
    ∀ᶠ x : ℝ in atTop,
      (((Nat.primesBelow ⌈x⌉₊).filter (fun p => p % l = 1 ∧
        (Real.log x) ^ 8 < (leastNonresidue l p : ℝ))).card : ℝ) ≤ x ^ ((1 : ℝ) / 3) := by
  classical
  filter_upwards [smooth_numeric, eventually_ge_atTop (1 : ℝ)] with x hs hx
  obtain ⟨y, k, hy, hN, hB⟩ := hs
  let P := (Nat.primesBelow ⌈x⌉₊).filter (fun p => p % l = 1 ∧
      (Real.log x) ^ 8 < (leastNonresidue l p : ℝ))
  change (P.card : ℝ) ≤ _
  have props (p) (hp : p ∈ P) : p.Prime ∧ p % l = 1 ∧ (p : ℝ) ≤ x ∧ y < leastNonresidue l p := by
    obtain ⟨hpr, hmod, hlt⟩ := mem_filter.mp hp
    obtain ⟨hpx, prime⟩ := Nat.mem_primesBelow.mp hpr
    exact ⟨prime, hmod, (Nat.lt_ceil.mp hpx).le, by exact_mod_cast hy.trans_lt hlt⟩
  let N := y ^ k + 1
  have aux := moment_complex P (products y k) N (fun p m => chiL l p (m : ZMod p))
    (x ^ 2) (sq_nonneg x) (products_size y k)
    (fun p hp m hm => products_one_l hl (props p hp).1 (props p hp).2.1 (props p hp).2.2.2 hm)
    (fun p hp => by
      have h := sum_le_sum (s := range N) (g := fun _ => (1 : ℝ)) fun m _ =>
        show ‖chiL l p (m : ZMod p)‖ ^ 2 ≤ 1 by
          have h1 := chiL_norm_le_one hl (props p hp).1 (props p hp).2.1 (m : ZMod p)
          nlinarith [norm_nonneg (chiL l p (m : ZMod p))]
      simpa using h)
    (fun p hp q hq hne => by
      have prod := correlation_complex hl (props p hp).1 (props q hq).1
        (props p hp).2.1 (props q hq).2.1 hne N
      have hle : ((p * q : ℕ) : ℝ) ≤ x ^ 2 := by
        rw [Nat.cast_mul, sq]
        gcongr
        · exact (props p hp).2.2.1
        · exact (props q hq).2.2.1
      exact prod.trans hle)
  rw [card_products] at aux
  have xp : 0 < x := by linarith
  have er : x ^ ((7 : ℝ) / 3) = x ^ 2 * x ^ ((1 : ℝ) / 3) := by
    rw [show (7 : ℝ) / 3 = 2 + (1 : ℝ) / 3 by norm_num, Real.rpow_add xp, Real.rpow_two]
  rw [er] at hN
  by_contra! bad
  have pos := Real.rpow_pos_of_pos xp ((1 : ℝ) / 3)
  have pp : (0 : ℝ) < P.card := lt_trans pos bad
  have impossible := mul_pos (mul_pos (sq_pos_of_pos xp) pp) (sub_pos.mpr bad)
  dsimp [N] at aux
  nlinarith only [aux, mul_le_mul_of_nonneg_right hB (sq_nonneg (P.card : ℝ)),
    mul_le_mul_of_nonneg_left hN pp.le, impossible, mul_nonneg (sq_nonneg x) (sq_nonneg (P.card : ℝ))]

end Exceptional

section Reduction

/-- Elementary Chebyshev bound: eventually `Nat.nth Nat.Prime j ≤ j ^ 2`. -/
lemma nth_prime_le_sq_eventually : ∀ᶠ j : ℕ in atTop, Nat.nth Nat.Prime j ≤ j ^ 2 := by
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 16)
  have hev : ∀ᶠ j : ℕ in atTop, 100 ≤ j ∧
      ‖Real.log ((j : ℝ) ^ 2)‖ ≤ (1 / 16 : ℝ) * ‖((j : ℝ) ^ 2) ^ ((1 : ℝ) / 2)‖ := by
    refine (eventually_ge_atTop 100).and ?_
    have hsq : Tendsto (fun j : ℕ => (j : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
    exact hsq.eventually hlog
  filter_upwards [hev] with j ⟨hj100n, hlj⟩
  have hj100 : (100 : ℝ) ≤ j := by exact_mod_cast hj100n
  have hj1 : (1 : ℝ) < (j : ℝ) ^ 2 := by nlinarith
  have hsqrt : ((j : ℝ) ^ 2) ^ ((1 : ℝ) / 2) = (j : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by linarith)]
  rw [hsqrt, Real.norm_of_nonneg (Real.log_nonneg hj1.le),
    Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ j)] at hlj
  have hpi := Chebyshev.pi_ge' hj1
  have hlog2 : Real.log ((j : ℝ) ^ 2 + 2) ≤ Real.log ((j : ℝ) ^ 2) + 1 := by
    calc Real.log ((j : ℝ) ^ 2 + 2)
        ≤ Real.log (2 * (j : ℝ) ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
      _ = Real.log 2 + Real.log ((j : ℝ) ^ 2) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ Real.log ((j : ℝ) ^ 2) + 1 := by linarith [Real.log_two_lt_d9]
  have hnum : (j : ℝ) ^ 2 / 4 ≤ ((j : ℝ) ^ 2 - 1) * Real.log 2 - Real.log ((j : ℝ) ^ 2 + 2) := by
    have := mul_nonneg (show 0 ≤ (j : ℝ) ^ 2 - 1 by nlinarith)
      (show 0 ≤ Real.log 2 - 1 / 2 by linarith [Real.log_two_gt_d9])
    nlinarith
  have hlog_pos : 0 < Real.log ((j : ℝ) ^ 2) := Real.log_pos hj1
  have hgt : (j : ℝ) < (Nat.primeCounting (j ^ 2) : ℝ) := by
    have hfl : ⌊(j : ℝ) ^ 2⌋₊ = j ^ 2 := by
      have : ((j ^ 2 : ℕ) : ℝ) = (j : ℝ) ^ 2 := by push_cast; rfl
      rw [← this, Nat.floor_natCast]
    rw [hfl] at hpi
    have h1 : (j : ℝ) < (j : ℝ) ^ 2 / 4 / Real.log ((j : ℝ) ^ 2) := by
      rw [lt_div_iff₀ hlog_pos]
      nlinarith
    have h2 : (j : ℝ) ^ 2 / 4 / Real.log ((j : ℝ) ^ 2) ≤ (Nat.primeCounting (j ^ 2) : ℝ) :=
      le_trans (div_le_div_of_nonneg_right hnum hlog_pos.le) hpi
    linarith
  have hcard : j < Nat.primeCounting (j ^ 2) := by exact_mod_cast hgt
  rw [Nat.primeCounting, Nat.primeCounting'] at hcard
  by_contra! hlt
  have hle : Nat.count Nat.Prime (j ^ 2 + 1) ≤ Nat.count Nat.Prime (Nat.nth Nat.Prime j) :=
    Nat.count_monotone Nat.Prime (by omega)
  rw [Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime] at hle
  omega

/-- Sum the middle layers and keep the two exceptional pieces unweighted. -/
private theorem weights (T : Finset ℕ) (v : ℕ → ℕ) {K J : ℕ} (hK : 1 ≤ K)
    (hKJ : K ≤ J) (starts : ∀ p ∈ T, K ^ 2 ≤ v p) {w C L B : ℝ}
    (hw : 0 ≤ w) (hC : 0 ≤ C) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (point : ∀ p ∈ T, (v p : ℝ) ≤ B)
    (count : ∀ j ∈ Icc K J, ((T.filter fun p => j ^ 2 ≤ v p).card : ℝ) * w ≤ C / (2 : ℝ) ^ j) :
    (∑ p ∈ T, (v p : ℝ)) * w ≤ 22 * C * ((K : ℝ) ^ 2 / (2 : ℝ) ^ K) +
      L * (C / (2 : ℝ) ^ J) + B * ((T.filter fun p => L < (v p : ℝ)).card : ℝ) * w := by
  classical
  let F (j : ℕ) : ℝ := (2 * (j : ℝ) ^ 2 + 8 * j + 12) / 2 ^ j
  have telescopes (j : ℕ) : ((j : ℝ) + 1) ^ 2 / (2 : ℝ) ^ j = F j - F (j + 1) := by
    simp only [F, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp; ring
  have sumF : ∑ j ∈ Ico K J, ((j : ℝ) + 1) ^ 2 / (2 : ℝ) ^ j = F K - F J := by
    clear count
    induction J, hKJ using Nat.le_induction with
    | base => simp
    | succ t ht ih => rw [sum_Ico_succ_top ht, ih, telescopes]; ring
  have FK : F K ≤ 22 * ((K : ℝ) ^ 2 / (2 : ℝ) ^ K) := by
    have kR : 1 ≤ (K : ℝ) := by exact_mod_cast hK
    dsimp [F]
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr kR) (show 0 ≤ (K : ℝ) by positivity),
      sq_nonneg ((K : ℝ) - 1)]
  let layer (j p : ℕ) : ℝ := if j ^ 2 ≤ v p then ((j : ℝ) + 1) ^ 2 else 0
  let mid (p : ℕ) : ℝ := if J ^ 2 ≤ v p then L else 0
  let far (p : ℕ) : ℝ := if L < (v p : ℝ) then B else 0
  have cost (p) (hp : p ∈ T) : (v p : ℝ) ≤ (∑ j ∈ Ico K J, layer j p) + mid p + far p := by
    have nonneg (j : ℕ) : 0 ≤ layer j p := by dsimp [layer]; split <;> positivity
    have hs := sum_nonneg (s := Ico K J) (fun j _ => nonneg j)
    have hm : 0 ≤ mid p := by dsimp [mid]; split <;> positivity
    have hf : 0 ≤ far p := by dsimp [far]; split <;> positivity
    by_cases big : L < (v p : ℝ)
    · rw [show far p = B from if_pos big]; linarith [point p hp]
    by_cases last : J ^ 2 ≤ v p
    · rw [show mid p = L from if_pos last]; linarith
    let j := Nat.sqrt (v p)
    have low : j ^ 2 ≤ v p := Nat.sqrt_le' _
    have high : v p < (j + 1) ^ 2 := Nat.lt_succ_sqrt' _
    have jmin : K ≤ j := by
      by_contra! h
      have fromStart := starts p hp
      have := Nat.pow_le_pow_left (show j + 1 ≤ K by omega) 2
      omega
    have jmax : j < J := by
      by_contra! h; exact last ((Nat.pow_le_pow_left h 2).trans low)
    have hj : layer j p ≤ ∑ l ∈ Ico K J, layer l p :=
      single_le_sum (f := fun l => layer l p) (fun l _ => nonneg l) (mem_Ico.mpr ⟨jmin, jmax⟩)
    rw [show layer j p = ((j : ℝ) + 1) ^ 2 from if_pos low] at hj
    have vR : (v p : ℝ) ≤ ((j : ℝ) + 1) ^ 2 := by exact_mod_cast high.le
    linarith
  have indicator (pred : ℕ → Prop) [DecidablePred pred] (z : ℝ) :
      (∑ p ∈ T, if pred p then z else 0) = ((T.filter pred).card : ℝ) * z := by
    rw [← sum_filter]; simp
  have avg : (∑ p ∈ T, (v p : ℝ)) * w ≤
      (∑ j ∈ Ico K J, ((T.filter fun p => j ^ 2 ≤ v p).card : ℝ) * ((j : ℝ) + 1) ^ 2) * w +
      (((T.filter fun p => J ^ 2 ≤ v p).card : ℝ) * L) * w +
      (((T.filter fun p => L < (v p : ℝ)).card : ℝ) * B) * w := by
    have h := mul_le_mul_of_nonneg_right (sum_le_sum cost) hw
    simp only [sum_add_distrib, add_mul] at h
    rw [sum_comm (s := T) (t := Ico K J)] at h
    simpa only [layer, mid, far, indicator] using h
  have layers : (∑ j ∈ Ico K J,
      ((T.filter fun p => j ^ 2 ≤ v p).card : ℝ) * ((j : ℝ) + 1) ^ 2) * w
      ≤ 22 * C * ((K : ℝ) ^ 2 / (2 : ℝ) ^ K) := by
    rw [sum_mul]
    calc (∑ j ∈ Ico K J, ((T.filter fun p => j ^ 2 ≤ v p).card : ℝ) * ((j : ℝ) + 1) ^ 2 * w)
        ≤ ∑ j ∈ Ico K J, C * (((j : ℝ) + 1) ^ 2 / 2 ^ j) := sum_le_sum <| by
            intro j hj
            have h := count j (mem_Icc.mpr ⟨(mem_Ico.mp hj).1, (mem_Ico.mp hj).2.le⟩)
            convert mul_le_mul_of_nonneg_right h (sq_nonneg ((j : ℝ) + 1)) using 1 <;> ring
      _ = C * (F K - F J) := by rw [← Finset.mul_sum, sumF]
      _ ≤ C * (22 * ((K : ℝ) ^ 2 / 2 ^ K)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        have : 0 ≤ F J := by dsimp [F]; positivity
        linarith
      _ = _ := by ring
  have middle := mul_le_mul_of_nonneg_left (count J (mem_Icc.mpr ⟨hKJ, le_rfl⟩)) hL
  linarith only [avg, layers, middle]

/-- Reduction of `OMA.R_Erdos980_erdos_980_R1.H2` for a prime `l` to `SievePatternBound l`. -/
theorem tail_of_sieve_pattern_bound {l : ℕ} (hl : l.Prime) (hsieve : SievePatternBound l) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in atTop, ∀ᶠ x : ℝ in atTop,
      (∑ p ∈ (Nat.primesBelow ⌈x⌉₊).filter (fun p ↦ p % l = 1 ∧
        Nat.nth Nat.Prime K ≤ leastNonresidue l p), (leastNonresidue l p : ℝ)) *
          (Real.log x / x) ≤ ε := by
  classical
  obtain ⟨C, hC, j₀, sieve⟩ := hsieve
  obtain ⟨J₁, hJ₁⟩ := eventually_atTop.mp nth_prime_le_sq_eventually
  have exceptional := exceptional_l hl
  intro ε hε
  have vanish : Tendsto (fun j : ℕ => 22 * C * ((j : ℝ) ^ 2 / (2 : ℝ) ^ j)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : 1 < (2 : ℝ))).const_mul (22 * C)
  obtain ⟨K, hK₀, hK⟩ := ((eventually_ge_atTop (max (max j₀ J₁) 1)).and
    (vanish.eventually_lt_const (by linarith : 0 < ε / 3))).exists
  filter_upwards [eventually_ge_atTop (K ^ 2)] with k hk
  have high : ∀ᶠ x : ℝ in atTop,
      2 * Real.sqrt x * x ^ ((1 : ℝ) / 3) * (Real.log x / x) ≤ ε / 3 := by
    have little := (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 6)).bound
      (by positivity : 0 < ε / 6)
    filter_upwards [little, eventually_gt_atTop (1 : ℝ)] with x hlx hx
    have xp : 0 < x := by linarith
    change ‖Real.log x‖ ≤ ε / 6 * ‖x ^ ((1 : ℝ) / 6)‖ at hlx
    rw [Real.norm_of_nonneg (Real.log_nonneg hx.le),
      Real.norm_of_nonneg (Real.rpow_nonneg xp.le _)] at hlx
    have mult : Real.sqrt x * x ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 6) = x := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add xp, ← Real.rpow_add xp]
      norm_num
    rw [← mul_div_assoc, div_le_iff₀ xp]
    calc 2 * Real.sqrt x * x ^ ((1 : ℝ) / 3) * Real.log x
        ≤ 2 * Real.sqrt x * x ^ ((1 : ℝ) / 3) * (ε / 6 * x ^ ((1 : ℝ) / 6)) :=
          mul_le_mul_of_nonneg_left hlx (by positivity)
      _ = ε / 3 * x := by
        calc _ = ε / 3 * (Real.sqrt x * x ^ ((1 : ℝ) / 3) * x ^ ((1 : ℝ) / 6)) := by ring
             _ = _ := by rw [mult]
  filter_upwards [sieve, exceptional, high, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max ((2 : ℝ) ^ K) (6 * C / ε + 1))]
    with x hs he hh hx hlog
  let L := Real.log x
  let w := L / x
  have xp : 0 < x := by linarith
  have lp : 0 < L := Real.log_pos hx
  have hw : 0 ≤ w := div_nonneg lp.le xp.le
  have lK : (2 : ℝ) ^ K ≤ L := (le_max_left ..).trans hlog
  have lC : 6 * C / ε + 1 ≤ L := (le_max_right ..).trans hlog
  have l1 : 1 ≤ L := (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℝ))).trans lK
  have Lten : L ≤ L ^ 10 := by
    simpa only [pow_one] using (pow_le_pow_right₀ l1 (by decide : 1 ≤ 10))
  obtain ⟨J, jlo, jhi⟩ := exists_nat_pow_near (l1.trans Lten) (by norm_num : 1 < (2 : ℝ))
  have KJ : K ≤ J := by
    by_contra! h
    have h' := pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (show J + 1 ≤ K by omega)
    linarith only [h', lK, Lten, jhi]
  have mid : L ^ 8 * (C / (2 : ℝ) ^ J) ≤ ε / 3 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    rw [pow_succ (2 : ℝ) J] at jhi
    have lc : 6 * C ≤ ε * L := by
      have := (div_le_iff₀ hε).mp (show 6 * C / ε ≤ L by linarith); linarith
    have lc' : 6 * C ≤ ε * L ^ 2 :=
      lc.trans (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (L - 1)]) hε.le)
    have z := mul_le_mul_of_nonneg_right lc' (show 0 ≤ L ^ 8 by positivity)
    have z' := mul_le_mul_of_nonneg_left jhi.le hε.le
    nlinarith only [z, z']
  let T := (Nat.primesBelow ⌈x⌉₊).filter fun p => p % l = 1 ∧ Nat.nth Nat.Prime k ≤ leastNonresidue l p
  let v := leastNonresidue l
  have starts (p) (hp : p ∈ T) : K ^ 2 ≤ v p := by
    have monotone := Nat.nth_strictMono Nat.infinite_setOfPred_prime
    exact hk.trans ((monotone.id_le k).trans (mem_filter.mp hp).2.2)
  have point (p) (hp : p ∈ T) : (v p : ℝ) ≤ 2 * Real.sqrt x := by
    have mem := Nat.mem_primesBelow.mp (mem_filter.mp hp).1
    exact rootBound_l hl mem.2 (Nat.lt_ceil.mp mem.1).le
  have count (j) (hj : j ∈ Icc K J) :
      ((T.filter fun p => j ^ 2 ≤ v p).card : ℝ) * w ≤ C / (2 : ℝ) ^ j := by
    obtain ⟨hjk, hjJ⟩ := mem_Icc.mp hj
    have hj0 : j₀ ≤ j := le_trans (le_trans (le_max_left j₀ J₁) (le_max_left _ 1)) (hK₀.trans hjk)
    have hj1 : J₁ ≤ j := le_trans (le_trans (le_max_right j₀ J₁) (le_max_left _ 1)) (hK₀.trans hjk)
    have hpat := hs j hj0 ((pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hjJ).trans jlo)
    apply le_trans _ hpat
    apply mul_le_mul_of_nonneg_right _ hw
    apply Nat.cast_le.mpr
    apply card_le_card
    intro p hp
    obtain ⟨ht, hv⟩ := mem_filter.mp hp
    obtain ⟨hprime, hmod, _⟩ := mem_filter.mp ht
    refine mem_filter.mpr ⟨hprime, hmod, fun i hi => smaller_lth_power hl.ne_zero ?_⟩
    have lt := (Nat.nth_strictMono Nat.infinite_setOfPred_prime) hi
    exact lt.trans_le ((hJ₁ j hj1).trans hv)
  have exSize : ((T.filter fun p => L ^ 8 < (v p : ℝ)).card : ℝ) ≤ x ^ ((1 : ℝ) / 3) := by
    apply le_trans _ he
    apply Nat.cast_le.mpr
    apply card_le_card
    intro p hp
    obtain ⟨ht, hv⟩ := mem_filter.mp hp
    obtain ⟨hprime, hmod, _⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨hprime, hmod, hv⟩
  have hK1 : 1 ≤ K := le_trans (le_max_right _ 1) hK₀
  have est := weights T v hK1 KJ starts hw hC.le
    (show 0 ≤ L ^ 8 by positivity) (show 0 ≤ 2 * Real.sqrt x by positivity) point count
  have large : 2 * Real.sqrt x * ((T.filter fun p => L ^ 8 < (v p : ℝ)).card : ℝ) * w ≤ ε / 3 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left exSize (by positivity)) hw).trans hh
  change (∑ p ∈ T, (v p : ℝ)) * w ≤ ε
  linarith only [est, hK, mid, large]

end Reduction

end Erdos980H2

/-
# Multidimensional Large Sieve and Montgomery's Arithmetic Large Sieve

Completely elementary, integral-free proof of the `d`-dimensional large sieve for
`δ`-well-separated points in `(ℝ/ℤ)^d` using a product of 1D trapezoidal Fejér-type kernels,
followed by `d`-dimensional Farey separation and Montgomery's arithmetic large sieve on `ℤ^d`.
-/

namespace Erdos980LS

open Finset Complex
open scoped BigOperators

/-- Additive character `e(x) = exp(2πi x)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp only [e, Complex.ofReal_add, mul_add, Complex.exp_add]

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_neg (x : ℝ) : e (-x) = star (e x) := by
  simp only [e, Complex.ofReal_neg, mul_neg]
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [map_ofNat, Complex.conj_ofReal, Complex.conj_I]

lemma e_int (k : ℤ) : e (k : ℝ) = 1 := by
  simp only [e, Complex.ofReal_intCast]
  have : 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

lemma e_add_int (x : ℝ) (k : ℤ) : e (x + k) = e x := by
  rw [e_add, e_int, mul_one]

lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  simp only [e]
  have : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

lemma e_int_mul (n : ℤ) (x : ℝ) : e ((n : ℝ) * x) = (e x) ^ n := by
  simp only [e, Complex.ofReal_mul, Complex.ofReal_intCast]
  rw [← Complex.exp_int_mul]
  congr 1; ring

lemma e_nat_mul (n : ℕ) (x : ℝ) : e ((n : ℝ) * x) = (e x) ^ n := by
  simpa using e_int_mul (n : ℤ) x

/-- Distance to the nearest integer. -/
noncomputable def dist1 (x : ℝ) : ℝ := |x - round x|

lemma dist1_nonneg (x : ℝ) : 0 ≤ dist1 x := abs_nonneg _

lemma dist1_le (x : ℝ) (k : ℤ) : dist1 x ≤ |x - k| := round_le x k

lemma dist1_le_half (x : ℝ) : dist1 x ≤ 1 / 2 := abs_sub_round x

lemma dist1_neg (x : ℝ) : dist1 (-x) = dist1 x := by
  apply le_antisymm
  · calc dist1 (-x) ≤ |-x - (-round x : ℤ)| := dist1_le (-x) (-round x)
      _ = |-(x - round x)| := by push_cast; ring_nf
      _ = dist1 x := abs_neg _
  · calc dist1 x ≤ |x - (-round (-x) : ℤ)| := dist1_le x (-round (-x))
      _ = |-((-x) - round (-x))| := by push_cast; ring_nf
      _ = dist1 (-x) := abs_neg _

lemma dist1_sub_comm (x y : ℝ) : dist1 (x - y) = dist1 (y - x) := by
  rw [← dist1_neg, neg_sub]

lemma dist1_add_int (x : ℝ) (k : ℤ) : dist1 (x + k) = dist1 x := by
  apply le_antisymm
  · calc dist1 (x + k) ≤ |x + k - (round x + k : ℤ)| := dist1_le (x + k) (round x + k)
      _ = dist1 x := by push_cast; simp [dist1, sub_eq_add_neg]
  · calc dist1 x ≤ |x - (round (x + k) - k : ℤ)| := dist1_le x (round (x + k) - k)
      _ = dist1 (x + k) := by push_cast; unfold dist1; congr 1; ring

lemma four_dist1_le_norm_e_sub_one (x : ℝ) : 4 * dist1 x ≤ ‖e x - 1‖ := by
  set y : ℝ := x - round x
  have hy_half : |y| ≤ 1 / 2 := abs_sub_round x
  have he : e x = e y := by
    have : x = y + round x := by dsimp [y]; ring
    rw [this, e_add_int]
  rw [he]
  have hfac : e y - 1 = e (y / 2) * (e (y / 2) - e (-(y / 2))) := by
    rw [mul_sub, ← e_add, ← e_add]
    have h1 : y / 2 + y / 2 = y := by ring
    have h2 : y / 2 + -(y / 2) = 0 := by ring
    rw [h1, h2, e_zero]
  have hsin : e (y / 2) - e (-(y / 2)) = 2 * Complex.I * Real.sin (Real.pi * y) := by
    have h1 : 2 * (Real.pi : ℂ) * Complex.I * ((y / 2 : ℝ) : ℂ) =
        ((Real.pi * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have h2 : 2 * (Real.pi : ℂ) * Complex.I * ((-(y / 2) : ℝ) : ℂ) =
        -(((Real.pi * y : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    simp only [e, h1, h2]
    rw [Complex.exp_neg, Complex.exp_mul_I]
    have hs : Complex.sin ((Real.pi * y : ℝ) : ℂ) = ((Real.sin (Real.pi * y) : ℝ) : ℂ) :=
      (Complex.ofReal_sin _).symm
    have hcs : (Complex.cos ((Real.pi * y : ℝ) : ℂ) + Complex.sin ((Real.pi * y : ℝ) : ℂ) * Complex.I) *
        (Complex.cos ((Real.pi * y : ℝ) : ℂ) - Complex.sin ((Real.pi * y : ℝ) : ℂ) * Complex.I) = 1 := by
      have : (Complex.cos ((Real.pi * y : ℝ) : ℂ)) ^ 2 + (Complex.sin ((Real.pi * y : ℝ) : ℂ)) ^ 2 = 1 :=
        Complex.cos_sq_add_sin_sq _
      linear_combination this - (Complex.sin ((Real.pi * y : ℝ) : ℂ)) ^ 2 * Complex.I_sq
    have hinv2 : (Complex.cos ((Real.pi * y : ℝ) : ℂ) + Complex.sin ((Real.pi * y : ℝ) : ℂ) * Complex.I)⁻¹ =
        Complex.cos ((Real.pi * y : ℝ) : ℂ) - Complex.sin ((Real.pi * y : ℝ) : ℂ) * Complex.I :=
      inv_eq_of_mul_eq_one_right hcs
    rw [hinv2, hs]; ring
  rw [hfac, norm_mul, norm_e, one_mul, hsin, norm_mul, norm_mul, Complex.norm_ofNat,
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpy : |Real.pi * y| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos hpi]
    have := mul_le_mul_of_nonneg_left hy_half hpi.le
    linarith
  have hsin_lb : 2 * |y| ≤ |Real.sin (Real.pi * y)| := by
    have h1 := Real.mul_le_sin (abs_nonneg (Real.pi * y)) hpy
    rw [abs_mul, abs_of_pos hpi] at h1
    have h2 : 2 / Real.pi * (Real.pi * |y|) = 2 * |y| := by field_simp [hpi.ne']
    rw [h2] at h1
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy] at h1 ⊢
      exact h1.trans (le_abs_self _)
    · rw [abs_of_nonpos hy] at h1 ⊢
      have hneg : Real.sin (Real.pi * (-y)) = -Real.sin (Real.pi * y) := by
        rw [mul_neg, Real.sin_neg]
      rw [hneg] at h1
      exact h1.trans (neg_le_abs _)
  change 4 * |y| ≤ 2 * |Real.sin (Real.pi * y)|
  linarith

lemma norm_sum_e_Ico_le (a : ℤ) (L : ℕ) (x : ℝ) (hx : 0 < dist1 x) :
    ‖∑ k ∈ Ico a (a + L), e ((k : ℝ) * x)‖ ≤ 1 / (2 * dist1 x) := by
  have hshift : ∑ k ∈ Ico a (a + L), e ((k : ℝ) * x) =
      e ((a : ℝ) * x) * ∑ j ∈ range L, (e x) ^ j := by
    rw [mul_sum]
    refine Finset.sum_bij (fun k _ => (k - a).toNat) ?_ ?_ ?_ ?_
    · intro k hk
      rw [mem_Ico] at hk; rw [mem_range]; omega
    · intro k1 hk1 k2 hk2 h
      rw [mem_Ico] at hk1 hk2; omega
    · intro j hj
      rw [mem_range] at hj
      exact ⟨a + j, mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k hk
      rw [mem_Ico] at hk
      rw [← e_nat_mul, ← e_add]
      congr 1
      have hsub : ((k - a).toNat : ℝ) = (k : ℝ) - (a : ℝ) := by
        have : ((k - a).toNat : ℤ) = k - a := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      rw [hsub]; ring
  rw [hshift, norm_mul, norm_e, one_mul]
  have hne : e x ≠ 1 := by
    intro h1
    have h4 := four_dist1_le_norm_e_sub_one x
    rw [h1, sub_self, norm_zero] at h4
    linarith
  rw [geom_sum_eq hne, norm_div]
  have hnum : ‖(e x) ^ L - 1‖ ≤ 2 := by
    calc ‖(e x) ^ L - 1‖ ≤ ‖(e x) ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_e, one_pow, norm_one]; norm_num
  have hden : 4 * dist1 x ≤ ‖e x - 1‖ := four_dist1_le_norm_e_sub_one x
  have hden_pos : 0 < 4 * dist1 x := by positivity
  calc ‖(e x) ^ L - 1‖ / ‖e x - 1‖
      ≤ 2 / (4 * dist1 x) := div_le_div₀ (by positivity) hnum hden_pos hden
    _ = 1 / (2 * dist1 x) := by field_simp [hx.ne']; ring

/-- 1D trapezoidal Fejér-type weight on `ℤ`, equal to `1` on `Ico M (M + N)` and supported on
`Ico (M - H) (M + N + H)`. -/
noncomputable def trapWeight (M : ℤ) (N H : ℕ) (n : ℤ) : ℝ :=
  (((range H).filter (fun h : ℕ => M ≤ n + (h : ℤ) ∧ n + (h : ℤ) < M + (N : ℤ) + (H : ℤ))).card : ℝ) /
    (H : ℝ)

lemma trapWeight_nonneg (M : ℤ) (N H : ℕ) (n : ℤ) : 0 ≤ trapWeight M N H n := by
  unfold trapWeight; positivity

lemma trapWeight_eq_one {M : ℤ} {N H : ℕ} (hH : 0 < H) {n : ℤ} (hn : n ∈ Ico M (M + N)) :
    trapWeight M N H n = 1 := by
  rw [mem_Ico] at hn
  unfold trapWeight
  have hfil : (range H).filter (fun h : ℕ => M ≤ n + (h : ℤ) ∧ n + (h : ℤ) < M + (N : ℤ) + (H : ℤ)) =
      range H := by
    rw [filter_eq_self]
    intro h hh
    rw [mem_range] at hh
    omega
  rw [hfil, card_range, div_self (Nat.cast_ne_zero.mpr hH.ne')]

lemma trapWeight_fourier (M : ℤ) (N H : ℕ) (_hH : 0 < H) (θ : ℝ) :
    ∑ n ∈ Ico (M - (H : ℤ)) (M + (N : ℤ) + (H : ℤ)), (trapWeight M N H n : ℂ) * e ((n : ℝ) * θ) =
      ((H : ℂ)⁻¹) * (∑ a ∈ Ico M (M + (N + H : ℕ)), e ((a : ℝ) * θ)) *
        (∑ h ∈ range H, e (-((h : ℝ) * θ))) := by
  have hcast : ∀ n : ℤ, (trapWeight M N H n : ℂ) =
      ((H : ℂ)⁻¹) * ∑ h ∈ range H,
        if M ≤ n + (h : ℤ) ∧ n + (h : ℤ) < M + (N : ℤ) + (H : ℤ) then (1 : ℂ) else 0 := by
    intro n
    simp only [trapWeight, div_eq_inv_mul, sum_boole]
    push_cast; rfl
  simp_rw [hcast, mul_assoc, ← mul_sum]
  congr 1
  simp_rw [sum_mul, ite_mul, one_mul, zero_mul]
  rw [sum_comm]
  simp_rw [mul_sum]
  rw [sum_comm (s := Ico M (M + (N + H : ℕ)))]
  refine sum_congr rfl fun h hh => ?_
  rw [mem_range] at hh
  rw [← sum_filter]
  refine Finset.sum_bij (fun n _ => n + (h : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    rw [mem_filter] at hn
    rw [mem_Ico]; push_cast; omega
  · intro n1 _ n2 _ he; omega
  · intro a ha
    rw [mem_Ico] at ha; push_cast at ha
    refine ⟨a - (h : ℤ), mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, by omega, by omega⟩, by omega⟩
  · intro n _
    rw [← e_add]
    congr 1; push_cast; ring

lemma norm_trapWeight_fourier_triv (M : ℤ) (N H : ℕ) (hH : 0 < H) (θ : ℝ) :
    ‖∑ n ∈ Ico (M - (H : ℤ)) (M + (N : ℤ) + (H : ℤ)), (trapWeight M N H n : ℂ) * e ((n : ℝ) * θ)‖ ≤
      (N : ℝ) + (H : ℝ) := by
  rw [trapWeight_fourier M N H hH θ, norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
  have h1 : ‖∑ a ∈ Ico M (M + (N + H : ℕ)), e ((a : ℝ) * θ)‖ ≤ ((N + H : ℕ) : ℝ) := by
    calc ‖∑ a ∈ Ico M (M + (N + H : ℕ)), e ((a : ℝ) * θ)‖
        ≤ ∑ _a ∈ Ico M (M + (N + H : ℕ)), (1 : ℝ) :=
          (norm_sum_le _ _).trans (sum_le_sum fun a _ => by rw [norm_e])
      _ = ((N + H : ℕ) : ℝ) := by
          simp only [sum_const, nsmul_eq_mul, mul_one, Int.card_Ico, add_sub_cancel_left,
            Int.toNat_natCast]
  have h2 : ‖∑ h ∈ range H, e (-((h : ℝ) * θ))‖ ≤ (H : ℝ) := by
    calc ‖∑ h ∈ range H, e (-((h : ℝ) * θ))‖
        ≤ ∑ _h ∈ range H, (1 : ℝ) :=
          (norm_sum_le _ _).trans (sum_le_sum fun h _ => by rw [norm_e])
      _ = (H : ℝ) := by simp
  have hHpos : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  calc (H : ℝ)⁻¹ * ‖∑ a ∈ Ico M (M + (N + H : ℕ)), e ((a : ℝ) * θ)‖ *
        ‖∑ h ∈ range H, e (-((h : ℝ) * θ))‖
      ≤ (H : ℝ)⁻¹ * ((N + H : ℕ) : ℝ) * (H : ℝ) := by gcongr
    _ = (N : ℝ) + (H : ℝ) := by push_cast; field_simp [hHpos.ne']

lemma norm_trapWeight_fourier_le (M : ℤ) (N H : ℕ) (hH : 0 < H) (θ : ℝ) (hθ : 0 < dist1 θ) :
    ‖∑ n ∈ Ico (M - (H : ℤ)) (M + (N : ℤ) + (H : ℤ)), (trapWeight M N H n : ℂ) * e ((n : ℝ) * θ)‖ ≤
      1 / (4 * (H : ℝ) * dist1 θ ^ 2) := by
  rw [trapWeight_fourier M N H hH θ, norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
  have h1 := norm_sum_e_Ico_le M (N + H) θ hθ
  have h2 : ‖∑ h ∈ range H, e (-((h : ℝ) * θ))‖ ≤ 1 / (2 * dist1 θ) := by
    have heq : ∑ h ∈ range H, e (-((h : ℝ) * θ)) = ∑ k ∈ Ico (0 : ℤ) (0 + H), e ((k : ℝ) * (-θ)) := by
      refine Finset.sum_bij (fun h _ => (h : ℤ)) ?_ ?_ ?_ ?_
      · intro h hh; rw [mem_range] at hh; rw [mem_Ico]; omega
      · intro h1 _ h2 _ he; exact_mod_cast he
      · intro k hk; rw [mem_Ico] at hk; exact ⟨k.toNat, mem_range.mpr (by omega), by omega⟩
      · intro h _; congr 1; push_cast; ring
    rw [heq]
    have := norm_sum_e_Ico_le 0 H (-θ) (by rwa [dist1_neg])
    rwa [dist1_neg] at this
  have hHpos : (0 : ℝ) < H := Nat.cast_pos.mpr hH
  calc (H : ℝ)⁻¹ * ‖∑ a ∈ Ico M (M + (N + H : ℕ)), e ((a : ℝ) * θ)‖ *
        ‖∑ h ∈ range H, e (-((h : ℝ) * θ))‖
      ≤ (H : ℝ)⁻¹ * (1 / (2 * dist1 θ)) * (1 / (2 * dist1 θ)) := by gcongr
    _ = 1 / (4 * (H : ℝ) * dist1 θ ^ 2) := by field_simp [hHpos.ne', hθ.ne']; ring

lemma sum_inv_sq_Icc_le (H : ℕ) : ∑ m ∈ Icc 1 H, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 := by
  induction H with
  | zero => simp
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk; norm_num
    · have hk1 : 1 ≤ k := by omega
      have htel : ∀ n : ℕ, 1 ≤ n → ∑ m ∈ Icc 1 n, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => norm_num
        | succ t ht iht =>
          rw [show Icc 1 (t + 1) = insert (t + 1) (Icc 1 t) by ext m; simp only [mem_Icc, mem_insert]; omega]
          rw [sum_insert (by simp)]
          have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
          have hstep : 1 / ((t + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (t : ℝ) - 1 / ((t + 1 : ℕ) : ℝ) := by
            push_cast
            rw [div_sub_div _ _ ht0.ne' (by positivity)]
            have : (1 : ℝ) * (t + 1) - t * 1 = 1 := by ring
            rw [this]
            gcongr
            nlinarith
          linarith
      have := htel (k + 1) (by omega)
      have hpos : (0 : ℝ) ≤ 1 / ((k + 1 : ℕ) : ℝ) := by positivity
      linarith

/-- Box of integer vectors in `ℤ^d`. -/
noncomputable def intBox (d : ℕ) (M : ℤ) (N : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ : Fin d => Ico M (M + N))

/-- Dual `d`-dimensional large sieve inequality for `δ`-separated points in `(ℝ/ℤ)^d`. -/
theorem dual_large_sieve_nd {d : ℕ} {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (x : ι → Fin d → ℝ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → ∃ i : Fin d, δ ≤ dist1 (x r i - x r' i))
    (M : ℤ) (N : ℕ) (b : ι → ℂ) :
    ∑ n ∈ intBox d M N, ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ ^ 2 ≤
      (2 * (N : ℝ) + 6 / δ) ^ d * ∑ r ∈ R, ‖b r‖ ^ 2 := by
  let H : ℕ := ⌈1 / δ⌉₊
  have hH_ge : 1 / δ ≤ (H : ℝ) := Nat.le_ceil _
  have hH_pos : 0 < H := by
    have : (0 : ℝ) < H := lt_of_lt_of_le (by positivity) hH_ge
    exact_mod_cast this
  have hH_le : (H : ℝ) ≤ 2 / δ := by
    have hlt : (H : ℝ) < 1 / δ + 1 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 1 / δ by positivity)
    have h1 : (1 : ℝ) ≤ 1 / δ := (one_le_div hδ).mpr hδ1
    have h2 : 2 / δ = 1 / δ + 1 / δ := by ring
    linarith
  let B : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ : Fin d => Ico (M - (H : ℤ)) (M + (N : ℤ) + (H : ℤ)))
  let W : (Fin d → ℤ) → ℝ := fun n => ∏ i : Fin d, trapWeight M N H (n i)
  have hW_nn (n) : 0 ≤ W n := prod_nonneg fun i _ => trapWeight_nonneg M N H (n i)
  have hsub : intBox d M N ⊆ B := by
    intro n hn
    rw [intBox, Fintype.mem_piFinset] at hn
    rw [Fintype.mem_piFinset]
    intro i
    have hi := mem_Ico.mp (hn i)
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  have hstep1 : ∑ n ∈ intBox d M N, ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ ^ 2 ≤
      ∑ n ∈ B, W n * ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ ^ 2 := by
    calc ∑ n ∈ intBox d M N, ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ ^ 2
        = ∑ n ∈ intBox d M N, W n * ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ ^ 2 := by
          refine sum_congr rfl fun n hn => ?_
          rw [intBox, Fintype.mem_piFinset] at hn
          have hW1 : W n = 1 := prod_eq_one fun i _ => trapWeight_eq_one hH_pos (hn i)
          rw [hW1, one_mul]
      _ ≤ ∑ n ∈ B, W n * ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => mul_nonneg (hW_nn n) (sq_nonneg _)
  let K1 (θ : ℝ) : ℂ :=
    ∑ k ∈ Ico (M - (H : ℤ)) (M + (N : ℤ) + (H : ℤ)), (trapWeight M N H k : ℂ) * e ((k : ℝ) * θ)
  let K (θ : Fin d → ℝ) : ℂ := ∏ i : Fin d, K1 (θ i)
  have hK_eq (θ : Fin d → ℝ) :
      ∑ n ∈ B, (W n : ℂ) * e (∑ i : Fin d, (n i : ℝ) * θ i) = K θ := by
    dsimp [K, K1, B, W]
    rw [← Finset.sum_prod_piFinset]
    refine sum_congr rfl fun n _ => ?_
    have heprod : e (∑ i : Fin d, (n i : ℝ) * θ i) = ∏ i : Fin d, e ((n i : ℝ) * θ i) := by
      simp only [e, Complex.ofReal_sum, mul_sum, Complex.exp_sum]
    rw [heprod, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  have hnorm_sq (z : ℂ) : (‖z‖ ^ 2 : ℝ) = (z * star z).re := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hexpan : ∑ n ∈ B, W n * ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ ^ 2 =
      (∑ r ∈ R, ∑ r' ∈ R, b r * star (b r') * K (fun i => x r i - x r' i)).re := by
    have hinner : ∀ n ∈ B,
        (W n : ℂ) * ((∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)) *
          star (∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i))) =
        ∑ r ∈ R, ∑ r' ∈ R, b r * star (b r') * ((W n : ℂ) * e (∑ i : Fin d, (n i : ℝ) * (x r i - x r' i))) := by
      intro n _
      rw [star_sum, sum_mul]
      simp_rw [mul_sum]
      refine sum_congr rfl fun r _ => sum_congr rfl fun r' _ => ?_
      rw [star_mul', ← e_neg]
      have hmul : e (∑ i : Fin d, (n i : ℝ) * x r i) * e (-(∑ i : Fin d, (n i : ℝ) * x r' i)) =
          e (∑ i : Fin d, (n i : ℝ) * (x r i - x r' i)) := by
        rw [← e_add]
        congr 1
        rw [← sub_eq_add_neg, ← sum_sub_distrib]
        refine sum_congr rfl fun i _ => by ring
      calc (W n : ℂ) * (b r * e (∑ i : Fin d, (n i : ℝ) * x r i) *
            (star (b r') * e (-(∑ i : Fin d, (n i : ℝ) * x r' i))))
          = b r * star (b r') * ((W n : ℂ) * (e (∑ i : Fin d, (n i : ℝ) * x r i) *
            e (-(∑ i : Fin d, (n i : ℝ) * x r' i)))) := by ring
        _ = _ := by rw [hmul]
    calc ∑ n ∈ B, W n * ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ ^ 2
        = ∑ n ∈ B, ((W n : ℂ) * ((∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)) *
            star (∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)))).re := by
          refine sum_congr rfl fun n _ => ?_
          rw [Complex.re_ofReal_mul, ← hnorm_sq]
      _ = (∑ n ∈ B, (W n : ℂ) * ((∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)) *
            star (∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)))).re := (Complex.re_sum _ _).symm
      _ = (∑ n ∈ B, ∑ r ∈ R, ∑ r' ∈ R,
            b r * star (b r') * ((W n : ℂ) * e (∑ i : Fin d, (n i : ℝ) * (x r i - x r' i)))).re := by
          congr 1; exact sum_congr rfl hinner
      _ = (∑ r ∈ R, ∑ r' ∈ R, b r * star (b r') * K (fun i => x r i - x r' i)).re := by
          congr 1
          rw [sum_comm]
          refine sum_congr rfl fun r _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun r' _ => ?_
          rw [← mul_sum, hK_eq]
  -- Row-sum bound for `K`
  have hrow (r : ι) (hr : r ∈ R) :
      ∑ r' ∈ R, ‖K (fun i => x r i - x r' i)‖ ≤ (2 * (N : ℝ) + 6 / δ) ^ d := by
    let u : ι → Fin d → ℝ := fun r' i => (x r i - x r' i) - round (x r i - x r' i)
    let m : ι → Fin d → ℕ := fun r' i => ⌊|u r' i| / δ⌋₊
    let s : ι → Fin d → Bool := fun r' i => decide (0 ≤ u r' i)
    let Φ : ι → (Fin d → ℕ) × (Fin d → Bool) := fun r' => (m r', s r')
    have hinj : Set.InjOn Φ (R : Set ι) := by
      intro r1 hr1 r2 hr2 heq
      by_contra hne
      obtain ⟨i, hi⟩ := hsep r1 hr1 r2 hr2 hne
      have hm : m r1 i = m r2 i := congrFun (congrArg Prod.fst heq) i
      have hs : s r1 i = s r2 i := congrFun (congrArg Prod.snd heq) i
      have h1_lo : (m r1 i : ℝ) * δ ≤ |u r1 i| :=
        (le_div_iff₀ hδ).mp (Nat.floor_le (by positivity))
      have h1_hi : |u r1 i| < ((m r1 i : ℝ) + 1) * δ :=
        (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one _)
      have h2_lo : (m r2 i : ℝ) * δ ≤ |u r2 i| :=
        (le_div_iff₀ hδ).mp (Nat.floor_le (by positivity))
      have h2_hi : |u r2 i| < ((m r2 i : ℝ) + 1) * δ :=
        (div_lt_iff₀ hδ).mp (Nat.lt_floor_add_one _)
      rw [← hm] at h2_lo h2_hi
      have hdiff_lt : |u r1 i - u r2 i| < δ := by
        by_cases hpos : 0 ≤ u r1 i
        · have hpos2 : 0 ≤ u r2 i := by
            have : s r2 i = true := by rw [← hs]; simp [s, hpos]
            simpa [s] using this
          rw [abs_of_nonneg hpos] at h1_lo h1_hi
          rw [abs_of_nonneg hpos2] at h2_lo h2_hi
          rw [abs_lt]; constructor <;> linarith
        · have hneg1 : u r1 i < 0 := not_le.mp hpos
          have hneg2 : u r2 i < 0 := by
            have : s r2 i = false := by rw [← hs]; simp [s, hpos]
            exact not_le.mp (by simpa [s] using this)
          rw [abs_of_neg hneg1] at h1_lo h1_hi
          rw [abs_of_neg hneg2] at h2_lo h2_hi
          rw [abs_lt]; constructor <;> linarith
      have hdist_le : dist1 (x r1 i - x r2 i) ≤ |u r1 i - u r2 i| := by
        have hrel : x r1 i - x r2 i = (u r2 i - u r1 i) +
            ((round (x r i - x r2 i) - round (x r i - x r1 i) : ℤ) : ℝ) := by
          dsimp [u]; push_cast; ring
        rw [hrel, dist1_add_int]
        calc dist1 (u r2 i - u r1 i) ≤ |(u r2 i - u r1 i) - (0 : ℤ)| := dist1_le _ 0
          _ = |u r1 i - u r2 i| := by simp [abs_sub_comm]
      linarith
    let bf : ℕ → ℝ := fun k => if k = 0 then (N : ℝ) + (H : ℝ) else (H : ℝ) / (4 * (k : ℝ) ^ 2)
    have hbf_nn (k : ℕ) : 0 ≤ bf k := by dsimp [bf]; split_ifs <;> positivity
    have hK_le (r' : ι) : ‖K (fun i => x r i - x r' i)‖ ≤ ∏ i : Fin d, bf (m r' i) := by
      dsimp [K]
      rw [norm_prod]
      refine prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
      by_cases hm0 : m r' i = 0
      · simp only [bf, hm0, ↓reduceIte]
        exact norm_trapWeight_fourier_triv M N H hH_pos _
      · simp only [bf, hm0, ↓reduceIte]
        have hm_pos : (1 : ℝ) ≤ (m r' i : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hm0)
        have hdist_ge : (m r' i : ℝ) * δ ≤ dist1 (x r i - x r' i) := by
          have := (le_div_iff₀ hδ).mp (Nat.floor_le (show 0 ≤ |u r' i| / δ by positivity))
          simpa [dist1, u] using this
        have hdist_pos : 0 < dist1 (x r i - x r' i) := lt_of_lt_of_le (by positivity) hdist_ge
        have h1 := norm_trapWeight_fourier_le M N H hH_pos (x r i - x r' i) hdist_pos
        have hH_inv : (m r' i : ℝ) / (H : ℝ) ≤ dist1 (x r i - x r' i) := by
          have : (m r' i : ℝ) / (H : ℝ) ≤ (m r' i : ℝ) * δ := by
            rw [div_le_iff₀ (Nat.cast_pos.mpr hH_pos)]
            calc (m r' i : ℝ) = (m r' i : ℝ) * (δ * (1 / δ)) := by field_simp [hδ.ne']
              _ ≤ (m r' i : ℝ) * (δ * (H : ℝ)) := by gcongr
              _ = (m r' i : ℝ) * δ * (H : ℝ) := by ring
          exact this.trans hdist_ge
        calc ‖K1 (x r i - x r' i)‖
            ≤ 1 / (4 * (H : ℝ) * dist1 (x r i - x r' i) ^ 2) := h1
          _ ≤ 1 / (4 * (H : ℝ) * ((m r' i : ℝ) / (H : ℝ)) ^ 2) := by
              gcongr
          _ = (H : ℝ) / (4 * (m r' i : ℝ) ^ 2) := by
              have hHp : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hH_pos.ne'
              have hmp : (m r' i : ℝ) ≠ 0 := by linarith
              field_simp [hHp, hmp]
    let Mset : Finset (Fin d → ℕ) := Fintype.piFinset (fun _ : Fin d => range (H + 1))
    have hΦ_mem : ∀ r' ∈ R, Φ r' ∈ Mset ×ˢ (univ : Finset (Fin d → Bool)) := by
      intro r' _
      refine mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun i => mem_range.mpr ?_, mem_univ _⟩
      have hle : |u r' i| / δ ≤ (H : ℝ) := by
        have hhalf : |u r' i| ≤ 1 / 2 := abs_sub_round _
        calc |u r' i| / δ ≤ (1 / 2) / δ := by gcongr
          _ ≤ 1 / δ := by gcongr; norm_num
          _ ≤ (H : ℝ) := hH_ge
      have hfl : m r' i ≤ H := Nat.floor_le_of_le hle
      dsimp [Φ]; omega
    calc ∑ r' ∈ R, ‖K (fun i => x r i - x r' i)‖
        ≤ ∑ r' ∈ R, ∏ i : Fin d, bf (m r' i) := sum_le_sum fun r' _ => hK_le r'
      _ = ∑ p ∈ R.image Φ, ∏ i : Fin d, bf (p.1 i) := by
          rw [sum_image hinj]
      _ ≤ ∑ p ∈ Mset ×ˢ (univ : Finset (Fin d → Bool)), ∏ i : Fin d, bf (p.1 i) :=
          sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hΦ_mem) fun p _ _ =>
            prod_nonneg fun i _ => hbf_nn _
      _ = (univ : Finset (Fin d → Bool)).card * ∑ f ∈ Mset, ∏ i : Fin d, bf (f i) := by
          rw [sum_product_right]
          simp [sum_const, nsmul_eq_mul]
      _ = (2 : ℝ) ^ d * (∑ k ∈ range (H + 1), bf k) ^ d := by
          rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
            Nat.cast_ofNat]
          congr 1
          dsimp [Mset]
          exact (Finset.sum_pow' (range (H + 1)) bf d).symm
      _ = (2 * ∑ k ∈ range (H + 1), bf k) ^ d := (mul_pow _ _ _).symm
      _ ≤ (2 * (N : ℝ) + 6 / δ) ^ d := by
          apply pow_le_pow_left₀ (by positivity)
          have hsum_bf : ∑ k ∈ range (H + 1), bf k ≤ (N : ℝ) + 3 / δ := by
            have hsplit : range (H + 1) = insert 0 (Icc 1 H) := by
              ext k; simp only [mem_range, mem_insert, mem_Icc]; omega
            rw [hsplit, sum_insert (by simp)]
            have h0 : bf 0 = (N : ℝ) + (H : ℝ) := by simp [bf]
            have hrest : ∑ k ∈ Icc 1 H, bf k = ((H : ℝ) / 4) * ∑ k ∈ Icc 1 H, (1 : ℝ) / (k : ℝ) ^ 2 := by
              rw [mul_sum]
              refine sum_congr rfl fun k hk => ?_
              have hk0 : k ≠ 0 := by rw [mem_Icc] at hk; omega
              simp only [bf, hk0, ↓reduceIte]; ring
            rw [h0, hrest]
            have h2 := sum_inv_sq_Icc_le H
            have hHnn : (0 : ℝ) ≤ H := Nat.cast_nonneg H
            have h3 : (3 : ℝ) / δ = 3 / 2 * (2 / δ) := by ring
            nlinarith [hH_le, h2, hHnn, h3]
          have h6 : 2 * ((N : ℝ) + 3 / δ) = 2 * (N : ℝ) + 6 / δ := by ring
          linarith
  -- Schur test
  have hschur : (∑ r ∈ R, ∑ r' ∈ R, b r * star (b r') * K (fun i => x r i - x r' i)).re ≤
      (2 * (N : ℝ) + 6 / δ) ^ d * ∑ r ∈ R, ‖b r‖ ^ 2 := by
    calc (∑ r ∈ R, ∑ r' ∈ R, b r * star (b r') * K (fun i => x r i - x r' i)).re
        ≤ ‖∑ r ∈ R, ∑ r' ∈ R, b r * star (b r') * K (fun i => x r i - x r' i)‖ :=
          Complex.re_le_norm _
      _ ≤ ∑ r ∈ R, ∑ r' ∈ R, ‖b r‖ * ‖b r'‖ * ‖K (fun i => x r i - x r' i)‖ := by
          refine (norm_sum_le _ _).trans (sum_le_sum fun r _ => (norm_sum_le _ _).trans
            (sum_le_sum fun r' _ => ?_))
          rw [norm_mul, norm_mul, norm_star]
      _ ≤ ∑ r ∈ R, ∑ r' ∈ R, ((‖b r‖ ^ 2 + ‖b r'‖ ^ 2) / 2) * ‖K (fun i => x r i - x r' i)‖ := by
          refine sum_le_sum fun r _ => sum_le_sum fun r' _ => ?_
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          nlinarith [sq_nonneg (‖b r‖ - ‖b r'‖)]
      _ = (1 / 2 : ℝ) * (∑ r ∈ R, ‖b r‖ ^ 2 * ∑ r' ∈ R, ‖K (fun i => x r i - x r' i)‖) +
          (1 / 2 : ℝ) * (∑ r' ∈ R, ‖b r'‖ ^ 2 * ∑ r ∈ R, ‖K (fun i => x r i - x r' i)‖) := by
          have hsplit : ∀ r r', ((‖b r‖ ^ 2 + ‖b r'‖ ^ 2) / 2) * ‖K (fun i => x r i - x r' i)‖ =
              (1 / 2 : ℝ) * (‖b r‖ ^ 2 * ‖K (fun i => x r i - x r' i)‖) +
              (1 / 2 : ℝ) * (‖b r'‖ ^ 2 * ‖K (fun i => x r i - x r' i)‖) := fun r r' => by ring
          simp_rw [hsplit, sum_add_distrib, ← mul_sum]
          congr 1
          rw [sum_comm]
          congr 1; refine sum_congr rfl fun r' _ => by rw [← mul_sum]
      _ ≤ (1 / 2 : ℝ) * (∑ r ∈ R, ‖b r‖ ^ 2 * (2 * (N : ℝ) + 6 / δ) ^ d) +
          (1 / 2 : ℝ) * (∑ r' ∈ R, ‖b r'‖ ^ 2 * (2 * (N : ℝ) + 6 / δ) ^ d) := by
          gcongr with r hr r' hr'
          · exact hrow r hr
          · have hsym : ∀ r ∈ R, ‖K (fun i => x r i - x r' i)‖ = ‖K (fun i => x r' i - x r i)‖ := by
              intro r _
              dsimp [K, K1]
              rw [norm_prod, norm_prod]
              refine prod_congr rfl fun i _ => ?_
              have hconj : star (∑ k ∈ Ico (M - (H : ℤ)) (M + (N : ℤ) + (H : ℤ)),
                  (trapWeight M N H k : ℂ) * e ((k : ℝ) * (x r i - x r' i))) =
                  ∑ k ∈ Ico (M - (H : ℤ)) (M + (N : ℤ) + (H : ℤ)),
                  (trapWeight M N H k : ℂ) * e ((k : ℝ) * (x r' i - x r i)) := by
                rw [star_sum]
                refine sum_congr rfl fun k _ => ?_
                rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def, ← e_neg]
                congr 2; ring
              rw [← hconj, norm_star]
            rw [sum_congr rfl hsym]
            exact hrow r' hr'
      _ = (2 * (N : ℝ) + 6 / δ) ^ d * ∑ r ∈ R, ‖b r‖ ^ 2 := by
          rw [← sum_mul]; ring
  linarith [hstep1, hexpan, hschur]

/-- Primal `d`-dimensional large sieve inequality via duality. -/
theorem large_sieve_points_nd {d : ℕ} {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (x : ι → Fin d → ℝ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → ∃ i : Fin d, δ ≤ dist1 (x r i - x r' i))
    (M : ℤ) (N : ℕ) (F : Finset (Fin d → ℤ)) (hF : F ⊆ intBox d M N) (c : (Fin d → ℤ) → ℂ) :
    ∑ r ∈ R, ‖∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ ^ 2 ≤
      (2 * (N : ℝ) + 6 / δ) ^ d * ∑ n ∈ F, ‖c n‖ ^ 2 := by
  let S : ι → ℂ := fun r => ∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * x r i)
  let b : ι → ℂ := fun r => star (S r)
  have hLHS : ∑ r ∈ R, ‖S r‖ ^ 2 =
      (∑ n ∈ F, c n * ∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)).re := by
    have heq : ∑ r ∈ R, S r * b r =
        ∑ n ∈ F, c n * ∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i) := by
      simp_rw [S, sum_mul]
      rw [sum_comm]
      refine sum_congr rfl fun n _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun r _ => by ring
    rw [← heq, Complex.re_sum]
    refine sum_congr rfl fun r _ => ?_
    dsimp [b]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hCS : (∑ r ∈ R, ‖S r‖ ^ 2) ^ 2 ≤
      (∑ n ∈ F, ‖c n‖ ^ 2) * (∑ n ∈ F, ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ ^ 2) := by
    have h1 : ∑ r ∈ R, ‖S r‖ ^ 2 ≤
        ∑ n ∈ F, ‖c n‖ * ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ := by
      rw [hLHS]
      calc (∑ n ∈ F, c n * ∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)).re
          ≤ ‖∑ n ∈ F, c n * ∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ :=
            Complex.re_le_norm _
        _ ≤ ∑ n ∈ F, ‖c n * ∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ :=
            norm_sum_le _ _
        _ = ∑ n ∈ F, ‖c n‖ * ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ := by
            refine sum_congr rfl fun n _ => norm_mul _ _
    have hnn : 0 ≤ ∑ r ∈ R, ‖S r‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    calc (∑ r ∈ R, ‖S r‖ ^ 2) ^ 2
        ≤ (∑ n ∈ F, ‖c n‖ * ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖) ^ 2 :=
          pow_le_pow_left₀ hnn h1 2
      _ ≤ (∑ n ∈ F, ‖c n‖ ^ 2) *
          (∑ n ∈ F, ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ ^ 2) :=
          sum_mul_sq_le_sq_mul_sq F _ _
  have hdual : ∑ n ∈ F, ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ ^ 2 ≤
      (2 * (N : ℝ) + 6 / δ) ^ d * ∑ r ∈ R, ‖S r‖ ^ 2 := by
    calc ∑ n ∈ F, ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ ^ 2
        ≤ ∑ n ∈ intBox d M N, ‖∑ r ∈ R, b r * e (∑ i : Fin d, (n i : ℝ) * x r i)‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hF fun _ _ _ => sq_nonneg _
      _ ≤ (2 * (N : ℝ) + 6 / δ) ^ d * ∑ r ∈ R, ‖b r‖ ^ 2 :=
          dual_large_sieve_nd R x δ hδ hδ1 hsep M N b
      _ = (2 * (N : ℝ) + 6 / δ) ^ d * ∑ r ∈ R, ‖S r‖ ^ 2 := by
          congr 1; refine sum_congr rfl fun r _ => by simp [b]
  by_cases hZ : ∑ r ∈ R, ‖S r‖ ^ 2 = 0
  · rw [hZ]; positivity
  · have hZpos : 0 < ∑ r ∈ R, ‖S r‖ ^ 2 :=
      lt_of_le_of_ne (sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hZ)
    have hprod : (∑ r ∈ R, ‖S r‖ ^ 2) ^ 2 ≤
        ((2 * (N : ℝ) + 6 / δ) ^ d * ∑ n ∈ F, ‖c n‖ ^ 2) * (∑ r ∈ R, ‖S r‖ ^ 2) := by
      calc (∑ r ∈ R, ‖S r‖ ^ 2) ^ 2
          ≤ (∑ n ∈ F, ‖c n‖ ^ 2) * ((2 * (N : ℝ) + 6 / δ) ^ d * ∑ r ∈ R, ‖S r‖ ^ 2) :=
            hCS.trans (mul_le_mul_of_nonneg_left hdual (sum_nonneg fun _ _ => sq_nonneg _))
        _ = ((2 * (N : ℝ) + 6 / δ) ^ d * ∑ n ∈ F, ‖c n‖ ^ 2) * (∑ r ∈ R, ‖S r‖ ^ 2) := by ring
    nlinarith

/-- Primitive `d`-dimensional residue vectors mod `q`: `a ∈ [0, q)^d` with `gcd(q, a_0, ..., a_{d-1}) = 1`. -/
def Und (d q : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ : Fin d => range q)).filter (fun a => q.Coprime (univ.gcd a))

lemma farey_sep_nd {d Q q q' : ℕ} (hq : 1 ≤ q) (hqQ : q ≤ Q) (hq' : 1 ≤ q') (hq'Q : q' ≤ Q)
    {a a' : Fin d → ℕ} (ha : a ∈ Und d q) (ha' : a' ∈ Und d q')
    (hne : (q, a) ≠ (q', a')) :
    ∃ i : Fin d, 1 / (Q : ℝ) ^ 2 ≤ dist1 ((a i : ℝ) / q - (a' i : ℝ) / q') := by
  have ha_lt : ∀ i, a i < q := fun i => mem_range.mp (Fintype.mem_piFinset.mp (mem_filter.mp ha).1 i)
  have ha'_lt : ∀ i, a' i < q' := fun i => mem_range.mp (Fintype.mem_piFinset.mp (mem_filter.mp ha').1 i)
  have hcop : q.Coprime (univ.gcd a) := (mem_filter.mp ha).2
  have hcop' : q'.Coprime (univ.gcd a') := (mem_filter.mp ha').2
  by_contra! hall
  have heq_rat : ∀ i : Fin d, a i * q' = a' i * q := by
    intro i
    by_contra hne_i
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hq'_pos : (0 : ℝ) < q' := by exact_mod_cast (by omega : 0 < q')
    have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
    have hlt1 : |(a i : ℝ) / q - (a' i : ℝ) / q'| < 1 := by
      have h1 : (0 : ℝ) ≤ (a i : ℝ) / q := by positivity
      have h2 : (a i : ℝ) / q < 1 := (div_lt_one hq_pos).mpr (by exact_mod_cast ha_lt i)
      have h3 : (0 : ℝ) ≤ (a' i : ℝ) / q' := by positivity
      have h4 : (a' i : ℝ) / q' < 1 := (div_lt_one hq'_pos).mpr (by exact_mod_cast ha'_lt i)
      rw [abs_lt]; constructor <;> linarith
    have hdist_ge : 1 / ((q : ℝ) * q') ≤ dist1 ((a i : ℝ) / q - (a' i : ℝ) / q') := by
      set k : ℤ := round ((a i : ℝ) / q - (a' i : ℝ) / q')
      change 1 / ((q : ℝ) * q') ≤ |(a i : ℝ) / q - (a' i : ℝ) / q' - (k : ℝ)|
      have hnum_ne : ((a i : ℤ) * q' - (a' i : ℤ) * q - k * (q : ℤ) * q') ≠ 0 := by
        intro h0
        have hdiff_int : (a i : ℝ) / q - (a' i : ℝ) / q' = (k : ℝ) := by
          have h0R : (a i : ℝ) * q' - (a' i : ℝ) * q - (k : ℝ) * q * q' = 0 := by exact_mod_cast h0
          field_simp [hq_pos.ne', hq'_pos.ne']
          linarith
        rw [hdiff_int] at hlt1
        have hk0 : k = 0 := by
          have : |(k : ℝ)| < 1 := hlt1
          have : -(1 : ℝ) < (k : ℝ) ∧ (k : ℝ) < 1 := abs_lt.mp this
          have : -(1 : ℤ) < k ∧ k < 1 := ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
          omega
        rw [hk0, zero_mul, zero_mul, sub_zero, sub_eq_zero] at h0
        exact hne_i (by exact_mod_cast h0)
      have hnum_ge : (1 : ℝ) ≤ |((a i : ℤ) * q' - (a' i : ℤ) * q - k * (q : ℤ) * q' : ℤ)| := by
        exact_mod_cast Int.one_le_abs hnum_ne
      have heq_f : |(a i : ℝ) / q - (a' i : ℝ) / q' - (k : ℝ)| =
          |((a i : ℤ) * q' - (a' i : ℤ) * q - k * (q : ℤ) * q' : ℤ)| / ((q : ℝ) * q') := by
        rw [Int.cast_abs, ← abs_of_pos (mul_pos hq_pos hq'_pos), ← abs_div]
        congr 1; push_cast; field_simp [hq_pos.ne', hq'_pos.ne']
      rw [heq_f]
      exact div_le_div_of_nonneg_right hnum_ge (by positivity)
    have hQ2 : 1 / (Q : ℝ) ^ 2 ≤ 1 / ((q : ℝ) * q') := by
      rw [sq]
      gcongr
    linarith [hall i]
  have hdvd1 : q ∣ q' := by
    have hd : q ∣ univ.gcd (fun i => a i * q') :=
      Finset.dvd_gcd fun i _ => ⟨a' i, by rw [heq_rat i, mul_comm]⟩
    have hmul : univ.gcd (fun i => a i * q') = univ.gcd a * q' := by
      rw [Finset.gcd_mul_right]; simp
    rw [hmul] at hd
    exact hcop.dvd_of_dvd_mul_left hd
  have hdvd2 : q' ∣ q := by
    have hd : q' ∣ univ.gcd (fun i => a' i * q) :=
      Finset.dvd_gcd fun i _ => ⟨a i, by rw [← heq_rat i, mul_comm]⟩
    have hmul : univ.gcd (fun i => a' i * q) = univ.gcd a' * q := by
      rw [Finset.gcd_mul_right]; simp
    rw [hmul] at hd
    exact hcop'.dvd_of_dvd_mul_left hd
  have hqq' : q = q' := Nat.dvd_antisymm hdvd1 hdvd2
  have haa' : a = a' := by
    ext i
    have hi := heq_rat i
    rw [hqq'] at hi
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q') hi
  exact hne (Prod.ext hqq' haa')

/-- `d`-dimensional Farey large sieve inequality. -/
theorem large_sieve_farey_nd {d : ℕ} (Q : ℕ) (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ)
    (F : Finset (Fin d → ℤ)) (hF : F ⊆ intBox d M N) (c : (Fin d → ℤ) → ℂ) :
    ∑ q ∈ Icc 1 Q, ∑ a ∈ Und d q,
        ‖∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * ((a i : ℝ) / q))‖ ^ 2 ≤
      (2 * (N : ℝ) + 6 * (Q : ℝ) ^ 2) ^ d * ∑ n ∈ F, ‖c n‖ ^ 2 := by
  let R : Finset (ℕ × (Fin d → ℕ)) := (Icc 1 Q).sigma (fun q => Und d q)
    |>.map ⟨fun p => (p.1, p.2), fun p1 p2 h => by
      cases p1; cases p2; simp only [Prod.mk.injEq] at h; exact Sigma.ext h.1 (heq_of_eq h.2)⟩
  have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hδ : 0 < 1 / (Q : ℝ) ^ 2 := by positivity
  have hδ1 : 1 / (Q : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    nlinarith
  have hsep : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' →
      ∃ i : Fin d, 1 / (Q : ℝ) ^ 2 ≤ dist1 ((r.2 i : ℝ) / r.1 - (r'.2 i : ℝ) / r'.1) := by
    intro r hr r' hr' hne
    obtain ⟨⟨q, a⟩, hqa, rfl⟩ := mem_map.mp hr
    obtain ⟨⟨q', a'⟩, hqa', rfl⟩ := mem_map.mp hr'
    rw [mem_sigma, mem_Icc] at hqa hqa'
    exact farey_sep_nd hqa.1.1 hqa.1.2 hqa'.1.1 hqa'.1.2 hqa.2 hqa'.2 hne
  have hls := large_sieve_points_nd R (fun r i => (r.2 i : ℝ) / r.1) (1 / (Q : ℝ) ^ 2) hδ hδ1
    hsep M N F hF c
  have hsum_eq : ∑ r ∈ R, ‖∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * ((r.2 i : ℝ) / r.1))‖ ^ 2 =
      ∑ q ∈ Icc 1 Q, ∑ a ∈ Und d q,
        ‖∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * ((a i : ℝ) / q))‖ ^ 2 := by
    dsimp [R]
    rw [sum_map, sum_sigma]
    rfl
  rw [hsum_eq] at hls
  have h6 : 6 / (1 / (Q : ℝ) ^ 2) = 6 * (Q : ℝ) ^ 2 := by field_simp [hQ_pos.ne']
  rwa [h6] at hls

section MontgomeryND

lemma sum_e_orth_1d (p : ℕ) (b b' : ℕ) (hb : b < p) (hb' : b' < p) :
    ∑ a ∈ range p, e (((b : ℝ) - b') * a / p) = if b = b' then (p : ℂ) else 0 := by
  by_cases hbb' : b = b'
  · subst hbb'
    simp [e_zero]
  · simp only [hbb', ↓reduceIte]
    have hp : 0 < p := by omega
    have hmul : ∀ a : ℕ, e (((b : ℝ) - b') * a / p) = (e (((b : ℝ) - b') / p)) ^ a := fun a => by
      rw [← e_nat_mul]; congr 1; ring
    simp_rw [hmul]
    have hne : e (((b : ℝ) - b') / p) ≠ 1 := by
      intro h1
      have h4 := four_dist1_le_norm_e_sub_one (((b : ℝ) - b') / p)
      rw [h1, sub_self, norm_zero] at h4
      have h0 : dist1 (((b : ℝ) - b') / p) = 0 := le_antisymm (by linarith) (dist1_nonneg _)
      have hlt : |((b : ℝ) - b') / p| < 1 := by
        have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
        have hbR : (b : ℝ) < p := by exact_mod_cast hb
        have hb'R : (b' : ℝ) < p := by exact_mod_cast hb'
        have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
        have hb'0 : (0 : ℝ) ≤ b' := Nat.cast_nonneg b'
        rw [abs_div, abs_of_pos hpR, div_lt_one hpR, abs_lt]
        constructor <;> linarith
      have hdist_eq : ((b : ℝ) - b') / p = (round (((b : ℝ) - b') / p) : ℤ) := by
        have := abs_eq_zero.mp h0; linarith
      rw [hdist_eq] at hlt
      have hk0 : round (((b : ℝ) - b') / p) = 0 := by
        have : -(1 : ℝ) < (round (((b : ℝ) - b') / p) : ℤ) ∧
            ((round (((b : ℝ) - b') / p) : ℤ) : ℝ) < 1 := abs_lt.mp hlt
        have : -(1 : ℤ) < round (((b : ℝ) - b') / p) ∧ round (((b : ℝ) - b') / p) < 1 :=
          ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
        omega
      rw [hk0, Int.cast_zero, div_eq_zero_iff] at hdist_eq
      rcases hdist_eq with hsub | hp0
      · exact hbb' (by exact_mod_cast sub_eq_zero.mp hsub)
      · exact hp.ne' (by exact_mod_cast hp0)
    rw [geom_sum_eq hne]
    have hp1 : (e (((b : ℝ) - b') / p)) ^ p = 1 := by
      rw [← e_nat_mul]
      have : (p : ℝ) * (((b : ℝ) - b') / p) = ((b : ℤ) - (b' : ℤ) : ℤ) := by
        have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
        push_cast; field_simp [hpR]
      rw [this, e_int]
    rw [hp1, sub_self, zero_div]

lemma parseval_mod_nd {d : ℕ} (p : ℕ) (_hp : 0 < p) (Z : (Fin d → ℕ) → ℂ) :
    ∑ a ∈ Fintype.piFinset (fun _ : Fin d => range p),
      ‖∑ h ∈ Fintype.piFinset (fun _ : Fin d => range p),
          Z h * e (∑ i : Fin d, (h i : ℝ) * ((a i : ℝ) / p))‖ ^ 2 =
      (p : ℝ) ^ d * ∑ h ∈ Fintype.piFinset (fun _ : Fin d => range p), ‖Z h‖ ^ 2 := by
  let P := Fintype.piFinset (fun _ : Fin d => range p)
  have hnorm_sq (z : ℂ) : (‖z‖ ^ 2 : ℝ) = (z * star z).re := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hC : ∑ a ∈ P,
      (∑ h ∈ P, Z h * e (∑ i : Fin d, (h i : ℝ) * ((a i : ℝ) / p))) *
      star (∑ h ∈ P, Z h * e (∑ i : Fin d, (h i : ℝ) * ((a i : ℝ) / p))) =
      ((p : ℂ) ^ d) * ∑ h ∈ P, Z h * star (Z h) := by
    calc ∑ a ∈ P,
          (∑ h ∈ P, Z h * e (∑ i : Fin d, (h i : ℝ) * ((a i : ℝ) / p))) *
          star (∑ h ∈ P, Z h * e (∑ i : Fin d, (h i : ℝ) * ((a i : ℝ) / p)))
        = ∑ a ∈ P, ∑ h ∈ P, ∑ h' ∈ P,
            Z h * star (Z h') * e (∑ i : Fin d, ((h i : ℝ) - h' i) * (a i : ℝ) / p) := by
          refine sum_congr rfl fun a _ => ?_
          rw [star_sum, sum_mul]
          refine sum_congr rfl fun h _ => ?_
          rw [mul_sum]
          refine sum_congr rfl fun h' _ => ?_
          rw [star_mul', ← e_neg]
          have he : e (∑ i : Fin d, (h i : ℝ) * ((a i : ℝ) / p)) *
              e (-(∑ i : Fin d, (h' i : ℝ) * ((a i : ℝ) / p))) =
              e (∑ i : Fin d, ((h i : ℝ) - h' i) * (a i : ℝ) / p) := by
            rw [← e_add]; congr 1
            rw [← sub_eq_add_neg, ← sum_sub_distrib]
            refine sum_congr rfl fun i _ => by ring
          calc Z h * e (∑ i : Fin d, (h i : ℝ) * ((a i : ℝ) / p)) *
                (star (Z h') * e (-(∑ i : Fin d, (h' i : ℝ) * ((a i : ℝ) / p))))
              = Z h * star (Z h') * (e (∑ i : Fin d, (h i : ℝ) * ((a i : ℝ) / p)) *
                e (-(∑ i : Fin d, (h' i : ℝ) * ((a i : ℝ) / p)))) := by ring
            _ = _ := by rw [he]
      _ = ∑ h ∈ P, ∑ h' ∈ P, Z h * star (Z h') *
            ∑ a ∈ P, e (∑ i : Fin d, ((h i : ℝ) - h' i) * (a i : ℝ) / p) := by
          rw [sum_comm]
          refine sum_congr rfl fun h _ => ?_
          rw [sum_comm]
          refine sum_congr rfl fun h' _ => by rw [← mul_sum]
      _ = ∑ h ∈ P, ∑ h' ∈ P, Z h * star (Z h') *
            (if h = h' then (p : ℂ) ^ d else 0) := by
          refine sum_congr rfl fun h hh => sum_congr rfl fun h' hh' => ?_
          congr 1
          have hprod : ∑ a ∈ P, e (∑ i : Fin d, ((h i : ℝ) - h' i) * (a i : ℝ) / p) =
              ∏ i : Fin d, ∑ a ∈ range p, e (((h i : ℝ) - h' i) * (a : ℝ) / p) := by
            dsimp [P]
            rw [← Finset.sum_prod_piFinset]
            refine sum_congr rfl fun a _ => ?_
            simp only [e, Complex.ofReal_sum, mul_sum, Complex.exp_sum]
          rw [hprod]
          have horth : ∀ i : Fin d,
              ∑ a ∈ range p, e (((h i : ℝ) - h' i) * (a : ℝ) / p) =
              if h i = h' i then (p : ℂ) else 0 := fun i =>
            sum_e_orth_1d p (h i) (h' i) (mem_range.mp (Fintype.mem_piFinset.mp hh i))
              (mem_range.mp (Fintype.mem_piFinset.mp hh' i))
          simp_rw [horth]
          by_cases hhh' : h = h'
          · subst hhh'; simp
          · rw [if_neg hhh']
            obtain ⟨i, hi⟩ : ∃ i, h i ≠ h' i := by
              by_contra! hall; exact hhh' (funext hall)
            exact prod_eq_zero (mem_univ i) (if_neg hi)
      _ = ((p : ℂ) ^ d) * ∑ h ∈ P, Z h * star (Z h) := by
          rw [mul_sum]
          refine sum_congr rfl fun h hh => ?_
          rw [sum_eq_single h]
          · simp [mul_comm]
          · intro h' _ hne; simp [Ne.symm hne]
          · intro hnot; exact absurd hh hnot
  calc ∑ a ∈ P, ‖∑ h ∈ P, Z h * e (∑ i : Fin d, (h i : ℝ) * ((a i : ℝ) / p))‖ ^ 2
      = (∑ a ∈ P, (∑ h ∈ P, Z h * e (∑ i : Fin d, (h i : ℝ) * ((a i : ℝ) / p))) *
          star (∑ h ∈ P, Z h * e (∑ i : Fin d, (h i : ℝ) * ((a i : ℝ) / p)))).re := by
        rw [Complex.re_sum]
        exact sum_congr rfl fun a _ => hnorm_sq _
    _ = (((p : ℂ) ^ d) * ∑ h ∈ P, Z h * star (Z h)).re := by rw [hC]
    _ = (p : ℝ) ^ d * ∑ h ∈ P, ‖Z h‖ ^ 2 := by
        have hpR : ((p : ℂ) ^ d) = (((p : ℝ) ^ d : ℝ) : ℂ) := by push_cast; rfl
        rw [hpR, Complex.re_ofReal_mul, Complex.re_sum]
        congr 1; exact sum_congr rfl fun h _ => (hnorm_sq _).symm

/-- Residue vector of `n : Fin d → ℤ` mod `p`. -/
def vecMod {d : ℕ} (p : ℕ) (n : Fin d → ℤ) : Fin d → ℕ :=
  fun i => (n i).natMod p

lemma vecMod_mem {d p : ℕ} (hp : 0 < p) (n : Fin d → ℤ) :
    vecMod p n ∈ Fintype.piFinset (fun _ : Fin d => range p) := by
  rw [Fintype.mem_piFinset]
  intro i
  rw [mem_range]
  dsimp [vecMod]
  have h1 : (n i).natMod p = (n i % (p : ℤ)).toNat := rfl
  rw [h1]
  have hlt := Int.emod_lt_of_pos (n i) (by exact_mod_cast hp : (0 : ℤ) < p)
  have hnn := Int.emod_nonneg (n i) (by exact_mod_cast hp.ne' : (p : ℤ) ≠ 0)
  omega

lemma e_vecMod {d p : ℕ} (hp : 0 < p) (n : Fin d → ℤ) (a : Fin d → ℕ) :
    e (∑ i : Fin d, (n i : ℝ) * ((a i : ℝ) / p)) =
      e (∑ i : Fin d, ((vecMod p n i : ℕ) : ℝ) * ((a i : ℝ) / p)) := by
  have hterm : ∀ i : Fin d,
      e ((n i : ℝ) * ((a i : ℝ) / p)) = e (((vecMod p n i : ℕ) : ℝ) * ((a i : ℝ) / p)) := by
    intro i
    have hdiv : n i = (n i % (p : ℤ)) + (p : ℤ) * (n i / (p : ℤ)) := (Int.emod_add_mul_ediv _ _).symm
    have hnn : 0 ≤ n i % (p : ℤ) := Int.emod_nonneg (n i) (by exact_mod_cast hp.ne')
    have hmod : ((vecMod p n i : ℕ) : ℤ) = n i % (p : ℤ) := Int.toNat_of_nonneg hnn
    have hdiff : (n i : ℝ) * ((a i : ℝ) / p) =
        ((vecMod p n i : ℕ) : ℝ) * ((a i : ℝ) / p) + (((n i / (p : ℤ)) * (a i : ℤ) : ℤ) : ℝ) := by
      have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
      have hnR : (n i : ℝ) = ((vecMod p n i : ℕ) : ℝ) + (p : ℝ) * ((n i / (p : ℤ) : ℤ) : ℝ) := by
        exact_mod_cast (hmod.symm ▸ hdiv)
      rw [hnR]; push_cast; field_simp [hpR]
    rw [hdiff, e_add_int]
  have hprod : ∀ f : Fin d → ℝ, e (∑ i : Fin d, f i) = ∏ i : Fin d, e (f i) := fun f => by
    simp only [e, Complex.ofReal_sum, mul_sum, Complex.exp_sum]
  rw [hprod, hprod]
  exact prod_congr rfl fun i _ => hterm i

/-- Nonnegative local density factor `ω(p) / (p^d - ω(p))`. -/
noncomputable def hfacND (d : ℕ) (Ω : ℕ → Finset (Fin d → ℕ)) (p : ℕ) : ℝ :=
  ((Ω p).card : ℝ) / ((p : ℝ) ^ d - ((Ω p).card : ℝ))

lemma hfacND_nonneg {d : ℕ} (Ω : ℕ → Finset (Fin d → ℕ)) (p : ℕ)
    (hΩ : Ω p ⊆ Fintype.piFinset (fun _ : Fin d => range p)) :
    0 ≤ hfacND d Ω p := by
  have hcard : (Ω p).card ≤ p ^ d := by
    calc (Ω p).card ≤ (Fintype.piFinset (fun _ : Fin d => range p)).card := card_le_card hΩ
      _ = p ^ d := by simp [Fintype.card_piFinset]
  have hle : ((Ω p).card : ℝ) ≤ (p : ℝ) ^ d := by exact_mod_cast hcard
  unfold hfacND
  exact div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hle)

lemma montgomery_prime_nd {d : ℕ} (p : ℕ) (hp : p.Prime)
    (Ω : Finset (Fin d → ℕ)) (hΩ : Ω ⊆ Fintype.piFinset (fun _ : Fin d => range p))
    (F : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ)
    (hvan : ∀ n ∈ F, vecMod p n ∈ Ω → c n = 0) :
    ((Ω.card : ℝ) / ((p : ℝ) ^ d - (Ω.card : ℝ))) * ‖∑ n ∈ F, c n‖ ^ 2 ≤
      ∑ a ∈ Und d p, ‖∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * ((a i : ℝ) / p))‖ ^ 2 := by
  let P := Fintype.piFinset (fun _ : Fin d => range p)
  have hcard_P : P.card = p ^ d := by dsimp [P]; rw [Fintype.card_piFinset]; simp
  have hΩ_le : Ω.card ≤ p ^ d := by rw [← hcard_P]; exact card_le_card hΩ
  let Z : (Fin d → ℕ) → ℂ := fun h => ∑ n ∈ F.filter (fun n => vecMod p n = h), c n
  have hZ_sum : ∑ h ∈ P, Z h = ∑ n ∈ F, c n := by
    dsimp [Z]
    rw [← sum_fiberwise_of_maps_to (fun n _ => vecMod_mem hp.pos n)]
  have hZ_van : ∀ h ∈ Ω, Z h = 0 := fun h hh => by
    dsimp [Z]
    exact sum_eq_zero fun n hn => hvan n (mem_filter.mp hn).1 ((mem_filter.mp hn).2.symm ▸ hh)
  have hS_eq : ∀ a : Fin d → ℕ,
      ∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * ((a i : ℝ) / p)) =
      ∑ h ∈ P, Z h * e (∑ i : Fin d, (h i : ℝ) * ((a i : ℝ) / p)) := by
    intro a
    rw [← sum_fiberwise_of_maps_to (g := vecMod p) (fun n _ => vecMod_mem hp.pos n)]
    refine sum_congr rfl fun h _ => ?_
    dsimp [Z]
    rw [sum_mul]
    refine sum_congr rfl fun n hn => ?_
    rw [e_vecMod hp.pos n a, (mem_filter.mp hn).2]
  have hparseval : ∑ a ∈ P, ‖∑ h ∈ P, Z h * e (∑ i : Fin d, (h i : ℝ) * ((a i : ℝ) / p))‖ ^ 2 =
      (p : ℝ) ^ d * ∑ h ∈ P, ‖Z h‖ ^ 2 := parseval_mod_nd p hp.pos Z
  simp_rw [← hS_eq] at hparseval
  have hUnd_eq : Und d p = P.erase (fun _ => 0) := by
    ext a
    simp only [Und, P, mem_filter, mem_erase, Fintype.mem_piFinset, mem_range]
    constructor
    · rintro ⟨ha, hcop⟩
      refine ⟨?_, ha⟩
      intro ha0
      subst ha0
      have hgcd0 : univ.gcd (fun _ : Fin d => 0) = 0 := by
        rw [Finset.gcd_eq_zero_iff]; intro _ _; rfl
      rw [hgcd0, Nat.coprime_zero_right] at hcop
      exact hp.ne_one hcop
    · rintro ⟨hne, ha⟩
      refine ⟨ha, ?_⟩
      rw [hp.coprime_iff_not_dvd]
      intro hdvd
      apply hne
      ext i
      have hdi : p ∣ a i := hdvd.trans (Finset.gcd_dvd (mem_univ i))
      exact Nat.eq_zero_of_dvd_of_lt hdi (ha i)
  have h0_mem : (fun _ : Fin d => 0) ∈ P := Fintype.mem_piFinset.mpr fun _ => mem_range.mpr hp.pos
  have hsplit : ∑ a ∈ P, ‖∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * ((a i : ℝ) / p))‖ ^ 2 =
      ‖∑ n ∈ F, c n‖ ^ 2 +
      ∑ a ∈ Und d p, ‖∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * ((a i : ℝ) / p))‖ ^ 2 := by
    rw [hUnd_eq, ← add_sum_erase _ _ h0_mem]
    congr 1
    have : ∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * (((0 : ℕ) : ℝ) / p)) = ∑ n ∈ F, c n := by
      refine sum_congr rfl fun n _ => by simp [e_zero]
    rw [this]
  by_cases hfull : Ω.card = p ^ d
  · have hEq : Ω = P := eq_of_subset_of_card_le hΩ (by rw [hcard_P, hfull])
    have h0 : ∑ n ∈ F, c n = 0 := by
      rw [← hZ_sum]
      exact sum_eq_zero fun h hh => hZ_van h (hEq ▸ hh)
    rw [h0, norm_zero, zero_pow (by decide), mul_zero]
    exact sum_nonneg fun _ _ => sq_nonneg _
  · have hlt : Ω.card < p ^ d := lt_of_le_of_ne hΩ_le hfull
    have hrem_pos : (0 : ℝ) < (p : ℝ) ^ d - (Ω.card : ℝ) := by
      have : ((Ω.card : ℕ) : ℝ) < (p : ℝ) ^ d := by exact_mod_cast hlt
      linarith
    have hcs : ‖∑ n ∈ F, c n‖ ^ 2 ≤ ((p : ℝ) ^ d - (Ω.card : ℝ)) * ∑ h ∈ P, ‖Z h‖ ^ 2 := by
      have hsum_sdiff : ∑ n ∈ F, c n = ∑ h ∈ P \ Ω, Z h := by
        rw [← hZ_sum]
        symm
        apply sum_subset sdiff_subset
        intro h hh hnot
        exact hZ_van h (by simpa [hh] using hnot)
      have hcard_sdiff : ((P \ Ω).card : ℝ) = (p : ℝ) ^ d - (Ω.card : ℝ) := by
        rw [card_sdiff_of_subset hΩ, hcard_P, Nat.cast_sub hΩ_le]; push_cast; rfl
      calc ‖∑ n ∈ F, c n‖ ^ 2
          = ‖∑ h ∈ P \ Ω, Z h‖ ^ 2 := by rw [hsum_sdiff]
        _ ≤ (∑ h ∈ P \ Ω, (1 : ℝ) * ‖Z h‖) ^ 2 := by
            apply pow_le_pow_left₀ (norm_nonneg _)
            simpa using norm_sum_le (P \ Ω) Z
        _ ≤ (∑ _h ∈ P \ Ω, (1 : ℝ) ^ 2) * (∑ h ∈ P \ Ω, ‖Z h‖ ^ 2) :=
            sum_mul_sq_le_sq_mul_sq (P \ Ω) _ _
        _ = ((p : ℝ) ^ d - (Ω.card : ℝ)) * ∑ h ∈ P \ Ω, ‖Z h‖ ^ 2 := by
            simp [hcard_sdiff]
        _ ≤ ((p : ℝ) ^ d - (Ω.card : ℝ)) * ∑ h ∈ P, ‖Z h‖ ^ 2 := by
            gcongr
            exact sdiff_subset
    have h1 : (p : ℝ) ^ d * ‖∑ n ∈ F, c n‖ ^ 2 ≤
        ((p : ℝ) ^ d - (Ω.card : ℝ)) *
          (‖∑ n ∈ F, c n‖ ^ 2 +
            ∑ a ∈ Und d p, ‖∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * ((a i : ℝ) / p))‖ ^ 2) := by
      rw [← hsplit, hparseval]
      nlinarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hrem_pos]
    nlinarith

/-- CRT factorization of primitive residue vectors mod `q1 * q2` for coprime `q1, q2`. -/
lemma sum_Und_mul {d : ℕ} (q1 q2 : ℕ) (h1 : 0 < q1) (h2 : 0 < q2) (hcop : q1.Coprime q2)
    (f : (Fin d → ℝ) → ℝ)
    (hper : ∀ x y : Fin d → ℝ, (∀ i, ∃ k : ℤ, x i - y i = k) → f x = f y) :
    ∑ a ∈ Und d (q1 * q2), f (fun i => (a i : ℝ) / (q1 * q2 : ℕ)) =
      ∑ a1 ∈ Und d q1, ∑ a2 ∈ Und d q2,
        f (fun i => (a1 i : ℝ) / q1 + (a2 i : ℝ) / q2) := by
  let φ : (Fin d → ℕ) × (Fin d → ℕ) → (Fin d → ℕ) :=
    fun p i => (p.1 i * q2 + p.2 i * q1) % (q1 * q2)
  have hmap : ∀ a1 ∈ Und d q1, ∀ a2 ∈ Und d q2, φ (a1, a2) ∈ Und d (q1 * q2) := by
    intro a1 ha1 a2 ha2
    have hc1 := (mem_filter.mp ha1).2
    have hc2 := (mem_filter.mp ha2).2
    refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i =>
      mem_range.mpr (Nat.mod_lt _ (Nat.mul_pos h1 h2)), ?_⟩
    rw [Nat.coprime_mul_iff_left]
    constructor
    · rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have hpq1 : p ∣ q1 := hpd.trans (Nat.gcd_dvd_left _ _)
      have hpg : p ∣ univ.gcd (φ (a1, a2)) := hpd.trans (Nat.gcd_dvd_right _ _)
      have hpa1 : p ∣ univ.gcd a1 := Finset.dvd_gcd fun i _ => by
        have hpi : p ∣ φ (a1, a2) i := hpg.trans (Finset.gcd_dvd (mem_univ i))
        have hdiv : p ∣ a1 i * q2 + a2 i * q1 :=
          (Nat.dvd_mod_iff (hpq1.trans (dvd_mul_right q1 q2))).mp hpi
        have hpa1q2 : p ∣ a1 i * q2 := (Nat.dvd_add_left (dvd_mul_of_dvd_right hpq1 _)).mp hdiv
        have hpnq2 : ¬ p ∣ q2 := fun h => hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hpq1 h)
        exact (hp.dvd_mul.mp hpa1q2).resolve_right hpnq2
      exact hp.not_dvd_one (hc1.gcd_eq_one ▸ Nat.dvd_gcd hpq1 hpa1)
    · rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have hpq2 : p ∣ q2 := hpd.trans (Nat.gcd_dvd_left _ _)
      have hpg : p ∣ univ.gcd (φ (a1, a2)) := hpd.trans (Nat.gcd_dvd_right _ _)
      have hpa2 : p ∣ univ.gcd a2 := Finset.dvd_gcd fun i _ => by
        have hpi : p ∣ φ (a1, a2) i := hpg.trans (Finset.gcd_dvd (mem_univ i))
        have hdiv : p ∣ a1 i * q2 + a2 i * q1 :=
          (Nat.dvd_mod_iff (hpq2.trans (dvd_mul_left q2 q1))).mp hpi
        have hpa2q1 : p ∣ a2 i * q1 := (Nat.dvd_add_right (dvd_mul_of_dvd_right hpq2 _)).mp hdiv
        have hpnq1 : ¬ p ∣ q1 := fun h => hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h hpq2)
        exact (hp.dvd_mul.mp hpa2q1).resolve_right hpnq1
      exact hp.not_dvd_one (hc2.gcd_eq_one ▸ Nat.dvd_gcd hpq2 hpa2)
  have hinj : Set.InjOn φ ((Und d q1 ×ˢ Und d q2 : Finset _) : Set _) := by
    rintro ⟨a1, a2⟩ h12 ⟨b1, b2⟩ h12' heq
    rw [mem_coe, mem_product] at h12 h12'
    have ha1 : ∀ i, a1 i < q1 := fun i => mem_range.mp (Fintype.mem_piFinset.mp (mem_filter.mp h12.1).1 i)
    have ha2 : ∀ i, a2 i < q2 := fun i => mem_range.mp (Fintype.mem_piFinset.mp (mem_filter.mp h12.2).1 i)
    have hb1 : ∀ i, b1 i < q1 := fun i => mem_range.mp (Fintype.mem_piFinset.mp (mem_filter.mp h12'.1).1 i)
    have hb2 : ∀ i, b2 i < q2 := fun i => mem_range.mp (Fintype.mem_piFinset.mp (mem_filter.mp h12'.2).1 i)
    have hmodeq : ∀ i, (a1 i * q2 + a2 i * q1) ≡ (b1 i * q2 + b2 i * q1) [MOD q1 * q2] := fun i =>
      congrFun heq i
    have h1eq : a1 = b1 := by
      ext i
      have hm1 : (a1 i * q2 + a2 i * q1) ≡ (b1 i * q2 + b2 i * q1) [MOD q1] :=
        (hmodeq i).of_dvd (dvd_mul_right q1 q2)
      have hm1' : a1 i * q2 ≡ b1 i * q2 [MOD q1] := by
        simpa [Nat.ModEq, Nat.add_mul_mod_self_right] using hm1
      have hcancel := Nat.ModEq.cancel_right_of_coprime hcop hm1'
      rwa [Nat.ModEq, Nat.mod_eq_of_lt (ha1 i), Nat.mod_eq_of_lt (hb1 i)] at hcancel
    have h2eq : a2 = b2 := by
      ext i
      have hm2 : (a1 i * q2 + a2 i * q1) ≡ (b1 i * q2 + b2 i * q1) [MOD q2] :=
        (hmodeq i).of_dvd (dvd_mul_left q2 q1)
      have hm2' : a2 i * q1 ≡ b2 i * q1 [MOD q2] := by
        simpa [Nat.ModEq, Nat.mul_add_mod_self_right, add_comm] using hm2
      have hcancel := Nat.ModEq.cancel_right_of_coprime hcop.symm hm2'
      rwa [Nat.ModEq, Nat.mod_eq_of_lt (ha2 i), Nat.mod_eq_of_lt (hb2 i)] at hcancel
    exact Prod.ext h1eq h2eq
  have hsurj : ∀ a ∈ Und d (q1 * q2), ∃ p ∈ Und d q1 ×ˢ Und d q2, φ p = a := by
    intro a ha
    have ha_lt : ∀ i, a i < q1 * q2 := fun i =>
      mem_range.mp (Fintype.mem_piFinset.mp (mem_filter.mp ha).1 i)
    have hcop_a : (q1 * q2).Coprime (univ.gcd a) := (mem_filter.mp ha).2
    have : NeZero q1 := ⟨h1.ne'⟩
    have : NeZero q2 := ⟨h2.ne'⟩
    let inv2 : ℕ := (ZMod.unitOfCoprime q2 hcop.symm)⁻¹.val.val
    let inv1 : ℕ := (ZMod.unitOfCoprime q1 hcop)⁻¹.val.val
    have hinv2 : inv2 * q2 ≡ 1 [MOD q1] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simp [inv2, mul_comm]
    have hinv1 : inv1 * q1 ≡ 1 [MOD q2] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simp [inv1, mul_comm]
    let a1 : Fin d → ℕ := fun i => (a i * inv2) % q1
    let a2 : Fin d → ℕ := fun i => (a i * inv1) % q2
    have hphi : φ (a1, a2) = a := by
      ext i
      have hm1 : (a1 i * q2 + a2 i * q1) ≡ a i [MOD q1] := by
        calc a1 i * q2 + a2 i * q1
            ≡ a1 i * q2 [MOD q1] := by simp [Nat.ModEq, Nat.add_mul_mod_self_right]
          _ ≡ (a i * inv2) * q2 [MOD q1] := (Nat.mod_modEq _ _).mul_right q2
          _ = a i * (inv2 * q2) := by ring
          _ ≡ a i * 1 [MOD q1] := hinv2.mul_left (a i)
          _ = a i := mul_one _
      have hm2 : (a1 i * q2 + a2 i * q1) ≡ a i [MOD q2] := by
        calc a1 i * q2 + a2 i * q1
            ≡ a2 i * q1 [MOD q2] := by simp [Nat.ModEq, Nat.add_mul_mod_self_right, add_comm]
          _ ≡ (a i * inv1) * q1 [MOD q2] := (Nat.mod_modEq _ _).mul_right q1
          _ = a i * (inv1 * q1) := by ring
          _ ≡ a i * 1 [MOD q2] := hinv1.mul_left (a i)
          _ = a i := mul_one _
      have hboth : (a1 i * q2 + a2 i * q1) ≡ a i [MOD q1 * q2] :=
        (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hm1, hm2⟩
      change (a1 i * q2 + a2 i * q1) % (q1 * q2) = a i
      rwa [Nat.ModEq, Nat.mod_eq_of_lt (ha_lt i)] at hboth
    have ha1_mem : a1 ∈ Und d q1 := by
      refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => mem_range.mpr (Nat.mod_lt _ h1), ?_⟩
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have hpq1 : p ∣ q1 := hpd.trans (Nat.gcd_dvd_left _ _)
      have hpg : p ∣ univ.gcd a1 := hpd.trans (Nat.gcd_dvd_right _ _)
      have hpa : p ∣ univ.gcd a := Finset.dvd_gcd fun i _ => by
        have hpi : p ∣ a1 i := hpg.trans (Finset.gcd_dvd (mem_univ i))
        have hdiv : p ∣ a1 i * q2 + a2 i * q1 :=
          dvd_add (dvd_mul_of_dvd_left hpi _) (dvd_mul_of_dvd_right hpq1 _)
        have hmod : p ∣ (a1 i * q2 + a2 i * q1) % (q1 * q2) :=
          (Nat.dvd_mod_iff (hpq1.trans (dvd_mul_right q1 q2))).mpr hdiv
        rwa [← (show φ (a1, a2) i = a i from congrFun hphi i)]
      exact hp.not_dvd_one (hcop_a.gcd_eq_one ▸ Nat.dvd_gcd (hpq1.trans (dvd_mul_right q1 q2)) hpa)
    have ha2_mem : a2 ∈ Und d q2 := by
      refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => mem_range.mpr (Nat.mod_lt _ h2), ?_⟩
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
      have hpq2 : p ∣ q2 := hpd.trans (Nat.gcd_dvd_left _ _)
      have hpg : p ∣ univ.gcd a2 := hpd.trans (Nat.gcd_dvd_right _ _)
      have hpa : p ∣ univ.gcd a := Finset.dvd_gcd fun i _ => by
        have hpi : p ∣ a2 i := hpg.trans (Finset.gcd_dvd (mem_univ i))
        have hdiv : p ∣ a1 i * q2 + a2 i * q1 :=
          dvd_add (dvd_mul_of_dvd_right hpq2 _) (dvd_mul_of_dvd_left hpi _)
        have hmod : p ∣ (a1 i * q2 + a2 i * q1) % (q1 * q2) :=
          (Nat.dvd_mod_iff (hpq2.trans (dvd_mul_left q2 q1))).mpr hdiv
        rwa [← (show φ (a1, a2) i = a i from congrFun hphi i)]
      exact hp.not_dvd_one (hcop_a.gcd_eq_one ▸ Nat.dvd_gcd (hpq2.trans (dvd_mul_left q2 q1)) hpa)
    exact ⟨(a1, a2), mem_product.mpr ⟨ha1_mem, ha2_mem⟩, hphi⟩
  rw [← sum_product']
  symm
  refine Finset.sum_bij (fun p _ => φ p) (fun p hp => hmap p.1 (mem_product.mp hp).1 p.2 (mem_product.mp hp).2)
    (fun p1 hp1 p2 hp2 he => hinj (mem_coe.mpr hp1) (mem_coe.mpr hp2) he)
    (fun b hb => let ⟨p, hp, hpe⟩ := hsurj b hb; ⟨p, hp, hpe⟩) ?_
  rintro ⟨a1, a2⟩ _
  apply hper
  intro i
  refine ⟨(((a1 i * q2 + a2 i * q1) / (q1 * q2) : ℕ) : ℤ), ?_⟩
  have hq1R : (q1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h1.ne'
  have hq2R : (q2 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h2.ne'
  have hdiv : ((a1 i : ℝ) * (q2 : ℝ) + (a2 i : ℝ) * (q1 : ℝ)) =
      ((q1 : ℝ) * (q2 : ℝ)) * (((a1 i * q2 + a2 i * q1) / (q1 * q2) : ℕ) : ℝ) +
      ((φ (a1, a2) i : ℕ) : ℝ) := by
    have hnat := (Nat.div_add_mod (a1 i * q2 + a2 i * q1) (q1 * q2)).symm
    have hR : ((a1 i * q2 + a2 i * q1 : ℕ) : ℝ) =
        ((q1 * q2 : ℕ) : ℝ) * (((a1 i * q2 + a2 i * q1) / (q1 * q2) : ℕ) : ℝ) +
        ((φ (a1, a2) i : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa [Nat.cast_add, Nat.cast_mul] using hR
  rw [Int.cast_natCast, Nat.cast_mul]
  field_simp [hq1R, hq2R]
  linarith [hdiv]

/-- `d`-dimensional Montgomery lemma for squarefree moduli. -/
theorem montgomery_nd {d : ℕ} (Ω : ℕ → Finset (Fin d → ℕ))
    (F : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ)
    (hΩ : ∀ p, p.Prime → Ω p ⊆ Fintype.piFinset (fun _ : Fin d => range p))
    (hvan : ∀ p, p.Prime → ∀ n ∈ F, vecMod p n ∈ Ω p → c n = 0)
    (q : ℕ) (hq : Squarefree q) :
    (∏ p ∈ q.primeFactors, hfacND d Ω p) * ‖∑ n ∈ F, c n‖ ^ 2 ≤
      ∑ a ∈ Und d q, ‖∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * ((a i : ℝ) / q))‖ ^ 2 := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hq1 : q = 1
    · subst hq1
      simp only [Nat.primeFactors_one, prod_empty, one_mul]
      have hU1 : Und d 1 = {fun _ => 0} := by
        ext a; simp only [Und, mem_filter, Fintype.mem_piFinset, mem_range, mem_singleton]
        constructor
        · rintro ⟨ha, _⟩; ext i; exact Nat.lt_one_iff.mp (ha i)
        · rintro rfl; exact ⟨fun _ => by norm_num, Nat.coprime_one_left _⟩
      rw [hU1, sum_singleton]
      simp [e_zero]
    · have hq0 : q ≠ 0 := hq.ne_zero
      have hq_gt1 : 1 < q := by omega
      obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd hq1
      let r := q / p
      have hpr : p * r = q := Nat.mul_div_cancel' hpq
      have hr_pos : 0 < r := Nat.div_pos (Nat.le_of_dvd (by omega) hpq) hp.pos
      have hr_lt : r < q := Nat.div_lt_self (by omega) hp.one_lt
      have hr_sq : Squarefree r := hq.squarefree_of_dvd ⟨p, by rw [mul_comm, hpr]⟩
      have hcop : p.Coprime r := by
        rw [hp.coprime_iff_not_dvd]
        intro hpr_dvd
        have hp2 : p * p ∣ q := by
          obtain ⟨k, hk⟩ := hpr_dvd
          exact ⟨k, by rw [← hpr, hk]; ring⟩
        exact hp.not_isUnit (hq p hp2)
      have hpf : q.primeFactors = insert p r.primeFactors := by
        rw [← hpr, Nat.primeFactors_mul hp.ne_zero hr_pos.ne', hp.primeFactors]
        simp
      have hp_not_mem : p ∉ r.primeFactors := by
        rw [Nat.mem_primeFactors]; intro h; exact hp.coprime_iff_not_dvd.mp hcop h.2.1
      rw [hpf, prod_insert hp_not_mem, ← hpr]
      rw [sum_Und_mul p r hp.pos hr_pos hcop
        (fun x => ‖∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * x i)‖ ^ 2)
        (fun x y hxy => by
          congr 2; refine sum_congr rfl fun n _ => ?_; congr 1
          have hsum : ∑ i : Fin d, (n i : ℝ) * x i =
              (∑ i : Fin d, (n i : ℝ) * y i) +
              ((∑ i : Fin d, n i * Classical.choose (hxy i) : ℤ) : ℝ) := by
            rw [Int.cast_sum, ← sum_add_distrib]
            refine sum_congr rfl fun i _ => ?_
            have hk := Classical.choose_spec (hxy i)
            push_cast; rw [← hk]; ring
          rw [hsum, e_add_int])]
      rw [sum_comm]
      have hinner : ∀ a2 ∈ Und d r,
          hfacND d Ω p * ‖∑ n ∈ F, (c n * e (∑ i : Fin d, (n i : ℝ) * ((a2 i : ℝ) / r)))‖ ^ 2 ≤
          ∑ a1 ∈ Und d p, ‖∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * ((a1 i : ℝ) / p + (a2 i : ℝ) / r))‖ ^ 2 := by
        intro a2 _
        have hmp := montgomery_prime_nd p hp (Ω p) (hΩ p hp) F
          (fun n => c n * e (∑ i : Fin d, (n i : ℝ) * ((a2 i : ℝ) / r)))
          (fun n hn hmem => by rw [hvan p hp n hn hmem, zero_mul])
        refine hmp.trans_eq ?_
        refine sum_congr rfl fun a1 _ => ?_
        congr 2
        refine sum_congr rfl fun n _ => ?_
        rw [mul_assoc, ← e_add]
        congr 2
        rw [← sum_add_distrib]
        refine sum_congr rfl fun i _ => by ring
      calc hfacND d Ω p * (∏ p' ∈ r.primeFactors, hfacND d Ω p') * ‖∑ n ∈ F, c n‖ ^ 2
          = hfacND d Ω p * ((∏ p' ∈ r.primeFactors, hfacND d Ω p') * ‖∑ n ∈ F, c n‖ ^ 2) := by ring
        _ ≤ hfacND d Ω p * ∑ a2 ∈ Und d r,
              ‖∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * ((a2 i : ℝ) / r))‖ ^ 2 :=
            mul_le_mul_of_nonneg_left (ih r hr_lt hr_sq) (hfacND_nonneg Ω p (hΩ p hp))
        _ = ∑ a2 ∈ Und d r, hfacND d Ω p *
              ‖∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * ((a2 i : ℝ) / r))‖ ^ 2 := by rw [mul_sum]
        _ ≤ ∑ a2 ∈ Und d r, ∑ a1 ∈ Und d p,
              ‖∑ n ∈ F, c n * e (∑ i : Fin d, (n i : ℝ) * ((a1 i : ℝ) / p + (a2 i : ℝ) / r))‖ ^ 2 :=
            sum_le_sum hinner

/-- `d`-dimensional arithmetic large sieve on a box `intBox d M N`. -/
theorem arith_large_sieve_nd {d : ℕ} (Q : ℕ) (hQ : 1 ≤ Q) (M : ℤ) (N : ℕ)
    (A : Finset (Fin d → ℤ)) (hA : A ⊆ intBox d M N)
    (Ω : ℕ → Finset (Fin d → ℕ))
    (hΩ : ∀ p, p.Prime → Ω p ⊆ Fintype.piFinset (fun _ : Fin d => range p))
    (havoid : ∀ p, p.Prime → p ≤ Q → ∀ n ∈ A, vecMod p n ∉ Ω p) :
    (A.card : ℝ) * (∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfacND d Ω p) ≤
      (2 * (N : ℝ) + 6 * (Q : ℝ) ^ 2) ^ d := by
  let Ω' : ℕ → Finset (Fin d → ℕ) := fun p => if p ≤ Q then Ω p else ∅
  have hΩ' : ∀ p, p.Prime → Ω' p ⊆ Fintype.piFinset (fun _ : Fin d => range p) := fun p hp => by
    dsimp [Ω']; split_ifs
    · exact hΩ p hp
    · exact empty_subset _
  have hvan : ∀ p, p.Prime → ∀ n ∈ A, vecMod p n ∈ Ω' p → (1 : ℂ) = 0 := fun p hp n hn hmem => by
    dsimp [Ω'] at hmem
    split_ifs at hmem with hpQ
    · exact absurd hmem (havoid p hp hpQ n hn)
    · simp at hmem
  have hls := large_sieve_farey_nd Q hQ M N A hA (fun _ => (1 : ℂ))
  have h1 : ∑ n ∈ A, ‖(1 : ℂ)‖ ^ 2 = (A.card : ℝ) := by simp
  rw [h1] at hls
  have hmont : (A.card : ℝ) ^ 2 *
      (∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfacND d Ω p) ≤
      ∑ q ∈ Icc 1 Q, ∑ a ∈ Und d q,
        ‖∑ n ∈ A, (1 : ℂ) * e (∑ i : Fin d, (n i : ℝ) * ((a i : ℝ) / q))‖ ^ 2 := by
    rw [mul_sum]
    calc ∑ q ∈ (Icc 1 Q).filter Squarefree,
            (A.card : ℝ) ^ 2 * ∏ p ∈ q.primeFactors, hfacND d Ω p
        = ∑ q ∈ (Icc 1 Q).filter Squarefree,
            (∏ p ∈ q.primeFactors, hfacND d Ω' p) * ‖∑ _n ∈ A, (1 : ℂ)‖ ^ 2 := by
          refine sum_congr rfl fun q hq => ?_
          have hqQ : q ≤ Q := (mem_Icc.mp (mem_filter.mp hq).1).2
          have hq0 : q ≠ 0 := (mem_filter.mp hq).2.ne_zero
          have hprod_eq : ∏ p ∈ q.primeFactors, hfacND d Ω' p =
              ∏ p ∈ q.primeFactors, hfacND d Ω p := by
            refine prod_congr rfl fun p hp => ?_
            have hpQ : p ≤ Q := (Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) (Nat.dvd_of_mem_primeFactors hp)).trans hqQ
            simp [hfacND, Ω', hpQ]
          rw [hprod_eq, sum_const, nsmul_eq_mul, mul_one, Complex.norm_natCast, mul_comm]
      _ ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, ∑ a ∈ Und d q,
            ‖∑ n ∈ A, (1 : ℂ) * e (∑ i : Fin d, (n i : ℝ) * ((a i : ℝ) / q))‖ ^ 2 :=
          sum_le_sum fun q hq => montgomery_nd Ω' A (fun _ => 1) hΩ' hvan q (mem_filter.mp hq).2
      _ ≤ ∑ q ∈ Icc 1 Q, ∑ a ∈ Und d q,
            ‖∑ n ∈ A, (1 : ℂ) * e (∑ i : Fin d, (n i : ℝ) * ((a i : ℝ) / q))‖ ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ =>
            sum_nonneg fun _ _ => sq_nonneg _
  by_cases hA0 : A.card = 0
  · rw [hA0, Nat.cast_zero, zero_mul]; positivity
  · have hApos : (0 : ℝ) < A.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hA0)
    have hcomb := hmont.trans hls
    nlinarith

end MontgomeryND

end Erdos980LS

/-
# Mertens Lower Bound in Arithmetic Progressions and Rankin Sieve-Sum Lower Bound

For any prime `l` (with `d = l - 1 = φ(l)`):
1. Elementary dyadic Chebyshev bounds for `∑_{p ≤ U} log p / p` and `∑' p, log p / p^σ`.
2. Using Mathlib's `DirichletCharacter.LSeries_eq_exp_LSeries` and
   `DirichletCharacter.LFunction_ne_zero_of_one_le_re`, we prove:
     `∑_{p ≤ U, p ≡ 1 (mod l)} 1 / p ≥ (1 / d) log (log U) - C_l`.
3. By Rankin's trick (`α = 1 / (6 * e * d + 1)`, `σ = 1 / (α * log Z)`), we prove the
   truncated squarefree sieve-sum lower bound:
     `∑_{1 ≤ m ≤ Z, μ²(m)=1, ∀ r ∣ m, r ≡ 1 (mod l) ∧ r ∉ Bad} ∏_{r ∣ m} (d / r)`
     `≥ c_l * log Z / ∏_{r ∈ Bad, r prime, r ≡ 1 (mod l)} (1 + d / r)`.
-/

namespace Erdos980Mertens

open Finset Filter ArithmeticFunction
open scoped BigOperators Classical Topology

section ChebyshevDyadic

private lemma dyadic_prime_block_le (k : ℕ) :
    ∑ p ∈ (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p),
      Real.log (p : ℝ) / (p : ℝ) ≤ 3 := by
  have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hle : ∑ p ∈ (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p),
      Real.log (p : ℝ) / (p : ℝ) ≤
      (∑ p ∈ (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p),
        Real.log (p : ℝ)) / (2 : ℝ) ^ k := by
    rw [sum_div]
    refine sum_le_sum fun p hp => ?_
    have h2kp : (2 : ℝ) ^ k ≤ (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2
    have hprime : p.Prime := Nat.prime_of_mem_primesBelow (mem_filter.mp hp).1
    have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
    exact div_le_div_of_nonneg_left hlog_nn h2k_pos h2kp
  have hsub : (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p) ⊆
      (Ioc 0 (2 ^ (k + 1))).filter Nat.Prime := by
    intro p hp
    have hm := Nat.mem_primesBelow.mp (mem_filter.mp hp).1
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hm.2.pos, hm.1.le⟩, hm.2⟩
  have hth : ∑ p ∈ (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p),
      Real.log (p : ℝ) ≤ Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ) := by
    rw [Chebyshev.theta, Nat.floor_natCast]
    exact sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
      Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_lt.le)
  have hbd := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ ((2 ^ (k + 1) : ℕ) : ℝ) by positivity)
  have hlog4 : Real.log 4 ≤ 3 / 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    linarith [Real.log_two_lt_d9]
  calc ∑ p ∈ (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p),
        Real.log (p : ℝ) / (p : ℝ)
      ≤ Chebyshev.theta ((2 ^ (k + 1) : ℕ) : ℝ) / (2 : ℝ) ^ k :=
        hle.trans (div_le_div_of_nonneg_right hth h2k_pos.le)
    _ ≤ (Real.log 4 * ((2 ^ (k + 1) : ℕ) : ℝ)) / (2 : ℝ) ^ k :=
        div_le_div_of_nonneg_right hbd h2k_pos.le
    _ = 2 * Real.log 4 := by
        push_cast; rw [pow_succ]; field_simp [h2k_pos.ne']
    _ ≤ 3 := by linarith

/-- Elementary dyadic Chebyshev bound: `∑_{p ≤ U} log p / p ≤ 6 * log U + 3` for `U ≥ 1`. -/
theorem sum_prime_log_div_le {U : ℝ} (hU : 1 ≤ U) :
    ∑ p ∈ Nat.primesBelow (⌊U⌋₊ + 1), Real.log (p : ℝ) / (p : ℝ) ≤ 6 * Real.log U + 3 := by
  let K : ℕ := ⌊Real.log U / Real.log 2⌋₊ + 1
  have hU_lt : U < (2 : ℝ) ^ K := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlt : Real.log U / Real.log 2 < (K : ℝ) := by
      dsimp [K]; push_cast; exact Nat.lt_floor_add_one _
    have h1 : Real.log U < (K : ℝ) * Real.log 2 := (div_lt_iff₀ hlog2).mp hlt
    rw [← Real.log_pow] at h1
    exact (Real.log_lt_log_iff (by linarith) (by positivity)).mp h1
  have hfl_lt : ⌊U⌋₊ < 2 ^ K := by
    have : (⌊U⌋₊ : ℝ) < (2 : ℝ) ^ K := (Nat.floor_le (by linarith)).trans_lt hU_lt
    exact_mod_cast this
  have hdisj : Set.PairwiseDisjoint (range K : Set ℕ)
      (fun k => (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p)) := by
    intro k1 _ k2 _ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := Nat.mem_primesBelow.mp (mem_filter.mp hp1).1
    have h1' := (mem_filter.mp hp1).2
    have h2 := Nat.mem_primesBelow.mp (mem_filter.mp hp2).1
    have h2' := (mem_filter.mp hp2).2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : 2 ^ (k1 + 1) ≤ 2 ^ k2 := Nat.pow_le_pow_right (by decide) hlt
      omega
    · have : 2 ^ (k2 + 1) ≤ 2 ^ k1 := Nat.pow_le_pow_right (by decide) hgt
      omega
  have hcover : Nat.primesBelow (⌊U⌋₊ + 1) ⊆
      (range K).biUnion (fun k => (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p)) := by
    intro p hp
    obtain ⟨hplt, hpr⟩ := Nat.mem_primesBelow.mp hp
    have hp_lt_2K : p < 2 ^ K := by omega
    have hlog_lt : Nat.log 2 p < K := Nat.log_lt_of_lt_pow hpr.ne_zero hp_lt_2K
    refine mem_biUnion.mpr ⟨Nat.log 2 p, mem_range.mpr hlog_lt, mem_filter.mpr
      ⟨Nat.mem_primesBelow.mpr ⟨Nat.lt_pow_succ_log_self (by decide) p, hpr⟩,
       Nat.pow_log_le_self 2 hpr.ne_zero⟩⟩
  have hsum_le : ∑ p ∈ Nat.primesBelow (⌊U⌋₊ + 1), Real.log (p : ℝ) / (p : ℝ) ≤
      ∑ k ∈ range K, ∑ p ∈ (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p),
        Real.log (p : ℝ) / (p : ℝ) := by
    rw [← sum_biUnion hdisj]
    exact sum_le_sum_of_subset_of_nonneg hcover fun p hp _ => by
      obtain ⟨_, _, hpf⟩ := mem_biUnion.mp hp
      have hpr := Nat.prime_of_mem_primesBelow (mem_filter.mp hpf).1
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)) (Nat.cast_nonneg _)
  calc ∑ p ∈ Nat.primesBelow (⌊U⌋₊ + 1), Real.log (p : ℝ) / (p : ℝ)
      ≤ ∑ _k ∈ range K, (3 : ℝ) := hsum_le.trans (sum_le_sum fun k _ => dyadic_prime_block_le k)
    _ = 3 * (K : ℝ) := by simp [mul_comm]
    _ ≤ 3 * (Real.log U / Real.log 2 + 1) := by
        gcongr
        dsimp [K]; push_cast
        have hfl := Nat.floor_le (show 0 ≤ Real.log U / Real.log 2 from
          div_nonneg (Real.log_nonneg hU) (Real.log_pos (by norm_num)).le)
        linarith
    _ ≤ 6 * Real.log U + 3 := by
        have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
        have hdiv : Real.log U / Real.log 2 ≤ 2 * Real.log U := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith [Real.log_nonneg hU]
        linarith

/-- Elementary bound on `∑_{p ∈ F} log p / p^σ ≤ 12 / (σ - 1)` for `1 < σ ≤ 2` and prime `F`. -/
lemma sum_prime_log_div_rpow_le {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime) :
    ∑ p ∈ F, Real.log (p : ℝ) / (p : ℝ) ^ σ ≤ 12 / (σ - 1) := by
  let M : ℕ := F.sup id + 1
  let K : ℕ := Nat.log 2 M + 1
  have hM_lt : M < 2 ^ K := Nat.lt_pow_succ_log_self (by decide) M
  have hF_sub : F ⊆
      (range K).biUnion (fun k => (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p)) := by
    intro q hqF
    have hqpr : q.Prime := hF q hqF
    have hq_le : q < M := Nat.lt_succ_of_le (le_sup (f := id) hqF)
    have hq_lt : q < 2 ^ K := hq_le.trans hM_lt
    have hlog_lt : Nat.log 2 q < K := Nat.log_lt_of_lt_pow hqpr.ne_zero hq_lt
    refine mem_biUnion.mpr ⟨Nat.log 2 q, mem_range.mpr hlog_lt, mem_filter.mpr
      ⟨Nat.mem_primesBelow.mpr ⟨Nat.lt_pow_succ_log_self (by decide) q, hqpr⟩,
       Nat.pow_log_le_self 2 hqpr.ne_zero⟩⟩
  have hdisj : Set.PairwiseDisjoint (range K : Set ℕ)
      (fun k => (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p)) := by
    intro k1 _ k2 _ hne
    dsimp [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := Nat.mem_primesBelow.mp (mem_filter.mp hp1).1
    have h1' := (mem_filter.mp hp1).2
    have h2 := Nat.mem_primesBelow.mp (mem_filter.mp hp2).1
    have h2' := (mem_filter.mp hp2).2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : 2 ^ (k1 + 1) ≤ 2 ^ k2 := Nat.pow_le_pow_right (by decide) hlt
      omega
    · have : 2 ^ (k2 + 1) ≤ 2 ^ k1 := Nat.pow_le_pow_right (by decide) hgt
      omega
  have hblock (k : ℕ) :
      ∑ p ∈ (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p),
        Real.log (p : ℝ) / (p : ℝ) ^ σ ≤ 3 * ((2 : ℝ) ^ (1 - σ)) ^ k := by
    have hsplit : ∀ p ∈ (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p),
        Real.log (p : ℝ) / (p : ℝ) ^ σ ≤
          (Real.log (p : ℝ) / (p : ℝ)) * ((2 : ℝ) ^ (1 - σ)) ^ k := by
      intro p hp
      have hpr := Nat.prime_of_mem_primesBelow (mem_filter.mp hp).1
      have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hpr.pos
      have h2k_le : (2 : ℝ) ^ k ≤ (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2
      have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
      have hrpow : (p : ℝ) ^ (1 - σ) ≤ ((2 : ℝ) ^ (1 - σ)) ^ k := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm,
          Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_nonpos (by positivity) h2k_le (by linarith)
      have heq : Real.log (p : ℝ) / (p : ℝ) ^ σ = (Real.log (p : ℝ) / (p : ℝ)) * (p : ℝ) ^ (1 - σ) := by
        rw [Real.rpow_sub hp_pos, Real.rpow_one]
        field_simp [hp_pos.ne', (Real.rpow_pos_of_pos hp_pos σ).ne']
      rw [heq]
      exact mul_le_mul_of_nonneg_left hrpow (div_nonneg hlog_nn hp_pos.le)
    calc ∑ p ∈ (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p),
          Real.log (p : ℝ) / (p : ℝ) ^ σ
        ≤ ∑ p ∈ (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p),
            (Real.log (p : ℝ) / (p : ℝ)) * ((2 : ℝ) ^ (1 - σ)) ^ k := sum_le_sum hsplit
      _ = (∑ p ∈ (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p),
            Real.log (p : ℝ) / (p : ℝ)) * ((2 : ℝ) ^ (1 - σ)) ^ k := (sum_mul ..).symm
      _ ≤ 3 * ((2 : ℝ) ^ (1 - σ)) ^ k :=
          mul_le_mul_of_nonneg_right (dyadic_prime_block_le k) (by positivity)
  have hr_lt1 : (2 : ℝ) ^ (1 - σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr_nn : 0 ≤ (2 : ℝ) ^ (1 - σ) := by positivity
  have hgeom : ∑ k ∈ range K, ((2 : ℝ) ^ (1 - σ)) ^ k ≤ 1 / (1 - (2 : ℝ) ^ (1 - σ)) := by
    rw [geom_sum_eq hr_lt1.ne]
    have hden_pos : 0 < 1 - (2 : ℝ) ^ (1 - σ) := by linarith
    rw [show (((2 : ℝ) ^ (1 - σ)) ^ K - 1) / ((2 : ℝ) ^ (1 - σ) - 1) =
        (1 - ((2 : ℝ) ^ (1 - σ)) ^ K) / (1 - (2 : ℝ) ^ (1 - σ)) by
      field_simp [hden_pos.ne', (show (2 : ℝ) ^ (1 - σ) - 1 ≠ 0 by linarith)]; ring]
    exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr_nn K]) hden_pos.le
  have hden_lb : (σ - 1) / 4 ≤ 1 - (2 : ℝ) ^ (1 - σ) := by
    have heq : (2 : ℝ) ^ (1 - σ) = Real.exp (-((σ - 1) * Real.log 2)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1; ring
    rw [heq]
    set t := (σ - 1) * Real.log 2
    have ht_pos : 0 < t := mul_pos (by linarith) (Real.log_pos (by norm_num))
    have ht_le1 : t ≤ 1 := by
      dsimp [t]; nlinarith [Real.log_two_lt_d9]
    have hexp_le : Real.exp (-t) ≤ 1 - t / 2 := by
      have h1 : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
      rw [Real.exp_neg]
      have hexp_pos : 0 < Real.exp t := Real.exp_pos t
      rw [inv_le_comm₀ hexp_pos (by linarith)]
      have h2 : (1 - t / 2) * (1 + t) = 1 + t / 2 - t ^ 2 / 2 := by ring
      have h3 : 1 ≤ (1 - t / 2) * (1 + t) := by nlinarith
      have h4 : (1 - t / 2)⁻¹ ≤ 1 + t := (inv_le_iff_one_le_mul₀' (by linarith)).mpr h3
      exact h4.trans h1
    have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have ht_ge : (σ - 1) / 2 ≤ t := by dsimp [t]; nlinarith
    linarith
  calc ∑ p ∈ F, Real.log (p : ℝ) / (p : ℝ) ^ σ
      ≤ ∑ p ∈ (range K).biUnion (fun k =>
            (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p)),
            Real.log (p : ℝ) / (p : ℝ) ^ σ :=
        sum_le_sum_of_subset_of_nonneg hF_sub fun p hp _ => by
          obtain ⟨_, _, hpf⟩ := mem_biUnion.mp hp
          have hpr := Nat.prime_of_mem_primesBelow (mem_filter.mp hpf).1
          exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)) (by positivity)
    _ = ∑ k ∈ range K, ∑ p ∈ (Nat.primesBelow (2 ^ (k + 1))).filter (fun p => 2 ^ k ≤ p),
          Real.log (p : ℝ) / (p : ℝ) ^ σ := sum_biUnion hdisj
    _ ≤ ∑ k ∈ range K, 3 * ((2 : ℝ) ^ (1 - σ)) ^ k := sum_le_sum fun k _ => hblock k
    _ = 3 * ∑ k ∈ range K, ((2 : ℝ) ^ (1 - σ)) ^ k := (mul_sum ..).symm
    _ ≤ 3 * (1 / (1 - (2 : ℝ) ^ (1 - σ))) := mul_le_mul_of_nonneg_left hgeom (by norm_num)
    _ ≤ 3 * (1 / ((σ - 1) / 4)) := by gcongr
    _ = 12 / (σ - 1) := by field_simp [(show σ - 1 ≠ 0 by linarith)]; ring

end ChebyshevDyadic

section MertensAP

/-- Elementary lower bound `1 / (σ - 1) ≤ ‖riemannZeta σ‖` for `1 < σ`. -/
lemma riemannZeta_norm_ge {σ : ℝ} (hσ : 1 < σ) :
    1 / (σ - 1) ≤ ‖riemannZeta (σ : ℂ)‖ := by
  have hre : 1 < (σ : ℂ).re := by simpa using hσ
  rw [← LSeries_one_eq_riemannZeta hre]
  have hsum : Summable (fun n : ℕ => ((n : ℝ) ^ (-σ))) := by
    have h := Real.summable_nat_rpow_inv.mpr hσ
    refine h.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
  let f : ℕ → ℝ := fun n => if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)
  have hL_eq : LSeries (1 : ℕ → ℂ) (σ : ℂ) = ((∑' n : ℕ, f n : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    congr 1; ext n
    by_cases hn : n = 0
    · simp [f, hn]
    · simp only [LSeries.term_of_ne_zero hn, Pi.one_apply, f, hn, ↓reduceIte, one_div]
      rw [Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_inv, Complex.ofReal_cpow (Nat.cast_nonneg n),
        Complex.ofReal_natCast]
  have hnn : 0 ≤ ∑' n : ℕ, f n :=
    tsum_nonneg fun n => by dsimp [f]; split_ifs <;> positivity
  rw [hL_eq, Complex.norm_real, Real.norm_of_nonneg hnn]
  change 1 / (σ - 1) ≤ ∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)
  have hsum_ite : Summable (fun n : ℕ => if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ)) :=
    Summable.of_nonneg_of_le
      (fun n => by split_ifs <;> first | exact le_rfl | exact Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (fun n => by split_ifs <;> first | exact le_rfl | exact Real.rpow_nonneg (Nat.cast_nonneg n) _)
      hsum
  -- Compare finite partial sums with integral `∫_1^(M+1) t^(-σ) dt`
  have hfin : ∀ M : ℕ, 1 ≤ M →
      (1 - ((M + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) ≤
        ∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ) := by
    intro M hM
    have hpart : (1 - ((M + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) ≤
        ∑ n ∈ Icc 1 M, (n : ℝ) ^ (-σ) := by
      have hstep : ∀ n ∈ Icc 1 M,
          ((n : ℝ) ^ (1 - σ) - ((n + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) ≤ (n : ℝ) ^ (-σ) := by
        intro n hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
        have hpos : (0 : ℝ) < n := by linarith
        have hderiv : ∀ t ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ),
            HasDerivAt (fun x : ℝ => x ^ (1 - σ) / (1 - σ)) (t ^ (-σ)) t := by
          intro t ht
          have htpos : 0 < t := lt_of_lt_of_le hpos ht.1
          have h1 := (Real.hasDerivAt_rpow_const (Or.inl htpos.ne') (p := 1 - σ)).div_const (1 - σ)
          have hne : (1 : ℝ) - σ ≠ 0 := by linarith
          have hval : (1 - σ) * t ^ (1 - σ - 1) / (1 - σ) = t ^ (-σ) := by
            rw [show 1 - σ - 1 = -σ by ring]; field_simp [hne]
          exact hval ▸ h1
        have hmvt := exists_hasDerivAt_eq_slope (fun x : ℝ => x ^ (1 - σ) / (1 - σ))
          (fun x : ℝ => x ^ (-σ)) (show (n : ℝ) < ((n + 1 : ℕ) : ℝ) by push_cast; linarith)
          (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
          (fun t ht => hderiv t (Set.Ioo_subset_Icc_self ht))
        obtain ⟨c, hc, hceq⟩ := hmvt
        have hdiff : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
        rw [hdiff, div_one] at hceq
        have hce : ((n : ℝ) ^ (1 - σ) - ((n + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) = c ^ (-σ) := by
          rw [hceq]
          have hne : σ - 1 ≠ 0 := by linarith
          have hne' : 1 - σ ≠ 0 := by linarith
          field_simp [hne, hne']; ring
        rw [hce]
        exact Real.rpow_le_rpow_of_nonpos hpos hc.1.le (by linarith)
      have htel : ∑ n ∈ Icc 1 M, ((n : ℝ) ^ (1 - σ) - ((n + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) =
          (1 - ((M + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1) := by
        rw [← sum_div]
        congr 1
        clear hstep
        induction M, hM using Nat.le_induction with
        | base => simp; norm_num
        | succ k hk ih =>
          rw [show Icc 1 (k + 1) = insert (k + 1) (Icc 1 k) by
            ext m; simp only [mem_Icc, mem_insert]; omega]
          rw [sum_insert (by simp), ih]; ring
      rw [← htel]
      exact sum_le_sum hstep
    calc (1 - ((M + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1)
        ≤ ∑ n ∈ Icc 1 M, (n : ℝ) ^ (-σ) := hpart
      _ = ∑ n ∈ Icc 1 M, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ) := by
          refine sum_congr rfl fun n hn => ?_
          have hn0 : n ≠ 0 := by rw [mem_Icc] at hn; omega
          simp [hn0]
      _ ≤ ∑' n : ℕ, if n = 0 then (0 : ℝ) else (n : ℝ) ^ (-σ) :=
          hsum_ite.sum_le_tsum (Icc 1 M) fun n _ => by
            split_ifs <;> first | exact le_rfl | exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have htend : Tendsto (fun M : ℕ => (1 - ((M + 1 : ℕ) : ℝ) ^ (1 - σ)) / (σ - 1)) atTop
      (𝓝 (1 / (σ - 1))) := by
    have hpow : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ) ^ (1 - σ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (show 0 < σ - 1 by linarith)).comp
        (by
          have : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℝ)) atTop atTop :=
            tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
          exact this) |> fun h => by
            convert h using 1; ext M; congr 1; ring
    have h1 := (tendsto_const_nhds (x := (1 : ℝ))).sub hpow
    rw [sub_zero] at h1
    exact h1.div_const (σ - 1)
  exact le_of_tendsto htend (eventually_atTop.mpr ⟨1, hfin⟩)

set_option maxHeartbeats 800000 in
/-- Mertens lower bound in the progression `p ≡ 1 (mod l)` for any prime `l`. -/
theorem mertens_ap_lower {l : ℕ} (hl : l.Prime) :
    ∃ C : ℝ, ∀ U : ℝ, 3 ≤ U →
      (1 / ((l - 1 : ℕ) : ℝ)) * Real.log (Real.log U) - C ≤
        ∑ p ∈ (Nat.primesBelow (⌊U⌋₊ + 1)).filter (fun p => p % l = 1), (1 : ℝ) / (p : ℝ) := by
  have : NeZero l := ⟨hl.ne_zero⟩
  have hl_tot : l.totient = l - 1 := Nat.totient_prime hl
  have hd_pos : (0 : ℝ) < ((l - 1 : ℕ) : ℝ) := by
    have := hl.two_le; exact_mod_cast (by omega : 0 < l - 1)
  -- Step 1: Uniform lower bound on `Real.log ‖LSeries χ σ‖` for `1 < σ ≤ 2` and `χ ≠ 1`
  have hchar_lb : ∀ χ : DirichletCharacter ℂ l, χ ≠ 1 →
      ∃ c : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 → c ≤ Real.log ‖LSeries (fun n : ℕ => χ n) (σ : ℂ)‖ := by
    intro χ hχ
    have hcont : Continuous (fun σ : ℝ => ‖DirichletCharacter.LFunction χ (σ : ℂ)‖) :=
      (DirichletCharacter.differentiable_LFunction hχ).continuous.comp Complex.continuous_ofReal
        |>.norm
    have hcomp : IsCompact (Set.Icc (1 : ℝ) 2) := isCompact_Icc
    have hne : (Set.Icc (1 : ℝ) 2).Nonempty := ⟨1, by norm_num⟩
    obtain ⟨σ₀, hσ₀_mem, hσ₀_min⟩ := hcomp.exists_isMinOn hne hcont.continuousOn
    have hpos : 0 < ‖DirichletCharacter.LFunction χ (σ₀ : ℂ)‖ := by
      rw [norm_pos_iff]
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simpa using hσ₀_mem.1)
    refine ⟨Real.log ‖DirichletCharacter.LFunction χ (σ₀ : ℂ)‖, fun σ hσ1 hσ2 => ?_⟩
    rw [← DirichletCharacter.LFunction_eq_LSeries χ (by simpa using hσ1)]
    exact Real.log_le_log hpos (hσ₀_min ⟨hσ1.le, hσ2⟩)
  -- Step 2: Uniform lower bound for trivial character `χ = 1`
  have htriv_lb : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      Real.log (1 / (σ - 1)) - Real.log 2 ≤ Real.log ‖LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ l) n) (σ : ℂ)‖ := by
    intro σ hσ1 _hσ2
    have hre : 1 < (σ : ℂ).re := by simpa using hσ1
    have hchg := DirichletCharacter.LSeries_changeLevel (one_dvd l) (1 : DirichletCharacter ℂ 1) hre
    have h1eq : DirichletCharacter.changeLevel (one_dvd l) (1 : DirichletCharacter ℂ 1) =
        (1 : DirichletCharacter ℂ l) := map_one _
    rw [h1eq, hl.primeFactors, prod_singleton] at hchg
    have hL1 : LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ 1) n) (σ : ℂ) = riemannZeta (σ : ℂ) := by
      rw [← LSeries_one_eq_riemannZeta hre]
      congr 1; ext n
      simp [MulChar.one_apply (isUnit_of_subsingleton _)]
    have h1l : (1 : DirichletCharacter ℂ 1) (l : ZMod 1) = 1 :=
      MulChar.one_apply (isUnit_of_subsingleton _)
    rw [hL1, h1l, one_mul] at hchg
    have hfac_lb : (1 / 2 : ℝ) ≤ ‖(1 : ℂ) - (l : ℂ) ^ (-(σ : ℂ))‖ := by
      have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
      have hnorm : ‖(l : ℂ) ^ (-(σ : ℂ))‖ ≤ 1 / 2 := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg,
          ← Complex.ofReal_cpow (Nat.cast_nonneg l), Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        rw [Real.rpow_neg (Nat.cast_nonneg l)]
        calc ((l : ℝ) ^ σ)⁻¹ ≤ ((2 : ℝ) ^ σ)⁻¹ := by gcongr
          _ ≤ ((2 : ℝ) ^ (1 : ℝ))⁻¹ := by gcongr; norm_num
          _ = 1 / 2 := by norm_num
      have htri := norm_sub_norm_le (1 : ℂ) ((l : ℂ) ^ (-(σ : ℂ)))
      rw [norm_one] at htri
      linarith
    have hzeta := riemannZeta_norm_ge hσ1
    have hprod_lb : (1 / (σ - 1)) / 2 ≤ ‖LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ l) n) (σ : ℂ)‖ := by
      rw [hchg, norm_mul]
      have h := mul_le_mul hzeta hfac_lb (by norm_num) (norm_nonneg _)
      linarith
    have hpos : 0 < (1 / (σ - 1)) / 2 := by
      have : 0 < σ - 1 := by linarith
      positivity
    calc Real.log (1 / (σ - 1)) - Real.log 2
        = Real.log ((1 / (σ - 1)) / 2) := (Real.log_div (by positivity) (by norm_num)).symm
      _ ≤ Real.log ‖LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ l) n) (σ : ℂ)‖ := Real.log_le_log hpos hprod_lb
  -- Aggregate lower bound over all characters mod `l`
  choose cχ hcχ using fun χ : {χ : DirichletCharacter ℂ l // χ ≠ 1} => hchar_lb χ.1 χ.2
  let C_char : ℝ := Real.log 2 + ∑ χ : {χ : DirichletCharacter ℂ l // χ ≠ 1}, |cχ χ|
  have hsum_log_lb : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      Real.log (1 / (σ - 1)) - C_char ≤
        ∑ χ : DirichletCharacter ℂ l, Real.log ‖LSeries (fun n : ℕ => χ n) (σ : ℂ)‖ := by
    intro σ hσ1 hσ2
    rw [← add_sum_erase _ _ (mem_univ (1 : DirichletCharacter ℂ l))]
    have htriv := htriv_lb σ hσ1 hσ2
    have hrest : -(∑ χ : {χ : DirichletCharacter ℂ l // χ ≠ 1}, |cχ χ|) ≤
        ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ l), Real.log ‖LSeries (fun n : ℕ => χ n) (σ : ℂ)‖ := by
      rw [← sum_neg_distrib]
      have hbij : ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ l), Real.log ‖LSeries (fun n : ℕ => χ n) (σ : ℂ)‖ =
          ∑ χ : {χ : DirichletCharacter ℂ l // χ ≠ 1}, Real.log ‖LSeries (fun n : ℕ => χ.1 n) (σ : ℂ)‖ := by
        symm
        refine Finset.sum_bij (fun χ _ => χ.1) (fun χ _ => mem_erase.mpr ⟨χ.2, mem_univ _⟩)
          (fun a _ b _ h => Subtype.ext h)
          (fun χ hχ => ⟨⟨χ, (mem_erase.mp hχ).1⟩, mem_univ _, rfl⟩) (fun _ _ => rfl)
      rw [hbij]
      exact sum_le_sum fun χ _ => (neg_abs_le (cχ χ)).trans (hcχ χ σ hσ1 hσ2)
    dsimp [C_char]
    linarith
  -- Step 3: Relate `∑_χ log ‖LSeries χ σ‖` to `∑_{p ≡ 1 (mod l)} 1 / p^σ`
  have hprime_tsum_lb : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (1 / ((l - 1 : ℕ) : ℝ)) * Real.log (1 / (σ - 1)) - (C_char / ((l - 1 : ℕ) : ℝ) + 2) ≤
        ∑' p : ℕ, if p.Prime ∧ p % l = 1 then (p : ℝ) ^ (-σ) else 0 := by
    intro σ hσ1 hσ2
    have hre : 1 < (σ : ℂ).re := by simpa using hσ1
    -- For each `χ`, `Real.log ‖LSeries χ σ‖ = (LSeries (fun n => χ n * Λ n / log n) σ).re`
    have hlog_eq (χ : DirichletCharacter ℂ l) :
        Real.log ‖LSeries (fun n : ℕ => χ n) (σ : ℂ)‖ =
          (LSeries (fun n : ℕ => χ n * (Λ n : ℂ) / (Real.log n : ℂ)) (σ : ℂ)).re := by
      rw [← DirichletCharacter.LSeries_eq_exp_LSeries χ hre, Complex.norm_exp, Real.log_exp]
    have hsumm_term (χ : DirichletCharacter ℂ l) :
        Summable (fun n : ℕ => LSeries.term (fun n : ℕ => χ n * (Λ n : ℂ) / (Real.log n : ℂ)) (σ : ℂ) n) := by
      have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
        have h := Real.summable_nat_rpow_inv.mpr hσ1
        exact h.congr fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n)]
      refine Summable.of_norm_bounded (g := fun n : ℕ => (n : ℝ) ^ (-σ)) h1 fun n => ?_
      by_cases hn : n = 0
      · simp [hn]; exact Real.rpow_nonneg le_rfl _
      · by_cases hn1 : n = 1
        · simp [hn1]
        · simp only [LSeries.term_of_ne_zero hn, norm_div, norm_mul, Complex.norm_real,
            Real.norm_eq_abs]
          have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
          have hΛ_le : |Λ n| ≤ Real.log (n : ℝ) := by
            rw [abs_of_nonneg vonMangoldt_nonneg]; exact vonMangoldt_le_log
          have hdiv_le : ‖χ n‖ * |Λ n| / |Real.log (n : ℝ)| ≤ 1 := by
            rw [abs_of_pos hlog_pos, div_le_one hlog_pos]
            calc ‖χ n‖ * |Λ n| ≤ 1 * Real.log (n : ℝ) :=
                  mul_le_mul (χ.norm_le_one _) hΛ_le (abs_nonneg _) zero_le_one
              _ = Real.log (n : ℝ) := one_mul _
          have hden : ‖(n : ℂ) ^ (σ : ℂ)‖ = (n : ℝ) ^ σ := by
            rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n),
              Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          rw [hden, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
          calc ‖χ n‖ * |Λ n| / |Real.log (n : ℝ)| * ((n : ℝ) ^ σ)⁻¹
              ≤ 1 * ((n : ℝ) ^ σ)⁻¹ := mul_le_mul_of_nonneg_right hdiv_le (by positivity)
            _ = ((n : ℝ) ^ σ)⁻¹ := one_mul _
    -- Sum over `χ`
    have hsum_orth :
        ∑ χ : DirichletCharacter ℂ l, Real.log ‖LSeries (fun n : ℕ => χ n) (σ : ℂ)‖ =
          ((l - 1 : ℕ) : ℝ) * ∑' n : ℕ,
            if n % l = 1 then (Λ n / Real.log (n : ℝ)) * (n : ℝ) ^ (-σ) else 0 := by
      simp_rw [hlog_eq, LSeries]
      rw [← Complex.re_sum, ← Summable.tsum_finsetSum (fun χ _ => hsumm_term χ)]
      have hinner (n : ℕ) :
          ∑ χ : DirichletCharacter ℂ l,
            LSeries.term (fun m : ℕ => χ m * (Λ m : ℂ) / (Real.log m : ℂ)) (σ : ℂ) n =
          ((((l - 1 : ℕ) : ℝ) * (if n % l = 1 then (Λ n / Real.log (n : ℝ)) * (n : ℝ) ^ (-σ) else 0) : ℝ) : ℂ) := by
        by_cases hn : n = 0
        · simp [hn]
        · simp only [LSeries.term_of_ne_zero hn]
          have hpull : ∑ χ : DirichletCharacter ℂ l,
              (χ n * (Λ n : ℂ) / (Real.log n : ℂ)) / (n : ℂ) ^ (σ : ℂ) =
              (∑ χ : DirichletCharacter ℂ l, χ n) *
                (((Λ n : ℂ) / (Real.log n : ℂ)) / (n : ℂ) ^ (σ : ℂ)) := by
            rw [sum_mul]; refine sum_congr rfl fun χ _ => by ring
          rw [hpull, DirichletCharacter.sum_characters_eq ℂ (n : ZMod l), hl_tot]
          have hmod_iff : (n : ZMod l) = 1 ↔ n % l = 1 := by
            rw [show (1 : ZMod l) = ((1 : ℕ) : ZMod l) by simp, ZMod.natCast_eq_natCast_iff',
              Nat.mod_eq_of_lt hl.one_lt]
          by_cases hm : n % l = 1
          · rw [if_pos (hmod_iff.mpr hm), if_pos hm]
            rw [← Complex.ofReal_natCast (n := n), ← Complex.ofReal_cpow (Nat.cast_nonneg n),
              Real.rpow_neg (Nat.cast_nonneg n)]
            push_cast
            ring
          · rw [if_neg (mt hmod_iff.mp hm), if_neg hm]; simp
      simp_rw [hinner]
      rw [← Complex.ofReal_tsum, Complex.ofReal_re, tsum_mul_left]
    -- Split `n` into primes and prime powers `p^k` (`k ≥ 2`)
    have hsplit_pp :
        (∑' n : ℕ, if n % l = 1 then (Λ n / Real.log (n : ℝ)) * (n : ℝ) ^ (-σ) else 0) ≤
          (∑' p : ℕ, if p.Prime ∧ p % l = 1 then (p : ℝ) ^ (-σ) else 0) + 2 := by
      have hf_summ : Summable (fun n : ℕ =>
          if n % l = 1 then (Λ n / Real.log (n : ℝ)) * (n : ℝ) ^ (-σ) else 0) := by
        have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
          have h := Real.summable_nat_rpow_inv.mpr hσ1
          exact h.congr fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n)]
        refine Summable.of_nonneg_of_le (fun n => by
          split_ifs
          · by_cases hn : n ≤ 1
            · interval_cases n <;> simp
            · exact mul_nonneg (div_nonneg vonMangoldt_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))) (by positivity)
          · exact le_rfl) (fun n => ?_) h1
        split_ifs
        · by_cases hn : n ≤ 1
          · interval_cases n
            · simp; positivity
            · simp
          · have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
            calc (Λ n / Real.log (n : ℝ)) * (n : ℝ) ^ (-σ)
                ≤ 1 * (n : ℝ) ^ (-σ) := mul_le_mul_of_nonneg_right
                    ((div_le_one hlog_pos).mpr vonMangoldt_le_log) (by positivity)
              _ = (n : ℝ) ^ (-σ) := one_mul _
        · positivity
      have hp_summ : Summable (fun p : ℕ =>
          if p.Prime ∧ p % l = 1 then (p : ℝ) ^ (-σ) else 0) := by
        have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
          have h := Real.summable_nat_rpow_inv.mpr hσ1
          exact h.congr fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n)]
        exact Summable.of_nonneg_of_le
          (fun p => by split_ifs <;> first | exact le_rfl | exact Real.rpow_nonneg (Nat.cast_nonneg p) _)
          (fun p => by split_ifs <;> first | exact le_rfl | exact Real.rpow_nonneg (Nat.cast_nonneg p) _) h1
      -- Bound every finite sum over `n ∈ range N` by prime part + non-prime-power tail `≤ 2`
      apply hf_summ.tsum_le_of_sum_range_le
      intro N
      let S1 := (range N).filter Nat.Prime
      let S2 := (range N).filter (fun n => ¬ n.Prime)
      have hpart : (∑ n ∈ range N, if n % l = 1 then (Λ n / Real.log (n : ℝ)) * (n : ℝ) ^ (-σ) else 0) =
          (∑ n ∈ S1, if n % l = 1 then (Λ n / Real.log (n : ℝ)) * (n : ℝ) ^ (-σ) else 0) +
          (∑ n ∈ S2, if n % l = 1 then (Λ n / Real.log (n : ℝ)) * (n : ℝ) ^ (-σ) else 0) :=
        (sum_filter_add_sum_filter_not (range N) Nat.Prime _).symm
      rw [hpart]
      apply add_le_add
      · -- Prime terms `n ∈ S1`
        have h1 : ∑ n ∈ S1, (if n % l = 1 then (Λ n / Real.log (n : ℝ)) * (n : ℝ) ^ (-σ) else 0) =
            ∑ p ∈ S1, if p.Prime ∧ p % l = 1 then (p : ℝ) ^ (-σ) else 0 := by
          refine sum_congr rfl fun n hn => ?_
          have hnpr : n.Prime := (mem_filter.mp hn).2
          have hlog_ne : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hnpr.one_lt)).ne'
          by_cases hm : n % l = 1
          · rw [if_pos hm, if_pos ⟨hnpr, hm⟩, vonMangoldt_apply_prime hnpr, div_self hlog_ne, one_mul]
          · rw [if_neg hm, if_neg (by tauto)]
        rw [h1]
        exact hp_summ.sum_le_tsum S1 fun p _ => by split_ifs <;> positivity
      · -- Non-prime prime powers `p^k` (`k ≥ 2`)
        have hpp_le : ∀ n ∈ S2,
            (if n % l = 1 then (Λ n / Real.log (n : ℝ)) * (n : ℝ) ^ (-σ) else 0) ≤
              if IsPrimePow n ∧ ¬ n.Prime then (n : ℝ) ^ (-(1 : ℝ)) else 0 := by
          intro n hn
          have hnp : ¬ n.Prime := (mem_filter.mp hn).2
          by_cases hpp : IsPrimePow n
          · simp only [hpp, hnp, not_false_eq_true, and_self, ↓reduceIte]
            split_ifs
            · have hn2 : 2 ≤ n := hpp.two_le
              have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
              calc (Λ n / Real.log (n : ℝ)) * (n : ℝ) ^ (-σ)
                  ≤ 1 * (n : ℝ) ^ (-σ) := mul_le_mul_of_nonneg_right
                      ((div_le_one hlog_pos).mpr vonMangoldt_le_log) (by positivity)
                _ = (n : ℝ) ^ (-σ) := one_mul _
                _ ≤ (n : ℝ) ^ (-(1 : ℝ)) :=
                    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by linarith)
            · positivity
          · simp only [hpp, false_and, ↓reduceIte]
            split_ifs
            · rw [vonMangoldt_eq_zero_iff.mpr hpp]; simp
            · exact le_rfl
        have hS2_le : ∑ n ∈ S2, (if IsPrimePow n ∧ ¬ n.Prime then (n : ℝ) ^ (-(1 : ℝ)) else 0) ≤ 2 := by
          -- Every non-prime prime power `n < N` is `p ^ (k + 2)` with `p < N`, `k < N`
          have hsub : S2.filter (fun n => IsPrimePow n ∧ ¬ n.Prime) ⊆
              ((Nat.primesBelow N) ×ˢ (range N)).image (fun pk : ℕ × ℕ => pk.1 ^ (pk.2 + 2)) := by
            intro n hn
            obtain ⟨hnS2, hpp, hnp⟩ := mem_filter.mp hn
            have hnN : n < N := mem_range.mp (mem_filter.mp hnS2).1
            rw [isPrimePow_nat_iff] at hpp
            obtain ⟨p, k, hp, hk, rfl⟩ := hpp
            have hk2 : 2 ≤ k := by
              by_contra! hlt
              have hk1 : k = 1 := by omega
              subst hk1; exact hnp (by simpa using hp)
            refine mem_image.mpr ⟨(p, k - 2), mem_product.mpr ⟨Nat.mem_primesBelow.mpr ⟨?_, hp⟩,
              mem_range.mpr ?_⟩, by congr 1; omega⟩
            · exact lt_of_le_of_lt (Nat.le_self_pow (by omega) p) hnN
            · have h2k : k < 2 ^ k := Nat.lt_two_pow_self
              have hpk : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
              omega
          rw [← sum_filter]
          calc ∑ n ∈ S2.filter (fun n => IsPrimePow n ∧ ¬ n.Prime), (n : ℝ) ^ (-(1 : ℝ))
              ≤ ∑ n ∈ ((Nat.primesBelow N) ×ˢ (range N)).image (fun pk : ℕ × ℕ => pk.1 ^ (pk.2 + 2)),
                  (n : ℝ) ^ (-(1 : ℝ)) :=
                sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
            _ ≤ ∑ pk ∈ (Nat.primesBelow N) ×ˢ (range N),
                  (((pk.1 ^ (pk.2 + 2) : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
                sum_image_le_of_nonneg (f := fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) fun _ _ => by positivity
            _ = ∑ p ∈ Nat.primesBelow N, ∑ k ∈ range N, ((p : ℝ)⁻¹ ^ (k + 2)) := by
                rw [sum_product]
                refine sum_congr rfl fun p _ => sum_congr rfl fun k _ => ?_
                rw [Real.rpow_neg_one, Nat.cast_pow, inv_pow]
            _ ≤ ∑ p ∈ Nat.primesBelow N, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
                refine sum_le_sum fun p hp => ?_
                have hpr := Nat.prime_of_mem_primesBelow hp
                have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
                have hp_inv_lt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
                have hshift : ∑ k ∈ range N, ((p : ℝ)⁻¹) ^ (k + 2) =
                    ((p : ℝ)⁻¹) ^ 2 * ∑ k ∈ range N, ((p : ℝ)⁻¹) ^ k := by
                  rw [mul_sum]; refine sum_congr rfl fun k _ => by rw [pow_add]; ring
                rw [hshift, geom_sum_eq hp_inv_lt.ne]
                have h1 : (1 - ((p : ℝ)⁻¹) ^ N) / (1 - (p : ℝ)⁻¹) ≤ 1 / (1 - (p : ℝ)⁻¹) :=
                  div_le_div_of_nonneg_right (by linarith [pow_nonneg (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ p)) N])
                    (by linarith)
                have h2 : (((p : ℝ)⁻¹) ^ N - 1) / ((p : ℝ)⁻¹ - 1) =
                    (1 - ((p : ℝ)⁻¹) ^ N) / (1 - (p : ℝ)⁻¹) := by
                  rw [← neg_div_neg_eq]; congr 1 <;> ring
                rw [h2]
                calc ((p : ℝ)⁻¹) ^ 2 * ((1 - ((p : ℝ)⁻¹) ^ N) / (1 - (p : ℝ)⁻¹))
                    ≤ ((p : ℝ)⁻¹) ^ 2 * (1 / (1 - (p : ℝ)⁻¹)) :=
                      mul_le_mul_of_nonneg_left h1 (by positivity)
                  _ = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
                      field_simp [(show (p : ℝ) ≠ 0 by linarith), (show (p : ℝ) - 1 ≠ 0 by linarith)]
            _ ≤ ∑ m ∈ Icc 2 (N + 2), (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) := by
                apply sum_le_sum_of_subset_of_nonneg
                · intro p hp
                  obtain ⟨hpN, hpr⟩ := Nat.mem_primesBelow.mp hp
                  exact mem_Icc.mpr ⟨hpr.two_le, by omega⟩
                · intro m hm _
                  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
                  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
                  positivity
            _ ≤ 2 := by
                have htel : ∀ M : ℕ, 2 ≤ M →
                    ∑ m ∈ Icc 2 M, (1 : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) = 1 - 1 / (M : ℝ) := by
                  intro M hM
                  induction M, hM using Nat.le_induction with
                  | base => norm_num
                  | succ k hk ih =>
                    rw [show Icc 2 (k + 1) = insert (k + 1) (Icc 2 k) by
                      ext m; simp only [mem_Icc, mem_insert]; omega]
                    rw [sum_insert (by simp), ih]
                    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
                    have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
                    push_cast; field_simp [hk0, hk1]; ring
                rw [htel (N + 2) (by omega)]
                have : (0 : ℝ) ≤ 1 / ((N + 2 : ℕ) : ℝ) := by positivity
                linarith
        exact (sum_le_sum hpp_le).trans hS2_le
    have h1 := hsum_log_lb σ hσ1 hσ2
    rw [hsum_orth] at h1
    have h2 : (Real.log (1 / (σ - 1)) - C_char) / ((l - 1 : ℕ) : ℝ) ≤
        ∑' n : ℕ, if n % l = 1 then (Λ n / Real.log (n : ℝ)) * (n : ℝ) ^ (-σ) else 0 :=
      (div_le_iff₀' hd_pos).mpr h1
    have h3 : (Real.log (1 / (σ - 1)) - C_char) / ((l - 1 : ℕ) : ℝ) =
        (1 / ((l - 1 : ℕ) : ℝ)) * Real.log (1 / (σ - 1)) - C_char / ((l - 1 : ℕ) : ℝ) := by ring
    linarith [h2, h3, hsplit_pp]
  -- Step 4: Set `σ = 1 + 1 / log U` and bound tail `p > U` via `sum_prime_log_div_rpow_le`
  refine ⟨C_char / ((l - 1 : ℕ) : ℝ) + 14, fun U hU => ?_⟩
  have hlogU_gt1 : 1 < Real.log U := by
    have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) (he.trans_le hU)
  let σ : ℝ := 1 + 1 / Real.log U
  have hσ1 : 1 < σ := by dsimp [σ]; linarith [show (0 : ℝ) < 1 / Real.log U by positivity]
  have hσ2 : σ ≤ 2 := by
    dsimp [σ]
    have : 1 / Real.log U ≤ 1 := (div_le_one (by linarith)).mpr hlogU_gt1.le
    linarith
  have hσ_sub : 1 / (σ - 1) = Real.log U := by
    dsimp [σ]; field_simp [(by linarith : Real.log U ≠ 0)]; ring
  have hlb := hprime_tsum_lb σ hσ1 hσ2
  rw [hσ_sub] at hlb
  -- Every finite sum of `1_{p prime, p ≡ 1 (l)} p^{-σ}` is bounded by `∑_{p ≤ U, p ≡ 1(l)} 1/p + 12`
  have hp_summ : Summable (fun p : ℕ =>
      if p.Prime ∧ p % l = 1 then (p : ℝ) ^ (-σ) else 0) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
      have h := Real.summable_nat_rpow_inv.mpr hσ1
      exact h.congr fun n => by rw [Real.rpow_neg (Nat.cast_nonneg n)]
    exact Summable.of_nonneg_of_le
      (fun p => by split_ifs <;> first | exact le_rfl | exact Real.rpow_nonneg (Nat.cast_nonneg p) _)
      (fun p => by split_ifs <;> first | exact le_rfl | exact Real.rpow_nonneg (Nat.cast_nonneg p) _) h1
  have htsum_ub : (∑' p : ℕ, if p.Prime ∧ p % l = 1 then (p : ℝ) ^ (-σ) else 0) ≤
      (∑ p ∈ (Nat.primesBelow (⌊U⌋₊ + 1)).filter (fun p => p % l = 1), (1 : ℝ) / (p : ℝ)) + 12 := by
    apply hp_summ.tsum_le_of_sum_range_le
    intro N
    let F := (range N).filter (fun p => p.Prime ∧ p % l = 1)
    have hrew : ∑ p ∈ range N, (if p.Prime ∧ p % l = 1 then (p : ℝ) ^ (-σ) else 0) =
        ∑ p ∈ F, (p : ℝ) ^ (-σ) := (sum_filter _ _).symm
    rw [hrew]
    let F_lo := F.filter (fun p => p ≤ ⌊U⌋₊)
    let F_hi := F.filter (fun p => ¬ p ≤ ⌊U⌋₊)
    rw [← sum_filter_add_sum_filter_not F (fun p => p ≤ ⌊U⌋₊)]
    apply add_le_add
    · -- `p ≤ U`: `p^(-σ) ≤ 1 / p`
      have hle_lo : ∑ p ∈ F_lo, (p : ℝ) ^ (-σ) ≤ ∑ p ∈ F_lo, (1 : ℝ) / (p : ℝ) := by
        refine sum_le_sum fun p hp => ?_
        have hpr : p.Prime := (mem_filter.mp (mem_filter.mp hp).1).2.1
        rw [one_div, ← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpr.one_lt.le) (by linarith)
      have hsub : F_lo ⊆ (Nat.primesBelow (⌊U⌋₊ + 1)).filter (fun p => p % l = 1) := by
        intro p hp
        obtain ⟨hpF, hple⟩ := mem_filter.mp hp
        obtain ⟨_, hpr, hmod⟩ := mem_filter.mp hpF
        exact mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨Nat.lt_succ_of_le hple, hpr⟩, hmod⟩
      exact hle_lo.trans (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity)
    · -- `p > U`: `p^(-σ) ≤ (log p / p^σ) / log U`, summed `≤ 12`
      have hhi_pr : ∀ p ∈ F_hi, p.Prime := fun p hp =>
        (mem_filter.mp (mem_filter.mp hp).1).2.1
      have hhi_le : ∀ p ∈ F_hi,
          (p : ℝ) ^ (-σ) ≤ (Real.log (p : ℝ) / (p : ℝ) ^ σ) / Real.log U := by
        intro p hp
        have hgt : U < (p : ℝ) := by
          have h1 : ⌊U⌋₊ < p := by have := (mem_filter.mp hp).2; omega
          exact (Nat.lt_floor_add_one U).trans_le (by exact_mod_cast h1)
        have hlog_ge : Real.log U ≤ Real.log (p : ℝ) := Real.log_le_log (by linarith) hgt.le
        rw [Real.rpow_neg (Nat.cast_nonneg _), ← one_div]
        rw [le_div_iff₀ (by linarith), div_mul_eq_mul_div, one_mul]
        exact div_le_div_of_nonneg_right hlog_ge (by positivity)
      calc ∑ p ∈ F_hi, (p : ℝ) ^ (-σ)
          ≤ ∑ p ∈ F_hi, (Real.log (p : ℝ) / (p : ℝ) ^ σ) / Real.log U := sum_le_sum hhi_le
        _ = (∑ p ∈ F_hi, Real.log (p : ℝ) / (p : ℝ) ^ σ) / Real.log U := (sum_div ..).symm
        _ ≤ (12 / (σ - 1)) / Real.log U :=
            div_le_div_of_nonneg_right (sum_prime_log_div_rpow_le hσ1 hσ2 F_hi hhi_pr) (by linarith)
        _ = 12 := by
            have : σ - 1 = 1 / Real.log U := by dsimp [σ]; ring
            rw [this]; field_simp [(by linarith : Real.log U ≠ 0)]
  linarith

end MertensAP

section RankinSieve

/-- Expanding a finite product `∏_{p ∈ S} (1 + f p)` over subsets `T ⊆ S`. -/
private lemma prod_one_add_eq_sum_powerset {S : Finset ℕ} (f : ℕ → ℝ) :
    ∏ p ∈ S, (1 + f p) = ∑ T ∈ S.powerset, ∏ p ∈ T, f p := by
  have h : ∏ p ∈ S, (1 + f p) = ∏ p ∈ S, (f p + 1) := prod_congr rfl fun _ _ => add_comm _ _
  rw [h, Finset.prod_add f (fun _ => (1 : ℝ)) S]
  refine sum_congr rfl fun T _ => by simp

set_option maxHeartbeats 800000 in
/-- Truncated squarefree sieve-sum lower bound via Rankin's trick and Mertens in AP. -/
theorem rankin_sieve_sum_lower {l : ℕ} (hl : l.Prime) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Z : ℕ), 10 ≤ Z → ∀ (Bad : Finset ℕ),
      (c * Real.log (Z : ℝ)) /
        (∏ r ∈ Bad.filter (fun r => r.Prime ∧ r % l = 1), (1 + ((l - 1 : ℕ) : ℝ) / (r : ℝ))) ≤
      ∑ m ∈ (Icc 1 Z).filter (fun m => Squarefree m ∧ ∀ r ∈ m.primeFactors, r % l = 1 ∧ r ∉ Bad),
        ∏ r ∈ m.primeFactors, (((l - 1 : ℕ) : ℝ) / (r : ℝ)) := by
  obtain ⟨C_mert, hMert⟩ := mertens_ap_lower hl
  let d : ℕ := l - 1
  have hd_pos : (0 : ℝ) < (d : ℝ) := by
    have := hl.two_le; dsimp [d]; exact_mod_cast (by omega : 0 < l - 1)
  -- Choose `α = 1 / (20 * d + 1)` so `e^(6 * e * d + ...) * Z^(-1/(α log Z)) ≤ 1/2`
  let α : ℝ := 1 / (24 * (d : ℝ) + 1)
  have hα_pos : 0 < α := by dsimp [α]; positivity
  have hα_lt1 : α < 1 := by
    dsimp [α]
    rw [div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by have := hl.two_le; omega)
    linarith
  -- Constant `C_sq = d^2` bounds `∑_{r prime} (d/r)^2 / 2`
  have hsq_sum : ∀ S : Finset ℕ, (∀ r ∈ S, r.Prime) →
      ∑ r ∈ S, (((d : ℝ) / (r : ℝ)) ^ 2) / 2 ≤ (d : ℝ) ^ 2 := by
    intro S hS
    have hsub : S ⊆ Icc 1 (S.sup id + 1) := by
      intro r hr
      exact mem_Icc.mpr ⟨(hS r hr).pos, Nat.le_succ_of_le (le_sup (f := id) hr)⟩
    have h2 : ∑ r ∈ S, (1 : ℝ) / (r : ℝ) ^ 2 ≤ 2 := by
      calc ∑ r ∈ S, (1 : ℝ) / (r : ℝ) ^ 2
          ≤ ∑ r ∈ Icc 1 (S.sup id + 1), (1 : ℝ) / (r : ℝ) ^ 2 :=
            sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ ≤ 2 := by
            have htel : ∀ n : ℕ, 1 ≤ n → ∑ m ∈ Icc 1 n, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
              intro n hn
              induction n, hn using Nat.le_induction with
              | base => norm_num
              | succ t ht ih =>
                rw [show Icc 1 (t + 1) = insert (t + 1) (Icc 1 t) by
                  ext m; simp only [mem_Icc, mem_insert]; omega]
                rw [sum_insert (by simp)]
                have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
                have hstep : 1 / ((t + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (t : ℝ) - 1 / ((t + 1 : ℕ) : ℝ) := by
                  push_cast
                  rw [div_sub_div _ _ ht0.ne' (by positivity)]
                  have : (1 : ℝ) * (t + 1) - t * 1 = 1 := by ring
                  rw [this]; gcongr; nlinarith
                linarith
            have := htel (S.sup id + 1) (by omega)
            have : (0 : ℝ) ≤ 1 / ((S.sup id + 1 : ℕ) : ℝ) := by positivity
            linarith
    calc ∑ r ∈ S, (((d : ℝ) / (r : ℝ)) ^ 2) / 2
        = ((d : ℝ) ^ 2 / 2) * ∑ r ∈ S, (1 : ℝ) / (r : ℝ) ^ 2 := by
          rw [mul_sum]; refine sum_congr rfl fun r _ => by ring
      _ ≤ ((d : ℝ) ^ 2 / 2) * 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (d : ℝ) ^ 2 := by ring
  -- Pick `Z₀` large enough that `(Z : ℝ)^α ≥ 3` and `Real.log ((Z : ℝ)^α) ≥ 1`
  let Z₀ : ℕ := max 10 (⌈Real.exp (2 / α)⌉₊ + 1)
  have hc_pos : 0 < min ((1 / 2 : ℝ) * Real.exp (-(d : ℝ) * C_mert - (d : ℝ) ^ 2) * α)
      (1 / Real.log (Z₀ : ℝ)) := by
    have hZ0 : (10 : ℝ) ≤ Z₀ := by exact_mod_cast le_max_left 10 _
    have hlogZ0 : 0 < Real.log (Z₀ : ℝ) := Real.log_pos (by linarith)
    exact lt_min (by positivity) (by positivity)
  refine ⟨min ((1 / 2 : ℝ) * Real.exp (-(d : ℝ) * C_mert - (d : ℝ) ^ 2) * α)
    (1 / Real.log (Z₀ : ℝ)), hc_pos, fun Z hZ10 Bad => ?_⟩
  let D : ℝ := ∏ r ∈ Bad.filter (fun r => r.Prime ∧ r % l = 1), (1 + (d : ℝ) / (r : ℝ))
  have hD_ge1 : 1 ≤ D := one_le_prod fun r _ => by
    linarith [show (0 : ℝ) ≤ (d : ℝ) / (r : ℝ) by positivity]
  have hD_pos : 0 < D := lt_of_lt_of_le zero_lt_one hD_ge1
  let S_trunc := (Icc 1 Z).filter (fun m => Squarefree m ∧ ∀ r ∈ m.primeFactors, r % l = 1 ∧ r ∉ Bad)
  have h1_mem : 1 ∈ S_trunc := by
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, by omega⟩, squarefree_one, by simp⟩
  have hS_ge1 : (1 : ℝ) ≤ ∑ m ∈ S_trunc, ∏ r ∈ m.primeFactors, ((d : ℝ) / (r : ℝ)) := by
    calc (1 : ℝ) = ∏ r ∈ (1 : ℕ).primeFactors, ((d : ℝ) / (r : ℝ)) := by simp
      _ ≤ ∑ m ∈ S_trunc, ∏ r ∈ m.primeFactors, ((d : ℝ) / (r : ℝ)) :=
          single_le_sum (f := fun m : ℕ => ∏ r ∈ m.primeFactors, ((d : ℝ) / (r : ℝ)))
            (fun m _ => prod_nonneg fun r _ => by positivity) h1_mem
  by_cases hZ_small : Z < Z₀
  · -- Small `Z < Z₀`: trivial since `1 ∈ S_trunc` gives RHS `≥ 1` and LHS `≤ 1`
    have hlog_le : Real.log (Z : ℝ) ≤ Real.log (Z₀ : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < Z)) (by exact_mod_cast hZ_small.le)
    have hZ0 : (10 : ℝ) ≤ Z₀ := by exact_mod_cast le_max_left 10 _
    have hlogZ0 : 0 < Real.log (Z₀ : ℝ) := Real.log_pos (by linarith)
    have hmin_le : min ((1 / 2 : ℝ) * Real.exp (-(d : ℝ) * C_mert - (d : ℝ) ^ 2) * α)
        (1 / Real.log (Z₀ : ℝ)) ≤ 1 / Real.log (Z₀ : ℝ) := min_le_right _ _
    have hnum_le1 : min ((1 / 2 : ℝ) * Real.exp (-(d : ℝ) * C_mert - (d : ℝ) ^ 2) * α)
        (1 / Real.log (Z₀ : ℝ)) * Real.log (Z : ℝ) ≤ 1 := by
      calc _ ≤ (1 / Real.log (Z₀ : ℝ)) * Real.log (Z₀ : ℝ) :=
            mul_le_mul hmin_le hlog_le (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Z)))
              (by positivity)
        _ = 1 := by field_simp [hlogZ0.ne']
    have hdiv_le1 : (min ((1 / 2 : ℝ) * Real.exp (-(d : ℝ) * C_mert - (d : ℝ) ^ 2) * α)
        (1 / Real.log (Z₀ : ℝ)) * Real.log (Z : ℝ)) / D ≤ 1 := by
      rw [div_le_one hD_pos]; exact hnum_le1.trans hD_ge1
    exact hdiv_le1.trans hS_ge1
  · -- Large `Z ≥ Z₀`: Rankin's trick with `U = Z^α`
    push Not at hZ_small
    have hZ_pos : (0 : ℝ) < (Z : ℝ) := by exact_mod_cast (by omega : 0 < Z)
    let U : ℝ := (Z : ℝ) ^ α
    have hlogZ_ge : 2 / α ≤ Real.log (Z : ℝ) := by
      have h1 : Real.exp (2 / α) ≤ (Z₀ : ℝ) := by
        have hce : Real.exp (2 / α) ≤ (⌈Real.exp (2 / α)⌉₊ : ℝ) := Nat.le_ceil _
        have hle : (⌈Real.exp (2 / α)⌉₊ : ℝ) ≤ Z₀ := by
          exact_mod_cast (Nat.le_succ _).trans (le_max_right 10 _)
        linarith
      have h2 : Real.exp (2 / α) ≤ (Z : ℝ) := h1.trans (by exact_mod_cast hZ_small)
      have := Real.log_le_log (Real.exp_pos _) h2
      rwa [Real.log_exp] at this
    have hlogU_eq : Real.log U = α * Real.log (Z : ℝ) := by
      dsimp [U]; rw [Real.log_rpow hZ_pos]
    have hlogU_ge2 : 2 ≤ Real.log U := by
      rw [hlogU_eq]
      have := (div_le_iff₀' hα_pos).mp hlogZ_ge
      linarith
    have hU_ge3 : 3 ≤ U := by
      have he2 : (3 : ℝ) ≤ Real.exp 2 := by
        have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        nlinarith
      calc (3 : ℝ) ≤ Real.exp 2 := he2
        _ ≤ Real.exp (Real.log U) := Real.exp_le_exp.mpr hlogU_ge2
        _ = U := Real.exp_log (by dsimp [U]; positivity)
    let Pr : Finset ℕ := (Nat.primesBelow (⌊U⌋₊ + 1)).filter (fun r => r % l = 1 ∧ r ∉ Bad)
    let P_full : ℝ := ∏ r ∈ Pr, (1 + (d : ℝ) / (r : ℝ))
    have hP_pos : 0 < P_full := prod_pos fun r _ => by positivity
    -- Expand `P_full` as sum over `T ∈ Pr.powerset`, split into `∏ T ≤ Z` and `∏ T > Z`
    have hP_exp : P_full = ∑ T ∈ Pr.powerset, ∏ r ∈ T, ((d : ℝ) / (r : ℝ)) :=
      prod_one_add_eq_sum_powerset _
    let PS_le := Pr.powerset.filter (fun T => ∏ r ∈ T, r ≤ Z)
    let PS_gt := Pr.powerset.filter (fun T => ¬ ∏ r ∈ T, r ≤ Z)
    have hPS_le_le_S : ∑ T ∈ PS_le, ∏ r ∈ T, ((d : ℝ) / (r : ℝ)) ≤
        ∑ m ∈ S_trunc, ∏ r ∈ m.primeFactors, ((d : ℝ) / (r : ℝ)) := by
      -- Map `T ↦ ∏ r ∈ T, r` is injective into `S_trunc`
      have hmap : ∀ T ∈ PS_le, (∏ r ∈ T, r) ∈ S_trunc := by
        intro T hT
        obtain ⟨hTsub, hprod_le⟩ := mem_filter.mp hT
        have hTPr : T ⊆ Pr := mem_powerset.mp hTsub
        have hTprime : ∀ r ∈ T, r.Prime := fun r hr =>
          Nat.prime_of_mem_primesBelow (mem_filter.mp (hTPr hr)).1
        have hprod_pos : 0 < ∏ r ∈ T, r := prod_pos fun r hr => (hTprime r hr).pos
        have hsq : Squarefree (∏ r ∈ T, r) := by
          rw [Nat.squarefree_iff_prime_squarefree]
          intro p hp hp2
          -- If `p^2 ∣ ∏ T`, since `T` is a set of distinct primes, impossible
          have hpT : p ∈ T := by
            have hd : p ∣ ∏ r ∈ T, r := (dvd_mul_left p p).trans hp2
            obtain ⟨r, hrT, hpr⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd
            exact (Nat.prime_dvd_prime_iff_eq hp (hTprime r hrT)).mp hpr ▸ hrT
          rw [← mul_prod_erase T (fun r => r) hpT] at hp2
          have hp_er : p ∣ ∏ r ∈ T.erase p, r := (mul_dvd_mul_iff_left hp.ne_zero).mp hp2
          obtain ⟨r, hr_er, hpr⟩ := (hp.prime.dvd_finsetProd_iff id).mp hp_er
          have hne : r ≠ p := (mem_erase.mp hr_er).1
          have hrpr : r.Prime := hTprime r (mem_erase.mp hr_er).2
          exact hne ((Nat.prime_dvd_prime_iff_eq hp hrpr).mp hpr).symm
        have hpf : (∏ r ∈ T, r).primeFactors = T := by
          ext r
          rw [Nat.mem_primeFactors_of_ne_zero hprod_pos.ne']
          constructor
          · rintro ⟨hr, hdvd⟩
            obtain ⟨q, hqT, hrq⟩ := (hr.prime.dvd_finsetProd_iff id).mp hdvd
            exact (Nat.prime_dvd_prime_iff_eq hr (hTprime q hqT)).mp hrq ▸ hqT
          · intro hrT
            exact ⟨hTprime r hrT, dvd_prod_of_mem id hrT⟩
        refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hprod_pos, hprod_le⟩, hsq, ?_⟩
        rw [hpf]
        intro r hrT
        exact (mem_filter.mp (hTPr hrT)).2
      have hinj : Set.InjOn (fun T : Finset ℕ => ∏ r ∈ T, r) (PS_le : Set (Finset ℕ)) := by
        intro T1 hT1 T2 hT2 heq
        have hpf_eq : ∀ T ∈ PS_le, (∏ r ∈ T, r).primeFactors = T := fun T hT => by
          have hTPr : T ⊆ Pr := mem_powerset.mp (mem_filter.mp hT).1
          have hTprime : ∀ r ∈ T, r.Prime := fun r hr =>
            Nat.prime_of_mem_primesBelow (mem_filter.mp (hTPr hr)).1
          have hpos : 0 < ∏ r ∈ T, r := prod_pos fun r hr => (hTprime r hr).pos
          ext r
          rw [Nat.mem_primeFactors_of_ne_zero hpos.ne']
          constructor
          · rintro ⟨hr, hdvd⟩
            obtain ⟨q, hqT, hrq⟩ := (hr.prime.dvd_finsetProd_iff id).mp hdvd
            exact (Nat.prime_dvd_prime_iff_eq hr (hTprime q hqT)).mp hrq ▸ hqT
          · intro hrT; exact ⟨hTprime r hrT, dvd_prod_of_mem id hrT⟩
        dsimp only at heq
        rw [← hpf_eq T1 hT1, ← hpf_eq T2 hT2, heq]
      have hpf_id : ∀ T ∈ PS_le, (∏ r ∈ T, r).primeFactors = T := fun T hT => by
        have hTPr : T ⊆ Pr := mem_powerset.mp (mem_filter.mp hT).1
        have hTprime : ∀ r ∈ T, r.Prime := fun r hr =>
          Nat.prime_of_mem_primesBelow (mem_filter.mp (hTPr hr)).1
        have hpos : 0 < ∏ r ∈ T, r := prod_pos fun r hr => (hTprime r hr).pos
        ext r
        rw [Nat.mem_primeFactors_of_ne_zero hpos.ne']
        constructor
        · rintro ⟨hr, hdvd⟩
          obtain ⟨q, hqT, hrq⟩ := (hr.prime.dvd_finsetProd_iff id).mp hdvd
          exact (Nat.prime_dvd_prime_iff_eq hr (hTprime q hqT)).mp hrq ▸ hqT
        · intro hrT; exact ⟨hTprime r hrT, dvd_prod_of_mem id hrT⟩
      calc ∑ T ∈ PS_le, ∏ r ∈ T, ((d : ℝ) / (r : ℝ))
          = ∑ T ∈ PS_le, ∏ r ∈ (∏ q ∈ T, q).primeFactors, ((d : ℝ) / (r : ℝ)) :=
            sum_congr rfl fun T hT => by rw [hpf_id T hT]
        _ = ∑ m ∈ PS_le.image (fun T => ∏ r ∈ T, r), ∏ r ∈ m.primeFactors, ((d : ℝ) / (r : ℝ)) :=
            (Finset.sum_image (f := fun m : ℕ => ∏ r ∈ m.primeFactors, ((d : ℝ) / (r : ℝ))) hinj).symm
        _ ≤ ∑ m ∈ S_trunc, ∏ r ∈ m.primeFactors, ((d : ℝ) / (r : ℝ)) :=
            sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hmap) fun _ _ _ =>
              prod_nonneg fun _ _ => by positivity
    -- Rankin tail bound: `∑ T ∈ PS_gt, ... ≤ (1 / 2) * P_full`
    let σ : ℝ := 1 / Real.log U
    have hσ_pos : 0 < σ := by dsimp [σ]; exact div_pos zero_lt_one (by linarith)
    have htail : ∑ T ∈ PS_gt, ∏ r ∈ T, ((d : ℝ) / (r : ℝ)) ≤ (1 / 2 : ℝ) * P_full := by
      have hterm_le : ∀ T ∈ PS_gt,
          ∏ r ∈ T, ((d : ℝ) / (r : ℝ)) ≤
            (Z : ℝ) ^ (-σ) * ∏ r ∈ T, (((d : ℝ) / (r : ℝ)) * (r : ℝ) ^ σ) := by
        intro T hT
        have hgt : Z < ∏ r ∈ T, r := by have := (mem_filter.mp hT).2; omega
        have hTPr : T ⊆ Pr := mem_powerset.mp (mem_filter.mp hT).1
        have hprod_ge : (Z : ℝ) ≤ ((∏ r ∈ T, r : ℕ) : ℝ) := by exact_mod_cast hgt.le
        have hpow_ge : (1 : ℝ) ≤ (Z : ℝ) ^ (-σ) * (((∏ r ∈ T, r : ℕ) : ℝ) ^ σ) := by
          rw [Real.rpow_neg hZ_pos.le, inv_mul_eq_div, one_le_div (by positivity)]
          exact Real.rpow_le_rpow hZ_pos.le hprod_ge hσ_pos.le
        have hprod_rpow : (((∏ r ∈ T, r : ℕ) : ℝ) ^ σ) = ∏ r ∈ T, (r : ℝ) ^ σ := by
          rw [Nat.cast_prod, Real.finsetProd_rpow T _ (fun r _ => Nat.cast_nonneg r)]
        rw [prod_mul_distrib, ← hprod_rpow]
        calc ∏ r ∈ T, ((d : ℝ) / (r : ℝ))
            = 1 * ∏ r ∈ T, ((d : ℝ) / (r : ℝ)) := (one_mul _).symm
          _ ≤ ((Z : ℝ) ^ (-σ) * ((∏ r ∈ T, r : ℕ) : ℝ) ^ σ) * ∏ r ∈ T, ((d : ℝ) / (r : ℝ)) :=
              mul_le_mul_of_nonneg_right hpow_ge (prod_nonneg fun _ _ => by positivity)
          _ = (Z : ℝ) ^ (-σ) * ((∏ r ∈ T, ((d : ℝ) / (r : ℝ))) * ((∏ r ∈ T, r : ℕ) : ℝ) ^ σ) := by ring
      have hratio : (∏ r ∈ Pr, (1 + ((d : ℝ) / (r : ℝ)) * (r : ℝ) ^ σ)) / P_full ≤
          Real.exp (24 * (d : ℝ)) := by
        dsimp [P_full]
        rw [← prod_div_distrib]
        have hfac : ∀ r ∈ Pr,
            (1 + ((d : ℝ) / (r : ℝ)) * (r : ℝ) ^ σ) / (1 + (d : ℝ) / (r : ℝ)) ≤
              Real.exp (3 * (d : ℝ) * σ * (Real.log (r : ℝ) / (r : ℝ))) := by
          intro r hr
          have hrm := Nat.mem_primesBelow.mp (mem_filter.mp hr).1
          have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr hrm.2.pos
          have hr_le : (r : ℝ) ≤ U := by
            have : r ≤ ⌊U⌋₊ := by omega
            exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by linarith))
          have hσlog : σ * Real.log (r : ℝ) ≤ 1 := by
            dsimp [σ]
            rw [one_div_mul_eq_div, div_le_one (by linarith)]
            exact Real.log_le_log hr_pos hr_le
          have hr_sub : (r : ℝ) ^ σ - 1 ≤ 3 * σ * Real.log (r : ℝ) := by
            rw [Real.rpow_def_of_pos hr_pos, mul_comm (Real.log (r : ℝ)) σ]
            set t := σ * Real.log (r : ℝ)
            have ht_nn : 0 ≤ t := mul_nonneg hσ_pos.le (Real.log_nonneg (by exact_mod_cast hrm.2.one_lt.le))
            have h2 : Real.exp t - 1 ≤ t * Real.exp t := by
              have h1t : 1 - t ≤ (Real.exp t)⁻¹ := by
                have := Real.add_one_le_exp (-t)
                rw [Real.exp_neg] at this
                linarith
              have hexp_pos : 0 < Real.exp t := Real.exp_pos t
              have h3 : (1 - t) * Real.exp t ≤ 1 := by
                have := mul_le_mul_of_nonneg_right h1t hexp_pos.le
                rwa [inv_mul_cancel₀ hexp_pos.ne'] at this
              linarith
            have h3 : Real.exp t ≤ 3 :=
              (Real.exp_le_exp.mpr hσlog).trans (by linarith [Real.exp_one_lt_d9])
            nlinarith
          have h1 : (1 + ((d : ℝ) / (r : ℝ)) * (r : ℝ) ^ σ) / (1 + (d : ℝ) / (r : ℝ)) ≤
              1 + ((d : ℝ) / (r : ℝ)) * ((r : ℝ) ^ σ - 1) := by
            rw [div_le_iff₀ (by positivity)]
            have : (0 : ℝ) ≤ ((d : ℝ) / (r : ℝ)) ^ 2 * ((r : ℝ) ^ σ - 1) := by
              have : 1 ≤ (r : ℝ) ^ σ := Real.one_le_rpow (by exact_mod_cast hrm.2.one_lt.le) hσ_pos.le
              exact mul_nonneg (sq_nonneg _) (by linarith)
            nlinarith
          have h2 : 1 + ((d : ℝ) / (r : ℝ)) * ((r : ℝ) ^ σ - 1) ≤
              1 + 3 * (d : ℝ) * σ * (Real.log (r : ℝ) / (r : ℝ)) := by
            have hmul := mul_le_mul_of_nonneg_left hr_sub (show (0 : ℝ) ≤ (d : ℝ) / (r : ℝ) by positivity)
            have heq : (d : ℝ) / (r : ℝ) * (3 * σ * Real.log (r : ℝ)) =
                3 * (d : ℝ) * σ * (Real.log (r : ℝ) / (r : ℝ)) := by ring
            linarith
          exact (h1.trans h2).trans (by linarith [Real.add_one_le_exp (3 * (d : ℝ) * σ * (Real.log (r : ℝ) / (r : ℝ)))])
        calc ∏ r ∈ Pr, ((1 + ((d : ℝ) / (r : ℝ)) * (r : ℝ) ^ σ) / (1 + (d : ℝ) / (r : ℝ)))
            ≤ ∏ r ∈ Pr, Real.exp (3 * (d : ℝ) * σ * (Real.log (r : ℝ) / (r : ℝ))) :=
              prod_le_prod (fun r _ => by positivity) hfac
          _ = Real.exp (∑ r ∈ Pr, 3 * (d : ℝ) * σ * (Real.log (r : ℝ) / (r : ℝ))) :=
              (Real.exp_sum Pr _).symm
          _ ≤ Real.exp (24 * (d : ℝ)) := by
              apply Real.exp_le_exp.mpr
              rw [← mul_sum]
              have hsub : Pr ⊆ Nat.primesBelow (⌊U⌋₊ + 1) := filter_subset _ _
              have hch := sum_prime_log_div_le (by linarith : 1 ≤ U)
              have hsum_le : ∑ r ∈ Pr, Real.log (r : ℝ) / (r : ℝ) ≤ 6 * Real.log U + 3 :=
                (sum_le_sum_of_subset_of_nonneg hsub fun r hr _ =>
                  div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesBelow hr).one_lt.le))
                    (Nat.cast_nonneg _)).trans hch
              have hσ_mul : σ * (6 * Real.log U + 3) ≤ 8 := by
                dsimp [σ]
                rw [one_div_mul_eq_div, div_le_iff₀ (by linarith)]
                linarith [hlogU_ge2]
              calc 3 * (d : ℝ) * σ * ∑ r ∈ Pr, Real.log (r : ℝ) / (r : ℝ)
                  ≤ 3 * (d : ℝ) * (σ * (6 * Real.log U + 3)) := by
                    rw [mul_assoc]
                    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum_le hσ_pos.le) (by positivity)
                _ ≤ 3 * (d : ℝ) * 8 := mul_le_mul_of_nonneg_left hσ_mul (by positivity)
                _ = 24 * (d : ℝ) := by ring
      have hZ_sig : (Z : ℝ) ^ (-σ) * Real.exp (24 * (d : ℝ)) ≤ 1 / 2 := by
        rw [Real.rpow_def_of_pos hZ_pos, ← Real.exp_add]
        have hexp_eq : Real.log (Z : ℝ) * (-σ) + 24 * (d : ℝ) = -1 := by
          dsimp [σ]
          rw [hlogU_eq]
          have hlogZ_pos : 0 < Real.log (Z : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < Z))
          have hlogZ_ne : Real.log (Z : ℝ) ≠ 0 := hlogZ_pos.ne'
          have h1 : Real.log (Z : ℝ) * (-(1 / (α * Real.log (Z : ℝ)))) = -(1 / α) := by
            field_simp [hα_pos.ne', hlogZ_ne]
          rw [h1]
          dsimp [α]
          field_simp [(by positivity : 24 * (d : ℝ) + 1 ≠ 0)]
          ring
        rw [hexp_eq, Real.exp_neg]
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        exact (inv_le_comm₀ (Real.exp_pos 1) (by norm_num)).mpr (by linarith)
      calc ∑ T ∈ PS_gt, ∏ r ∈ T, ((d : ℝ) / (r : ℝ))
          ≤ ∑ T ∈ PS_gt, (Z : ℝ) ^ (-σ) * ∏ r ∈ T, (((d : ℝ) / (r : ℝ)) * (r : ℝ) ^ σ) :=
            sum_le_sum hterm_le
        _ = (Z : ℝ) ^ (-σ) * ∑ T ∈ PS_gt, ∏ r ∈ T, (((d : ℝ) / (r : ℝ)) * (r : ℝ) ^ σ) :=
            (mul_sum ..).symm
        _ ≤ (Z : ℝ) ^ (-σ) * ∑ T ∈ Pr.powerset, ∏ r ∈ T, (((d : ℝ) / (r : ℝ)) * (r : ℝ) ^ σ) :=
            mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ =>
              prod_nonneg fun _ _ => by positivity) (by positivity)
        _ = (Z : ℝ) ^ (-σ) * ∏ r ∈ Pr, (1 + ((d : ℝ) / (r : ℝ)) * (r : ℝ) ^ σ) := by
            rw [prod_one_add_eq_sum_powerset]
        _ = (Z : ℝ) ^ (-σ) * ((∏ r ∈ Pr, (1 + ((d : ℝ) / (r : ℝ)) * (r : ℝ) ^ σ)) / P_full) * P_full := by
            field_simp [hP_pos.ne']
        _ ≤ ((Z : ℝ) ^ (-σ) * Real.exp (24 * (d : ℝ))) * P_full := by gcongr
        _ ≤ (1 / 2 : ℝ) * P_full := mul_le_mul_of_nonneg_right hZ_sig hP_pos.le
    have hS_ge_halfP : (1 / 2 : ℝ) * P_full ≤ ∑ m ∈ S_trunc, ∏ r ∈ m.primeFactors, ((d : ℝ) / (r : ℝ)) := by
      have hsplit : P_full = (∑ T ∈ PS_le, ∏ r ∈ T, ((d : ℝ) / (r : ℝ))) +
          (∑ T ∈ PS_gt, ∏ r ∈ T, ((d : ℝ) / (r : ℝ))) := by
        rw [hP_exp]; exact (sum_filter_add_sum_filter_not _ _ _).symm
      linarith
    -- Lower bound `P_full * D` using `mertens_ap_lower` and `log(1 + u) ≥ u - u^2 / 2`
    let Pr_all : Finset ℕ := (Nat.primesBelow (⌊U⌋₊ + 1)).filter (fun r => r % l = 1)
    have hP_mul_D : ∏ r ∈ Pr_all, (1 + (d : ℝ) / (r : ℝ)) ≤ P_full * D := by
      let Pr_bad := Pr_all.filter (fun r => r ∈ Bad)
      have hsplit : ∏ r ∈ Pr_all, (1 + (d : ℝ) / (r : ℝ)) =
          P_full * ∏ r ∈ Pr_bad, (1 + (d : ℝ) / (r : ℝ)) := by
        have hPr_eq : Pr_all.filter (fun r => ¬ r ∈ Bad) = Pr := by
          ext r; simp only [Pr_all, Pr, mem_filter]; tauto
        rw [← prod_filter_mul_prod_filter_not Pr_all (fun r => r ∈ Bad), hPr_eq, mul_comm]
      rw [hsplit]
      apply mul_le_mul_of_nonneg_left _ hP_pos.le
      have hsub_bad : Pr_bad ⊆ Bad.filter (fun r => r.Prime ∧ r % l = 1) := by
        intro r hr
        obtain ⟨hr_all, hr_bad⟩ := mem_filter.mp hr
        obtain ⟨hr_pr, hr_mod⟩ := mem_filter.mp hr_all
        exact mem_filter.mpr ⟨hr_bad, Nat.prime_of_mem_primesBelow hr_pr, hr_mod⟩
      have hle_D : ∏ r ∈ Pr_bad, (1 + (d : ℝ) / (r : ℝ)) ≤ D := by
        dsimp [D]
        rw [← Finset.prod_sdiff hsub_bad]
        have h1 : (1 : ℝ) ≤ ∏ r ∈ Bad.filter (fun r => r.Prime ∧ r % l = 1) \ Pr_bad,
            (1 + (d : ℝ) / (r : ℝ)) :=
          one_le_prod fun r _ => by linarith [show (0 : ℝ) ≤ (d : ℝ) / (r : ℝ) by positivity]
        have h2 : (0 : ℝ) ≤ ∏ r ∈ Pr_bad, (1 + (d : ℝ) / (r : ℝ)) :=
          prod_nonneg fun r _ => by positivity
        nlinarith
      exact hle_D
    have hprod_all_lb : Real.exp (-(d : ℝ) * C_mert - (d : ℝ) ^ 2) * Real.log U ≤
        ∏ r ∈ Pr_all, (1 + (d : ℝ) / (r : ℝ)) := by
      have hlog_ge : ∀ r ∈ Pr_all,
          (d : ℝ) / (r : ℝ) - (((d : ℝ) / (r : ℝ)) ^ 2) / 2 ≤ Real.log (1 + (d : ℝ) / (r : ℝ)) := by
        intro r _
        set u := (d : ℝ) / (r : ℝ)
        have hu : 0 ≤ u := by positivity
        have hf_mono : MonotoneOn (fun t : ℝ => Real.log (1 + t) - (t - t ^ 2 / 2)) (Set.Ici 0) := by
          apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
          · exact ((continuous_const.add continuous_id).continuousOn.log fun t ht => by
              dsimp; have : (0 : ℝ) ≤ t := ht; linarith).sub
              (continuousOn_id.sub ((continuousOn_id.pow 2).div_const 2))
          · intro t ht
            have ht0 : 0 < t := by simpa [interior_Ici] using ht
            have h1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + t)) t := by
              have := ((hasDerivAt_id t).const_add 1).log (by dsimp; linarith)
              simpa [one_div] using this
            have h2 : HasDerivAt (fun x : ℝ => x - x ^ 2 / 2) (1 - t) t := by
              have hd := (hasDerivAt_id t).sub ((hasDerivAt_pow 2 t).div_const 2)
              have hval : (1 : ℝ) - (2 : ℕ) * t ^ (2 - 1) / 2 = 1 - t := by norm_num
              exact hval ▸ hd
            exact (h1.sub h2).differentiableAt.differentiableWithinAt
          · intro t ht
            have ht0 : 0 < t := by simpa [interior_Ici] using ht
            have h1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + t)) t := by
              have := ((hasDerivAt_id t).const_add 1).log (by dsimp; linarith)
              simpa [one_div] using this
            have h2 : HasDerivAt (fun x : ℝ => x - x ^ 2 / 2) (1 - t) t := by
              have hd := (hasDerivAt_id t).sub ((hasDerivAt_pow 2 t).div_const 2)
              have hval : (1 : ℝ) - (2 : ℕ) * t ^ (2 - 1) / 2 = 1 - t := by norm_num
              exact hval ▸ hd
            have hd : HasDerivAt (fun t : ℝ => Real.log (1 + t) - (t - t ^ 2 / 2))
                (1 / (1 + t) - (1 - t)) t := h1.sub h2
            rw [hd.deriv]
            have : 1 / (1 + t) - (1 - t) = t ^ 2 / (1 + t) := by
              field_simp [(by linarith : 1 + t ≠ 0)]; ring
            rw [this]; positivity
        have h0 := hf_mono (Set.self_mem_Ici) hu hu
        simp only [add_zero, Real.log_one, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero] at h0
        linarith
      have hlog_prod : Real.log (∏ r ∈ Pr_all, (1 + (d : ℝ) / (r : ℝ))) =
          ∑ r ∈ Pr_all, Real.log (1 + (d : ℝ) / (r : ℝ)) :=
        Real.log_prod fun r _ => by positivity
      have hm := hMert U hU_ge3
      have hsq := hsq_sum Pr_all fun r hr => Nat.prime_of_mem_primesBelow (mem_filter.mp hr).1
      have hsum_d : Real.log (Real.log U) - (d : ℝ) * C_mert ≤ ∑ r ∈ Pr_all, (d : ℝ) / (r : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_left hm hd_pos.le
        rw [mul_sum] at hmul
        have hlhs : (d : ℝ) * (1 / (d : ℝ) * Real.log (Real.log U) - C_mert) =
            Real.log (Real.log U) - (d : ℝ) * C_mert := by
          field_simp [hd_pos.ne']
        have hrhs : ∑ r ∈ Pr_all, (d : ℝ) * (1 / (r : ℝ)) = ∑ r ∈ Pr_all, (d : ℝ) / (r : ℝ) :=
          sum_congr rfl fun r _ => by ring
        linarith
      have hlog_lb : Real.log (Real.log U) - (d : ℝ) * C_mert - (d : ℝ) ^ 2 ≤
          Real.log (∏ r ∈ Pr_all, (1 + (d : ℝ) / (r : ℝ))) := by
        rw [hlog_prod]
        calc Real.log (Real.log U) - (d : ℝ) * C_mert - (d : ℝ) ^ 2
            ≤ (∑ r ∈ Pr_all, (d : ℝ) / (r : ℝ)) - ∑ r ∈ Pr_all, (((d : ℝ) / (r : ℝ)) ^ 2) / 2 := by
              linarith
          _ = ∑ r ∈ Pr_all, ((d : ℝ) / (r : ℝ) - (((d : ℝ) / (r : ℝ)) ^ 2) / 2) :=
              (sum_sub_distrib ..).symm
          _ ≤ ∑ r ∈ Pr_all, Real.log (1 + (d : ℝ) / (r : ℝ)) := sum_le_sum hlog_ge
      have hexp := Real.exp_le_exp.mpr hlog_lb
      rw [Real.exp_log (prod_pos fun r _ => by positivity),
        show Real.log (Real.log U) - (d : ℝ) * C_mert - (d : ℝ) ^ 2 =
          (-(d : ℝ) * C_mert - (d : ℝ) ^ 2) + Real.log (Real.log U) by ring,
        Real.exp_add, Real.exp_log (by linarith)] at hexp
      exact hexp
    have hP_lb : (Real.exp (-(d : ℝ) * C_mert - (d : ℝ) ^ 2) * (α * Real.log (Z : ℝ))) / D ≤ P_full := by
      rw [div_le_iff₀ hD_pos, ← hlogU_eq]
      exact hprod_all_lb.trans hP_mul_D
    have hmin_le : min ((1 / 2 : ℝ) * Real.exp (-(d : ℝ) * C_mert - (d : ℝ) ^ 2) * α)
        (1 / Real.log (Z₀ : ℝ)) ≤ (1 / 2 : ℝ) * Real.exp (-(d : ℝ) * C_mert - (d : ℝ) ^ 2) * α :=
      min_le_left _ _
    calc (min ((1 / 2 : ℝ) * Real.exp (-(d : ℝ) * C_mert - (d : ℝ) ^ 2) * α)
          (1 / Real.log (Z₀ : ℝ)) * Real.log (Z : ℝ)) / D
        ≤ (((1 / 2 : ℝ) * Real.exp (-(d : ℝ) * C_mert - (d : ℝ) ^ 2) * α) * Real.log (Z : ℝ)) / D := by
          gcongr
      _ = (1 / 2 : ℝ) * ((Real.exp (-(d : ℝ) * C_mert - (d : ℝ) ^ 2) * (α * Real.log (Z : ℝ))) / D) := by
          ring
      _ ≤ (1 / 2 : ℝ) * P_full := mul_le_mul_of_nonneg_left hP_lb (by norm_num)
      _ ≤ ∑ m ∈ S_trunc, ∏ r ∈ m.primeFactors, ((d : ℝ) / (r : ℝ)) := hS_ge_halfP

end RankinSieve

end Erdos980Mertens

/-
# Cyclotomic Primary Elements, Stickelberger Factorization, and Eisenstein Reciprocity

For an odd prime `l` and `K = CyclotomicField l ℚ`, `R = 𝓞 K`:
1. Primary elements (`IsPrimary`): existence of `ζ^k * α` primary when `(ζ - 1) ∤ α`,
   and uniqueness up to `±1` for primary elements differing by a torsion unit.
2. `l`-th power residue symbol `powResSymb α 𝔭` and ideal extension `powResIdeal α 𝔞`.
3. Gauss sums `g_t` in `AdjoinRoot (Polynomial.cyclotomic p R)` for a degree-1 prime ideal `𝔭`:
   `Φ_𝔭 := g_1^l ∈ R`, `‖φ Φ_𝔭‖^2 = p^l`, `Φ_𝔭 ≡ -1 (mod l R)`, Stickelberger factorization,
   and Frobenius evaluation `powResIdeal Φ_𝔭 (span {q}) = powResSymb q 𝔭`.
4. Eisenstein Reciprocity (`eisenstein_reciprocity_deg1`) for primary `α ∈ R` whose ideal
   factors into degree-1 prime ideals coprime to `l * q`.
-/

namespace Erdos980Eisenstein

open Ideal NumberField RingOfIntegers Polynomial Finset
open scoped BigOperators Classical Pointwise

abbrev CycK (l : ℕ) := CyclotomicField l ℚ
abbrev CycR (l : ℕ) := 𝓞 (CycK l)

instance instIsCyclotomicCycK (l : ℕ) [hl : Fact l.Prime] :
    IsCyclotomicExtension {l} ℚ (CycK l) := by
  have : NeZero l := ⟨hl.out.ne_zero⟩
  have : NeZero (l : ℚ) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  exact CyclotomicField.isCyclotomicExtension l ℚ

instance instNumberFieldCycK (l : ℕ) [Fact l.Prime] : NumberField (CycK l) :=
  IsCyclotomicExtension.numberField {l} ℚ (CycK l)

noncomputable def zetaK (l : ℕ) [Fact l.Prime] : CycK l :=
  IsCyclotomicExtension.zeta l ℚ (CycK l)

lemma zetaK_spec (l : ℕ) [Fact l.Prime] : IsPrimitiveRoot (zetaK l) l :=
  IsCyclotomicExtension.zeta_spec l ℚ (CycK l)

noncomputable def zetaR (l : ℕ) [Fact l.Prime] : CycR l :=
  (zetaK_spec l).toInteger

lemma zetaR_spec (l : ℕ) [Fact l.Prime] : IsPrimitiveRoot (zetaR l) l :=
  (zetaK_spec l).toInteger_isPrimitiveRoot

noncomputable def lamR (l : ℕ) [Fact l.Prime] : CycR l :=
  zetaR l - 1

section Helpers

lemma absNorm_eq_card_quotient {l : ℕ} [Fact l.Prime] (I : Ideal (CycR l)) :
    Ideal.absNorm I = Nat.card (CycR l ⧸ I) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

lemma absNorm_span_lamR {l : ℕ} [hl : Fact l.Prime] :
    Ideal.absNorm (span {lamR l}) = l := by
  have hpow : l ^ (0 + 1) = l := pow_one l
  have : IsCyclotomicExtension {l ^ (0 + 1)} ℚ (CycK l) := hpow.symm ▸ instIsCyclotomicCycK l
  have hζ : IsPrimitiveRoot (zetaK l) (l ^ (0 + 1)) := hpow.symm ▸ zetaK_spec l
  have h := IsCyclotomicExtension.Rat.absNorm_span_zeta_sub_one l 0 hζ
  have heq : hζ.toInteger = zetaR l := by
    apply RingOfIntegers.ext
    exact hζ.coe_toInteger.trans (zetaK_spec l).coe_toInteger.symm
  simpa [lamR, heq] using h

lemma zmod_val_neg_of_ne_zero {n : ℕ} [NeZero n] {x : ZMod n} (hx : x ≠ 0) :
    (-x).val = n - x.val := by
  have : NeZero x := ⟨hx⟩
  exact ZMod.val_neg_of_ne_zero x

lemma primRoot_pow_eq_pow_iff_modEq {M : Type*} [CommMonoid M] {ζ : M} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0) {i j : ℕ} :
    ζ ^ i = ζ ^ j ↔ i ≡ j [MOD n] := by
  rw [(hζ.isOfFinOrder hn).pow_inj_mod, ← hζ.eq_orderOf]; rfl

lemma multiset_prod_pow {α : Type*} [CommMonoid α] (m : Multiset α) (k : ℕ) :
    m.prod ^ k = (m.map (· ^ k)).prod := by
  refine Multiset.induction_on m (by simp) fun a s ih => ?_
  rw [Multiset.prod_cons, mul_pow, ih, Multiset.map_cons, Multiset.prod_cons]

lemma add_pow_eq_of_natCast_eq_zero {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime)
    (hp0 : (p : A) = 0) (x y : A) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow]
  have hrange : range (p + 1) = insert 0 (insert p (Ioo 0 p)) := by
    ext k; simp only [mem_range, mem_insert, mem_Ioo]; omega
  rw [hrange, sum_insert (by simp [hp.ne_zero.symm]), sum_insert (by simp)]
  have hmid : ∑ k ∈ Ioo 0 p, x ^ k * y ^ (p - k) * (Nat.choose p k : A) = 0 := by
    refine sum_eq_zero fun k hk => ?_
    obtain ⟨hk0, hkp⟩ := mem_Ioo.mp hk
    obtain ⟨c, hc⟩ := hp.dvd_choose_self hk0.ne' hkp
    rw [hc, Nat.cast_mul, hp0, zero_mul, mul_zero]
  rw [hmid, add_zero]
  simp; ring

lemma sum_pow_eq_of_natCast_eq_zero {A : Type*} [CommRing A] {p : ℕ} (hp : p.Prime)
    (hp0 : (p : A) = 0) {ι : Type*} (s : Finset ι) (f : ι → A) :
    (∑ i ∈ s, f i) ^ p = ∑ i ∈ s, f i ^ p := by
  induction s using Finset.induction_on with
  | empty => simp [zero_pow hp.ne_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha, add_pow_eq_of_natCast_eq_zero hp hp0, ih]

lemma galRestrict_eq_smul {l : ℕ} [Fact l.Prime] (σ : Gal(CycK l / ℚ)) (x : CycR l) :
    galRestrict ℤ ℚ (CycK l) (CycR l) σ x = σ • x := by
  apply RingOfIntegers.ext
  exact algebraMap_galRestrict_apply (A := ℤ) (K := ℚ) (L := CycK l) (B := CycR l) σ x

lemma galois_smul_ideal_eq_map {l : ℕ} [Fact l.Prime] (σ : Gal(CycK l / ℚ)) (I : Ideal (CycR l)) :
    σ • I = Ideal.map ((galRestrict ℤ ℚ (CycK l) (CycR l) σ).toRingEquiv : CycR l →+* CycR l) I := by
  let e := (galRestrict ℤ ℚ (CycK l) (CycR l) σ).toRingEquiv
  have he : ∀ x : CycR l, (e : CycR l →+* CycR l) x = σ • x := fun x => galRestrict_eq_smul σ x
  ext x
  change x ∈ σ • I ↔ x ∈ Ideal.map (e : CycR l →+* CycR l) I
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, Ideal.mem_map_iff_of_surjective (e : CycR l →+* CycR l) e.surjective]
  constructor
  · intro hx
    exact ⟨σ⁻¹ • x, hx, by rw [he]; exact smul_inv_smul σ x⟩
  · rintro ⟨y, hy, rfl⟩
    rw [he, inv_smul_smul]; exact hy

lemma galois_smul_absNorm {l : ℕ} [Fact l.Prime] (σ : Gal(CycK l / ℚ)) (I : Ideal (CycR l)) :
    Ideal.absNorm (σ • I) = Ideal.absNorm I := by
  let e := (galRestrict ℤ ℚ (CycK l) (CycR l) σ).toRingEquiv
  have hmap := galois_smul_ideal_eq_map σ I
  rw [absNorm_eq_card_quotient, absNorm_eq_card_quotient]
  exact Nat.card_congr (Ideal.quotientEquiv I (σ • I) e hmap).toEquiv.symm

lemma galois_smul_mul_ideal {l : ℕ} [Fact l.Prime] (σ : Gal(CycK l / ℚ)) (I J : Ideal (CycR l)) :
    σ • (I * J) = (σ • I) * (σ • J) := by
  rw [galois_smul_ideal_eq_map, galois_smul_ideal_eq_map, galois_smul_ideal_eq_map, Ideal.map_mul]

lemma galois_smul_pow_ideal {l : ℕ} [Fact l.Prime] (σ : Gal(CycK l / ℚ)) (I : Ideal (CycR l)) (n : ℕ) :
    σ • (I ^ n) = (σ • I) ^ n := by
  rw [galois_smul_ideal_eq_map, galois_smul_ideal_eq_map, Ideal.map_pow]

lemma galois_smul_span_singleton {l : ℕ} [Fact l.Prime] (σ : Gal(CycK l / ℚ)) (x : CycR l) :
    σ • span {x} = span {σ • x} := by
  rw [galois_smul_ideal_eq_map, Ideal.map_span, Set.image_singleton]
  congr 1; exact Set.singleton_eq_singleton_iff.mpr (galRestrict_eq_smul σ x)

lemma star_embedding_eq_smul_neg {l : ℕ} [hl : Fact l.Prime] (φ : CycK l →+* ℂ) (x : CycR l) :
    star (φ (x : CycK l)) =
      φ ((((IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm (-1)) • x : CycR l) : CycK l) := by
  let σneg : Gal(CycK l / ℚ) := (IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm (-1)
  have hσneg_val : (IsCyclotomicExtension.Rat.galEquivZMod l (CycK l) σneg).val.val = l - 1 := by
    simp only [σneg, MulEquiv.apply_symm_apply, Units.val_neg, Units.val_one]
    rw [zmod_val_neg_of_ne_zero (one_ne_zero : (1 : ZMod l) ≠ 0), ZMod.val_one]
  let pb := (zetaK_spec l).integralPowerBasis
  have hgen : pb.gen = zetaR l := (zetaK_spec l).integralPowerBasis_gen
  let e := galRestrict ℤ ℚ (CycK l) (CycR l) σneg
  have he : ∀ y : CycR l, σneg • y = e y := fun y => (galRestrict_eq_smul σneg y).symm
  have hζ_star : (starRingEnd ℂ) (φ ((zetaR l : CycR l) : CycK l)) =
      φ (((σneg • zetaR l : CycR l) : CycK l)) := by
    have h1 : φ ((zetaR l : CycR l) : CycK l) ^ l = 1 := by
      rw [← map_pow, NumberField.RingOfIntegers.coe_eq_algebraMap, ← map_pow,
        (zetaR_spec l).pow_eq_one, map_one, map_one]
    have hnorm1 : ‖φ ((zetaR l : CycR l) : CycK l)‖ = 1 := by
      have h := congrArg norm h1; rw [norm_pow, norm_one] at h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).mp h
    have hmul1 : φ ((zetaR l : CycR l) : CycK l) * (starRingEnd ℂ) (φ ((zetaR l : CycR l) : CycK l)) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm1, one_pow, Complex.ofReal_one]
    have hσζ : σneg • zetaR l = zetaR l ^ (l - 1) := by
      rw [IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq l (CycK l) σneg
        (zetaR_spec l).pow_eq_one, hσneg_val]
    have hmul2 : φ ((zetaR l : CycR l) : CycK l) * φ (((σneg • zetaR l : CycR l) : CycK l)) = 1 := by
      have hpow_emb : φ (((σneg • zetaR l : CycR l) : CycK l)) = φ ((zetaR l : CycR l) : CycK l) ^ (l - 1) := by
        rw [hσζ, NumberField.RingOfIntegers.coe_eq_algebraMap, map_pow, map_pow,
          ← NumberField.RingOfIntegers.coe_eq_algebraMap]
      rw [hpow_emb, ← pow_succ', show l - 1 + 1 = l by have := hl.out.one_lt; omega, h1]
    have hne : φ ((zetaR l : CycR l) : CycK l) ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hmul1; exact zero_ne_one hmul1
    exact mul_left_cancel₀ hne (hmul1.trans hmul2.symm)
  conv_lhs => rw [← pb.basis.sum_repr x]
  conv_rhs => rw [← pb.basis.sum_repr x]
  rw [he, map_sum, NumberField.RingOfIntegers.coe_eq_algebraMap,
    NumberField.RingOfIntegers.coe_eq_algebraMap, map_sum, map_sum, map_sum, map_sum, star_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [pb.basis_eq_pow, hgen, zsmul_eq_mul, map_mul, map_intCast, map_pow,
    map_mul, map_intCast, map_pow, map_mul, map_intCast, map_pow, map_mul, map_intCast, map_pow,
    map_mul, map_intCast, map_pow, star_mul', star_pow, Complex.star_def, map_intCast,
    ← he, ← NumberField.RingOfIntegers.coe_eq_algebraMap,
    ← NumberField.RingOfIntegers.coe_eq_algebraMap, hζ_star]

end Helpers

section PrimaryAndTorsion

variable {l : ℕ} [hl : Fact l.Prime]

/-- An element `α ∈ ℤ[ζ_l]` is primary if `(ζ - 1) ∤ α` and `α ≡ c (mod (ζ - 1)^2)` for some `c ∈ ℤ`. -/
def IsPrimary (α : CycR l) : Prop :=
  ¬ (lamR l ∣ α) ∧ ∃ c : ℤ, lamR l ^ 2 ∣ (α - (c : CycR l))

lemma lamR_pow_two_dvd_l (hl2 : l ≠ 2) : lamR l ^ 2 ∣ (l : CycR l) := by
  have hassoc := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime l (zetaK_spec l)
  have hdvd : lamR l ^ (l - 1) ∣ (l : CycR l) := hassoc.dvd
  have h2le : 2 ≤ l - 1 := by have := hl.out.two_le; omega
  exact (pow_dvd_pow (lamR l) h2le).trans hdvd

lemma lamR_dvd_intCast_iff (c : ℤ) : lamR l ∣ (c : CycR l) ↔ (l : ℤ) ∣ c :=
  IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff' l (zetaK_spec l)

lemma lamR_pow_two_dvd_intCast_of_dvd (hl2 : l ≠ 2) {c : ℤ} (hc : (l : ℤ) ∣ c) :
    lamR l ^ 2 ∣ (c : CycR l) := by
  obtain ⟨k, rfl⟩ := hc
  push_cast
  exact dvd_mul_of_dvd_left (lamR_pow_two_dvd_l hl2) (k : CycR l)

lemma zetaR_pow_sub_one_sub_mul_lamR (k : ℕ) :
    lamR l ^ 2 ∣ (zetaR l ^ k - 1 - (k : CycR l) * lamR l) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : zetaR l ^ (k + 1) - 1 - ((k + 1 : ℕ) : CycR l) * lamR l =
        (zetaR l ^ k - 1 - (k : CycR l) * lamR l) * zetaR l +
        (k : CycR l) * lamR l ^ 2 := by
      have hζ : zetaR l = 1 + lamR l := by simp [lamR]
      push_cast; rw [pow_succ, hζ]; ring
    rw [hstep]
    exact dvd_add (dvd_mul_of_dvd_left ih _) (dvd_mul_left _ _)

lemma exists_decomp_mod_lamR_sq (hl2 : l ≠ 2) (α : CycR l) :
    ∃ c₀ c₁ : ℤ, lamR l ^ 2 ∣ (α - (c₀ : CycR l) - (c₁ : CycR l) * lamR l) := by
  let pb := (zetaK_spec l).subOneIntegralPowerBasis
  have hgen : pb.gen = lamR l := by
    apply RingOfIntegers.ext
    simp only [pb, lamR, zetaR, IsPrimitiveRoot.subOneIntegralPowerBasis_gen, map_sub, map_one]
    exact congrArg (· - 1) (zetaK_spec l).coe_toInteger.symm
  have hdim : pb.dim = l - 1 := by
    have h2 := (zetaK_spec l).integralPowerBasis_dim
    have h3 : Module.finrank ℤ (CycR l) = l - 1 := by
      rw [(zetaK_spec l).integralPowerBasis.finrank, h2, Nat.totient_prime hl.out]
    rw [← pb.finrank, h3]
  have h2le : 2 ≤ pb.dim := by have := hl.out.two_le; omega
  let r := pb.basis.repr α
  let i0 : Fin pb.dim := ⟨0, by omega⟩
  let i1 : Fin pb.dim := ⟨1, by omega⟩
  refine ⟨r i0, r i1, ?_⟩
  have hexp : α = ∑ i : Fin pb.dim, (r i : CycR l) * lamR l ^ (i : ℕ) := by
    conv_lhs => rw [← pb.basis.sum_repr α]
    refine sum_congr rfl fun i _ => by rw [pb.basis_eq_pow, hgen, zsmul_eq_mul]
  have hsplit : α - (r i0 : CycR l) - (r i1 : CycR l) * lamR l =
      ∑ i ∈ univ.filter (fun i : Fin pb.dim => 2 ≤ (i : ℕ)),
        (r i : CycR l) * lamR l ^ (i : ℕ) := by
    rw [hexp]
    have hcompl : univ = insert i0 (insert i1 (univ.filter (fun i : Fin pb.dim => 2 ≤ (i : ℕ)))) := by
      ext i; simp only [mem_univ, mem_insert, mem_filter, true_and, true_iff]
      rcases i with ⟨n, hn⟩; dsimp only
      by_cases h0 : n = 0
      · left; exact Fin.ext h0
      · by_cases h1 : n = 1
        · right; left; exact Fin.ext h1
        · right; right; omega
    conv_lhs => rw [hcompl]
    rw [sum_insert (by simp [i0, i1]), sum_insert (by simp [i1])]
    simp only [i0, i1, pow_zero, mul_one, pow_one]; ring
  rw [hsplit]
  refine Finset.dvd_sum fun i hi =>
    dvd_mul_of_dvd_right (pow_dvd_pow (lamR l) (mem_filter.mp hi).2) _

/-- Any `α ∈ ℤ[ζ_l]` coprime to `ζ - 1` has a primary associate `ζ^k * α` (`k < l`). -/
theorem exists_pow_zeta_mul_isPrimary (hl2 : l ≠ 2) {α : CycR l} (hα : ¬ lamR l ∣ α) :
    ∃ k : ℕ, k < l ∧ IsPrimary (zetaR l ^ k * α) := by
  obtain ⟨c₀, c₁, hmod⟩ := exists_decomp_mod_lamR_sq hl2 α
  have hc0_ndvd : ¬ (l : ℤ) ∣ c₀ := by
    intro hd; apply hα
    have h1 : lamR l ∣ (α - (c₀ : CycR l) - (c₁ : CycR l) * lamR l) := by
      have := (pow_dvd_pow (lamR l) (by decide : 1 ≤ 2)).trans hmod; simpa using this
    have h2 : lamR l ∣ (c₀ : CycR l) := (lamR_dvd_intCast_iff c₀).mpr hd
    have h3 : lamR l ∣ (c₁ : CycR l) * lamR l := dvd_mul_left _ _
    have h4 : α = (α - (c₀ : CycR l) - (c₁ : CycR l) * lamR l) + (c₀ : CycR l) + (c₁ : CycR l) * lamR l := by ring
    rw [h4]; exact dvd_add (dvd_add h1 h2) h3
  have hc0_ne : (c₀ : ZMod l) ≠ 0 := fun h0 => hc0_ndvd ((ZMod.intCast_zmod_eq_zero_iff_dvd c₀ l).mp h0)
  let kz : ZMod l := -(c₁ : ZMod l) * (c₀ : ZMod l)⁻¹
  refine ⟨kz.val, ZMod.val_lt kz, ?_, ⟨c₀, ?_⟩⟩
  · intro hd
    have hunit : IsUnit (zetaR l ^ kz.val) := ((zetaR_spec l).isUnit hl.out.ne_zero).pow _
    exact hα (hunit.dvd_mul_left.mp hd)
  · have hkz_eq : ((c₁ + (kz.val : ℤ) * c₀ : ℤ) : ZMod l) = 0 := by
      push_cast; rw [ZMod.natCast_zmod_val]; simp [kz, mul_assoc, inv_mul_cancel₀ hc0_ne]
    have hlam_dvd_lin : lamR l ∣ ((c₁ + (kz.val : ℤ) * c₀ : ℤ) : CycR l) :=
      (lamR_dvd_intCast_iff _).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp hkz_eq)
    have hlam2_lin : lamR l ^ 2 ∣ ((c₁ : CycR l) + (kz.val : CycR l) * (c₀ : CycR l)) * lamR l := by
      have : ((c₁ + (kz.val : ℤ) * c₀ : ℤ) : CycR l) = (c₁ : CycR l) + (kz.val : CycR l) * (c₀ : CycR l) := by
        push_cast; ring
      rw [← this, sq]; exact mul_dvd_mul_right hlam_dvd_lin (lamR l)
    have hid : zetaR l ^ kz.val * α - (c₀ : CycR l) =
        zetaR l ^ kz.val * (α - (c₀ : CycR l) - (c₁ : CycR l) * lamR l) +
        (zetaR l ^ kz.val - 1 - (kz.val : CycR l) * lamR l) * ((c₀ : CycR l) + (c₁ : CycR l) * lamR l) +
        ((c₁ : CycR l) + (kz.val : CycR l) * (c₀ : CycR l)) * lamR l +
        (kz.val : CycR l) * (c₁ : CycR l) * lamR l ^ 2 := by ring
    rw [hid]
    exact dvd_add (dvd_add (dvd_add (dvd_mul_of_dvd_right hmod _)
      (dvd_mul_of_dvd_left (zetaR_pow_sub_one_sub_mul_lamR kz.val) _)) hlam2_lin) (dvd_mul_left _ _)

lemma IsPrimary.mul {α β : CycR l} (hα : IsPrimary α) (hβ : IsPrimary β) :
    IsPrimary (α * β) := by
  refine ⟨?_, ?_⟩
  · intro hd
    have hpr : Prime (lamR l) := (zetaK_spec l).zeta_sub_one_prime'
    exact (hpr.dvd_or_dvd hd).elim hα.1 hβ.1
  · obtain ⟨a, ha⟩ := hα.2; obtain ⟨b, hb⟩ := hβ.2
    refine ⟨a * b, ?_⟩
    have hid : α * β - ((a * b : ℤ) : CycR l) =
        (α - (a : CycR l)) * β + (a : CycR l) * (β - (b : CycR l)) := by push_cast; ring
    rw [hid]; exact dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hb _)

lemma IsPrimary.galois_smul {α : CycR l} (hα : IsPrimary α) (σ : Gal(CycK l / ℚ)) :
    IsPrimary (σ • α) := by
  let e : CycR l ≃ₐ[ℤ] CycR l := galRestrict ℤ ℚ (CycK l) (CycR l) σ
  have he : ∀ x : CycR l, σ • x = e x := fun x => (galRestrict_eq_smul σ x).symm
  have hlam_assoc : Associated (lamR l) (e (lamR l)) := by
    have := (zetaR_spec l).associated_sub_one_map_sub_one e
    simpa [lamR, map_sub, map_one] using this
  have hlam2_assoc : Associated (lamR l ^ 2) (e (lamR l) ^ 2) := by
    obtain ⟨u, hu⟩ := hlam_assoc; exact ⟨u ^ 2, by rw [← hu, mul_pow, Units.val_pow_eq_pow_val]⟩
  refine ⟨?_, ?_⟩
  · intro hd; apply hα.1
    rw [he] at hd
    obtain ⟨y, hy⟩ := hlam_assoc.dvd_iff_dvd_left.mp hd
    refine ⟨e.symm y, e.injective ?_⟩
    rw [map_mul, e.apply_symm_apply, hy]
  · obtain ⟨c, hc⟩ := hα.2
    refine ⟨c, ?_⟩
    have hc' : e (lamR l) ^ 2 ∣ e (α - (c : CycR l)) := by
      obtain ⟨y, hy⟩ := hc; exact ⟨e y, by rw [hy, map_mul, map_pow]⟩
    rw [map_sub, map_intCast] at hc'
    rw [he]
    exact hlam2_assoc.dvd_iff_dvd_left.mpr hc'

lemma IsPrimary.prod {ι : Type*} (s : Finset ι) (f : ι → CycR l)
    (hf : ∀ i ∈ s, IsPrimary (f i)) : IsPrimary (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨fun hd => ((zetaK_spec l).zeta_sub_one_prime').not_isUnit (isUnit_of_dvd_one hd), ⟨1, by simp⟩⟩
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact (hf a (mem_insert_self a s)).mul (ih fun i hi => hf i (mem_insert_of_mem hi))

lemma torsion_unit_eq_pm_pow_zeta (hl2 : l ≠ 2) (u : (CycR l)ˣ)
    (hu : ∀ φ : CycK l →+* ℂ, ‖φ ((u : CycR l) : CycK l)‖ = 1) :
    ∃ s : CycR l, (s = 1 ∨ s = -1) ∧ ∃ k : ℕ, k < l ∧ (u : CycR l) = s * zetaR l ^ k := by
  have hmem : u ∈ NumberField.Units.torsion (CycK l) := by
    rw [NumberField.Units.mem_torsion]
    intro w
    rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.apply]
    exact hu w.embedding
  rw [← NumberField.Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at hmem
  have htors : NumberField.Units.torsionOrder (CycK l) = 2 * l := by
    rw [IsCyclotomicExtension.Rat.torsionOrder_eq (n := l) (K := CycK l)]
    have hnot : ¬ Even l := fun he => hl2 ((Nat.Prime.even_iff hl.out).mp he)
    rw [if_neg hnot]
  rw [htors] at hmem
  have hsq : ((u : CycR l) ^ l) ^ 2 = 1 := by
    have : (u : CycR l) ^ (2 * l) = 1 := by simpa using congrArg Units.val hmem
    rw [← pow_mul, mul_comm l 2]; exact this
  have hpm : (u : CycR l) ^ l = 1 ∨ (u : CycR l) ^ l = -1 := sq_eq_one_iff.mp hsq
  let s : CycR l := (u : CycR l) ^ l
  have hsl : s ^ l = s := by
    rcases hpm with hs | hs
    · simp [s, hs]
    · simp only [s, hs]; exact (hl.out.odd_of_ne_two hl2).neg_one_pow
  have hss : s * s = 1 := by rcases hpm with hs | hs <;> simp [s, hs]
  have hpow1 : (s * (u : CycR l)) ^ l = 1 := by rw [mul_pow, hsl]; exact hss
  have hpowK : (((s * (u : CycR l) : CycR l) : CycK l)) ^ l = 1 := by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, ← map_pow, hpow1, map_one]
  obtain ⟨k, hk, hkeq⟩ := (zetaK_spec l).eq_pow_of_pow_eq_one hpowK
  have hR : s * (u : CycR l) = zetaR l ^ k := by
    apply RingOfIntegers.ext
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap,
      map_pow, show algebraMap (CycR l) (CycK l) (zetaR l) = zetaK l from (zetaK_spec l).coe_toInteger]
    exact hkeq.symm
  refine ⟨s, hpm, k, hk, ?_⟩
  calc (u : CycR l) = (s * s) * (u : CycR l) := by rw [hss, one_mul]
    _ = s * (s * (u : CycR l)) := by ring
    _ = s * zetaR l ^ k := by rw [hR]

theorem isPrimary_unit_eq_pm_one (hl2 : l ≠ 2) {α β : CycR l} {u : (CycR l)ˣ}
    (hα : IsPrimary α) (hβ : IsPrimary β)
    (hu : ∀ φ : CycK l →+* ℂ, ‖φ ((u : CycR l) : CycK l)‖ = 1)
    (heq : β = (u : CycR l) * α) :
    (u : CycR l) = 1 ∨ (u : CycR l) = -1 := by
  obtain ⟨s, hs_pm, k, hk, hu_eq⟩ := torsion_unit_eq_pm_pow_zeta hl2 u hu
  obtain ⟨a, ha⟩ := hα.2; obtain ⟨b, hb⟩ := hβ.2
  have ha_ndvd : ¬ (l : ℤ) ∣ a := by
    intro hd; apply hα.1
    have h1 : lamR l ∣ (α - (a : CycR l)) := by
      have := (pow_dvd_pow (lamR l) (by decide : 1 ≤ 2)).trans ha; simpa using this
    have h2 : lamR l ∣ (a : CycR l) := (lamR_dvd_intCast_iff a).mpr hd
    have : α = (α - (a : CycR l)) + (a : CycR l) := by ring
    rw [this]; exact dvd_add h1 h2
  obtain ⟨sz, hsz_pm, hsz_eq⟩ : ∃ sz : ℤ, (sz = 1 ∨ sz = -1) ∧ (sz : CycR l) = s := by
    rcases hs_pm with rfl | rfl
    · exact ⟨1, Or.inl rfl, by simp⟩
    · exact ⟨-1, Or.inr rfl, by simp⟩
  have hcong : lamR l ^ 2 ∣ ((b - sz * a : ℤ) : CycR l) - ((sz * a * (k : ℤ) : ℤ) : CycR l) * lamR l := by
    have hid : ((b - sz * a : ℤ) : CycR l) - ((sz * a * (k : ℤ) : ℤ) : CycR l) * lamR l =
        -(β - (b : CycR l)) + (u : CycR l) * (α - (a : CycR l)) +
        s * (a : CycR l) * (zetaR l ^ k - 1 - (k : CycR l) * lamR l) := by
      rw [heq, hu_eq, ← hsz_eq]; push_cast; ring
    rw [hid]
    exact dvd_add (dvd_add (dvd_neg.mpr hb) (dvd_mul_of_dvd_right ha _))
      (dvd_mul_of_dvd_right (zetaR_pow_sub_one_sub_mul_lamR k) _)
  have hdvd_ba : (l : ℤ) ∣ (b - sz * a) := by
    rw [← lamR_dvd_intCast_iff]
    have h1 : lamR l ∣ ((b - sz * a : ℤ) : CycR l) - ((sz * a * (k : ℤ) : ℤ) : CycR l) * lamR l := by
      have := (pow_dvd_pow (lamR l) (by decide : 1 ≤ 2)).trans hcong; simpa using this
    have h2 : lamR l ∣ ((sz * a * (k : ℤ) : ℤ) : CycR l) * lamR l := dvd_mul_left _ _
    have : ((b - sz * a : ℤ) : CycR l) =
        (((b - sz * a : ℤ) : CycR l) - ((sz * a * (k : ℤ) : ℤ) : CycR l) * lamR l) +
        ((sz * a * (k : ℤ) : ℤ) : CycR l) * lamR l := by ring
    rw [this]; exact dvd_add h1 h2
  have hlam2_term : lamR l ^ 2 ∣ ((sz * a * (k : ℤ) : ℤ) : CycR l) * lamR l := by
    have : ((sz * a * (k : ℤ) : ℤ) : CycR l) * lamR l =
        ((b - sz * a : ℤ) : CycR l) -
        (((b - sz * a : ℤ) : CycR l) - ((sz * a * (k : ℤ) : ℤ) : CycR l) * lamR l) := by ring
    rw [this]; exact dvd_sub (lamR_pow_two_dvd_intCast_of_dvd hl2 hdvd_ba) hcong
  have hlam_ne0 : lamR l ≠ 0 := Prime.ne_zero (zetaK_spec l).zeta_sub_one_prime'
  have hlam_dvd : lamR l ∣ ((sz * a * (k : ℤ) : ℤ) : CycR l) := by
    rw [sq] at hlam2_term; exact (mul_dvd_mul_iff_right hlam_ne0).mp hlam2_term
  have hl_dvd_prod : (l : ℤ) ∣ sz * a * (k : ℤ) := (lamR_dvd_intCast_iff _).mp hlam_dvd
  have hk_zero : k = 0 := by
    rcases (Nat.prime_iff_prime_int.mp hl.out).dvd_or_dvd hl_dvd_prod with hsa | hk'
    · exfalso; exact ha_ndvd (by rcases hsz_pm with rfl | rfl <;> simpa using hsa)
    · exact Nat.eq_zero_of_dvd_of_lt (Int.ofNat_dvd.mp hk') hk
  rw [hu_eq, hk_zero, pow_zero, mul_one]; exact hs_pm

end PrimaryAndTorsion

section PowerResidueSymbol

variable {l : ℕ} [hl : Fact l.Prime]

lemma zetaR_isPrimitiveRoot_quot {𝔭 : Ideal (CycR l)} (hlam : lamR l ∉ 𝔭) :
    IsPrimitiveRoot (Ideal.Quotient.mk 𝔭 (zetaR l)) l := by
  refine ⟨by rw [← map_pow, (zetaR_spec l).pow_eq_one, map_one], fun k hk => ?_⟩
  by_contra hndvd
  have hassoc : Associated (zetaR l - 1) (zetaR l ^ k - 1) :=
    (zetaR_spec l).associated_sub_one_pow_sub_one_of_coprime (hl.out.coprime_iff_not_dvd.mpr hndvd).symm
  have hmem : zetaR l ^ k - 1 ∈ 𝔭 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, hk, sub_self]
  obtain ⟨u, hu⟩ := hassoc.symm
  exact hlam (by change zetaR l - 1 ∈ 𝔭; rw [← hu]; exact 𝔭.mul_mem_right _ hmem)

lemma dvd_absNorm_sub_one {𝔭 : Ideal (CycR l)} [h𝔭 : 𝔭.IsPrime]
    (hbot : 𝔭 ≠ ⊥) (hlam : lamR l ∉ 𝔭) : l ∣ (Ideal.absNorm 𝔭 - 1) := by
  have : 𝔭.IsMaximal := h𝔭.isMaximal hbot
  let : Field (CycR l ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have : Finite (CycR l ⧸ 𝔭) := Ring.HasFiniteQuotients.finiteQuotient hbot
  let : Fintype (CycR l ⧸ 𝔭) := Fintype.ofFinite _
  have hprim := zetaR_isPrimitiveRoot_quot hlam
  have hu : IsUnit (Ideal.Quotient.mk 𝔭 (zetaR l)) := hprim.isUnit hl.out.ne_zero
  have hord_u : orderOf hu.unit = l := by
    rw [← orderOf_units, IsUnit.unit_spec]; exact hprim.eq_orderOf.symm
  have hdvd : orderOf hu.unit ∣ Fintype.card (CycR l ⧸ 𝔭)ˣ := orderOf_dvd_card
  rw [hord_u, Fintype.card_units, ← Nat.card_eq_fintype_card, ← absNorm_eq_card_quotient] at hdvd
  exact hdvd

lemma existsUnique_powResSymb {𝔭 : Ideal (CycR l)} [h𝔭 : 𝔭.IsPrime]
    (hbot : 𝔭 ≠ ⊥) (hlam : lamR l ∉ 𝔭) {α : CycR l} (hα : α ∉ 𝔭) :
    ∃! k : Fin l, Ideal.Quotient.mk 𝔭 (zetaR l ^ (k : ℕ)) =
      (Ideal.Quotient.mk 𝔭 α) ^ ((Ideal.absNorm 𝔭 - 1) / l) := by
  have : 𝔭.IsMaximal := h𝔭.isMaximal hbot
  let : Field (CycR l ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have : Finite (CycR l ⧸ 𝔭) := Ring.HasFiniteQuotients.finiteQuotient hbot
  let : Fintype (CycR l ⧸ 𝔭) := Fintype.ofFinite _
  have hprim := zetaR_isPrimitiveRoot_quot hlam
  have hdvd := dvd_absNorm_sub_one hbot hlam
  set x : CycR l ⧸ 𝔭 := Ideal.Quotient.mk 𝔭 α
  have hx0 : x ≠ 0 := fun h0 => hα (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have hpowl : (x ^ ((Ideal.absNorm 𝔭 - 1) / l)) ^ l = 1 := by
    rw [← pow_mul, Nat.div_mul_cancel hdvd]
    have hcard : Fintype.card (CycR l ⧸ 𝔭) = Ideal.absNorm 𝔭 := by
      rw [← Nat.card_eq_fintype_card, absNorm_eq_card_quotient]
    rw [← hcard]; exact FiniteField.pow_card_sub_one_eq_one x hx0
  obtain ⟨k, hkl, hkeq⟩ := hprim.eq_pow_of_pow_eq_one hpowl
  refine ⟨⟨k, hkl⟩, by dsimp only; rw [map_pow, hkeq], fun j hj => ?_⟩
  dsimp only at hj; rw [map_pow] at hj
  have hmod : (j : ℕ) ≡ k [MOD l] := (primRoot_pow_eq_pow_iff_modEq hprim hl.out.ne_zero).mp (by rw [hj, hkeq])
  exact Fin.ext (by rw [Nat.ModEq, Nat.mod_eq_of_lt j.2, Nat.mod_eq_of_lt hkl] at hmod; exact hmod)

noncomputable def powResSymb (α : CycR l) (𝔭 : Ideal (CycR l)) : CycR l :=
  if h : 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ lamR l ∉ 𝔭 ∧ α ∉ 𝔭 then
    let _ := h.1
    zetaR l ^ ((existsUnique_powResSymb h.2.1 h.2.2.1 h.2.2.2).exists.choose : ℕ)
  else 1

lemma powResSymb_spec {𝔭 : Ideal (CycR l)} [h𝔭 : 𝔭.IsPrime]
    (hbot : 𝔭 ≠ ⊥) (hlam : lamR l ∉ 𝔭) {α : CycR l} (hα : α ∉ 𝔭) :
    (∃ k < l, powResSymb α 𝔭 = zetaR l ^ k) ∧
    Ideal.Quotient.mk 𝔭 (powResSymb α 𝔭) =
      (Ideal.Quotient.mk 𝔭 α) ^ ((Ideal.absNorm 𝔭 - 1) / l) := by
  have h : 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ lamR l ∉ 𝔭 ∧ α ∉ 𝔭 := ⟨h𝔭, hbot, hlam, hα⟩
  simp only [powResSymb, dif_pos h]
  let k := (existsUnique_powResSymb hbot hlam hα).exists.choose
  exact ⟨⟨k.1, k.2, rfl⟩, (existsUnique_powResSymb hbot hlam hα).exists.choose_spec⟩

lemma powResSymb_pow_l (α : CycR l) (𝔭 : Ideal (CycR l)) :
    powResSymb α 𝔭 ^ l = 1 := by
  by_cases h : 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ lamR l ∉ 𝔭 ∧ α ∉ 𝔭
  · have := h.1
    obtain ⟨⟨k, _, heq⟩, _⟩ := powResSymb_spec h.2.1 h.2.2.1 h.2.2.2
    rw [heq, ← pow_mul, mul_comm, pow_mul, (zetaR_spec l).pow_eq_one, one_pow]
  · simp [powResSymb, dif_neg h]

lemma powResSymb_eq_pow_iff {𝔭 : Ideal (CycR l)} [h𝔭 : 𝔭.IsPrime]
    (hbot : 𝔭 ≠ ⊥) (hlam : lamR l ∉ 𝔭) {α : CycR l} (hα : α ∉ 𝔭) (k : ℕ) :
    powResSymb α 𝔭 = zetaR l ^ k ↔
      Ideal.Quotient.mk 𝔭 (zetaR l ^ k) =
        (Ideal.Quotient.mk 𝔭 α) ^ ((Ideal.absNorm 𝔭 - 1) / l) := by
  obtain ⟨⟨j, _, hj_eq⟩, hj_mk⟩ := powResSymb_spec hbot hlam hα
  have hprim := zetaR_isPrimitiveRoot_quot hlam
  constructor
  · intro h; rw [← h]; exact hj_mk
  · intro hmk
    rw [hj_eq]
    have h1 : (Ideal.Quotient.mk 𝔭 (zetaR l)) ^ j = (Ideal.Quotient.mk 𝔭 (zetaR l)) ^ k := by
      rw [← map_pow, ← hj_eq, hj_mk, ← hmk, map_pow]
    exact (primRoot_pow_eq_pow_iff_modEq (zetaR_spec l) hl.out.ne_zero).mpr
      ((primRoot_pow_eq_pow_iff_modEq hprim hl.out.ne_zero).mp h1)

lemma powResSymb_mul {𝔭 : Ideal (CycR l)} [h𝔭 : 𝔭.IsPrime]
    (hbot : 𝔭 ≠ ⊥) (hlam : lamR l ∉ 𝔭) {α β : CycR l} (hα : α ∉ 𝔭) (hβ : β ∉ 𝔭) :
    powResSymb (α * β) 𝔭 = powResSymb α 𝔭 * powResSymb β 𝔭 := by
  have hαβ : α * β ∉ 𝔭 := fun h => (h𝔭.mem_or_mem h).elim hα hβ
  obtain ⟨⟨i, _, hi⟩, hi_mk⟩ := powResSymb_spec hbot hlam hα
  obtain ⟨⟨j, _, hj⟩, hj_mk⟩ := powResSymb_spec hbot hlam hβ
  rw [hi, hj, ← pow_add, powResSymb_eq_pow_iff hbot hlam hαβ,
    pow_add, map_mul, ← hi, ← hj, hi_mk, hj_mk, ← mul_pow, ← map_mul]

lemma powResSymb_one {𝔭 : Ideal (CycR l)} [h𝔭 : 𝔭.IsPrime]
    (hbot : 𝔭 ≠ ⊥) (hlam : lamR l ∉ 𝔭) : powResSymb (1 : CycR l) 𝔭 = 1 := by
  have h1 : (1 : CycR l) ∉ 𝔭 := fun h => h𝔭.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 h isUnit_one)
  conv_rhs => rw [show (1 : CycR l) = zetaR l ^ 0 by simp]
  rw [powResSymb_eq_pow_iff hbot hlam h1]; simp

lemma powResSymb_neg_one (hl2 : l ≠ 2) {𝔭 : Ideal (CycR l)} [h𝔭 : 𝔭.IsPrime]
    (hbot : 𝔭 ≠ ⊥) (hlam : lamR l ∉ 𝔭) : powResSymb (-1 : CycR l) 𝔭 = 1 := by
  have h1 : (-1 : CycR l) ∉ 𝔭 := fun h => h𝔭.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 h isUnit_one.neg)
  conv_rhs => rw [show (1 : CycR l) = zetaR l ^ 0 by simp]
  rw [powResSymb_eq_pow_iff hbot hlam h1]
  simp only [pow_zero, map_one, map_neg]
  have : 𝔭.IsMaximal := h𝔭.isMaximal hbot
  let : Field (CycR l ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  by_cases h2 : (2 : CycR l ⧸ 𝔭) = 0
  · have hneg1 : (-1 : CycR l ⧸ 𝔭) = 1 :=
      neg_eq_iff_add_eq_zero.mpr (by rw [show (1 : CycR l ⧸ 𝔭) + 1 = 2 from one_add_one_eq_two]; exact h2)
    rw [hneg1, one_pow]
  · have : Finite (CycR l ⧸ 𝔭) := Ring.HasFiniteQuotients.finiteQuotient hbot
    let : Fintype (CycR l ⧸ 𝔭) := Fintype.ofFinite _
    have : CharP (CycR l ⧸ 𝔭) (ringChar (CycR l ⧸ 𝔭)) := ringChar.charP _
    have hchar_ne2 : ringChar (CycR l ⧸ 𝔭) ≠ 2 := fun hc =>
      h2 (by rw [show (2 : CycR l ⧸ 𝔭) = ((2 : ℕ) : CycR l ⧸ 𝔭) by norm_num, ← hc, CharP.cast_eq_zero])
    have hchar_pr : (ringChar (CycR l ⧸ 𝔭)).Prime :=
      (CharP.char_is_prime_or_zero (CycR l ⧸ 𝔭) _).resolve_right
        (CharP.char_ne_zero_of_finite (CycR l ⧸ 𝔭) _)
    obtain ⟨f, _, hcard⟩ := FiniteField.card (CycR l ⧸ 𝔭) (ringChar (CycR l ⧸ 𝔭))
    have habs_odd : Odd (Ideal.absNorm 𝔭) := by
      rw [absNorm_eq_card_quotient, Nat.card_eq_fintype_card, hcard]
      exact (hchar_pr.odd_of_ne_two hchar_ne2).pow
    have h2dvd : 2 ∣ (Ideal.absNorm 𝔭 - 1) := by obtain ⟨m, hm⟩ := habs_odd; omega
    have hcop : Nat.Coprime 2 l := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun h =>
      hl2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hl.out).mp h).symm
    have h2l : 2 * l ∣ (Ideal.absNorm 𝔭 - 1) := hcop.mul_dvd_of_dvd_of_dvd h2dvd (dvd_absNorm_sub_one hbot hlam)
    have heven : Even ((Ideal.absNorm 𝔭 - 1) / l) := by
      obtain ⟨m, hm⟩ := h2l
      refine ⟨m, ?_⟩
      rw [hm, mul_comm 2 l, mul_assoc, Nat.mul_div_cancel_left _ hl.out.pos]; ring
    exact heven.neg_one_pow.symm

lemma powResSymb_congr {𝔭 : Ideal (CycR l)} [h𝔭 : 𝔭.IsPrime]
    (hbot : 𝔭 ≠ ⊥) (hlam : lamR l ∉ 𝔭) {α β : CycR l} (hα : α ∉ 𝔭) (hsub : α - β ∈ 𝔭) :
    powResSymb α 𝔭 = powResSymb β 𝔭 := by
  have hβ : β ∉ 𝔭 := by
    intro h; apply hα
    have : α = (α - β) + β := by ring
    rw [this]; exact 𝔭.add_mem hsub h
  obtain ⟨⟨k, _, hk⟩, hkmk⟩ := powResSymb_spec hbot hlam hα
  rw [hk]; symm
  rw [powResSymb_eq_pow_iff hbot hlam hβ, ← hk, hkmk, Ideal.Quotient.eq.mpr hsub]

lemma powResSymb_eq_one_iff_isPow {𝔭 : Ideal (CycR l)} [h𝔭 : 𝔭.IsPrime]
    (hbot : 𝔭 ≠ ⊥) (hlam : lamR l ∉ 𝔭) {α : CycR l} (hα : α ∉ 𝔭) :
    powResSymb α 𝔭 = 1 ↔ ∃ y : CycR l ⧸ 𝔭, y ^ l = Ideal.Quotient.mk 𝔭 α := by
  have : 𝔭.IsMaximal := h𝔭.isMaximal hbot
  let : Field (CycR l ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have : Finite (CycR l ⧸ 𝔭) := Ring.HasFiniteQuotients.finiteQuotient hbot
  let : Fintype (CycR l ⧸ 𝔭) := Fintype.ofFinite _
  have hdvd := dvd_absNorm_sub_one hbot hlam
  have hcard : Fintype.card (CycR l ⧸ 𝔭)ˣ = Ideal.absNorm 𝔭 - 1 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, absNorm_eq_card_quotient]
  set x : CycR l ⧸ 𝔭 := Ideal.Quotient.mk 𝔭 α
  have hx0 : x ≠ 0 := fun h0 => hα (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  rw [show (1 : CycR l) = zetaR l ^ 0 by simp, powResSymb_eq_pow_iff hbot hlam hα, pow_zero, map_one]
  constructor
  · intro h1
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (CycR l ⧸ 𝔭)ˣ)
    let ux : (CycR l ⧸ 𝔭)ˣ := Units.mk0 x hx0
    obtain ⟨m, hm⟩ : ∃ m : ℕ, g ^ m = ux := by
      obtain ⟨z, hz⟩ := hg ux; dsimp only at hz
      have hpos : 0 < orderOf g := orderOf_pos g
      refine ⟨(z % (orderOf g : ℤ)).toNat, ?_⟩
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg z (by exact_mod_cast hpos.ne')),
        zpow_mod_orderOf, hz]
    have hg_ord : orderOf g = Ideal.absNorm 𝔭 - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard]
    have hpow : g ^ (m * ((Ideal.absNorm 𝔭 - 1) / l)) = 1 := by
      rw [pow_mul, hm]; ext; simpa [ux] using h1.symm
    have hord_dvd : (Ideal.absNorm 𝔭 - 1) ∣ m * ((Ideal.absNorm 𝔭 - 1) / l) := by
      have := orderOf_dvd_of_pow_eq_one hpow
      rwa [hg_ord] at this
    have hl_dvd_m : l ∣ m := by
      have hm_pos : 0 < (Ideal.absNorm 𝔭 - 1) / l := by
        have h2 : 1 < Ideal.absNorm 𝔭 := by
          rw [absNorm_eq_card_quotient, Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
        have hmul := Nat.div_mul_cancel hdvd
        exact Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at hmul; omega
      obtain ⟨c, hc⟩ := hord_dvd
      refine ⟨c, Nat.eq_of_mul_eq_mul_left hm_pos ?_⟩
      have hdiv := Nat.div_mul_cancel hdvd
      linarith [show m * ((Ideal.absNorm 𝔭 - 1) / l) = (Ideal.absNorm 𝔭 - 1) * c from hc,
                show (Ideal.absNorm 𝔭 - 1) * c = ((Ideal.absNorm 𝔭 - 1) / l) * (l * c) by
                  rw [← mul_assoc, hdiv]]
    obtain ⟨r, rfl⟩ := hl_dvd_m
    refine ⟨((g ^ r : (CycR l ⧸ 𝔭)ˣ) : CycR l ⧸ 𝔭), ?_⟩
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, hm]; simp [ux, x]
  · rintro ⟨y, hy⟩
    change 1 = x ^ ((Ideal.absNorm 𝔭 - 1) / l)
    rw [← hy, ← pow_mul, mul_comm l, Nat.div_mul_cancel hdvd]
    have hy0 : y ≠ 0 := fun h0 => by rw [h0, zero_pow hl.out.ne_zero] at hy; exact hx0 hy.symm
    have hcard' : Fintype.card (CycR l ⧸ 𝔭) = Ideal.absNorm 𝔭 := by
      rw [← Nat.card_eq_fintype_card, absNorm_eq_card_quotient]
    rw [← hcard']; exact (FiniteField.pow_card_sub_one_eq_one y hy0).symm

lemma powResSymb_galois {𝔭 : Ideal (CycR l)} [h𝔭 : 𝔭.IsPrime]
    (hbot : 𝔭 ≠ ⊥) (hlam : lamR l ∉ 𝔭) {α : CycR l} (hα : α ∉ 𝔭) (σ : Gal(CycK l / ℚ)) :
    powResSymb (σ • α) (σ • 𝔭) =
      (powResSymb α 𝔭) ^ (IsCyclotomicExtension.Rat.galEquivZMod l (CycK l) σ).val.val := by
  let e : CycR l ≃ₐ[ℤ] CycR l := galRestrict ℤ ℚ (CycK l) (CycR l) σ
  have hmap_eq := galois_smul_ideal_eq_map σ 𝔭
  have h𝔭'_prime : (σ • 𝔭).IsPrime := by rw [hmap_eq]; exact Ideal.map_isPrime_of_equiv e.toRingEquiv
  have : (σ • 𝔭).IsPrime := h𝔭'_prime
  have h𝔭'_bot : σ • 𝔭 ≠ ⊥ := fun h0 => hbot (by rw [← inv_smul_smul σ 𝔭, h0]; simp)
  have hlam' : lamR l ∉ σ • 𝔭 := by
    intro hmem
    have hinv : σ⁻¹ • lamR l ∈ 𝔭 := Ideal.mem_pointwise_smul_iff_inv_smul_mem.mp hmem
    let e_inv := galRestrict ℤ ℚ (CycK l) (CycR l) σ⁻¹
    have hassoc : Associated (lamR l) (σ⁻¹ • lamR l) := by
      have hev : σ⁻¹ • lamR l = e_inv (lamR l) := (galRestrict_eq_smul σ⁻¹ _).symm
      rw [hev]
      simpa [lamR, map_sub, map_one] using (zetaR_spec l).associated_sub_one_map_sub_one e_inv
    obtain ⟨u, hu⟩ := hassoc.symm
    exact hlam (by rw [← hu]; exact 𝔭.mul_mem_right _ hinv)
  have hα' : σ • α ∉ σ • 𝔭 := fun hmem =>
    hα (by simpa using Ideal.mem_pointwise_smul_iff_inv_smul_mem.mp hmem)
  let qEquiv : (CycR l ⧸ 𝔭) ≃+* (CycR l ⧸ (σ • 𝔭)) :=
    Ideal.quotientEquiv 𝔭 (σ • 𝔭) e.toRingEquiv hmap_eq
  have hq_mk : ∀ x : CycR l, qEquiv (Ideal.Quotient.mk 𝔭 x) = Ideal.Quotient.mk (σ • 𝔭) (σ • x) :=
    fun x => by
      change Ideal.Quotient.mk (σ • 𝔭) (e x) = Ideal.Quotient.mk (σ • 𝔭) (σ • x)
      rw [galRestrict_eq_smul]
  obtain ⟨⟨k, _, hk⟩, hkmk⟩ := powResSymb_spec hbot hlam hα
  rw [hk, ← pow_mul, powResSymb_eq_pow_iff h𝔭'_bot hlam' hα']
  have hζ_smul : σ • (zetaR l ^ k) =
      zetaR l ^ (k * (IsCyclotomicExtension.Rat.galEquivZMod l (CycK l) σ).val.val) := by
    have h1 : (zetaR l ^ k) ^ l = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, (zetaR_spec l).pow_eq_one, one_pow]
    rw [IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq l (CycK l) σ h1, ← pow_mul]
  rw [← hζ_smul, ← hq_mk, ← hk, hkmk, map_pow, hq_mk, galois_smul_absNorm]

noncomputable def powResIdeal (α : CycR l) (𝔞 : Ideal (CycR l)) : CycR l :=
  ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map (powResSymb α)).prod

lemma powResIdeal_pow_l (α : CycR l) (𝔞 : Ideal (CycR l)) :
    powResIdeal α 𝔞 ^ l = 1 := by
  unfold powResIdeal
  rw [multiset_prod_pow, Multiset.map_map]
  have h1 : (UniqueFactorizationMonoid.normalizedFactors 𝔞).map (fun 𝔭 => powResSymb α 𝔭 ^ l) =
      (UniqueFactorizationMonoid.normalizedFactors 𝔞).map (fun _ => (1 : CycR l)) :=
    Multiset.map_congr rfl fun 𝔭 _ => powResSymb_pow_l α 𝔭
  change ((UniqueFactorizationMonoid.normalizedFactors 𝔞).map (fun 𝔭 => powResSymb α 𝔭 ^ l)).prod = 1
  rw [h1, Multiset.map_const', Multiset.prod_replicate, one_pow]

lemma powResIdeal_prime {𝔭 : Ideal (CycR l)} (h𝔭 : 𝔭.IsPrime) (hbot : 𝔭 ≠ ⊥) (α : CycR l) :
    powResIdeal α 𝔭 = powResSymb α 𝔭 := by
  unfold powResIdeal
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible (Ideal.prime_of_isPrime hbot h𝔭).irreducible]
  simp [normalize_eq]

lemma powResIdeal_mul {𝔞 𝔟 : Ideal (CycR l)} (h𝔞 : 𝔞 ≠ ⊥) (h𝔟 : 𝔟 ≠ ⊥) (α : CycR l) :
    powResIdeal α (𝔞 * 𝔟) = powResIdeal α 𝔞 * powResIdeal α 𝔟 := by
  unfold powResIdeal
  rw [UniqueFactorizationMonoid.normalizedFactors_mul h𝔞 h𝔟, Multiset.map_add, Multiset.prod_add]

lemma mem_normalizedFactors_prime {𝔞 𝔭 : Ideal (CycR l)}
    (h𝔭 : 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔞) :
    𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ 𝔞 ≤ 𝔭 := by
  have hpr := UniqueFactorizationMonoid.prime_of_normalized_factor 𝔭 h𝔭
  exact ⟨Ideal.isPrime_of_prime hpr, hpr.ne_zero,
    Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h𝔭)⟩

lemma powResIdeal_mul_left {𝔞 : Ideal (CycR l)}
    (hlam : IsCoprime (span {lamR l}) 𝔞)
    {α β : CycR l} (hα : IsCoprime (span {α}) 𝔞) (hβ : IsCoprime (span {β}) 𝔞) :
    powResIdeal (α * β) 𝔞 = powResIdeal α 𝔞 * powResIdeal β 𝔞 := by
  unfold powResIdeal
  rw [← Multiset.prod_map_mul]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun 𝔭 h𝔭 => ?_)
  obtain ⟨hpr, hbot, hle⟩ := mem_normalizedFactors_prime h𝔭
  have : 𝔭.IsPrime := hpr
  have hlam𝔭 : lamR l ∉ 𝔭 := fun hm =>
    hpr.ne_top (eq_top_iff.mpr <| by rw [← hlam.sup_eq]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hm) hle)
  have hα𝔭 : α ∉ 𝔭 := fun hm =>
    hpr.ne_top (eq_top_iff.mpr <| by rw [← hα.sup_eq]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hm) hle)
  have hβ𝔭 : β ∉ 𝔭 := fun hm =>
    hpr.ne_top (eq_top_iff.mpr <| by rw [← hβ.sup_eq]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hm) hle)
  exact powResSymb_mul hbot hlam𝔭 hα𝔭 hβ𝔭

lemma powResIdeal_one {𝔞 : Ideal (CycR l)} (hlam : IsCoprime (span {lamR l}) 𝔞) :
    powResIdeal (1 : CycR l) 𝔞 = 1 := by
  unfold powResIdeal
  have : (UniqueFactorizationMonoid.normalizedFactors 𝔞).map (powResSymb (1 : CycR l)) =
      (UniqueFactorizationMonoid.normalizedFactors 𝔞).map (fun _ => (1 : CycR l)) := by
    refine Multiset.map_congr rfl fun 𝔭 h𝔭 => ?_
    obtain ⟨hpr, hbot, hle⟩ := mem_normalizedFactors_prime h𝔭
    have : 𝔭.IsPrime := hpr
    have hlam𝔭 : lamR l ∉ 𝔭 := fun hm =>
      hpr.ne_top (eq_top_iff.mpr <| by rw [← hlam.sup_eq]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hm) hle)
    exact powResSymb_one hbot hlam𝔭
  rw [this, Multiset.map_const', Multiset.prod_replicate, one_pow]

lemma powResIdeal_neg_one (hl2 : l ≠ 2) {𝔞 : Ideal (CycR l)}
    (hlam : IsCoprime (span {lamR l}) 𝔞) : powResIdeal (-1 : CycR l) 𝔞 = 1 := by
  unfold powResIdeal
  have : (UniqueFactorizationMonoid.normalizedFactors 𝔞).map (powResSymb (-1 : CycR l)) =
      (UniqueFactorizationMonoid.normalizedFactors 𝔞).map (fun _ => (1 : CycR l)) := by
    refine Multiset.map_congr rfl fun 𝔭 h𝔭 => ?_
    obtain ⟨hpr, hbot, hle⟩ := mem_normalizedFactors_prime h𝔭
    have : 𝔭.IsPrime := hpr
    have hlam𝔭 : lamR l ∉ 𝔭 := fun hm =>
      hpr.ne_top (eq_top_iff.mpr <| by rw [← hlam.sup_eq]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hm) hle)
    exact powResSymb_neg_one hl2 hbot hlam𝔭
  rw [this, Multiset.map_const', Multiset.prod_replicate, one_pow]

lemma powResIdeal_congr {𝔞 : Ideal (CycR l)} (hlam : IsCoprime (span {lamR l}) 𝔞)
    {α β : CycR l} (hα : IsCoprime (span {α}) 𝔞) (hsub : α - β ∈ 𝔞) :
    powResIdeal α 𝔞 = powResIdeal β 𝔞 := by
  unfold powResIdeal
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun 𝔭 h𝔭 => ?_)
  obtain ⟨hpr, hbot, hle⟩ := mem_normalizedFactors_prime h𝔭
  have : 𝔭.IsPrime := hpr
  have hlam𝔭 : lamR l ∉ 𝔭 := fun hm =>
    hpr.ne_top (eq_top_iff.mpr <| by rw [← hlam.sup_eq]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hm) hle)
  have hα𝔭 : α ∉ 𝔭 := fun hm =>
    hpr.ne_top (eq_top_iff.mpr <| by rw [← hα.sup_eq]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hm) hle)
  exact powResSymb_congr hbot hlam𝔭 hα𝔭 (hle hsub)

lemma powResIdeal_prod_left {ι : Type*} (s : Finset ι) (f : ι → CycR l)
    {𝔞 : Ideal (CycR l)} (hlam : IsCoprime (span {lamR l}) 𝔞)
    (hf : ∀ i ∈ s, IsCoprime (span {f i}) 𝔞) :
    powResIdeal (∏ i ∈ s, f i) 𝔞 = ∏ i ∈ s, powResIdeal (f i) 𝔞 := by
  induction s using Finset.induction_on with
  | empty => simp [powResIdeal_one hlam]
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    have hprod_cop : IsCoprime (span {∏ i ∈ s, f i}) 𝔞 := by
      rw [← Ideal.prod_span_singleton]
      exact IsCoprime.prod_left fun i hi => hf i (mem_insert_of_mem hi)
    rw [powResIdeal_mul_left hlam (hf a (mem_insert_self a s)) hprod_cop,
      ih fun i hi => hf i (mem_insert_of_mem hi)]

lemma powResIdeal_pow_left {𝔞 : Ideal (CycR l)} (hlam : IsCoprime (span {lamR l}) 𝔞)
    {α : CycR l} (hα : IsCoprime (span {α}) 𝔞) (n : ℕ) :
    powResIdeal (α ^ n) 𝔞 = powResIdeal α 𝔞 ^ n := by
  induction n with
  | zero => simp [powResIdeal_one hlam]
  | succ n ih =>
    rw [pow_succ, pow_succ, powResIdeal_mul_left hlam
      (by rw [← Ideal.span_singleton_pow]; exact hα.pow_left) hα, ih]

lemma isCoprime_lamR_span_prime {q : ℕ} (hq : q.Prime) (hql : q ≠ l) :
    IsCoprime (span {lamR l}) (span {(q : CycR l)}) := by
  have hnot : ¬ lamR l ∣ (q : CycR l) := fun hd =>
    hql ((Nat.prime_dvd_prime_iff_eq hl.out hq).mp
      (Int.ofNat_dvd.mp ((lamR_dvd_intCast_iff (q : ℤ)).mp (by simpa using hd)))).symm
  have hcop := IsCyclotomicExtension.Rat.isCoprime_of_not_zeta_sub_one_dvd l (zetaK_spec l) hnot
  have h1 : IsCoprime (span {(l : CycR l)}) (span {(q : CycR l)}) := by
    rw [Ideal.isCoprime_iff_exists]
    obtain ⟨a, b, hab⟩ := hcop
    exact ⟨a * (l : CycR l), Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)),
      b * (q : CycR l), Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _)), hab⟩
  have hassoc := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime l (zetaK_spec l)
  rw [← Ideal.span_singleton_eq_span_singleton.mpr hassoc, ← Ideal.span_singleton_pow] at h1
  exact (IsCoprime.pow_left_iff (by have := hl.out.one_lt; omega)).mp h1

lemma powResIdeal_galois_span_natCast {q : ℕ} (hq : q.Prime) (hql : q ≠ l)
    {α : CycR l} (hα : IsCoprime (span {α}) (span {(q : CycR l)})) (σ : Gal(CycK l / ℚ)) :
    powResIdeal (σ • α) (span {(q : CycR l)}) =
      (powResIdeal α (span {(q : CycR l)})) ^
        (IsCyclotomicExtension.Rat.galEquivZMod l (CycK l) σ).val.val := by
  have hq_ne : (span {(q : CycR l)}) ≠ ⊥ := by simp [hq.ne_zero]
  have hlam_cop := isCoprime_lamR_span_prime hq hql
  let e := galRestrict ℤ ℚ (CycK l) (CycR l) σ
  have hsmul_q : σ • (span {(q : CycR l)}) = span {(q : CycR l)} := by
    rw [galois_smul_span_singleton, ← galRestrict_eq_smul, map_natCast]
  have hfac_eq : (UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)})).map (fun 𝔭 => σ • 𝔭) =
      UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)}) := by
    have hrel : Multiset.Rel Associated
        ((UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)})).map (fun 𝔭 => σ • 𝔭))
        (UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)})) := by
      apply UniqueFactorizationMonoid.factors_unique
      · intro 𝔭 h𝔭
        obtain ⟨𝔭₀, h𝔭₀, rfl⟩ := Multiset.mem_map.mp h𝔭
        obtain ⟨hpr, hbot, _⟩ := mem_normalizedFactors_prime h𝔭₀
        have hpr' : (σ • 𝔭₀).IsPrime := by
          rw [galois_smul_ideal_eq_map]; exact Ideal.map_isPrime_of_equiv e.toRingEquiv
        have hbot' : σ • 𝔭₀ ≠ ⊥ := fun h0 => hbot (by rw [← inv_smul_smul σ 𝔭₀, h0]; simp)
        exact (Ideal.prime_of_isPrime hbot' hpr').irreducible
      · intro 𝔭 h𝔭; exact (UniqueFactorizationMonoid.prime_of_normalized_factor 𝔭 h𝔭).irreducible
      · rw [Ideal.prod_normalizedFactors_eq_self hq_ne]
        have hprod_smul : ∀ m : Multiset (Ideal (CycR l)),
            (m.map (fun 𝔭 => σ • 𝔭)).prod = σ • m.prod := fun m => by
          refine Multiset.induction_on m (by rw [Multiset.map_zero, Multiset.prod_zero,
            Ideal.one_eq_top, galois_smul_ideal_eq_map, Ideal.map_top]) fun a s ih => ?_
          rw [Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, ih, galois_smul_mul_ideal]
        rw [hprod_smul, Ideal.prod_normalizedFactors_eq_self hq_ne, hsmul_q]
        exact Associated.refl _
    exact Multiset.rel_eq.mp (hrel.mono fun _ _ _ _ hab => associated_iff_eq.mp hab)
  unfold powResIdeal
  conv_lhs => rw [← hfac_eq]
  rw [Multiset.map_map, multiset_prod_pow, Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun 𝔭 h𝔭 => ?_)
  obtain ⟨hpr, hbot, hle⟩ := mem_normalizedFactors_prime h𝔭
  have : 𝔭.IsPrime := hpr
  have hlam𝔭 : lamR l ∉ 𝔭 := fun hm =>
    hpr.ne_top (eq_top_iff.mpr <| by rw [← hlam_cop.sup_eq]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hm) hle)
  have hα𝔭 : α ∉ 𝔭 := fun hm =>
    hpr.ne_top (eq_top_iff.mpr <| by rw [← hα.sup_eq]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hm) hle)
  exact powResSymb_galois hbot hlam𝔭 hα𝔭 σ

end PowerResidueSymbol

section GaussSumAndStickelberger

variable {l : ℕ} [hl : Fact l.Prime]

lemma of_mem_map_ideal_iff {A : Type*} [CommRing A] {g : A[X]} (hg : g.Monic) (hdeg : 0 < g.natDegree)
    (I : Ideal A) (r : A) :
    AdjoinRoot.of g r ∈ Ideal.map (AdjoinRoot.of g) I ↔ r ∈ I := by
  constructor
  · intro hmem
    let pb := AdjoinRoot.powerBasis' hg
    have hall : ∀ x ∈ Ideal.map (AdjoinRoot.of g) I, ∀ i : Fin pb.dim, pb.basis.repr x i ∈ I := by
      intro x hx
      rw [Ideal.map] at hx
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨a, ha, rfl⟩ i
        have h1 : AdjoinRoot.of g a = a • (1 : AdjoinRoot g) := by rw [Algebra.smul_def, mul_one]; rfl
        rw [h1, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact I.mul_mem_right _ ha
      · intro i; simp
      · intro x y _ _ hx hy i
        rw [map_add, Finsupp.coe_add, Pi.add_apply]; exact I.add_mem (hx i) (hy i)
      · intro s x _ hx i
        have hs : s = ∑ j : Fin pb.dim, pb.basis.repr s j • pb.basis j := (pb.basis.sum_repr s).symm
        have hx' : x = ∑ k : Fin pb.dim, pb.basis.repr x k • pb.basis k := (pb.basis.sum_repr x).symm
        have hmul : s * x = ∑ j : Fin pb.dim, ∑ k : Fin pb.dim,
            (pb.basis.repr s j * pb.basis.repr x k) • (pb.basis j * pb.basis k) := by
          conv_lhs => rw [hs, hx']
          rw [sum_mul]; refine sum_congr rfl fun j _ => ?_
          rw [mul_sum]; refine sum_congr rfl fun k _ => ?_
          rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
        rw [smul_eq_mul, hmul, map_sum]
        simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
        refine I.sum_mem fun j _ => ?_
        rw [map_sum]; simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
        refine I.sum_mem fun k _ => ?_
        rw [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact I.mul_mem_right _ (I.mul_mem_left _ (hx k))
    have h0 := hall (AdjoinRoot.of g r) hmem ⟨0, by simpa [pb] using hdeg⟩
    have hrep0 : pb.basis.repr (AdjoinRoot.of g r) ⟨0, by simpa [pb] using hdeg⟩ = r := by
      have h1 : AdjoinRoot.of g r = r • pb.basis ⟨0, by simpa [pb] using hdeg⟩ := by
        rw [pb.basis_eq_pow, pow_zero, Algebra.smul_def, mul_one]; rfl
      rw [h1, map_smul, pb.basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
        Finsupp.single_eq_same]
    rwa [hrep0] at h0
  · exact Ideal.mem_map_of_mem _

lemma zmod_units_pow_sum_eq_zero {p : ℕ} [hp : Fact p.Prime] {s : ℕ} (hs0 : 0 < s) (hs : s < p - 1) :
    ∑ a : (ZMod p)ˣ, (a : ZMod p) ^ s = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hp.out]
  have hgs_ne : (g : ZMod p) ^ s ≠ 1 := fun h1 =>
    absurd (Nat.le_of_dvd hs0 (hord ▸ orderOf_dvd_of_pow_eq_one (Units.ext (by simpa using h1))))
      (not_le.mpr hs)
  have hmul : (g : ZMod p) ^ s * ∑ a : (ZMod p)ˣ, (a : ZMod p) ^ s =
      ∑ a : (ZMod p)ˣ, (a : ZMod p) ^ s := by
    rw [mul_sum]; exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun a => by simp [mul_pow]
  exact (mul_eq_zero.mp (by rw [sub_mul, one_mul, hmul, sub_self])).resolve_left (sub_ne_zero.mpr hgs_ne)

lemma sum_pow_mul_choose_zmod_eq_zero {p : ℕ} [hp : Fact p.Prime] {d k : ℕ}
    (hd0 : 0 < d) (hdk : d + k < p - 1) :
    ((∑ a ∈ Ico 1 p, a ^ d * Nat.choose a k : ℕ) : ZMod p) = 0 := by
  have hk_lt : k < p := by omega
  have hfac_ne : ((k.factorial : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (hp.out.dvd_factorial.mp h) (by omega)
  suffices h : ((k.factorial : ℕ) : ZMod p) * ((∑ a ∈ Ico 1 p, a ^ d * Nat.choose a k : ℕ) : ZMod p) = 0 from
    (mul_eq_zero.mp h).resolve_left hfac_ne
  push_cast; rw [mul_sum]
  have hdesc : ∀ a : ℕ, (k.factorial : ZMod p) * (Nat.choose a k : ZMod p) =
      ∏ i ∈ range k, ((a : ZMod p) - (i : ZMod p)) := by
    intro a
    rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose]
    clear hdk hk_lt hfac_ne
    induction k with
    | zero => simp
    | succ j ih =>
      rw [Nat.descFactorial_succ, prod_range_succ, Nat.cast_mul, ← ih]
      by_cases hja : j ≤ a
      · rw [Nat.cast_sub hja]; ring
      · have h0 : Nat.descFactorial a j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
        rw [h0, Nat.cast_zero, mul_zero, zero_mul]
  have hrew : ∑ a ∈ Ico 1 p, (k.factorial : ZMod p) * ((a : ZMod p) ^ d * (Nat.choose a k : ZMod p)) =
      ∑ a : (ZMod p)ˣ, (a : ZMod p) ^ d * (∏ i ∈ range k, ((a : ZMod p) - (i : ZMod p))) := by
    have h1 : ∑ a ∈ Ico 1 p, (k.factorial : ZMod p) * ((a : ZMod p) ^ d * (Nat.choose a k : ZMod p)) =
        ∑ a ∈ Ico 1 p, (a : ZMod p) ^ d * ∏ i ∈ range k, ((a : ZMod p) - (i : ZMod p)) :=
      sum_congr rfl fun a _ => by rw [← hdesc a]; ring
    rw [h1]; symm
    refine Finset.sum_bij (fun (a : (ZMod p)ˣ) _ => a.val.val)
      (fun a _ => mem_Ico.mpr ⟨Nat.pos_of_ne_zero fun h0 => a.ne_zero (by
        have := ZMod.natCast_zmod_val a.val; rw [h0, Nat.cast_zero] at this; exact this.symm),
        ZMod.val_lt a.val⟩)
      (fun a _ b _ h => Units.ext (ZMod.val_injective p h))
      (fun n hn => ?_) (fun _ _ => by simp)
    obtain ⟨hn1, hnp⟩ := mem_Ico.mp hn
    have hne : (n : ZMod p) ≠ 0 := fun h0 =>
      absurd (Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff n p).mp h0)) (by omega)
    exact ⟨Units.mk0 (n : ZMod p) hne, mem_univ _, by simp [Units.mk0, ZMod.val_natCast_of_lt hnp]⟩
  rw [hrew]
  let P : (ZMod p)[X] := ∏ i ∈ range k, (X - C (i : ZMod p))
  have hP_deg : P.natDegree ≤ k := by
    calc P.natDegree ≤ ∑ i ∈ range k, (X - C (i : ZMod p)).natDegree := natDegree_prod_le _ _
      _ = ∑ _i ∈ range k, 1 := sum_congr rfl fun i _ => natDegree_X_sub_C _
      _ = k := by simp
  have hP_eval : ∀ x : ZMod p, (∏ i ∈ range k, (x - (i : ZMod p))) =
      ∑ j ∈ range (k + 1), P.coeff j * x ^ j := fun x => by
    rw [← show P.eval x = ∏ i ∈ range k, (x - (i : ZMod p)) by simp [P, eval_prod],
      eval_eq_sum_range' (Nat.lt_succ_of_le hP_deg)]
  simp_rw [hP_eval, mul_sum]; rw [sum_comm]
  refine sum_eq_zero fun j hj => ?_
  have hjle : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have hpull : ∑ a : (ZMod p)ˣ, (a : ZMod p) ^ d * (P.coeff j * (a : ZMod p) ^ j) =
      P.coeff j * ∑ a : (ZMod p)ˣ, (a : ZMod p) ^ (d + j) := by
    rw [mul_sum]; exact sum_congr rfl fun a _ => by rw [pow_add]; ring
  rw [hpull, zmod_units_pow_sum_eq_zero (by omega) (by omega), mul_zero]

set_option maxHeartbeats 1600000 in
/-- Main Stickelberger + Gauss-sum package for a degree-1 prime ideal `𝔭` (`absNorm 𝔭 = p ≠ l`). -/
theorem exists_stickelberger_element (hl2 : l ≠ 2) {𝔭 : Ideal (CycR l)} [h𝔭 : 𝔭.IsPrime]
    {p : ℕ} (hp : p.Prime) (hpl : p ≠ l) (hnorm : Ideal.absNorm 𝔭 = p) :
    ∃ Φ : CycR l,
      IsPrimary Φ ∧
      (∀ φ : CycK l →+* ℂ, ‖φ (Φ : CycK l)‖ ^ 2 = (p : ℝ) ^ l) ∧
      span {Φ} = ∏ t : (ZMod l)ˣ,
        (((IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm t)⁻¹ • 𝔭) ^ (l - t.val.val) ∧
      (∀ q : ℕ, q.Prime → q ≠ l → q ≠ p →
        powResIdeal Φ (span {(q : CycR l)}) = powResSymb (q : CycR l) 𝔭) := by
  have : Fact p.Prime := ⟨hp⟩
  have hbot : 𝔭 ≠ ⊥ := Ideal.absNorm_eq_zero_iff.not.mp (by rw [hnorm]; exact hp.ne_zero)
  have : 𝔭.IsMaximal := h𝔭.isMaximal hbot
  have hlam : lamR l ∉ 𝔭 := by
    intro hm
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hm)
    rw [absNorm_span_lamR, hnorm] at hdvd
    exact hpl ((Nat.prime_dvd_prime_iff_eq hp hl.out).mp hdvd)
  have hl_dvd_p1 : l ∣ (p - 1) := by rw [← hnorm]; exact dvd_absNorm_sub_one hbot hlam
  have hp_in_𝔭 : (p : CycR l) ∈ 𝔭 := by rw [← hnorm]; exact Ideal.absNorm_mem 𝔭
  let gP : (CycR l)[X] := Polynomial.cyclotomic p (CycR l)
  have hgP_monic : gP.Monic := Polynomial.cyclotomic.monic p (CycR l)
  have hgP_deg : gP.natDegree = p - 1 := by rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hp]
  have hgP_deg_pos : 0 < gP.natDegree := by rw [hgP_deg]; have := hp.two_le; omega
  let S := AdjoinRoot gP
  let ξ : S := AdjoinRoot.root gP
  let ofR : CycR l →+* S := AdjoinRoot.of gP
  have hgP_eq : gP = ∑ i ∈ range p, (X : (CycR l)[X]) ^ i := Polynomial.cyclotomic_prime (CycR l) p
  have hξ_root : Polynomial.aeval ξ gP = 0 := by rw [AdjoinRoot.aeval_eq]; simp
  have hξ_sum : ∑ i ∈ range p, ξ ^ i = 0 := by
    have h0 := congrArg (Polynomial.aeval ξ) hgP_eq
    rw [hξ_root, map_sum] at h0
    simpa [map_pow] using h0.symm
  have hξ_pow_p : ξ ^ p = 1 := by
    have h0 := congrArg (Polynomial.aeval ξ) (Polynomial.cyclotomic_prime_mul_X_sub_one (CycR l) p)
    simp only [map_mul, map_sub, map_pow, aeval_X, map_one] at h0
    change Polynomial.aeval ξ gP * (ξ - 1) = ξ ^ p - 1 at h0
    rw [hξ_root, zero_mul] at h0
    exact sub_eq_zero.mp h0.symm
  have hξ_units_sum : ∑ a : (ZMod p)ˣ, ξ ^ a.val.val = -1 := by
    have hbi : ∑ a : (ZMod p)ˣ, ξ ^ a.val.val = ∑ i ∈ Ico 1 p, ξ ^ i := by
      refine Finset.sum_bij (fun (a : (ZMod p)ˣ) _ => a.val.val)
        (fun a _ => mem_Ico.mpr ⟨Nat.pos_of_ne_zero fun h0 => a.ne_zero (by
          have := ZMod.natCast_zmod_val a.val; rw [h0, Nat.cast_zero] at this; exact this.symm),
          ZMod.val_lt a.val⟩)
        (fun a _ b _ h => Units.ext (ZMod.val_injective p h))
        (fun n hn => ?_) (fun _ _ => rfl)
      obtain ⟨hn1, hnp⟩ := mem_Ico.mp hn
      have hne : (n : ZMod p) ≠ 0 := fun h0 =>
        absurd (Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff n p).mp h0)) (by omega)
      exact ⟨Units.mk0 (n : ZMod p) hne, mem_univ _, by simp [Units.mk0, ZMod.val_natCast_of_lt hnp]⟩
    rw [hbi]
    have hsplit : ∑ i ∈ range p, ξ ^ i = 1 + ∑ i ∈ Ico 1 p, ξ ^ i := by
      rw [show range p = insert 0 (Ico 1 p) by ext i; simp only [mem_range, mem_insert, mem_Ico]; omega,
        sum_insert (by simp), pow_zero]
    rw [hsplit] at hξ_sum; exact eq_neg_of_add_eq_zero_right hξ_sum
  have hξ_pow_mod : ∀ n : ℕ, ξ ^ n = ξ ^ (n % p) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n p]
    rw [pow_add, pow_mul, hξ_pow_p, one_pow, one_mul]
  let χ : (ZMod p)ˣ → CycR l := fun a => powResSymb ((a.val.val : ℕ) : CycR l) 𝔭
  have ha_not_mem : ∀ a : (ZMod p)ˣ, ((a.val.val : ℕ) : CycR l) ∉ 𝔭 := by
    intro a hm
    have ha_pos : 0 < a.val.val := Nat.pos_of_ne_zero fun h0 => a.ne_zero (by
      have := ZMod.natCast_zmod_val a.val; rw [h0, Nat.cast_zero] at this; exact this.symm)
    have hcop : Nat.Coprime a.val.val p :=
      (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt ha_pos (ZMod.val_lt a.val))).symm
    have hbez := Nat.gcd_eq_gcd_ab a.val.val p
    rw [hcop.gcd_eq_one] at hbez
    have h1 : (1 : CycR l) ∈ 𝔭 := by
      have hc : (1 : CycR l) = ((a.val.val : ℕ) : CycR l) * (Nat.gcdA a.val.val p : CycR l) +
          (p : CycR l) * (Nat.gcdB a.val.val p : CycR l) := by
        have := congrArg (Int.cast (R := CycR l)) hbez; push_cast at this; exact this
      rw [hc]; exact 𝔭.add_mem (𝔭.mul_mem_right _ hm) (𝔭.mul_mem_right _ hp_in_𝔭)
    exact h𝔭.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 h1 isUnit_one)
  have hχ_mul : ∀ a b : (ZMod p)ˣ, χ (a * b) = χ a * χ b := fun a b => by
    change powResSymb (((a * b).val.val : ℕ) : CycR l) 𝔭 =
      powResSymb ((a.val.val : ℕ) : CycR l) 𝔭 * powResSymb ((b.val.val : ℕ) : CycR l) 𝔭
    have hsub : (((a * b).val.val : ℕ) : CycR l) - ((a.val.val : ℕ) : CycR l) * ((b.val.val : ℕ) : CycR l) ∈ 𝔭 := by
      have hmod : ((a * b).val.val : ℤ) ≡ (a.val.val : ℤ) * (b.val.val : ℤ) [ZMOD p] := by
        rw [← ZMod.intCast_eq_intCast_iff]; push_cast; simp
      obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod.symm
      have heq : (((a * b).val.val : ℕ) : CycR l) - ((a.val.val : ℕ) : CycR l) * ((b.val.val : ℕ) : CycR l) =
          (p : CycR l) * (k : CycR l) := by
        have := congrArg (Int.cast (R := CycR l)) hk; push_cast at this; exact this
      rw [heq]; exact 𝔭.mul_mem_right _ hp_in_𝔭
    rw [powResSymb_congr hbot hlam (ha_not_mem (a * b)) hsub,
      powResSymb_mul hbot hlam (ha_not_mem a) (ha_not_mem b)]
  have hχ_one : χ 1 = 1 := by
    change powResSymb (((1 : (ZMod p)ˣ).val.val : ℕ) : CycR l) 𝔭 = 1
    rw [Units.val_one, ZMod.val_one, Nat.cast_one]; exact powResSymb_one hbot hlam
  have hχ_neg_one : χ (-1) = 1 := by
    change powResSymb (((-1 : (ZMod p)ˣ).val.val : ℕ) : CycR l) 𝔭 = 1
    have hsub : (((-1 : (ZMod p)ˣ).val.val : ℕ) : CycR l) - (-1 : CycR l) ∈ 𝔭 := by
      have hmod : ((-1 : (ZMod p)ˣ).val.val : ℤ) ≡ -1 [ZMOD p] := by
        rw [← ZMod.intCast_eq_intCast_iff]; push_cast; simp
      obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod.symm
      have heq : (((-1 : (ZMod p)ˣ).val.val : ℕ) : CycR l) - (-1 : CycR l) = (p : CycR l) * (k : CycR l) := by
        have := congrArg (Int.cast (R := CycR l)) hk; push_cast at this; exact this
      rw [heq]; exact 𝔭.mul_mem_right _ hp_in_𝔭
    rw [powResSymb_congr hbot hlam (ha_not_mem (-1)) hsub]; exact powResSymb_neg_one hl2 hbot hlam
  have hχ_pow_l : ∀ a : (ZMod p)ˣ, χ a ^ l = 1 := fun a => powResSymb_pow_l _ _
  have hχ_inv : ∀ a : (ZMod p)ˣ, χ a⁻¹ = χ a ^ (l - 1) := fun a => by
    have h1 : χ a * χ a⁻¹ = 1 := by rw [← hχ_mul, mul_inv_cancel, hχ_one]
    have h2 : χ a * χ a ^ (l - 1) = 1 := by
      rw [← pow_succ', show l - 1 + 1 = l by have := hl.out.one_lt; omega, hχ_pow_l]
    calc χ a⁻¹ = χ a⁻¹ * (χ a * χ a ^ (l - 1)) := by rw [h2, mul_one]
      _ = (χ a * χ a⁻¹) * χ a ^ (l - 1) := by ring
      _ = χ a ^ (l - 1) := by rw [h1, one_mul]
  have hχ_nontriv : ∃ a : (ZMod p)ˣ, χ a ≠ 1 := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    refine ⟨g, fun h1 => ?_⟩
    have hord : orderOf g = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime hp]
    have hmk := (powResSymb_spec hbot hlam (ha_not_mem g)).2
    change Ideal.Quotient.mk 𝔭 (χ g) = _ at hmk
    rw [h1, map_one, hnorm] at hmk
    -- `g.val.val ^ ((p - 1) / l) - 1 ∈ 𝔭`, so `p ∣ (g.val.val ^ ((p - 1) / l) - 1)` in `ℤ`!
    have hmem_z : (((g.val.val ^ ((p - 1) / l) : ℤ) - 1 : ℤ) : CycR l) ∈ 𝔭 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_intCast, Int.cast_sub, Int.cast_pow, Int.cast_natCast,
        Int.cast_one, ← map_natCast (Ideal.Quotient.mk 𝔭), ← hmk, sub_self]
    have hp_dvd_z : (p : ℤ) ∣ ((g.val.val ^ ((p - 1) / l) : ℤ) - 1) := by
      have hcomap : 𝔭.comap (algebraMap ℤ (CycR l)) = Ideal.span {(p : ℤ)} := by
        symm
        refine (Int.ideal_span_isMaximal_of_prime p).eq_of_le (h𝔭.comap _).ne_top ?_
        rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, algebraMap_int_eq, map_natCast]
        exact hp_in_𝔭
      have hmem_span : ((g.val.val ^ ((p - 1) / l) : ℤ) - 1 : ℤ) ∈ Ideal.span {(p : ℤ)} := by
        rw [← hcomap, Ideal.mem_comap, algebraMap_int_eq]; exact hmem_z
      exact Ideal.mem_span_singleton.mp hmem_span
    have hgp : g ^ ((p - 1) / l) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      have h0 : (((g.val.val ^ ((p - 1) / l) : ℤ) - 1 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hp_dvd_z
      push_cast at h0
      rw [ZMod.natCast_zmod_val] at h0
      exact sub_eq_zero.mp h0
    have hdvd : (p - 1) ∣ ((p - 1) / l) := by
      have := orderOf_dvd_of_pow_eq_one hgp
      rwa [hord] at this
    have hlt : (p - 1) / l < p - 1 := Nat.div_lt_self (by have := hp.two_le; omega) hl.out.one_lt
    have hmul := Nat.div_mul_cancel hl_dvd_p1
    have hpos : 0 < (p - 1) / l := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_mul] at hmul; have := hp.two_le; omega
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
  have hχ_sum_zero : ∑ a : (ZMod p)ˣ, χ a = 0 := by
    obtain ⟨g, hg⟩ := hχ_nontriv
    have hmul : χ g * ∑ a : (ZMod p)ˣ, χ a = ∑ a : (ZMod p)ˣ, χ a := by
      rw [mul_sum]; exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun a => (hχ_mul g a).symm
    exact (mul_eq_zero.mp (by rw [sub_mul, one_mul, hmul, sub_self])).resolve_left (sub_ne_zero.mpr hg)
  let gs : ℕ → S := fun t => ∑ a : (ZMod p)ˣ, ofR (χ a ^ t) * ξ ^ a.val.val
  have hτ_root : ∀ c : (ZMod p)ˣ, Polynomial.eval₂ ofR (ξ ^ c.val.val) gP = 0 := fun c => by
    rw [congrArg (Polynomial.eval₂ ofR (ξ ^ c.val.val)) hgP_eq, Polynomial.eval₂_finsetSum]
    simp only [Polynomial.eval₂_pow, Polynomial.eval₂_X]
    have hbi : ∑ i ∈ range p, (ξ ^ c.val.val) ^ i = ∑ i ∈ range p, ξ ^ i := by
      have hrew : ∀ i ∈ range p, (ξ ^ c.val.val) ^ i = ξ ^ ((c.val * (i : ZMod p)).val) := fun i _ => by
        rw [← pow_mul, hξ_pow_mod]; congr 1
        rw [ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod_mod]
      rw [sum_congr rfl hrew]
      have hc_inv_mul : c⁻¹.val * c.val = 1 := by exact_mod_cast Units.inv_mul c
      have hc_mul_inv : c.val * c⁻¹.val = 1 := by exact_mod_cast Units.mul_inv c
      refine Finset.sum_bij (fun i _ => (c.val * (i : ZMod p)).val)
        (fun i _ => mem_range.mpr (ZMod.val_lt _))
        (fun i hi j hj heq => ?_)
        (fun j hj => ?_) (fun _ _ => rfl)
      · have h2 : (i : ZMod p) = (j : ZMod p) := by
          have := congrArg (fun x => c⁻¹.val * x) (ZMod.val_injective p heq)
          rw [← mul_assoc, ← mul_assoc, hc_inv_mul, one_mul, one_mul] at this
          exact this
        have h3 := congrArg ZMod.val h2
        rwa [ZMod.val_natCast_of_lt (mem_range.mp hi), ZMod.val_natCast_of_lt (mem_range.mp hj)] at h3
      · refine ⟨(c⁻¹.val * (j : ZMod p)).val, mem_range.mpr (ZMod.val_lt _), ?_⟩
        rw [ZMod.natCast_zmod_val, ← mul_assoc, hc_mul_inv, one_mul,
          ZMod.val_natCast_of_lt (mem_range.mp hj)]
    rw [hbi, hξ_sum]
  let τ : (ZMod p)ˣ → (S →+* S) := fun c => AdjoinRoot.lift ofR (ξ ^ c.val.val) (hτ_root c)
  have hτ_ξ : ∀ c : (ZMod p)ˣ, τ c ξ = ξ ^ c.val.val := fun c => AdjoinRoot.lift_root (hτ_root c)
  have hτ_of : ∀ (c : (ZMod p)ˣ) (r : CycR l), τ c (ofR r) = ofR r := fun c r => AdjoinRoot.lift_of (hτ_root c)
  have hτ_gs : ∀ (c : (ZMod p)ˣ) (t : ℕ), τ c (gs t) = ofR (χ c⁻¹ ^ t) * gs t := fun c t => by
    dsimp [gs]; rw [map_sum, mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft c) _ _ fun a => ?_
    rw [map_mul, hτ_of, map_pow (τ c), hτ_ξ, ← pow_mul]
    change ofR (χ a ^ t) * ξ ^ (c.val.val * a.val.val) =
      ofR (χ c⁻¹ ^ t) * (ofR (χ (c * a) ^ t) * ξ ^ (c * a).val.val)
    rw [hξ_pow_mod, ← mul_assoc, ← map_mul, ← mul_pow, ← hχ_mul, inv_mul_cancel_left]
    congr 2; rw [Units.val_mul, ZMod.val_mul]
  have hfixed : ∀ c : (ZMod p)ˣ, τ c (gs 1 ^ l) = gs 1 ^ l := fun c => by
    rw [map_pow, hτ_gs c 1, mul_pow, ← map_pow, pow_one, hχ_pow_l, map_one, one_mul]
  -- Extract `Φ : CycR l` with `ofR Φ = gs 1 ^ l`
  obtain ⟨Φ, hΦ_eq⟩ : ∃ Φ : CycR l, ofR Φ = gs 1 ^ l := by
    let pb := AdjoinRoot.powerBasis' hgP_monic
    let x := gs 1 ^ l
    let i0 : Fin pb.dim := ⟨0, by simpa [pb] using hgP_deg_pos⟩
    let r0 : CycR l := pb.basis.repr x i0
    refine ⟨r0, ?_⟩
    have hx_exp : x = ∑ i : Fin pb.dim, ofR (pb.basis.repr x i) * ξ ^ (i : ℕ) := by
      conv_lhs => rw [← pb.basis.sum_repr x]
      refine sum_congr rfl fun i _ => by rw [pb.basis_eq_pow, Algebra.smul_def]; rfl
    have hsum_τ : ((p - 1 : ℕ) : S) * x = ∑ c : (ZMod p)ˣ, τ c x := by
      rw [sum_congr rfl fun c _ => hfixed c, sum_const, card_univ, ZMod.card_units_eq_totient,
        Nat.totient_prime hp, nsmul_eq_mul]
    have hsum_rhs : ∑ c : (ZMod p)ˣ, τ c x =
        ofR (((p - 1 : ℕ) : CycR l) * r0 - ∑ i ∈ univ.filter (fun i : Fin pb.dim => 0 < (i : ℕ)),
          pb.basis.repr x i) := by
      conv_lhs => enter [2, c]; rw [hx_exp, map_sum]
      rw [sum_comm, ← add_sum_erase _ _ (mem_univ i0)]
      have hterm0 : ∑ c : (ZMod p)ˣ, τ c (ofR (pb.basis.repr x i0) * ξ ^ (i0 : ℕ)) =
          ofR (((p - 1 : ℕ) : CycR l) * r0) := by
        simp only [i0, pow_zero, mul_one, hτ_of, sum_const, card_univ, ZMod.card_units_eq_totient,
          Nat.totient_prime hp, nsmul_eq_mul, map_mul, map_natCast]; rfl
      have hrest : ∑ i ∈ univ.erase i0, ∑ c : (ZMod p)ˣ, τ c (ofR (pb.basis.repr x i) * ξ ^ (i : ℕ)) =
          ofR (-(∑ i ∈ univ.filter (fun i : Fin pb.dim => 0 < (i : ℕ)), pb.basis.repr x i)) := by
        have her : univ.erase i0 = univ.filter (fun i : Fin pb.dim => 0 < (i : ℕ)) := by
          ext i
          have hi0_val : (i0 : ℕ) = 0 := rfl
          simp only [mem_erase, mem_univ, and_true, mem_filter, true_and, ne_eq, Fin.ext_iff, hi0_val]
          omega
        rw [her, map_neg, map_sum, ← sum_neg_distrib]
        refine sum_congr rfl fun i hi => ?_
        have hi0 : 0 < (i : ℕ) := (mem_filter.mp hi).2
        have hilt : (i : ℕ) < p := by
          have : (i : ℕ) < p - 1 := by simpa [pb, hgP_deg] using i.2
          have := hp.two_le; omega
        have hi_ne : ((i : ℕ) : ZMod p) ≠ 0 := fun h0 =>
          absurd (Nat.le_of_dvd hi0 ((ZMod.natCast_eq_zero_iff _ p).mp h0)) (by omega)
        let ui : (ZMod p)ˣ := Units.mk0 ((i : ℕ) : ZMod p) hi_ne
        have hinner : ∑ c : (ZMod p)ˣ, τ c (ofR (pb.basis.repr x i) * ξ ^ (i : ℕ)) =
            ofR (pb.basis.repr x i) * ∑ c : (ZMod p)ˣ, ξ ^ (c * ui).val.val := by
          rw [mul_sum]; refine sum_congr rfl fun c _ => ?_
          rw [map_mul, hτ_of, map_pow (τ c), hτ_ξ, ← pow_mul, hξ_pow_mod]
          congr 2
          rw [Units.val_mul, ZMod.val_mul, show ui.val = ((i : ℕ) : ZMod p) from rfl, ZMod.val_natCast_of_lt hilt]
        rw [hinner, Fintype.sum_equiv (Equiv.mulRight ui) (fun c => ξ ^ (c * ui).val.val)
          (fun c => ξ ^ c.val.val) (fun _ => rfl), hξ_units_sum, mul_neg_one]
      rw [hterm0, hrest, ← map_add, sub_eq_add_neg]
    have hcoeff_zero : ∀ i : Fin pb.dim, 0 < (i : ℕ) → pb.basis.repr x i = 0 := by
      intro i hi
      set sc : CycR l := ((p - 1 : ℕ) : CycR l) * r0 -
        ∑ j ∈ univ.filter (fun j : Fin pb.dim => 0 < (j : ℕ)), pb.basis.repr x j
      have heq_s : ((p - 1 : ℕ) : CycR l) • x = ofR sc := by
        rw [Algebra.smul_def, ← hsum_rhs, ← hsum_τ]; simp
      have hrep := congrArg (fun y => pb.basis.repr y i) heq_s
      rw [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at hrep
      have hrhs_rep : pb.basis.repr (ofR sc) i = 0 := by
        have h1 : ofR sc = sc • pb.basis i0 := by rw [pb.basis_eq_pow, pow_zero, Algebra.smul_def, mul_one]; rfl
        rw [h1, map_smul, pb.basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
          Finsupp.single_eq_of_ne (fun h => absurd (congrArg Fin.val h) (by simp [i0]; omega))]
      rw [hrhs_rep] at hrep
      exact (mul_eq_zero.mp hrep).resolve_left (Nat.cast_ne_zero.mpr (by have := hp.two_le; omega))
    change ofR r0 = x
    rw [hx_exp, Finset.sum_eq_single i0]
    · simp [r0, i0]
    · intro i _ hne
      rw [hcoeff_zero i (Nat.pos_of_ne_zero fun h => hne (Fin.ext h)), map_zero, zero_mul]
    · intro h; exact absurd (mem_univ _) h
  -- Step 2: `gs 1 * gs (l - 1) = p`
  have hprod_gs : gs 1 * gs (l - 1) = ofR (p : CycR l) := by
    dsimp [gs]; rw [sum_mul]; simp_rw [mul_sum]
    have hrew : ∑ a : (ZMod p)ˣ, ∑ b : (ZMod p)ˣ,
        (ofR (χ a ^ 1) * ξ ^ a.val.val) * (ofR (χ b ^ (l - 1)) * ξ ^ b.val.val) =
        ∑ u : (ZMod p)ˣ, ofR (χ u) * ∑ b : (ZMod p)ˣ, ξ ^ ((u.val + 1) * b.val).val := by
      rw [sum_comm]
      have hinner : ∀ b : (ZMod p)ˣ,
          ∑ a : (ZMod p)ˣ, (ofR (χ a ^ 1) * ξ ^ a.val.val) * (ofR (χ b ^ (l - 1)) * ξ ^ b.val.val) =
          ∑ u : (ZMod p)ˣ, ofR (χ u) * ξ ^ ((u.val + 1) * b.val).val := fun b => by
        refine Fintype.sum_equiv (Equiv.mulRight b⁻¹) _ _ fun a => ?_
        have hχab : χ a ^ 1 * χ b ^ (l - 1) = χ (a * b⁻¹) := by rw [pow_one, ← hχ_inv, hχ_mul]
        have hmul : (ofR (χ a ^ 1) * ξ ^ a.val.val) * (ofR (χ b ^ (l - 1)) * ξ ^ b.val.val) =
            ofR (χ (a * b⁻¹)) * ξ ^ (a.val.val + b.val.val) := by
          rw [← hχab, map_mul, pow_add]; ring
        rw [hmul, hξ_pow_mod]
        change ofR (χ (a * b⁻¹)) * ξ ^ ((a.val.val + b.val.val) % p) =
          ofR (χ (a * b⁻¹)) * ξ ^ (((a * b⁻¹).val + 1) * b.val).val
        congr 2
        have hz : ((a * b⁻¹).val + 1) * b.val = a.val + b.val := by
          have hb_inv : b⁻¹.val * b.val = 1 := by exact_mod_cast Units.inv_mul b
          rw [add_mul, one_mul, Units.val_mul, mul_assoc, hb_inv, mul_one]
        rw [hz, ZMod.val_add]
      simp_rw [hinner]; rw [sum_comm]
      exact sum_congr rfl fun u _ => (mul_sum ..).symm
    rw [hrew]
    have hsplit : ∑ u : (ZMod p)ˣ, ofR (χ u) * ∑ b : (ZMod p)ˣ, ξ ^ ((u.val + 1) * b.val).val =
        ofR (χ (-1)) * ((p - 1 : ℕ) : S) + ∑ u ∈ univ.erase (-1 : (ZMod p)ˣ), ofR (χ u) * (-1 : S) := by
      rw [← add_sum_erase _ _ (mem_univ (-1 : (ZMod p)ˣ))]
      congr 1
      · congr 1
        simp [ZMod.card_units_eq_totient, Nat.totient_prime hp]
      · refine sum_congr rfl fun u hu => ?_
        have hu_ne : u.val + 1 ≠ 0 := fun h0 =>
          (mem_erase.mp hu).1 (Units.ext (eq_neg_of_add_eq_zero_left h0))
        let w : (ZMod p)ˣ := Units.mk0 (u.val + 1) hu_ne
        congr 1
        have heq : ∑ b : (ZMod p)ˣ, ξ ^ ((u.val + 1) * b.val).val =
            ∑ b : (ZMod p)ˣ, ξ ^ (w * b).val.val := rfl
        rw [heq, Fintype.sum_equiv (Equiv.mulLeft w) (fun b => ξ ^ (w * b).val.val)
          (fun b => ξ ^ b.val.val) (fun _ => rfl), hξ_units_sum]
    rw [hsplit, hχ_neg_one, map_one, one_mul]
    have hsum_er : ∑ u ∈ univ.erase (-1 : (ZMod p)ˣ), ofR (χ u) = -1 := by
      have h0 : ∑ u : (ZMod p)ˣ, ofR (χ u) = 0 := by rw [← map_sum, hχ_sum_zero, map_zero]
      rw [← add_sum_erase _ _ (mem_univ (-1 : (ZMod p)ˣ)), hχ_neg_one, map_one] at h0
      exact eq_neg_of_add_eq_zero_right h0
    have hmul_neg : ∑ u ∈ univ.erase (-1 : (ZMod p)ˣ), ofR (χ u) * (-1 : S) = 1 := by
      rw [← sum_mul, hsum_er]; ring
    rw [hmul_neg, map_natCast, ← Nat.cast_one (R := S), ← Nat.cast_add, Nat.sub_add_cancel hp.one_lt.le]
  -- Galois action on `Φ`
  have hgal_S : ∀ σ : Gal(CycK l / ℚ),
      ofR (σ • Φ) = gs (IsCyclotomicExtension.Rat.galEquivZMod l (CycK l) σ).val.val ^ l := by
    intro σ
    let e := galRestrict ℤ ℚ (CycK l) (CycR l) σ
    let eS : S →+* S := AdjoinRoot.lift (ofR.comp e.toRingHom) ξ (by
      rw [← Polynomial.eval₂_map, Polynomial.map_cyclotomic]; exact AdjoinRoot.eval₂_root gP)
    have heS_of : ∀ r : CycR l, eS (ofR r) = ofR (σ • r) := fun r => by
      change AdjoinRoot.lift (ofR.comp e.toRingHom) ξ _ (AdjoinRoot.of gP r) = ofR (σ • r)
      rw [AdjoinRoot.lift_of]; exact congrArg ofR (galRestrict_eq_smul σ r)
    have heS_ξ : eS ξ = ξ := AdjoinRoot.lift_root _
    rw [← heS_of, hΦ_eq, map_pow]; congr 1
    dsimp [gs]; rw [map_sum]
    refine sum_congr rfl fun a _ => ?_
    rw [map_mul, heS_of, map_pow eS, heS_ξ, pow_one,
      IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq l (CycK l) σ (hχ_pow_l a)]
  -- Step 3: `Φ * σ_{-1}(Φ) = p^l`, hence `‖φ Φ‖^2 = p^l`
  let σneg : Gal(CycK l / ℚ) := (IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm (-1)
  have hσneg_val : (IsCyclotomicExtension.Rat.galEquivZMod l (CycK l) σneg).val.val = l - 1 := by
    simp only [σneg, MulEquiv.apply_symm_apply, Units.val_neg, Units.val_one]
    rw [zmod_val_neg_of_ne_zero (one_ne_zero : (1 : ZMod l) ≠ 0), ZMod.val_one]
  have hΦ_conj_mul : Φ * (σneg • Φ) = (p : CycR l) ^ l := by
    have hS : ofR (Φ * (σneg • Φ)) = ofR ((p : CycR l) ^ l) := by
      rw [map_mul, hΦ_eq, hgal_S σneg, hσneg_val, ← mul_pow, hprod_gs, map_pow]
    have hsub : ofR (Φ * (σneg • Φ) - (p : CycR l) ^ l) ∈ Ideal.map ofR (⊥ : Ideal (CycR l)) := by
      rw [map_sub, hS, sub_self]; exact Ideal.zero_mem _
    exact sub_eq_zero.mp (Ideal.mem_bot.mp ((of_mem_map_ideal_iff hgP_monic hgP_deg_pos ⊥ _).mp hsub))
  have hnorm_sq : ∀ φ : CycK l →+* ℂ, ‖φ (Φ : CycK l)‖ ^ 2 = (p : ℝ) ^ l := by
    intro φ
    have hmul : φ (Φ : CycK l) * star (φ (Φ : CycK l)) = ((p : ℂ) ^ l) := by
      rw [star_embedding_eq_smul_neg φ Φ, NumberField.RingOfIntegers.coe_eq_algebraMap,
        NumberField.RingOfIntegers.coe_eq_algebraMap, ← map_mul, ← map_mul, hΦ_conj_mul]
      simp
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hmul
    simpa [← Complex.ofReal_natCast, ← Complex.ofReal_pow] using congrArg Complex.re hmul
  -- Step 4: `Φ ≡ -1 (mod l R)`, hence `IsPrimary Φ`
  have hΦ_mod_l : (l : CycR l) ∣ (Φ + 1) := by
    let J : Ideal S := Ideal.map ofR (span {(l : CycR l)})
    have hl0 : (l : S ⧸ J) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
      rw [show (l : S) = ofR (l : CycR l) by simp]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton _))
    have hq_mem : ofR (Φ + 1) ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_add, map_one, hΦ_eq, map_add, map_one]
      dsimp [gs]
      rw [map_pow, map_sum, sum_pow_eq_of_natCast_eq_zero hl.out hl0]
      have hterm : ∀ a : (ZMod p)ˣ,
          (Ideal.Quotient.mk J (ofR (χ a ^ 1) * ξ ^ a.val.val)) ^ l =
            Ideal.Quotient.mk J (ξ ^ (l * a.val.val)) := fun a => by
        rw [← map_pow, mul_pow, pow_one, ← map_pow, hχ_pow_l, map_one, one_mul, ← pow_mul, mul_comm]
      rw [sum_congr rfl fun a _ => hterm a, ← map_sum]
      have hcop_l : (l : ZMod p) ≠ 0 := fun h0 =>
        hpl ((Nat.prime_dvd_prime_iff_eq hp hl.out).mp ((ZMod.natCast_eq_zero_iff l p).mp h0))
      let ul : (ZMod p)ˣ := Units.mk0 (l : ZMod p) hcop_l
      have hbi : ∑ a : (ZMod p)ˣ, ξ ^ (l * a.val.val) = -1 := by
        have hrew : ∀ a : (ZMod p)ˣ, ξ ^ (l * a.val.val) = ξ ^ (ul * a).val.val := fun a => by
          rw [hξ_pow_mod]; congr 1
          rw [Units.val_mul, ZMod.val_mul, show ul.val = (l : ZMod p) from rfl, ZMod.val_natCast, Nat.mod_mul_mod]
        rw [sum_congr rfl fun a _ => hrew a,
          Fintype.sum_equiv (Equiv.mulLeft ul) (fun a => ξ ^ (ul * a).val.val) (fun a => ξ ^ a.val.val) (fun _ => rfl),
          hξ_units_sum]
      rw [hbi, map_neg, map_one, neg_add_cancel]
    exact Ideal.mem_span_singleton.mp ((of_mem_map_ideal_iff hgP_monic hgP_deg_pos _ _).mp hq_mem)
  have hΦ_primary : IsPrimary Φ := by
    have hlam2 : lamR l ^ 2 ∣ (Φ - ((-1 : ℤ) : CycR l)) := by
      rw [show Φ - ((-1 : ℤ) : CycR l) = Φ + 1 by push_cast; ring]
      exact (lamR_pow_two_dvd_l hl2).trans hΦ_mod_l
    refine ⟨fun hd => ?_, ⟨-1, hlam2⟩⟩
    have h1 : lamR l ∣ (Φ + 1) := by
      have := (pow_dvd_pow (lamR l) (by decide : 1 ≤ 2)).trans ((lamR_pow_two_dvd_l hl2).trans hΦ_mod_l)
      simpa using this
    have hunit : IsUnit (lamR l) :=
      isUnit_of_dvd_one (by rw [show (1 : CycR l) = (Φ + 1) - Φ by ring]; exact dvd_sub h1 hd)
    exact ((zetaK_spec l).zeta_sub_one_prime').not_isUnit hunit
  -- Step 5: Stickelberger factorization
  have hstick : span {Φ} = ∏ t : (ZMod l)ˣ,
      (((IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm t)⁻¹ • 𝔭) ^ (l - t.val.val) := by
    let π : S := ξ - 1
    have hπ_pow : π ^ (p - 1) ∈ Ideal.map ofR 𝔭 := by
      have hpoly : gP.comp (X + 1) = ∑ k ∈ range p, C ((Nat.choose p (k + 1) : ℕ) : CycR l) * X ^ k := by
        have h1 : X * (gP.comp (X + 1)) = X * ∑ k ∈ range p, C ((Nat.choose p (k + 1) : ℕ) : CycR l) * X ^ k := by
          have hc := congrArg (fun q : (CycR l)[X] => q.comp (X + 1)) (Polynomial.cyclotomic_prime_mul_X_sub_one (CycR l) p)
          simp only [Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp,
            Polynomial.one_comp, add_sub_cancel_right] at hc
          change gP.comp (X + 1) * X = (X + 1) ^ p - 1 at hc
          rw [mul_comm, hc, add_pow, sum_range_succ']
          simp only [Nat.choose_zero_right, pow_zero, one_pow, mul_one, Nat.cast_one, add_sub_cancel_right,
            mul_sum]
          refine sum_congr rfl fun k _ => by rw [pow_succ', map_natCast]; ring
        exact mul_left_cancel₀ Polynomial.X_ne_zero h1
      have heval : ∑ k ∈ range p, ofR ((Nat.choose p (k + 1) : ℕ) : CycR l) * π ^ k = 0 := by
        have h0 := congrArg (Polynomial.aeval π) hpoly
        have hlhs : Polynomial.aeval π (gP.comp (X + 1)) = 0 := by
          rw [Polynomial.aeval_comp, map_add, aeval_X, map_one, show π + 1 = ξ by simp [π]]; exact hξ_root
        rw [hlhs] at h0; simpa [map_sum, map_mul, map_pow, ofR] using h0.symm
      rw [show range p = insert (p - 1) (range (p - 1)) by
          rw [← Finset.range_add_one, Nat.sub_add_cancel hp.one_lt.le],
        sum_insert (by simp), Nat.sub_add_cancel hp.one_lt.le, Nat.choose_self, Nat.cast_one,
        map_one, one_mul] at heval
      rw [eq_neg_of_add_eq_zero_left heval]
      refine Submodule.neg_mem _ (Ideal.sum_mem _ fun k hk => ?_)
      have hk_lt : k < p - 1 := mem_range.mp hk
      obtain ⟨c, hc⟩ := hp.dvd_choose_self (by omega : k + 1 ≠ 0) (by omega : k + 1 < p)
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (by
        rw [hc, Nat.cast_mul]; exact 𝔭.mul_mem_right _ hp_in_𝔭))
    have hdiv_each : ∀ t : (ZMod l)ˣ,
        (((IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm t)⁻¹ • 𝔭) ^ (l - t.val.val) ∣ span {Φ} := by
      intro t
      let σ : Gal(CycK l / ℚ) := (IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm t
      have ht_val : (IsCyclotomicExtension.Rat.galEquivZMod l (CycK l) σ).val.val = t.val.val := by
        dsimp [σ]; rw [MulEquiv.apply_symm_apply]
      have ht_pos : 0 < t.val.val := Nat.pos_of_ne_zero fun h0 => t.ne_zero (by
        have := ZMod.natCast_zmod_val t.val; rw [h0, Nat.cast_zero] at this; exact this.symm)
      have ht_lt : t.val.val < l := ZMod.val_lt t.val
      set u : ℕ := l - t.val.val
      set m : ℕ := (p - 1) / l
      have hml : m * l = p - 1 := Nat.div_mul_cancel hl_dvd_p1
      have hm_pos : 0 < m := Nat.pos_of_ne_zero fun h0 => by
        rw [h0, zero_mul] at hml; have := hp.two_le; omega
      have hgs_decomp : ∃ a0 ∈ Ideal.map ofR 𝔭, ∃ y : S, gs t.val.val = a0 + π ^ (m * u) * y := by
        let S1 : S := ∑ a ∈ Ico 1 p, ofR (((a ^ (m * t.val.val) : ℕ) : CycR l)) * ξ ^ a
        have hdiff_mem : gs t.val.val - S1 ∈ Ideal.map ofR 𝔭 := by
          have hS1_units : S1 = ∑ a : (ZMod p)ˣ, ofR (((a.val.val ^ (m * t.val.val) : ℕ) : CycR l)) * ξ ^ a.val.val := by
            symm
            refine Finset.sum_bij (fun (a : (ZMod p)ˣ) _ => a.val.val)
              (fun a _ => mem_Ico.mpr ⟨Nat.pos_of_ne_zero fun h0 => a.ne_zero (by
                have := ZMod.natCast_zmod_val a.val; rw [h0, Nat.cast_zero] at this; exact this.symm),
                ZMod.val_lt a.val⟩)
              (fun a _ b _ h => Units.ext (ZMod.val_injective p h))
              (fun n hn => ?_) (fun _ _ => rfl)
            obtain ⟨hn1, hnp⟩ := mem_Ico.mp hn
            have hne : (n : ZMod p) ≠ 0 := fun h0 =>
              absurd (Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff n p).mp h0)) (by omega)
            exact ⟨Units.mk0 (n : ZMod p) hne, mem_univ _, by simp [Units.mk0, ZMod.val_natCast_of_lt hnp]⟩
          change (∑ a : (ZMod p)ˣ, ofR (χ a ^ t.val.val) * ξ ^ a.val.val) - S1 ∈ Ideal.map ofR 𝔭
          rw [hS1_units, ← sum_sub_distrib]
          refine Ideal.sum_mem _ fun a _ => ?_
          rw [← sub_mul, ← map_sub]
          refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, (powResSymb_spec hbot hlam (ha_not_mem a)).2,
            hnorm, ← pow_mul, Nat.cast_pow, map_pow, sub_self]
        have hS1_exp : S1 = ∑ k ∈ range p,
            ofR (((∑ a ∈ Ico 1 p, a ^ (m * t.val.val) * Nat.choose a k : ℕ) : CycR l)) * π ^ k := by
          dsimp [S1]
          have hξ1 : ∀ a ∈ Ico 1 p, ξ ^ a = ∑ k ∈ range p, ofR ((Nat.choose a k : ℕ) : CycR l) * π ^ k := by
            intro a ha
            have hap : a < p := (mem_Ico.mp ha).2
            rw [show ξ = π + 1 by simp [π], add_pow]
            rw [← sum_subset (range_mono (Nat.succ_le_of_lt hap)) (fun k _ hk => by
              have : a < k := by simp only [mem_range] at hk; omega
              rw [Nat.choose_eq_zero_of_lt this, Nat.cast_zero, map_zero, zero_mul])]
            exact sum_congr rfl fun k _ => by rw [one_pow, mul_one, mul_comm, map_natCast]
          have hstep : ∑ a ∈ Ico 1 p, ofR (((a ^ (m * t.val.val) : ℕ) : CycR l)) * ξ ^ a =
              ∑ a ∈ Ico 1 p, ∑ k ∈ range p,
                ofR (((a ^ (m * t.val.val) * Nat.choose a k : ℕ) : CycR l)) * π ^ k := by
            refine sum_congr rfl fun a ha => ?_
            rw [hξ1 a ha, mul_sum]
            exact sum_congr rfl fun k _ => by rw [← mul_assoc, ← map_mul, Nat.cast_mul]
          rw [hstep, sum_comm]
          exact sum_congr rfl fun k _ => by rw [← sum_mul, ← map_sum, Nat.cast_sum]
        have hmu_lt : m * u < p := by
          have : m * u < m * l := Nat.mul_lt_mul_of_pos_left (by omega) hm_pos
          omega
        have hS1_split : S1 =
            (∑ k ∈ range (m * u), ofR (((∑ a ∈ Ico 1 p, a ^ (m * t.val.val) * Nat.choose a k : ℕ) : CycR l)) * π ^ k) +
            π ^ (m * u) * (∑ k ∈ Ico (m * u) p,
              ofR (((∑ a ∈ Ico 1 p, a ^ (m * t.val.val) * Nat.choose a k : ℕ) : CycR l)) * π ^ (k - m * u)) := by
          rw [hS1_exp, ← sum_range_add_sum_Ico _ hmu_lt.le, mul_sum]
          congr 1
          exact sum_congr rfl fun k hk => by
            rw [← mul_assoc, mul_comm (π ^ (m * u)), mul_assoc, ← pow_add, Nat.add_sub_of_le (mem_Ico.mp hk).1]
        have hlo_mem : ∑ k ∈ range (m * u),
            ofR (((∑ a ∈ Ico 1 p, a ^ (m * t.val.val) * Nat.choose a k : ℕ) : CycR l)) * π ^ k ∈
            Ideal.map ofR 𝔭 := by
          refine Ideal.sum_mem _ fun k hk => ?_
          have hsum_tu : m * t.val.val + m * u = p - 1 := by
            rw [← mul_add, show t.val.val + u = l by omega, hml]
          have hdk : m * t.val.val + k < p - 1 := by have := mem_range.mp hk; omega
          obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff _ p).mp
            (sum_pow_mul_choose_zmod_eq_zero (p := p) (d := m * t.val.val) (k := k) (Nat.mul_pos hm_pos ht_pos) hdk)
          exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (by
            rw [hc, Nat.cast_mul]; exact 𝔭.mul_mem_right _ hp_in_𝔭))
        exact ⟨(gs t.val.val - S1) + _, Ideal.add_mem _ hdiff_mem hlo_mem, _, by
          rw [add_assoc, ← hS1_split, sub_add_cancel]⟩
      obtain ⟨a0, ha0, y, hgs_eq⟩ := hgs_decomp
      have hpow_mem : gs t.val.val ^ l ∈ Ideal.map ofR (𝔭 ^ u) := by
        rw [hgs_eq, add_pow]
        refine Ideal.sum_mem _ fun j hj => ?_
        have hjle : j ≤ l := Nat.lt_succ_iff.mp (mem_range.mp hj)
        let qj : ℕ := (u * (l - j)) / l
        have hqj_ge : u ≤ j + qj := by
          have h1 : l * (j + qj) + (u * (l - j)) % l = l * j + u * (l - j) := by
            rw [mul_add, add_assoc, Nat.div_add_mod]
          have hu_le : u ≤ l := Nat.sub_le _ _
          have h2 : l * u ≤ l * j + u * (l - j) := by zify [hjle]; nlinarith
          have h3 : (u * (l - j)) % l < l := Nat.mod_lt _ hl.out.pos
          by_contra hlt; push Not at hlt
          have h4 : l * (j + qj) + (u * (l - j)) % l < l * u := by
            have : j + qj + 1 ≤ u := hlt
            have : l * (j + qj) + l ≤ l * u := by
              rw [show l * (j + qj) + l = l * (j + qj + 1) by ring]
              exact Nat.mul_le_mul_left l this
            omega
          omega
        have ha0_j : a0 ^ j ∈ Ideal.map ofR (𝔭 ^ j) := by rw [Ideal.map_pow]; exact Ideal.pow_mem_pow ha0 j
        have hpi_exp : qj * (p - 1) ≤ m * u * (l - j) := by
          rw [← hml, show qj * (m * l) = m * (qj * l) by ring, mul_assoc]
          exact Nat.mul_le_mul_left m (Nat.div_mul_le_self _ l)
        have hpi_qj : (π ^ (m * u) * y) ^ (l - j) ∈ Ideal.map ofR (𝔭 ^ qj) := by
          rw [mul_pow, ← pow_mul, Ideal.map_pow]
          have h1 : π ^ (m * u * (l - j)) = (π ^ (p - 1)) ^ qj * π ^ (m * u * (l - j) - qj * (p - 1)) := by
            rw [← pow_mul, mul_comm (p - 1), ← pow_add, Nat.add_sub_of_le hpi_exp]
          rw [h1]
          exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπ_pow qj))
        have hmul_mem : a0 ^ j * (π ^ (m * u) * y) ^ (l - j) ∈ Ideal.map ofR (𝔭 ^ (j + qj)) := by
          rw [pow_add, Ideal.map_mul]; exact Ideal.mul_mem_mul ha0_j hpi_qj
        exact Ideal.mul_mem_right _ _ (Ideal.map_mono (Ideal.pow_le_pow_right hqj_ge) hmul_mem)
      rw [← ht_val, ← hgal_S σ] at hpow_mem
      have hσΦ_mem : σ • Φ ∈ 𝔭 ^ u := (of_mem_map_ideal_iff hgP_monic hgP_deg_pos (𝔭 ^ u) (σ • Φ)).mp hpow_mem
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, ← galois_smul_pow_ideal,
        Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv]
      exact hσΦ_mem
    have h𝔭_lies : 𝔭.LiesOver (Ideal.span {(p : ℤ)}) := by
      rw [Ideal.liesOver_iff]
      refine (Int.ideal_span_isMaximal_of_prime p).eq_of_le (h𝔭.comap _).ne_top ?_
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, algebraMap_int_eq, map_natCast]; exact hp_in_𝔭
    have hcop_pl : p.Coprime l := hp.coprime_iff_not_dvd.mpr fun hd =>
      hpl ((Nat.prime_dvd_prime_iff_eq hp hl.out).mp hd)
    have hstab_triv : ∀ σ : Gal(CycK l / ℚ), σ • 𝔭 = 𝔭 → σ = 1 := by
      intro σ hσ
      have hmem := IsCyclotomicExtension.Rat.mem_zpowers_galEquivZMod_of_mem_stabilizer
        l (CycK l) p 𝔭 hcop_pl hσ
      have hp1 : ZMod.unitOfCoprime p hcop_pl = 1 := by
        apply Units.ext; rw [ZMod.coe_unitOfCoprime, Units.val_one]
        obtain ⟨k, hk⟩ := hl_dvd_p1
        have hp_eq : p = l * k + 1 := by have := hp.one_lt; omega
        have hmod : p ≡ 1 [MOD l] := by
          rw [Nat.ModEq, hp_eq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
        simpa using (ZMod.natCast_eq_natCast_iff p 1 l).mpr hmod
      rw [hp1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hmem
      exact (IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).injective (by simpa using hmem)
    have hpair_cop : Pairwise fun t1 t2 : (ZMod l)ˣ =>
        IsCoprime ((((IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm t1)⁻¹ • 𝔭) ^ (l - t1.val.val))
          ((((IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm t2)⁻¹ • 𝔭) ^ (l - t2.val.val)) := by
      intro t1 t2 hne; apply IsCoprime.pow
      let σ1 := ((IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm t1)⁻¹
      let σ2 := ((IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm t2)⁻¹
      have hmax1 : (σ1 • 𝔭).IsMaximal := by
        rw [galois_smul_ideal_eq_map]; exact Ideal.map_isMaximal_of_equiv (galRestrict ℤ ℚ (CycK l) (CycR l) σ1).toRingEquiv
      have hmax2 : (σ2 • 𝔭).IsMaximal := by
        rw [galois_smul_ideal_eq_map]; exact Ideal.map_isMaximal_of_equiv (galRestrict ℤ ℚ (CycK l) (CycR l) σ2).toRingEquiv
      have hneq_id : σ1 • 𝔭 ≠ σ2 • 𝔭 := fun heq => by
        have h2 := hstab_triv (σ2⁻¹ * σ1) (by rw [mul_smul, heq, inv_smul_smul])
        have h3 : σ2 = σ1 := eq_of_inv_mul_eq_one h2
        exact hne ((IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm.injective (inv_injective h3.symm))
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hnt
      exact hneq_id ((hmax1.eq_of_le hnt le_sup_left).trans (hmax2.eq_of_le hnt le_sup_right).symm)
    have hprod_dvd : (∏ t : (ZMod l)ˣ,
        (((IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm t)⁻¹ • 𝔭) ^ (l - t.val.val)) ∣ span {Φ} :=
      Finset.prod_dvd_of_coprime (fun t1 _ t2 _ hne => hpair_cop hne) (fun t _ => hdiv_each t)
    have hnorm_Φ : Ideal.absNorm (span {Φ}) = p ^ (l * (l - 1) / 2) := by
      have hconj_norm : Ideal.absNorm (span {σneg • Φ}) = Ideal.absNorm (span {Φ}) := by
        rw [← galois_smul_span_singleton, galois_smul_absNorm]
      have hsq : Ideal.absNorm (span {Φ}) ^ 2 = (p ^ (l * (l - 1) / 2)) ^ 2 := by
        calc Ideal.absNorm (span {Φ}) ^ 2
            = Ideal.absNorm (span {Φ}) * Ideal.absNorm (span {σneg • Φ}) := by rw [sq, hconj_norm]
          _ = Ideal.absNorm (span {Φ * (σneg • Φ)}) := by rw [← map_mul, Ideal.span_singleton_mul_span_singleton]
          _ = Ideal.absNorm (span {(p : CycR l)} ^ l) := by rw [hΦ_conj_mul, Ideal.span_singleton_pow]
          _ = (p ^ (l - 1)) ^ l := by
              rw [map_pow, Ideal.absNorm_span_natCast, (zetaK_spec l).integralPowerBasis.finrank,
                (zetaK_spec l).integralPowerBasis_dim, Nat.totient_prime hl.out]
          _ = (p ^ (l * (l - 1) / 2)) ^ 2 := by
              rw [← pow_mul, ← pow_mul]
              congr 1
              have heven : 2 ∣ l * (l - 1) := by
                obtain ⟨k, hk⟩ := hl.out.odd_of_ne_two hl2
                refine ⟨l * k, ?_⟩
                have hl1 : l - 1 = 2 * k := by omega
                rw [hl1]; ring
              rw [Nat.div_mul_cancel heven, mul_comm]
      exact Nat.pow_left_injective (by decide : 2 ≠ 0) hsq
    have hnorm_prod : Ideal.absNorm (∏ t : (ZMod l)ˣ,
        (((IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm t)⁻¹ • 𝔭) ^ (l - t.val.val)) =
        p ^ (l * (l - 1) / 2) := by
      rw [map_prod]
      have hfac : ∀ t : (ZMod l)ˣ,
          Ideal.absNorm ((((IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm t)⁻¹ • 𝔭) ^ (l - t.val.val)) =
            p ^ (l - t.val.val) := fun t => by rw [map_pow, galois_smul_absNorm, hnorm]
      rw [prod_congr rfl fun t _ => hfac t, prod_pow_eq_pow_sum]
      congr 1
      have hsum : ∑ t : (ZMod l)ˣ, (l - t.val.val) = ∑ i ∈ Ico 1 l, i := by
        refine Finset.sum_bij (fun (t : (ZMod l)ˣ) _ => l - t.val.val)
          (fun t _ => by
            have ht0 : 0 < t.val.val := Nat.pos_of_ne_zero fun h0 => t.ne_zero (by
              have := ZMod.natCast_zmod_val t.val; rw [h0, Nat.cast_zero] at this; exact this.symm)
            have htl : t.val.val < l := ZMod.val_lt t.val
            exact mem_Ico.mpr ⟨by omega, by omega⟩)
          (fun t1 _ t2 _ h => by
            have h1 := ZMod.val_lt t1.val; have h2 := ZMod.val_lt t2.val
            exact Units.ext (ZMod.val_injective l (by omega)))
          (fun n hn => ?_) (fun _ _ => rfl)
        obtain ⟨hn1, hnl⟩ := mem_Ico.mp hn
        have hne : ((l - n : ℕ) : ZMod l) ≠ 0 := fun h0 =>
          absurd (Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff _ l).mp h0)) (by omega)
        refine ⟨Units.mk0 ((l - n : ℕ) : ZMod l) hne, mem_univ _, ?_⟩
        simp only [Units.mk0, ZMod.val_natCast_of_lt (by omega : l - n < l)]; omega
      rw [hsum]
      have htri : ∑ i ∈ Ico 1 l, i = ∑ i ∈ range l, i := by
        have hl_pos := hl.out.pos
        rw [show range l = insert 0 (Ico 1 l) by ext i; simp only [mem_range, mem_insert, mem_Ico]; omega,
          sum_insert (by simp), zero_add]
      rw [htri, Finset.sum_range_id]
    obtain ⟨J, hJ⟩ := hprod_dvd
    have hnormJ : Ideal.absNorm J = 1 := by
      have h := congrArg Ideal.absNorm hJ
      rw [map_mul, hnorm_Φ, hnorm_prod] at h
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) (by simpa using h.symm)
    have hJ1 : J = 1 := by rw [Ideal.one_eq_top]; exact Ideal.absNorm_eq_one_iff.mp hnormJ
    rw [hJ, hJ1, mul_one]
  -- Step 6: Frobenius evaluation `powResIdeal Φ (span {q}) = powResSymb q 𝔭`
  have hfrob : ∀ q : ℕ, q.Prime → q ≠ l → q ≠ p →
      powResIdeal Φ (span {(q : CycR l)}) = powResSymb (q : CycR l) 𝔭 := by
    intro q hq hql hqp
    have : Fact q.Prime := ⟨hq⟩
    have hq_ne : (span {(q : CycR l)}) ≠ ⊥ := by simp [hq.ne_zero]
    have hq_not_𝔭 : (q : CycR l) ∉ 𝔭 := by
      intro hm
      have hcop : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr fun hd =>
        hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd).symm
      have hbez := Nat.gcd_eq_gcd_ab p q; rw [hcop.gcd_eq_one] at hbez
      have h1 : (1 : CycR l) ∈ 𝔭 := by
        have hc : (1 : CycR l) = (p : CycR l) * (Nat.gcdA p q : CycR l) +
            (q : CycR l) * (Nat.gcdB p q : CycR l) := by
          have := congrArg (Int.cast (R := CycR l)) hbez; push_cast at this; exact this
        rw [hc]; exact 𝔭.add_mem (𝔭.mul_mem_right _ hp_in_𝔭) (𝔭.mul_mem_right _ hm)
      exact h𝔭.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 h1 isUnit_one)
    have hper_𝔮 : ∀ 𝔮 ∈ UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)}),
        powResSymb Φ 𝔮 = powResSymb (q : CycR l) 𝔭 ^ ((l - 1) * Ideal.inertiaDeg 𝔮 ℤ) := by
      intro 𝔮 h𝔮
      obtain ⟨h𝔮_pr, h𝔮_bot, h𝔮_le⟩ := mem_normalizedFactors_prime h𝔮
      have : 𝔮.IsPrime := h𝔮_pr
      have : 𝔮.IsMaximal := h𝔮_pr.isMaximal h𝔮_bot
      have hq_in_𝔮 : (q : CycR l) ∈ 𝔮 := h𝔮_le (Ideal.subset_span (Set.mem_singleton _))
      have : 𝔮.LiesOver (Ideal.span {(q : ℤ)}) := by
        rw [Ideal.liesOver_iff]
        refine (Int.ideal_span_isMaximal_of_prime q).eq_of_le (h𝔮_pr.comap _).ne_top ?_
        rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, algebraMap_int_eq, map_natCast]; exact hq_in_𝔮
      set f : ℕ := Ideal.inertiaDeg 𝔮 ℤ
      have hN𝔮 : Ideal.absNorm 𝔮 = q ^ f := (Ideal.pow_inertiaDeg q 𝔮).symm
      have hf_pos : 0 < f := by
        by_contra h0; push Not at h0
        have : f = 0 := by omega
        rw [this, pow_zero] at hN𝔮
        exact h𝔮_pr.ne_top (Ideal.absNorm_eq_one_iff.mp hN𝔮)
      have hlam_𝔮 : lamR l ∉ 𝔮 := by
        intro hm
        have hdvd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hm)
        rw [absNorm_span_lamR, hN𝔮] at hdvd
        exact hql ((Nat.prime_dvd_prime_iff_eq hq hl.out).mp ((dvd_pow_self q hf_pos.ne').trans hdvd))
      have hp_not_𝔮 : (p : CycR l) ∉ 𝔮 := by
        intro hm
        have hcop : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr fun hd =>
          hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd).symm
        have hbez := Nat.gcd_eq_gcd_ab p q; rw [hcop.gcd_eq_one] at hbez
        have h1 : (1 : CycR l) ∈ 𝔮 := by
          have hc : (1 : CycR l) = (p : CycR l) * (Nat.gcdA p q : CycR l) +
              (q : CycR l) * (Nat.gcdB p q : CycR l) := by
            have := congrArg (Int.cast (R := CycR l)) hbez; push_cast at this; exact this
          rw [hc]; exact 𝔮.add_mem (𝔮.mul_mem_right _ hm) (𝔮.mul_mem_right _ hq_in_𝔮)
        exact h𝔮_pr.ne_top (Ideal.eq_top_of_isUnit_mem 𝔮 h1 isUnit_one)
      have hΦ_not_𝔮 : Φ ∉ 𝔮 := fun hm =>
        hp_not_𝔮 (h𝔮_pr.mem_of_pow_mem l (by rw [← hΦ_conj_mul]; exact 𝔮.mul_mem_right _ hm))
      have hdvd_qf : l ∣ (q ^ f - 1) := hN𝔮 ▸ dvd_absNorm_sub_one h𝔮_bot hlam_𝔮
      have hqf_mod : q ^ f ≡ 1 [MOD l] := by
        obtain ⟨k, hk⟩ := hdvd_qf
        have h1 : 1 ≤ q ^ f := Nat.one_le_pow f q hq.pos
        have hqf_eq : q ^ f = l * k + 1 := by omega
        rw [Nat.ModEq, hqf_eq, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
      let J𝔮 : Ideal S := Ideal.map ofR 𝔮
      have hq0_J : (q : S ⧸ J𝔮) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk J𝔮), Ideal.Quotient.eq_zero_iff_mem,
          show (q : S) = ofR (q : CycR l) by simp]
        exact Ideal.mem_map_of_mem _ hq_in_𝔮
      have hcop_qp : ((q : ℕ) : ZMod p) ≠ 0 := fun h0 =>
        hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp ((ZMod.natCast_eq_zero_iff q p).mp h0)).symm
      let uq : (ZMod p)ˣ := Units.mk0 ((q : ℕ) : ZMod p) hcop_qp
      have hχ_uq : χ uq = powResSymb (q : CycR l) 𝔭 := by
        change powResSymb ((uq.val.val : ℕ) : CycR l) 𝔭 = powResSymb (q : CycR l) 𝔭
        have hsub : ((uq.val.val : ℕ) : CycR l) - (q : CycR l) ∈ 𝔭 := by
          have hmod : (uq.val.val : ℤ) ≡ (q : ℤ) [ZMOD p] := by
            rw [← ZMod.intCast_eq_intCast_iff]; push_cast; simp [uq]
          obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod.symm
          have heq : ((uq.val.val : ℕ) : CycR l) - (q : CycR l) = (p : CycR l) * (k : CycR l) := by
            have := congrArg (Int.cast (R := CycR l)) hk; push_cast at this; exact this
          rw [heq]; exact 𝔭.mul_mem_right _ hp_in_𝔭
        exact powResSymb_congr hbot hlam (ha_not_mem uq) hsub
      have hfrob_gs : Ideal.Quotient.mk J𝔮 (gs 1 ^ (q ^ f)) =
          Ideal.Quotient.mk J𝔮 (ofR (χ (uq ^ f)⁻¹) * gs 1) := by
        have hsum_qf : ∀ (n : ℕ) (s : Finset (ZMod p)ˣ) (fn : (ZMod p)ˣ → S ⧸ J𝔮),
            (∑ a ∈ s, fn a) ^ (q ^ n) = ∑ a ∈ s, (fn a) ^ (q ^ n) := fun n s fn => by
          induction n with
          | zero => simp
          | succ r ih =>
            rw [pow_succ, pow_mul, ih, sum_pow_eq_of_natCast_eq_zero hq hq0_J]
            exact sum_congr rfl fun a _ => by rw [← pow_mul]
        dsimp [gs]; rw [map_pow, map_sum, hsum_qf]
        have hterm : ∀ a : (ZMod p)ˣ,
            (Ideal.Quotient.mk J𝔮 (ofR (χ a ^ 1) * ξ ^ a.val.val)) ^ (q ^ f) =
              Ideal.Quotient.mk J𝔮 (ofR (χ a) * ξ ^ (uq ^ f * a).val.val) := fun a => by
          rw [← map_pow, mul_pow, pow_one, ← map_pow, ← pow_mul]
          have hχqf : χ a ^ (q ^ f) = χ a := by
            obtain ⟨⟨k, _, hk⟩, _⟩ := powResSymb_spec hbot hlam (ha_not_mem a)
            change powResSymb ((a.val.val : ℕ) : CycR l) 𝔭 ^ (q ^ f) = powResSymb ((a.val.val : ℕ) : CycR l) 𝔭
            rw [hk, ← pow_mul]
            simpa [mul_one] using (primRoot_pow_eq_pow_iff_modEq (zetaR_spec l) hl.out.ne_zero).mpr
              (Nat.ModEq.mul_left k hqf_mod)
          rw [hχqf, hξ_pow_mod]; congr 3
          rw [Units.val_mul, ZMod.val_mul, Units.val_pow_eq_pow_val, show uq.val = (q : ZMod p) from rfl,
            ← Nat.cast_pow, ZMod.val_natCast, Nat.mul_comm, Nat.mod_mul_mod]
        rw [sum_congr rfl fun a _ => hterm a, ← map_sum, mul_sum]; congr 1
        refine Fintype.sum_equiv (Equiv.mulLeft (uq ^ f)) _ _ fun a => ?_
        change ofR (χ a) * ξ ^ (uq ^ f * a).val.val =
          ofR (χ (uq ^ f)⁻¹) * (ofR (χ (uq ^ f * a) ^ 1) * ξ ^ (uq ^ f * a).val.val)
        rw [pow_one, ← mul_assoc, ← map_mul, ← hχ_mul, inv_mul_cancel_left]
      have hpow_split : gs 1 ^ (q ^ f) = ofR (Φ ^ ((q ^ f - 1) / l)) * gs 1 := by
        rw [map_pow, hΦ_eq, ← pow_mul, Nat.mul_div_cancel' hdvd_qf, ← pow_succ,
          Nat.sub_add_cancel (Nat.one_le_pow f q hq.pos)]
      have hmul_p : ofR ((p : CycR l) * (Φ ^ ((q ^ f - 1) / l) - χ (uq ^ f)⁻¹)) ∈ J𝔮 := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        have h1 := congrArg (· * Ideal.Quotient.mk J𝔮 (gs (l - 1))) hfrob_gs
        rw [hpow_split, map_mul, mul_assoc, ← map_mul, hprod_gs, map_mul, mul_assoc,
          ← map_mul (Ideal.Quotient.mk J𝔮) (gs 1), hprod_gs] at h1
        have h2 : Ideal.Quotient.mk J𝔮 (ofR (Φ ^ ((q ^ f - 1) / l)) * ofR (p : CycR l)) -
            Ideal.Quotient.mk J𝔮 (ofR (χ (uq ^ f)⁻¹) * ofR (p : CycR l)) = 0 := sub_eq_zero.mpr h1
        simpa [map_mul, map_sub, mul_sub, mul_comm] using h2
      have hdiff_𝔮 : Φ ^ ((q ^ f - 1) / l) - χ (uq ^ f)⁻¹ ∈ 𝔮 :=
        (h𝔮_pr.mem_or_mem ((of_mem_map_ideal_iff hgP_monic hgP_deg_pos 𝔮 _).mp hmul_p)).resolve_left hp_not_𝔮
      have hχ_uqf : χ (uq ^ f)⁻¹ = powResSymb (q : CycR l) 𝔭 ^ ((l - 1) * f) := by
        have hpow_χ : ∀ n : ℕ, χ (uq ^ n) = χ uq ^ n := fun n => by
          induction n with | zero => simp [hχ_one] | succ n ih => rw [pow_succ, pow_succ, hχ_mul, ih]
        rw [hχ_inv, hpow_χ, hχ_uq, ← pow_mul, mul_comm]
      rw [hχ_uqf] at hdiff_𝔮
      obtain ⟨⟨k, _, hk⟩, _⟩ := powResSymb_spec hbot hlam hq_not_𝔭
      rw [hk, ← pow_mul, powResSymb_eq_pow_iff h𝔮_bot hlam_𝔮 hΦ_not_𝔮, hN𝔮, ← map_pow]
      symm; rw [Ideal.Quotient.eq]; simpa [hk, ← pow_mul] using hdiff_𝔮
    unfold powResIdeal
    rw [Multiset.map_congr rfl fun 𝔮 h𝔮 => hper_𝔮 𝔮 h𝔮]
    have hprod_pow : ∀ (m : Multiset (Ideal (CycR l))) (x : CycR l),
        (m.map (fun 𝔮 => x ^ ((l - 1) * Ideal.inertiaDeg 𝔮 ℤ))).prod =
          x ^ ((l - 1) * (m.map (fun 𝔮 => Ideal.inertiaDeg 𝔮 ℤ)).sum) := fun m x => by
      refine Multiset.induction_on m (by simp) fun a s ih => by simp [ih, mul_add, pow_add]
    rw [hprod_pow]
    have hsum_f : ((UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)})).map
        (fun 𝔮 => Ideal.inertiaDeg 𝔮 ℤ)).sum = l - 1 := by
      have habs_q : Ideal.absNorm (span {(q : CycR l)}) = q ^ (l - 1) := by
        rw [Ideal.absNorm_span_natCast, (zetaK_spec l).integralPowerBasis.finrank,
          (zetaK_spec l).integralPowerBasis_dim, Nat.totient_prime hl.out]
      have habs_fac : Ideal.absNorm (span {(q : CycR l)}) =
          q ^ ((UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)})).map
            (fun 𝔮 => Ideal.inertiaDeg 𝔮 ℤ)).sum := by
        conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hq_ne]
        rw [map_multiset_prod]
        have hmap_n : (UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)})).map Ideal.absNorm =
            (UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)})).map
              (fun 𝔮 => q ^ Ideal.inertiaDeg 𝔮 ℤ) := by
          refine Multiset.map_congr rfl fun 𝔮 h𝔮 => ?_
          obtain ⟨hpr, hbot', hle⟩ := mem_normalizedFactors_prime h𝔮
          have : 𝔮.IsPrime := hpr; have : 𝔮.IsMaximal := hpr.isMaximal hbot'
          have : 𝔮.LiesOver (Ideal.span {(q : ℤ)}) := by
            rw [Ideal.liesOver_iff]
            refine (Int.ideal_span_isMaximal_of_prime q).eq_of_le (hpr.comap _).ne_top ?_
            rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, algebraMap_int_eq, map_natCast]
            exact hle (Ideal.subset_span (Set.mem_singleton _))
          exact (Ideal.pow_inertiaDeg q 𝔮).symm
        rw [hmap_n]
        have hprod_p : ∀ m : Multiset (Ideal (CycR l)),
            (m.map (fun 𝔮 => q ^ Ideal.inertiaDeg 𝔮 ℤ)).prod =
              q ^ (m.map (fun 𝔮 => Ideal.inertiaDeg 𝔮 ℤ)).sum := fun m => by
          refine Multiset.induction_on m (by simp) fun a s ih => by simp [ih, pow_add]
        exact hprod_p _
      rw [habs_q] at habs_fac
      exact (Nat.pow_right_injective hq.one_lt habs_fac).symm
    rw [hsum_f]
    obtain ⟨⟨k, _, hk⟩, _⟩ := powResSymb_spec hbot hlam hq_not_𝔭
    rw [hk, ← pow_mul]
    have hmod1 : (l - 1) * (l - 1) ≡ 1 [MOD l] := by
      have h1 : (l - 1) * (l - 1) = l * (l - 2) + 1 := by
        have := hl.out.two_le; zify [show 1 ≤ l by omega, show 2 ≤ l by omega]; ring
      rw [Nat.ModEq, h1, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
    simpa [mul_one] using (primRoot_pow_eq_pow_iff_modEq (zetaR_spec l) hl.out.ne_zero).mpr
      (Nat.ModEq.mul_left k hmod1)
  exact ⟨Φ, hΦ_primary, hnorm_sq, hstick, hfrob⟩

end GaussSumAndStickelberger

section EisensteinReciprocity

variable {l : ℕ} [hl : Fact l.Prime]

set_option maxHeartbeats 1200000 in
/-- Eisenstein Reciprocity for a primary element `α ∈ ℤ[ζ_l]` (`l` odd prime) whose ideal factors
    exclusively into degree-1 prime ideals coprime to `l * q` (`q` prime, `q ≠ l`). -/
theorem eisenstein_reciprocity_deg1 (hl2 : l ≠ 2) {q : ℕ} (hq : q.Prime) (hql : q ≠ l)
    {α : CycR l} (hα_prim : IsPrimary α)
    (hα_cop_q : IsCoprime (span {α}) (span {(q : CycR l)}))
    (hdeg1 : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors (span {α}),
      (Ideal.absNorm 𝔭).Prime ∧ Ideal.absNorm 𝔭 ≠ l) :
    powResIdeal (q : CycR l) (span {α}) = powResIdeal α (span {(q : CycR l)}) := by
  have hα_ne0 : α ≠ 0 := fun h0 => hα_prim.1 (by simp [h0])
  have hα_bot : span {α} ≠ ⊥ := by simp [hα_ne0]
  have hlam_cop_q := isCoprime_lamR_span_prime hq hql
  let fac := UniqueFactorizationMonoid.normalizedFactors (span {α})
  have hfac_spec : ∀ 𝔭 ∈ fac,
      ∃ Φ : CycR l,
        IsPrimary Φ ∧
        (∀ φ : CycK l →+* ℂ, ‖φ (Φ : CycK l)‖ ^ 2 = (Ideal.absNorm 𝔭 : ℝ) ^ l) ∧
        span {Φ} = ∏ t : (ZMod l)ˣ,
          (((IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm t)⁻¹ • 𝔭) ^ (l - t.val.val) ∧
        powResIdeal Φ (span {(q : CycR l)}) = powResSymb (q : CycR l) 𝔭 := by
    intro 𝔭 h𝔭
    obtain ⟨hpr, _, hle⟩ := mem_normalizedFactors_prime h𝔭
    have : 𝔭.IsPrime := hpr
    obtain ⟨hp_pr, hp_nel⟩ := hdeg1 𝔭 h𝔭
    have hp_neq : Ideal.absNorm 𝔭 ≠ q := fun heq =>
      hpr.ne_top (eq_top_iff.mpr <| by
        rw [← hα_cop_q.sup_eq]; exact sup_le hle ((Ideal.span_singleton_le_iff_mem _).mpr (heq ▸ Ideal.absNorm_mem 𝔭)))
    obtain ⟨Φ, h1, h2, h3, h4⟩ := exists_stickelberger_element hl2 hp_pr hp_nel (rfl : Ideal.absNorm 𝔭 = _)
    exact ⟨Φ, h1, h2, h3, h4 q hq hql hp_neq.symm⟩
  let Φf : {𝔭 // 𝔭 ∈ fac} → CycR l := fun x => (hfac_spec x.1 x.2).choose
  let Φα : CycR l := (fac.attach.map Φf).prod
  have hΦα_prim : IsPrimary Φα := by
    have hprod_prim : ∀ (m : Multiset {𝔭 // 𝔭 ∈ fac}),
        (∀ x ∈ m, IsPrimary (Φf x)) → IsPrimary (m.map Φf).prod := by
      intro m
      refine Multiset.induction_on m (fun _ => ⟨fun hd => ((zetaK_spec l).zeta_sub_one_prime').not_isUnit
        (isUnit_of_dvd_one hd), ⟨1, by simp⟩⟩) fun a s ih hm => ?_
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact (hm a (Multiset.mem_cons_self a s)).mul (ih fun x hx => hm x (Multiset.mem_cons_of_mem hx))
    exact hprod_prim fac.attach fun x _ => (hfac_spec x.1 x.2).choose_spec.1
  let σinv : (ZMod l)ˣ → Gal(CycK l / ℚ) := fun t =>
    ((IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm t)⁻¹
  let β : CycR l := ∏ t : (ZMod l)ˣ, (σinv t • α) ^ (l - t.val.val)
  have hβ_prim : IsPrimary β := by
    refine IsPrimary.prod _ _ fun t _ => ?_
    have h1 := hα_prim.galois_smul (σinv t)
    induction (l - t.val.val) with
    | zero =>
      rw [pow_zero]
      exact ⟨fun hd => ((zetaK_spec l).zeta_sub_one_prime').not_isUnit (isUnit_of_dvd_one hd), ⟨1, by simp⟩⟩
    | succ n ih => rw [pow_succ]; exact ih.mul h1
  have hspan_eq : span {Φα} = span {β} := by
    have hΦ_span : span {Φα} = (fac.attach.map (fun x => span {Φf x})).prod := by
      dsimp [Φα]
      have h1 : ∀ m : Multiset {𝔭 // 𝔭 ∈ fac}, span {(m.map Φf).prod} = (m.map (fun x => span {Φf x})).prod := fun m => by
        refine Multiset.induction_on m (by simp [Ideal.one_eq_top]) fun a s ih => ?_
        rw [Multiset.map_cons, Multiset.prod_cons, ← Ideal.span_singleton_mul_span_singleton, ih,
          Multiset.map_cons, Multiset.prod_cons]
      exact h1 fac.attach
    rw [hΦ_span]
    have hstep : (fac.attach.map (fun x => span {Φf x})).prod =
        (fac.attach.map (fun x => ∏ t : (ZMod l)ˣ, (σinv t • x.1) ^ (l - t.val.val))).prod :=
      congrArg Multiset.prod (Multiset.map_congr rfl fun x _ => (hfac_spec x.1 x.2).choose_spec.2.2.1)
    rw [hstep]
    have hswap : ∀ (m : Multiset {𝔭 // 𝔭 ∈ fac}),
        (m.map (fun x => ∏ t : (ZMod l)ˣ, (σinv t • x.1) ^ (l - t.val.val))).prod =
          ∏ t : (ZMod l)ˣ, ((m.map (fun x => σinv t • x.1)).prod) ^ (l - t.val.val) := fun m => by
      refine Multiset.induction_on m (by rw [Multiset.map_zero, Multiset.prod_zero, Ideal.one_eq_top]; simp [Ideal.top_pow]) fun a s ih => ?_
      rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Finset.prod_mul_distrib]
      exact prod_congr rfl fun t _ => by rw [Multiset.map_cons, Multiset.prod_cons, mul_pow]
    rw [hswap]
    have hβ_span : span {β} = ∏ t : (ZMod l)ˣ, span {σinv t • α} ^ (l - t.val.val) := by
      dsimp [β]; rw [← Ideal.prod_span_singleton]
      exact prod_congr rfl fun t _ => (Ideal.span_singleton_pow _ _).symm
    rw [hβ_span]
    refine prod_congr rfl fun t _ => congrArg (· ^ (l - t.val.val)) ?_
    have hattach : fac.attach.map (fun x => σinv t • x.1) = fac.map (fun 𝔭 => σinv t • 𝔭) := by
      simpa only [Multiset.map_map, Function.comp_def] using
        congrArg (Multiset.map (fun 𝔭 => σinv t • 𝔭)) (Multiset.attach_map_val fac)
    have hprod_smul : ∀ m : Multiset (Ideal (CycR l)), (m.map (fun 𝔭 => σinv t • 𝔭)).prod = σinv t • m.prod := fun m => by
      refine Multiset.induction_on m (by rw [Multiset.map_zero, Multiset.prod_zero,
        Ideal.one_eq_top, galois_smul_ideal_eq_map, Ideal.map_top]) fun a s ih => ?_
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, ih, galois_smul_mul_ideal]
    rw [hattach, hprod_smul, Ideal.prod_normalizedFactors_eq_self hα_bot, galois_smul_span_singleton]
  have hnorm_eq : ∀ φ : CycK l →+* ℂ, ‖φ (Φα : CycK l)‖ = ‖φ (β : CycK l)‖ := by
    intro φ
    have hΦ_n : ‖φ (Φα : CycK l)‖ ^ 2 = (Ideal.absNorm (span {α}) : ℝ) ^ l := by
      have h1 : ∀ m : Multiset {𝔭 // 𝔭 ∈ fac},
          ‖φ (((m.map Φf).prod : CycR l) : CycK l)‖ ^ 2 =
            ((m.map (fun x => (Ideal.absNorm x.1 : ℝ) ^ l)).prod) := fun m => by
        refine Multiset.induction_on m (by simp) fun a s ih => ?_
        rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
          NumberField.RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul, mul_pow,
          ← NumberField.RingOfIntegers.coe_eq_algebraMap, ← NumberField.RingOfIntegers.coe_eq_algebraMap,
          ih, (hfac_spec a.1 a.2).choose_spec.2.1 φ]
      rw [h1 fac.attach]
      have hm : ∀ m : Multiset {𝔭 // 𝔭 ∈ fac},
          (m.map (fun x => (Ideal.absNorm x.1 : ℝ) ^ l)).prod =
            (((m.map (fun x => Ideal.absNorm x.1)).prod : ℕ) : ℝ) ^ l := fun m => by
        refine Multiset.induction_on m (by simp) fun a s ih => by simp [ih, mul_pow]
      rw [hm]
      have hattach : fac.attach.map (fun x => Ideal.absNorm x.1) = fac.map Ideal.absNorm := by
        simpa only [Multiset.map_map, Function.comp_def] using
          congrArg (Multiset.map Ideal.absNorm) (Multiset.attach_map_val fac)
      rw [hattach, ← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hα_bot]
    have hβ_n : ‖φ (β : CycK l)‖ ^ 2 = (Ideal.absNorm (span {α}) : ℝ) ^ l := by
      let σneg : Gal(CycK l / ℚ) := (IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm (-1)
      have hnorm_neg : ∀ x : CycR l, ‖φ ((σneg • x : CycR l) : CycK l)‖ = ‖φ (x : CycK l)‖ := fun x => by
        rw [← star_embedding_eq_smul_neg φ x, norm_star]
      have h1 : ‖φ (β : CycK l)‖ = ∏ t : (ZMod l)ˣ, ‖φ ((σinv t • α : CycR l) : CycK l)‖ ^ (l - t.val.val) := by
        dsimp [β]
        rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_prod, map_prod, norm_prod]
        exact prod_congr rfl fun t _ => by
          rw [map_pow, map_pow, norm_pow, ← NumberField.RingOfIntegers.coe_eq_algebraMap]
      have h2 : ‖φ (β : CycK l)‖ = ∏ t : (ZMod l)ˣ, ‖φ ((σinv t • α : CycR l) : CycK l)‖ ^ t.val.val := by
        rw [h1]
        refine Fintype.prod_equiv (Equiv.mulLeft (-1 : (ZMod l)ˣ)) _ _ fun t => ?_
        have hσ_eq : σinv (-1 * t) = σneg * σinv t := by
          have hinv_neg : (-1 : (ZMod l)ˣ)⁻¹ = -1 := by ext; simp
          dsimp [σinv, σneg]
          rw [← map_inv, ← map_inv, ← map_mul, mul_inv_rev, hinv_neg, mul_comm]
        have hneg : (-1 * t).val.val = l - t.val.val := by
          rw [neg_one_mul, Units.val_neg, zmod_val_neg_of_ne_zero t.ne_zero]
        change ‖φ ((σinv t • α : CycR l) : CycK l)‖ ^ (l - t.val.val) =
          ‖φ ((σinv (-1 * t) • α : CycR l) : CycK l)‖ ^ (-1 * t).val.val
        rw [hneg, hσ_eq, mul_smul, hnorm_neg]
      have hβ_sq : ‖φ (β : CycK l)‖ ^ 2 = (∏ t : (ZMod l)ˣ, ‖φ ((σinv t • α : CycR l) : CycK l)‖) ^ l := by
        rw [sq]
        conv_lhs => arg 1; rw [h1]
        conv_lhs => arg 2; rw [h2]
        rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
        exact prod_congr rfl fun t _ => by
          rw [← pow_add, show l - t.val.val + t.val.val = l by have := ZMod.val_lt t.val; omega]
      rw [hβ_sq]; congr 1
      have : IsGalois ℚ (CycK l) := IsCyclotomicExtension.isGalois {l} ℚ (CycK l)
      have hprod_gal : ∏ t : (ZMod l)ˣ, ‖φ ((σinv t • α : CycR l) : CycK l)‖ =
          ‖φ (((Algebra.norm ℤ α : ℤ) : CycK l))‖ := by
        have hnorm_K : ((Algebra.norm ℤ α : ℤ) : CycK l) = ∏ σ : Gal(CycK l / ℚ), σ (α : CycK l) := by
          rw [show ((Algebra.norm ℤ α : ℤ) : CycK l) = algebraMap ℚ (CycK l) ((Algebra.norm ℤ α : ℤ) : ℚ) by simp,
            Algebra.coe_norm_int α, Algebra.norm_eq_prod_automorphisms]
        rw [hnorm_K, map_prod, norm_prod]
        refine Fintype.prod_equiv ((IsCyclotomicExtension.Rat.galEquivZMod l (CycK l)).symm.toEquiv.trans
          (Equiv.inv (Gal(CycK l / ℚ)))) _ _ fun t => rfl
      rw [hprod_gal, map_intCast, Complex.norm_intCast, Ideal.absNorm_span_singleton, Nat.cast_natAbs,
        ← Int.cast_abs]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hΦ_n.trans hβ_n.symm)
  obtain ⟨u, hu_eq⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan_eq.symm
  have hu_norm : ∀ φ : CycK l →+* ℂ, ‖φ ((u : CycR l) : CycK l)‖ = 1 := by
    intro φ
    have h1 := hnorm_eq φ
    rw [← hu_eq, NumberField.RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul,
      ← NumberField.RingOfIntegers.coe_eq_algebraMap, ← NumberField.RingOfIntegers.coe_eq_algebraMap] at h1
    have hβ_ne0 : ‖φ (β : CycK l)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero_iff φ φ.injective]
      exact fun h0 => hβ_prim.1 (by have hβ0 : β = 0 := RingOfIntegers.ext (by simpa using h0); simp [hβ0])
    exact mul_left_cancel₀ hβ_ne0 (by simpa [mul_comm] using h1)
  have hu_pm := isPrimary_unit_eq_pm_one hl2 hβ_prim hΦα_prim hu_norm (by rw [← hu_eq, mul_comm])
  have hσ_cop : ∀ t : (ZMod l)ˣ, IsCoprime (span {σinv t • α}) (span {(q : CycR l)}) := fun t => by
    let e := (galRestrict ℤ ℚ (CycK l) (CycR l) (σinv t)).toRingEquiv
    have h1 : span {σinv t • α} = Ideal.map (e : CycR l →+* CycR l) (span {α}) := by
      rw [← galois_smul_span_singleton, galois_smul_ideal_eq_map]
    have h2 : span {(q : CycR l)} = Ideal.map (e : CycR l →+* CycR l) (span {(q : CycR l)}) := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [h1, h2]
    exact Ideal.isCoprime_iff_sup_eq.mpr (by rw [← Ideal.map_sup, hα_cop_q.sup_eq, Ideal.map_top])
  have hβ_cop_q : IsCoprime (span {β}) (span {(q : CycR l)}) := by
    dsimp [β]; rw [← Ideal.prod_span_singleton]
    exact IsCoprime.prod_left fun t _ => by rw [← Ideal.span_singleton_pow]; exact (hσ_cop t).pow_left
  have hlhs : powResIdeal Φα (span {(q : CycR l)}) = powResIdeal (q : CycR l) (span {α}) := by
    have hcop_each : ∀ x : {𝔭 // 𝔭 ∈ fac}, IsCoprime (span {Φf x}) (span {(q : CycR l)}) := fun x => by
      obtain ⟨c, hc⟩ := Multiset.dvd_prod (Multiset.mem_map_of_mem Φf (Multiset.mem_attach _ x))
      have hJ : span {Φα} = span {Φf x} * span {c} := by
        dsimp [Φα]; rw [hc, Ideal.span_singleton_mul_span_singleton]
      have hcop_Φα : IsCoprime (span {Φα}) (span {(q : CycR l)}) := hspan_eq ▸ hβ_cop_q
      rw [hJ] at hcop_Φα; exact hcop_Φα.of_mul_left_left
    have hall_cop : ∀ m : Multiset {𝔭 // 𝔭 ∈ fac}, IsCoprime (span {(m.map Φf).prod}) (span {(q : CycR l)}) := by
      intro m
      induction m using Multiset.induction_on with
      | empty =>
        rw [Multiset.map_zero, Multiset.prod_zero, Ideal.span_singleton_one, ← Ideal.one_eq_top]
        exact isCoprime_one_left
      | cons b t iht =>
        rw [Multiset.map_cons, Multiset.prod_cons, ← Ideal.span_singleton_mul_span_singleton]
        exact (hcop_each b).mul_left iht
    have hprod_res : ∀ m : Multiset {𝔭 // 𝔭 ∈ fac},
        powResIdeal (m.map Φf).prod (span {(q : CycR l)}) =
          (m.map (fun x => powResIdeal (Φf x) (span {(q : CycR l)}))).prod := fun m => by
      refine Multiset.induction_on m (by simp [powResIdeal_one hlam_cop_q]) fun a s ih => ?_
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, ← ih]
      exact powResIdeal_mul_left hlam_cop_q (hcop_each a) (hall_cop s)
    change powResIdeal (fac.attach.map Φf).prod (span {(q : CycR l)}) = _
    rw [hprod_res fac.attach]
    have hcongr : fac.attach.map (fun x => powResIdeal (Φf x) (span {(q : CycR l)})) =
        fac.map (powResSymb (q : CycR l)) := by
      rw [Multiset.map_congr rfl fun x _ => (hfac_spec x.1 x.2).choose_spec.2.2.2]
      simpa only [Multiset.map_map, Function.comp_def] using
        congrArg (Multiset.map (powResSymb (q : CycR l))) (Multiset.attach_map_val fac)
    rw [hcongr]; rfl
  have hrhs : powResIdeal Φα (span {(q : CycR l)}) = powResIdeal α (span {(q : CycR l)}) := by
    have hu_cop : IsCoprime (span {(u : CycR l)}) (span {(q : CycR l)}) := by
      rw [Ideal.span_singleton_eq_top.mpr u.isUnit, ← Ideal.one_eq_top]; exact isCoprime_one_left
    have h1 : powResIdeal Φα (span {(q : CycR l)}) = powResIdeal β (span {(q : CycR l)}) := by
      rw [← hu_eq, mul_comm, powResIdeal_mul_left hlam_cop_q hu_cop hβ_cop_q]
      rcases hu_pm with h | h
      · rw [h, powResIdeal_one hlam_cop_q, one_mul]
      · rw [h, powResIdeal_neg_one hl2 hlam_cop_q, one_mul]
    rw [h1]; dsimp [β]
    rw [powResIdeal_prod_left _ _ hlam_cop_q (fun t _ => by rw [← Ideal.span_singleton_pow]; exact (hσ_cop t).pow_left)]
    set w : CycR l := powResIdeal α (span {(q : CycR l)})
    have hw_l : w ^ l = 1 := powResIdeal_pow_l _ _
    have hw_pow : ∀ a b : ℕ, a ≡ b [MOD l] → w ^ a = w ^ b := fun a b hab => by
      rw [← Nat.div_add_mod a l, ← Nat.div_add_mod b l, pow_add, pow_add,
        pow_mul, pow_mul, hw_l, one_pow, one_pow, one_mul, one_mul, hab]
    have hterm : ∀ t : (ZMod l)ˣ,
        powResIdeal ((σinv t • α) ^ (l - t.val.val)) (span {(q : CycR l)}) = w ^ (l - 1) := fun t => by
      rw [powResIdeal_pow_left hlam_cop_q (hσ_cop t),
        powResIdeal_galois_span_natCast hq hql hα_cop_q (σinv t), ← pow_mul]
      have hval : (IsCyclotomicExtension.Rat.galEquivZMod l (CycK l) (σinv t)).val = t⁻¹.val := by
        dsimp [σinv]; rw [map_inv, MulEquiv.apply_symm_apply]
      rw [hval]
      refine hw_pow _ _ ?_
      rw [← ZMod.natCast_eq_natCast_iff]
      have ht_inv : t⁻¹.val * t.val = 1 := by exact_mod_cast Units.inv_mul t
      rw [Nat.cast_mul, Nat.cast_sub (ZMod.val_lt t.val).le, Nat.cast_sub hl.out.one_lt.le,
        ZMod.natCast_self, zero_sub, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        mul_neg, ht_inv, zero_sub, Nat.cast_one]
    rw [prod_congr rfl fun t _ => hterm t, prod_const, card_univ, ZMod.card_units_eq_totient,
      Nat.totient_prime hl.out, ← pow_mul]
    have hmod1 : (l - 1) * (l - 1) ≡ 1 [MOD l] := by
      have h1' : (l - 1) * (l - 1) = l * (l - 2) + 1 := by
        have := hl.out.two_le; zify [show 1 ≤ l by omega, show 2 ≤ l by omega]; ring
      rw [Nat.ModEq, h1', Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod]
    simpa [pow_one] using hw_pow _ _ hmod1
  exact hlhs.symm.trans hrhs

end EisensteinReciprocity

end Erdos980Eisenstein

/-
# Ideal Class Representatives, Fundamental Cone Box Bounds, and Local Sieve Densities

For an odd prime `l` (`d = l - 1`, `K = CyclotomicField l ℚ`, `R = 𝓞 K`):
1. `exists_deg1_class_rep`: Every ideal class `C⁻¹ ∈ ClassGroup R` contains a nonzero integral
   ideal `𝔟` factoring exclusively into degree-1 prime ideals coprime to `(l)`.
2. `exists_deg1_prime_of_mod_eq_one`: Every rational prime `p ≡ 1 (mod l)` has a degree-1 prime
   ideal `𝔭` of norm `p` whose `l`-th power residue symbol tests `l`-th powers mod `p`.
3. `coordR` & `exists_primary_box_bound`: Every ideal `𝔭` of class `C` coprime to `(l)` yields a
   primary generator `α` of `𝔭 * 𝔟` whose `ℤ[ζ_l]` coordinates satisfy `|c_i| ≤ C_box * N(𝔭)^(1/d)`.
4. Local sieve densities:
   - `forbiddenPowRes l q w`: at most `q^d / l` residue classes mod `q` have `(α / (q))_l = w`.
   - `forbiddenSplit l r`: for `r ≡ 1 (mod l)`, exactly `(r - 1)^d` residue classes mod `r` are
     coprime to `(r)`.
-/

namespace Erdos980Box

open Ideal NumberField RingOfIntegers Polynomial Finset Filter Erdos980Eisenstein
open scoped BigOperators Classical nonZeroDivisors Topology

section CoordAndDegreeOnePrimes

variable (l : ℕ) [hl : Fact l.Prime]

lemma integralPowerBasis_dim_eq : (zetaK_spec l).integralPowerBasis.dim = l - 1 := by
  rw [(zetaK_spec l).integralPowerBasis_dim, Nat.totient_prime hl.out]

/-- `ℤ`-linear equivalence `𝓞 (CyclotomicField l ℚ) ≃ₗ[ℤ] (Fin (l - 1) → ℤ)` via `1, ζ, ..., ζ^(l-2)`. -/
noncomputable def coordR : CycR l ≃ₗ[ℤ] (Fin (l - 1) → ℤ) :=
  ((zetaK_spec l).integralPowerBasis.basis.equivFun).trans
    (LinearEquiv.funCongrLeft ℤ ℤ (finCongr (integralPowerBasis_dim_eq l).symm))

lemma coordR_symm_apply (v : Fin (l - 1) → ℤ) :
    (coordR l).symm v = ∑ i : Fin (l - 1), (v i : CycR l) * zetaR l ^ (i : ℕ) := by
  let pb := (zetaK_spec l).integralPowerBasis
  let e : Fin (l - 1) ≃ Fin pb.dim := finCongr (integralPowerBasis_dim_eq l).symm
  have h1 : (coordR l).symm v = pb.basis.equivFun.symm (v ∘ e.symm) := rfl
  rw [h1, Module.Basis.equivFun_symm_apply]
  refine Fintype.sum_equiv e.symm _ _ fun j => ?_
  rw [pb.basis_eq_pow, (zetaK_spec l).integralPowerBasis_gen, zsmul_eq_mul]
  simp [e, zetaR]

lemma coordR_sub_mem_span_natCast {q : ℕ} {α β : CycR l} :
    α - β ∈ span {(q : CycR l)} ↔ ∀ i : Fin (l - 1), (q : ℤ) ∣ (coordR l α i - coordR l β i) := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨γ, hγ⟩ i
    refine ⟨coordR l γ i, ?_⟩
    have h1 := congrArg (fun x => coordR l x i) hγ
    rw [map_sub, Pi.sub_apply, show (q : CycR l) * γ = (q : ℤ) • γ by simp [zsmul_eq_mul],
      map_zsmul, Pi.smul_apply, smul_eq_mul] at h1
    exact h1
  · intro h
    choose c hc using h
    refine ⟨(coordR l).symm c, ?_⟩
    apply (coordR l).injective
    ext i
    rw [map_sub, Pi.sub_apply, show (q : CycR l) * (coordR l).symm c = (q : ℤ) • (coordR l).symm c by
        simp [zsmul_eq_mul],
      map_zsmul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul]
    exact hc i

/-- Bijection between `Fintype.piFinset (fun _ : Fin (l - 1) => range q)` and `CycR l ⧸ span {q}`. -/
lemma mod_box_bijective {q : ℕ} (hq : 0 < q) :
    Function.Bijective (fun v : {v : Fin (l - 1) → ℕ // v ∈ Fintype.piFinset (fun _ : Fin (l - 1) => range q)} =>
      Ideal.Quotient.mk (span {(q : CycR l)}) ((coordR l).symm (fun i => (v.1 i : ℤ)))) := by
  constructor
  · rintro ⟨v1, hv1⟩ ⟨v2, hv2⟩ heq
    apply Subtype.ext; funext i
    have hsub : (coordR l).symm (fun i => (v1 i : ℤ)) - (coordR l).symm (fun i => (v2 i : ℤ)) ∈
        span {(q : CycR l)} := Ideal.Quotient.eq.mp heq
    have hdvd := (coordR_sub_mem_span_natCast l).mp hsub i
    simp only [LinearEquiv.apply_symm_apply] at hdvd
    have h1 : v1 i < q := mem_range.mp ((Fintype.mem_piFinset.mp hv1) i)
    have h2 : v2 i < q := mem_range.mp ((Fintype.mem_piFinset.mp hv2) i)
    obtain ⟨k, hk⟩ := hdvd
    have hk0 : k = 0 := by nlinarith
    have hsub0 : (v1 i : ℤ) - (v2 i : ℤ) = 0 := by rw [hk, hk0, mul_zero]
    exact_mod_cast sub_eq_zero.mp hsub0
  · intro y
    obtain ⟨α, rfl⟩ := Ideal.Quotient.mk_surjective y
    let v : Fin (l - 1) → ℕ := fun i => (coordR l α i % (q : ℤ)).toNat
    have hv_mem : v ∈ Fintype.piFinset (fun _ : Fin (l - 1) => range q) := by
      rw [Fintype.mem_piFinset]; intro i
      rw [mem_range]
      have hnn : 0 ≤ coordR l α i % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
      have hlt : coordR l α i % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
      dsimp only [v]; omega
    refine ⟨⟨v, hv_mem⟩, Ideal.Quotient.eq.mpr ?_⟩
    rw [coordR_sub_mem_span_natCast]
    intro i
    simp only [LinearEquiv.apply_symm_apply, v]
    have hnn : 0 ≤ coordR l α i % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq.ne')
    rw [Int.toNat_of_nonneg hnn]
    exact ⟨-(coordR l α i / (q : ℤ)), by linarith [Int.emod_add_mul_ediv (coordR l α i) (q : ℤ)]⟩

/-- Every rational prime `p ≡ 1 (mod l)` has a degree-1 prime ideal `𝔭` of norm `p` whose
    `l`-th power residue symbol tests `l`-th powers mod `p`. -/
theorem exists_deg1_prime_of_mod_eq_one {p : ℕ} (hp : p.Prime) (hp_mod : p % l = 1) :
    ∃ 𝔭 : Ideal (CycR l),
      𝔭.IsPrime ∧
      Ideal.absNorm 𝔭 = p ∧
      (∀ q : ℕ, ¬ p ∣ q →
        ((∃ y : ZMod p, y ^ l = (q : ZMod p)) ↔ powResSymb (q : CycR l) 𝔭 = 1)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hpl : p ≠ l := by
    intro h; rw [h, Nat.mod_self] at hp_mod; exact zero_ne_one hp_mod
  have hl_dvd : l ∣ (p - 1) := by
    have h1 : l * (p / l) + p % l = p := Nat.div_add_mod p l
    exact ⟨p / l, by omega⟩
  -- Pick primitive `l`-th root of unity `ω` in `ZMod p`
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hg_ord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hp]
  let ωu : (ZMod p)ˣ := g ^ ((p - 1) / l)
  let ω : ZMod p := ωu.val
  have hω_pow : ω ^ l = 1 := by
    dsimp [ω]
    rw [← Units.val_pow_eq_pow_val, show ωu ^ l = g ^ ((p - 1) / l * l) from (pow_mul g _ l).symm,
      Nat.div_mul_cancel hl_dvd, ← hg_ord, pow_orderOf_eq_one, Units.val_one]
  have hω_ne1 : ω ≠ 1 := by
    intro h1
    have hu1 : ωu = 1 := Units.ext h1
    have hdvd : (p - 1) ∣ ((p - 1) / l) := by
      have := orderOf_dvd_of_pow_eq_one hu1
      rwa [hg_ord] at this
    have hlt : (p - 1) / l < p - 1 := Nat.div_lt_self (by have := hp.two_le; omega) hl.out.one_lt
    have hmul := Nat.div_mul_cancel hl_dvd
    have hpos : 0 < (p - 1) / l := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_mul] at hmul; have := hp.two_le; omega
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
  -- `ω` is a root of `minpoly ℤ (zetaR l) = cyclotomic l ℤ`!
  have hminpoly : minpoly ℤ (zetaR l) = Polynomial.cyclotomic l ℤ := by
    have h1 : minpoly ℤ (zetaR l) = minpoly ℤ (zetaK l) := by
      rw [← (zetaK_spec l).coe_toInteger]
      exact (minpoly.algHom_eq (IsScalarTower.toAlgHom ℤ (CycR l) (CycK l))
        (fun a b h => RingOfIntegers.ext h) (zetaR l)).symm
    rw [h1]
    exact (Polynomial.cyclotomic_eq_minpoly (zetaK_spec l) hl.out.pos).symm
  have hω_root : Polynomial.aeval ω (minpoly ℤ (zetaR l)) = 0 := by
    rw [hminpoly, Polynomial.cyclotomic_prime ℤ l]
    have hmul : (ω - 1) * Polynomial.aeval ω (∑ i ∈ range l, (X : ℤ[X]) ^ i) = 0 := by
      rw [map_sum]
      simp only [map_pow, aeval_X]
      rw [mul_comm, geom_sum_mul, hω_pow, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hω_ne1)
  -- Build surjective `ℤ`-algebra hom `φ : CycR l →ₐ[ℤ] ZMod p` via `integralPowerBasis.lift`
  let pb := (zetaK_spec l).integralPowerBasis
  have hpb_root : Polynomial.aeval ω (minpoly ℤ pb.gen) = 0 := by
    rw [(zetaK_spec l).integralPowerBasis_gen]; exact hω_root
  let φ : CycR l →ₐ[ℤ] ZMod p := pb.lift ω hpb_root
  have hφ_surj : Function.Surjective (φ : CycR l →+* ZMod p) := by
    intro z
    refine ⟨(z.val : CycR l), ?_⟩
    rw [map_natCast, ZMod.natCast_zmod_val]
  let 𝔭 : Ideal (CycR l) := RingHom.ker (φ : CycR l →+* ZMod p)
  let qEquiv : (CycR l ⧸ 𝔭) ≃+* ZMod p := RingHom.quotientKerEquivOfSurjective hφ_surj
  have h𝔭_max : 𝔭.IsMaximal := RingHom.ker_isMaximal_of_surjective (φ : CycR l →+* ZMod p) hφ_surj
  have h𝔭_pr : 𝔭.IsPrime := h𝔭_max.isPrime
  have h𝔭_norm : Ideal.absNorm 𝔭 = p := by
    rw [absNorm_eq_card_quotient, Nat.card_congr qEquiv.toEquiv, Nat.card_zmod]
  have h𝔭_bot : 𝔭 ≠ ⊥ := Ideal.absNorm_eq_zero_iff.not.mp (by rw [h𝔭_norm]; exact hp.ne_zero)
  have hlam : lamR l ∉ 𝔭 := by
    intro hm
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hm)
    rw [absNorm_span_lamR, h𝔭_norm] at hdvd
    exact hpl ((Nat.prime_dvd_prime_iff_eq hp hl.out).mp hdvd)
  refine ⟨𝔭, h𝔭_pr, h𝔭_norm, fun q hqp => ?_⟩
  have hq_not_mem : (q : CycR l) ∉ 𝔭 := by
    intro hm
    have h0 : ((q : CycR l) |> φ) = 0 := hm
    rw [map_natCast] at h0
    exact hqp ((ZMod.natCast_eq_zero_iff q p).mp h0)
  rw [powResSymb_eq_one_iff_isPow h𝔭_bot hlam hq_not_mem]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨qEquiv.symm y, ?_⟩
    apply qEquiv.injective
    rw [map_pow, qEquiv.apply_symm_apply, hy, RingHom.quotientKerEquivOfSurjective_apply_mk, map_natCast]
  · rintro ⟨y, hy⟩
    refine ⟨qEquiv y, ?_⟩
    rw [← map_pow, hy, RingHom.quotientKerEquivOfSurjective_apply_mk, map_natCast]

end CoordAndDegreeOnePrimes

section IdealClassRepresentative

variable {l : ℕ} [hl : Fact l.Prime]

/-- Upper bound `∑_{n ∈ Ioc R₀ N} 1 / n^2 ≤ 1 / R₀` for `R₀ ≥ 1`. -/
private lemma sum_Ioc_inv_sq_le (R₀ N : ℕ) (hR : 1 ≤ R₀) :
    ∑ n ∈ Ioc R₀ N, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (R₀ : ℝ) := by
  by_cases hle : N ≤ R₀
  · have hemp : Ioc R₀ N = ∅ := by ext n; simp only [mem_Ioc, notMem_empty, iff_false]; omega
    rw [hemp, sum_empty]; positivity
  · push Not at hle
    have htel : ∀ n ∈ Ioc R₀ N, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ) := by
      intro n hn
      obtain ⟨hn1, _⟩ := mem_Ioc.mp hn
      have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
      rw [div_sub_div _ _ hn1_pos.ne' hn_pos.ne']
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      rw [hcast]
      have hnum : (1 : ℝ) * (n : ℝ) - ((n : ℝ) - 1) * 1 = 1 := by ring
      rw [hnum]
      exact div_le_div_of_nonneg_left zero_le_one (by rw [← hcast]; positivity) (by nlinarith)
    have hsum_tel : ∀ M : ℕ, R₀ ≤ M →
        ∑ n ∈ Ioc R₀ M, (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) = 1 / (R₀ : ℝ) - 1 / (M : ℝ) := by
      intro M hM
      induction M, hM using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        rw [show Ioc R₀ (k + 1) = insert (k + 1) (Ioc R₀ k) by
          ext m; simp only [mem_Ioc, mem_insert]; omega]
        rw [sum_insert (by simp), ih]
        simp only [Nat.add_sub_cancel]; ring
    calc ∑ n ∈ Ioc R₀ N, (1 : ℝ) / (n : ℝ) ^ 2
        ≤ ∑ n ∈ Ioc R₀ N, (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) := sum_le_sum htel
      _ = 1 / (R₀ : ℝ) - 1 / (N : ℝ) := hsum_tel N hle.le
      _ ≤ 1 / (R₀ : ℝ) := by linarith [show (0 : ℝ) ≤ 1 / (N : ℝ) by positivity]

private lemma sum_biUnion_le_nonneg {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset α} {t : α → Finset β} {f : β → ℝ} (hf : ∀ b, 0 ≤ f b) :
    ∑ b ∈ s.biUnion t, f b ≤ ∑ a ∈ s, ∑ b ∈ t a, f b := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [biUnion_insert, sum_insert ha]
    have h1 : ∑ b ∈ t a ∪ s.biUnion t, f b ≤ ∑ b ∈ t a, f b + ∑ b ∈ s.biUnion t, f b := by
      have hu := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      have hnn : 0 ≤ ∑ b ∈ t a ∩ s.biUnion t, f b := sum_nonneg fun b _ => hf b
      linarith
    linarith

private lemma ie_good_count_tendsto {l : ℕ} [Fact l.Prime]
    (C : ClassGroup (CycR l)) (BadSmall : Finset (Ideal (CycR l)))
    (hBadSmall_prop : ∀ 𝔮 ∈ BadSmall, 𝔮.IsPrime ∧ 𝔮 ≠ ⊥) :
    let K := CycK l
    let R := CycR l
    let cK : ℝ := (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
        (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K * NumberField.Units.regulator K) /
      (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|)
    Tendsto (fun s : ℝ =>
      (Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹ ∧
        ∀ 𝔮 ∈ BadSmall, ¬ 𝔮 ∣ I.1} : ℝ) / s) atTop
      (𝓝 (cK * ∏ 𝔮 ∈ BadSmall, (1 - (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)))) := by
  intro K R cK
  have hprod_ne : ∀ T ∈ BadSmall.powerset, (∏ 𝔮 ∈ T, 𝔮) ≠ ⊥ := fun T hT => by
    have hTsub := mem_powerset.mp hT
    clear hT
    induction T using Finset.induction_on with
    | empty => simp [Ideal.one_eq_top]
    | insert a s ha ih =>
      rw [prod_insert ha]
      exact mul_ne_zero (hBadSmall_prop a (hTsub (mem_insert_self a s))).2
        (ih fun b hb => hTsub (mem_insert_of_mem hb))
  let prodT : ∀ T ∈ BadSmall.powerset, (Ideal R)⁰ := fun T hT =>
    ⟨∏ 𝔮 ∈ T, 𝔮, mem_nonZeroDivisors_of_ne_zero (hprod_ne T hT)⟩
  have hterm_tendsto : ∀ T ∈ BadSmall.powerset,
      Tendsto (fun s : ℝ =>
        ((-1 : ℝ) ^ T.card) *
          ((Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹ ∧
            (∏ 𝔮 ∈ T, 𝔮) ∣ I.1} : ℝ) / s)) atTop
        (𝓝 (((-1 : ℝ) ^ T.card) * (cK / (Ideal.absNorm (∏ 𝔮 ∈ T, 𝔮) : ℝ)))) := by
    intro T hT
    let J : (Ideal R)⁰ := prodT T hT
    have hJ_pos : (0 : ℝ) < (Ideal.absNorm J.1 : ℝ) :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hprod_ne T hT)))
    have hcard_eq : ∀ s : ℝ,
        Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹ ∧ J.1 ∣ I.1} =
        Nat.card {I' : (Ideal R)⁰ // (Ideal.absNorm I'.1 : ℝ) ≤ s / (Ideal.absNorm J.1 : ℝ) ∧
          ClassGroup.mk0 I' = C⁻¹ * (ClassGroup.mk0 J)⁻¹} := by
      intro s
      refine Nat.card_congr ?_
      refine (Equiv.ofBijective (fun x : {I' : (Ideal R)⁰ // (Ideal.absNorm I'.1 : ℝ) ≤ s / (Ideal.absNorm J.1 : ℝ) ∧
          ClassGroup.mk0 I' = C⁻¹ * (ClassGroup.mk0 J)⁻¹} =>
        (⟨J * x.1, ?_⟩ : {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹ ∧ J.1 ∣ I.1})) ⟨?_, ?_⟩).symm
      · refine ⟨?_, ?_, dvd_mul_right J.1 x.1.1⟩
        · change (Ideal.absNorm (J.1 * x.1.1) : ℝ) ≤ s
          rw [map_mul, Nat.cast_mul]
          exact (le_div_iff₀' hJ_pos).mp x.2.1
        · rw [map_mul, x.2.2, mul_comm C⁻¹, mul_inv_cancel_left]
      · rintro ⟨I1, h1⟩ ⟨I2, h2⟩ heq
        apply Subtype.ext; apply Subtype.ext
        have hmul : J.1 * I1.1 = J.1 * I2.1 := congrArg (fun z => z.1.1) heq
        exact mul_left_cancel₀ (nonZeroDivisors.ne_zero J.2) hmul
      · rintro ⟨I, hle, hcls, hdvd⟩
        obtain ⟨I', hI'⟩ := hdvd
        have hI'_ne : I' ≠ ⊥ := fun h0 => nonZeroDivisors.ne_zero I.2 (by rw [hI', h0, Ideal.mul_bot]; rfl)
        let I'0 : (Ideal R)⁰ := ⟨I', mem_nonZeroDivisors_of_ne_zero hI'_ne⟩
        have hmul0 : J * I'0 = I := Subtype.ext hI'.symm
        refine ⟨⟨I'0, ?_, ?_⟩, Subtype.ext hmul0⟩
        · rw [le_div_iff₀' hJ_pos, ← Nat.cast_mul, ← map_mul, ← hI']; exact hle
        · rw [← hmul0, map_mul] at hcls
          rw [← hcls, mul_comm (ClassGroup.mk0 J), mul_inv_cancel_right]
    have ht := NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop K (C⁻¹ * (ClassGroup.mk0 J)⁻¹)
    have hscale : Tendsto (fun s : ℝ => s / (Ideal.absNorm J.1 : ℝ)) atTop atTop :=
      Tendsto.atTop_div_const hJ_pos tendsto_id
    have hcomp := (ht.comp hscale).div_const (Ideal.absNorm J.1 : ℝ)
    have hlim := hcomp.const_mul ((-1 : ℝ) ^ T.card)
    refine hlim.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    dsimp only [Function.comp_def]
    rw [hcard_eq s, div_div, div_mul_cancel₀ s hJ_pos.ne']
  have hsum_tend := tendsto_finsetSum BadSmall.powerset hterm_tendsto
  have hlim_eq : ∑ T ∈ BadSmall.powerset, ((-1 : ℝ) ^ T.card) * (cK / (Ideal.absNorm (∏ 𝔮 ∈ T, 𝔮) : ℝ)) =
      cK * ∏ 𝔮 ∈ BadSmall, (1 - (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)) := by
    have hprod_exp : ∏ 𝔮 ∈ BadSmall, (1 - (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)) =
        ∑ T ∈ BadSmall.powerset, ∏ 𝔮 ∈ T, (-(1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)) := by
      have h1 : ∏ 𝔮 ∈ BadSmall, (1 - (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)) =
          ∏ 𝔮 ∈ BadSmall, ((-(1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)) + 1) :=
        prod_congr rfl fun 𝔮 _ => by ring
      rw [h1, Finset.prod_add]
      exact sum_congr rfl fun T _ => by simp
    rw [hprod_exp, mul_sum]
    refine sum_congr rfl fun T _ => ?_
    have hprod_neg : ∏ 𝔮 ∈ T, (-(1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)) =
        (-1 : ℝ) ^ T.card / (Ideal.absNorm (∏ 𝔮 ∈ T, 𝔮) : ℝ) := by
      rw [map_prod, Nat.cast_prod,
        show ∏ 𝔮 ∈ T, (-(1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)) =
          ∏ 𝔮 ∈ T, ((-1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)) by exact prod_congr rfl fun _ _ => by ring,
        Finset.prod_div_distrib, prod_const]
    rw [hprod_neg]; ring
  rw [hlim_eq] at hsum_tend
  refine hsum_tend.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  have hfin : Finite {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹} := by
    have : Finite {I : (Ideal R)⁰ // Ideal.absNorm I.1 ≤ ⌊s⌋₊} := Ideal.finite_setOfPred_absNorm_le₀ ⌊s⌋₊
    exact Finite.of_injective (fun x : {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹} =>
        (⟨x.1, Nat.le_floor x.2.1⟩ : {I : (Ideal R)⁰ // Ideal.absNorm I.1 ≤ ⌊s⌋₊}))
      (fun a b h => Subtype.ext (Subtype.mk.inj h))
  let : Fintype {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹} := Fintype.ofFinite _
  let U : Finset {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹} := Finset.univ
  have hdiv_prod : ∀ (I : (Ideal R)⁰) (T : Finset (Ideal R)), T ⊆ BadSmall →
      ((∏ 𝔮 ∈ T, 𝔮) ∣ I.1 ↔ ∀ 𝔮 ∈ T, 𝔮 ∣ I.1) := by
    intro I T hT
    constructor
    · intro h 𝔮 h𝔮; exact (Finset.dvd_prod_of_mem id h𝔮).trans h
    · intro h
      refine Finset.prod_dvd_of_coprime (fun 𝔮1 h1 𝔮2 h2 hne => ?_) h
      have hm1 : 𝔮1.IsMaximal := (hBadSmall_prop 𝔮1 (hT h1)).1.isMaximal (hBadSmall_prop 𝔮1 (hT h1)).2
      have hm2 : 𝔮2.IsMaximal := (hBadSmall_prop 𝔮2 (hT h2)).1.isMaximal (hBadSmall_prop 𝔮2 (hT h2)).2
      dsimp only [Function.onFun]
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hnt
      exact hne ((hm1.eq_of_le hnt le_sup_left).trans (hm2.eq_of_le hnt le_sup_right).symm)
  have hIE_int :
      ∑ T ∈ BadSmall.powerset, (-1 : ℝ) ^ T.card *
        ((Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹ ∧
          (∏ 𝔮 ∈ T, 𝔮) ∣ I.1} : ℝ)) =
      (Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹ ∧
        ∀ 𝔮 ∈ BadSmall, ¬ 𝔮 ∣ I.1} : ℝ) := by
    have hcard_T : ∀ T ∈ BadSmall.powerset,
        (Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹ ∧
          (∏ 𝔮 ∈ T, 𝔮) ∣ I.1} : ℝ) =
        ∑ x ∈ U, if (∏ 𝔮 ∈ T, 𝔮) ∣ x.1.1 then (1 : ℝ) else 0 := by
      intro T _
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      congr 1
      rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
      refine Nat.card_congr ?_
      exact
        { toFun := fun x => ⟨⟨x.1, x.2.1, x.2.2.1⟩, mem_filter.mpr ⟨mem_univ _, x.2.2.2⟩⟩
          invFun := fun y => ⟨y.1.1, y.1.2.1, y.1.2.2, (mem_filter.mp y.2).2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have hcard_good :
        (Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹ ∧
          ∀ 𝔮 ∈ BadSmall, ¬ 𝔮 ∣ I.1} : ℝ) =
        ∑ x ∈ U, if (∀ 𝔮 ∈ BadSmall, ¬ 𝔮 ∣ x.1.1) then (1 : ℝ) else 0 := by
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      congr 1
      rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
      refine Nat.card_congr ?_
      exact
        { toFun := fun x => ⟨⟨x.1, x.2.1, x.2.2.1⟩, mem_filter.mpr ⟨mem_univ _, x.2.2.2⟩⟩
          invFun := fun y => ⟨y.1.1, y.1.2.1, y.1.2.2, (mem_filter.mp y.2).2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [sum_congr rfl fun T hT => by rw [hcard_T T hT, mul_sum], sum_comm, hcard_good]
    refine sum_congr rfl fun x _ => ?_
    let D_x : Finset (Ideal R) := BadSmall.filter (fun 𝔮 => 𝔮 ∣ x.1.1)
    have hrew : ∑ T ∈ BadSmall.powerset, (-1 : ℝ) ^ T.card * (if (∏ 𝔮 ∈ T, 𝔮) ∣ x.1.1 then (1 : ℝ) else 0) =
        ∑ T ∈ D_x.powerset, (-1 : ℝ) ^ T.card := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [← sum_filter]
      have hflt : BadSmall.powerset.filter (fun T => (∏ 𝔮 ∈ T, 𝔮) ∣ x.1.1) = D_x.powerset := by
        ext T
        simp only [mem_filter, mem_powerset, D_x, Finset.subset_iff]
        constructor
        · rintro ⟨hTsub, hdvd⟩ 𝔮 h𝔮
          exact ⟨hTsub h𝔮, (hdiv_prod x.1 T hTsub).mp hdvd 𝔮 h𝔮⟩
        · intro h
          have hTsub : T ⊆ BadSmall := fun 𝔮 h𝔮 => (h h𝔮).1
          exact ⟨hTsub, (hdiv_prod x.1 T hTsub).mpr fun 𝔮 h𝔮 => (h h𝔮).2⟩
      rw [hflt]
    rw [hrew]
    have hpow_sum : ∑ T ∈ D_x.powerset, (-1 : ℝ) ^ T.card = ∏ _𝔮 ∈ D_x, ((1 : ℝ) + (-1 : ℝ)) := by
      have h1 := Finset.prod_add (fun _ : Ideal R => (-1 : ℝ)) (fun _ => (1 : ℝ)) D_x
      rw [show (∏ _𝔮 ∈ D_x, ((1 : ℝ) + (-1 : ℝ))) = ∏ _𝔮 ∈ D_x, ((-1 : ℝ) + 1) by
        exact prod_congr rfl fun _ _ => add_comm _ _, h1]
      exact sum_congr rfl fun T _ => by simp
    rw [hpow_sum]
    by_cases hD : D_x = ∅
    · have hall : ∀ 𝔮 ∈ BadSmall, ¬ 𝔮 ∣ x.1.1 := by
        intro 𝔮 h𝔮 hdvd
        have : 𝔮 ∈ D_x := mem_filter.mpr ⟨h𝔮, hdvd⟩
        rw [hD] at this; exact notMem_empty _ this
      rw [hD, prod_empty, if_pos hall]
    · have hnot : ¬ ∀ 𝔮 ∈ BadSmall, ¬ 𝔮 ∣ x.1.1 := by
        obtain ⟨𝔮, h𝔮⟩ := Finset.nonempty_iff_ne_empty.mpr hD
        obtain ⟨h1, h2⟩ := mem_filter.mp h𝔮
        exact fun hall => hall 𝔮 h1 h2
      rw [if_neg hnot]
      obtain ⟨𝔮, h𝔮⟩ := Finset.nonempty_iff_ne_empty.mpr hD
      rw [← mul_prod_erase D_x _ h𝔮]; simp
  have hdiv : ∑ T ∈ BadSmall.powerset, (-1 : ℝ) ^ T.card *
      ((Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹ ∧
        (∏ 𝔮 ∈ T, 𝔮) ∣ I.1} : ℝ) / s) =
      (∑ T ∈ BadSmall.powerset, (-1 : ℝ) ^ T.card *
        (Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹ ∧
          (∏ 𝔮 ∈ T, 𝔮) ∣ I.1} : ℝ)) / s := by
    rw [sum_div]; exact sum_congr rfl fun _ _ => (mul_div_assoc ..).symm
  rw [hdiv, hIE_int]

set_option maxHeartbeats 1600000 in
/-- Every ideal class `C⁻¹ ∈ ClassGroup (CycR l)` (`l` odd prime) contains a nonzero integral ideal
    factoring exclusively into degree-1 prime ideals coprime to `(l)`. -/
theorem exists_deg1_class_rep (hl2 : l ≠ 2) (C : ClassGroup (CycR l)) :
    ∃ 𝔟 : (Ideal (CycR l))⁰,
      ClassGroup.mk0 𝔟 = C⁻¹ ∧
      ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔟.1,
        (Ideal.absNorm 𝔭).Prime ∧ Ideal.absNorm 𝔭 ≠ l := by
  let K := CycK l
  let R := CycR l
  let d : ℕ := l - 1
  have hd_pos : 0 < d := by have := hl.out.two_le; omega
  have hfinrank : Module.finrank ℤ R = d := by
    rw [(zetaK_spec l).integralPowerBasis.finrank, integralPowerBasis_dim_eq l]
  -- Asymptotic constant `cK > 0` from `NumberField.Ideal.tendsto_norm_le_and_mk_eq_div_atTop`
  let cK : ℝ := (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
      (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K * NumberField.Units.regulator K) /
    (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|)
  have hcK_pos : 0 < cK := by
    dsimp [cK]
    have hreg : 0 < NumberField.Units.regulator K := NumberField.Units.regulator_pos K
    have htors : 0 < (NumberField.Units.torsionOrder K : ℝ) :=
      Nat.cast_pos.mpr (NumberField.Units.torsionOrder_pos K)
    have hdisc : (NumberField.discr K : ℝ) ≠ 0 :=
      Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)
    have hsqrt : 0 < Real.sqrt |(NumberField.discr K : ℝ)| :=
      Real.sqrt_pos.mpr (abs_pos.mpr hdisc)
    have hpi : 0 < Real.pi := Real.pi_pos
    positivity
  -- Global upper bound `Nat.card {I : (Ideal R)⁰ // absNorm I ≤ s} ≤ C_all * s` for all `s ≥ 1`
  have h_all_bound : ∃ C_all : ℝ, 0 < C_all ∧ ∀ s : ℝ, 1 ≤ s →
      (Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s} : ℝ) ≤ C_all * s := by
    have ht := NumberField.Ideal.tendsto_norm_le_div_atTop₀ K
    set L := (2 ^ NumberField.InfinitePlace.nrRealPlaces K *
      (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K * NumberField.Units.regulator K *
      NumberField.classNumber K) /
      (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|)
    have hev : ∀ᶠ s : ℝ in atTop,
        (Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s} : ℝ) / s ≤ L + 1 :=
      (Filter.eventually_atTop.mpr (Metric.tendsto_atTop.mp ht 1 zero_lt_one)).mono fun s hs => by
        rw [Real.dist_eq] at hs; linarith [(abs_lt.mp hs).2]
    obtain ⟨S₀, hS₀⟩ := eventually_atTop.mp hev
    let S1 : ℝ := max S₀ 1
    let N1 : ℕ := ⌈S1⌉₊
    let C_all : ℝ := max (L + 1) ((Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ S1} : ℝ) + 1)
    have hC_pos : 0 < C_all := by
      dsimp [C_all]; exact lt_of_lt_of_le (by positivity) (le_max_right _ _)
    refine ⟨C_all, hC_pos, fun s hs1 => ?_⟩
    by_cases hs : S1 ≤ s
    · have hs_pos : 0 < s := by linarith
      have h1 := hS₀ s ((le_max_left S₀ 1).trans hs)
      have hle : (Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s} : ℝ) ≤ (L + 1) * s :=
        (div_le_iff₀ hs_pos).mp h1
      exact hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hs_pos.le)
    · push Not at hs
      have hmono : Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s} ≤
          Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ S1} := by
        have hfin : Finite {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ S1} := by
          have : Finite {I : (Ideal R)⁰ // Ideal.absNorm I.1 ≤ ⌊S1⌋₊} :=
            Ideal.finite_setOfPred_absNorm_le₀ ⌊S1⌋₊
          refine Finite.of_injective (fun x : {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ S1} =>
            (⟨x.1, Nat.le_floor x.2⟩ : {I : (Ideal R)⁰ // Ideal.absNorm I.1 ≤ ⌊S1⌋₊})) ?_
          intro a b h; exact Subtype.ext (Subtype.mk.inj h)
        refine Nat.card_le_card_of_injective (fun x : {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s} =>
          (⟨x.1, x.2.trans hs.le⟩ : {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ S1})) ?_
        intro a b h; exact Subtype.ext (Subtype.mk.inj h)
      have h1 : (Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s} : ℝ) ≤ C_all := by
        have hle_S1 : (Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s} : ℝ) ≤
            (Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ S1} : ℝ) := by exact_mod_cast hmono
        have hmax : (Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ S1} : ℝ) + 1 ≤ C_all :=
          le_max_right _ _
        linarith
      have hC0 : 0 ≤ C_all := hC_pos.le
      nlinarith
  obtain ⟨C_all, hC_all_pos, hC_all⟩ := h_all_bound
  -- Lower bound constant `δ := exp(-4*d - 2) * cK / 2`
  let δ : ℝ := Real.exp (-(4 * (d : ℝ) + 2)) * cK
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  -- Choose cutoff `R₀ ≥ l + 10` so `C_all * d / R₀ < δ / 4`
  let R₀ : ℕ := max (l + 10) (⌈4 * C_all * (d : ℝ) / δ⌉₊ + 1)
  have hR₀_ge1 : 1 ≤ R₀ := by have := le_max_left (l + 10) (⌈4 * C_all * (d : ℝ) / δ⌉₊ + 1); omega
  have hR₀_tail : C_all * ((d : ℝ) / (R₀ : ℝ)) < δ / 4 := by
    have hR₀_gt : 4 * C_all * (d : ℝ) / δ < (R₀ : ℝ) := by
      have h1 : 4 * C_all * (d : ℝ) / δ ≤ (⌈4 * C_all * (d : ℝ) / δ⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈4 * C_all * (d : ℝ) / δ⌉₊ + 1 : ℕ) ≤ R₀ := le_max_right _ _
      have h3 : ((⌈4 * C_all * (d : ℝ) / δ⌉₊ : ℝ) + 1) ≤ (R₀ : ℝ) := by exact_mod_cast h2
      linarith
    have hR₀_pos : (0 : ℝ) < (R₀ : ℝ) := by exact_mod_cast (by omega : 0 < R₀)
    have hmul : 4 * C_all * (d : ℝ) < δ * (R₀ : ℝ) := by
      have := (div_lt_iff₀ hδ_pos).mp hR₀_gt; linarith
    rw [show C_all * ((d : ℝ) / (R₀ : ℝ)) = (C_all * (d : ℝ)) / (R₀ : ℝ) by ring]
    rw [div_lt_iff₀ hR₀_pos]; linarith
  -- Helper: every nonzero prime ideal `𝔮` has a unique rational prime `r` with `𝔮 ∣ span {r}` and `absNorm 𝔮 = r^f`
  have hprime_over : ∀ 𝔮 : Ideal R, 𝔮.IsPrime → 𝔮 ≠ ⊥ →
      ∃ r : ℕ, r.Prime ∧ 𝔮 ∈ UniqueFactorizationMonoid.normalizedFactors (span {(r : R)}) ∧
        ∃ f : ℕ, 1 ≤ f ∧ Ideal.absNorm 𝔮 = r ^ f := by
    intro 𝔮 h𝔮 hbot
    have : 𝔮.IsMaximal := h𝔮.isMaximal hbot
    let : Field (R ⧸ 𝔮) := Ideal.Quotient.field 𝔮
    have : Finite (R ⧸ 𝔮) := Ring.HasFiniteQuotients.finiteQuotient hbot
    let : Fintype (R ⧸ 𝔮) := Fintype.ofFinite _
    have : CharP (R ⧸ 𝔮) (ringChar (R ⧸ 𝔮)) := ringChar.charP _
    let r : ℕ := ringChar (R ⧸ 𝔮)
    have hr_ne0 : r ≠ 0 := CharP.char_ne_zero_of_finite (R ⧸ 𝔮) r
    have hr_pr : r.Prime := (CharP.char_is_prime_or_zero (R ⧸ 𝔮) r).resolve_right hr_ne0
    obtain ⟨f, hf, hcard⟩ := FiniteField.card (R ⧸ 𝔮) r
    have hN : Ideal.absNorm 𝔮 = r ^ (f : ℕ) := by
      rw [absNorm_eq_card_quotient, Nat.card_eq_fintype_card, hcard]
    have hr_mem : (r : R) ∈ 𝔮 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact CharP.cast_eq_zero (R ⧸ 𝔮) r
    have hdvd : 𝔮 ∣ span {(r : R)} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hr_mem)
    have hr_bot : span {(r : R)} ≠ ⊥ := by simp [hr_pr.ne_zero]
    have h𝔮_mem : 𝔮 ∈ UniqueFactorizationMonoid.normalizedFactors (span {(r : R)}) := by
      have hpr := Ideal.prime_of_isPrime hbot h𝔮
      obtain ⟨𝔮', h𝔮'_mem, hassoc⟩ :=
        UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hr_bot hpr.irreducible hdvd
      rwa [associated_iff_eq.mp hassoc]
    exact ⟨r, hr_pr, h𝔮_mem, f, f.pos, hN⟩
  -- Helper: at most `d` prime ideals divide `span {r}` for any prime `r`
  have hcard_over_le : ∀ r : ℕ, r.Prime →
      (UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})).toFinset.card ≤ d := by
    intro r hr
    have hr_bot : span {(r : R)} ≠ ⊥ := by simp [hr.ne_zero]
    have habs : Ideal.absNorm (span {(r : R)}) = r ^ d := by
      rw [Ideal.absNorm_span_natCast, hfinrank]
    have hle_card : (UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})).toFinset.card ≤
        Multiset.card (UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})) :=
      Multiset.toFinset_card_le _
    have hpow_le : r ^ Multiset.card (UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})) ≤ r ^ d := by
      conv_rhs => rw [← habs, ← Ideal.prod_normalizedFactors_eq_self hr_bot, map_multiset_prod]
      have hge_r : ∀ 𝔮 ∈ UniqueFactorizationMonoid.normalizedFactors (span {(r : R)}), r ≤ Ideal.absNorm 𝔮 := by
        intro 𝔮 h𝔮
        obtain ⟨hpr, hbot, hle⟩ := mem_normalizedFactors_prime h𝔮
        obtain ⟨r', hr', _, f, hf, hN⟩ := hprime_over 𝔮 hpr hbot
        have hr_in : (r : R) ∈ 𝔮 := hle (Ideal.subset_span (Set.mem_singleton _))
        have hdvd_n : (Ideal.absNorm 𝔮 : ℤ) ∣ Algebra.norm ℤ (r : R) := Ideal.absNorm_dvd_norm_of_mem hr_in
        rw [Algebra.norm_natCast, hN] at hdvd_n
        have h1 : r' ^ f ∣ r ^ Module.finrank ℤ R := Int.ofNat_dvd.mp (by exact_mod_cast hdvd_n)
        have h2 : r' = r := (Nat.prime_dvd_prime_iff_eq hr' hr).mp
          (hr'.dvd_of_dvd_pow ((dvd_pow_self r' (by omega)).trans h1))
        rw [hN, h2]; exact Nat.le_self_pow (by omega) r
      have hprod_ge : ∀ m : Multiset (Ideal R), (∀ 𝔮 ∈ m, r ≤ Ideal.absNorm 𝔮) →
          r ^ Multiset.card m ≤ (m.map Ideal.absNorm).prod := by
        intro m
        refine Multiset.induction_on m (by simp) fun a s ih hm => ?_
        rw [Multiset.card_cons, pow_succ', Multiset.map_cons, Multiset.prod_cons]
        exact Nat.mul_le_mul (hm a (Multiset.mem_cons_self a s)) (ih fun b hb => hm b (Multiset.mem_cons_of_mem hb))
      exact hprod_ge _ hge_r
    exact hle_card.trans ((Nat.pow_le_pow_iff_right hr.one_lt).mp hpow_le)
  -- Define finite set `BadSmall` of bad prime ideals lying over primes `r ≤ R₀`
  let BadSmall : Finset (Ideal R) :=
    ((Nat.primesBelow (R₀ + 1)).biUnion fun r =>
      (UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})).toFinset).filter
        (fun 𝔮 => ¬ (Ideal.absNorm 𝔮).Prime ∨ Ideal.absNorm 𝔮 = l)
  -- Every `𝔮 ∈ BadSmall` is a nonzero prime ideal with `absNorm 𝔮 ≥ 3`
  have hBadSmall_prop : ∀ 𝔮 ∈ BadSmall, 𝔮.IsPrime ∧ 𝔮 ≠ ⊥ ∧ 3 ≤ Ideal.absNorm 𝔮 := by
    intro 𝔮 h𝔮
    obtain ⟨hmem_bi, hbad⟩ := mem_filter.mp h𝔮
    obtain ⟨r, hr_mem, h𝔮_fac⟩ := mem_biUnion.mp hmem_bi
    have h𝔮_in := Multiset.mem_toFinset.mp h𝔮_fac
    obtain ⟨hpr, hbot, _⟩ := mem_normalizedFactors_prime h𝔮_in
    refine ⟨hpr, hbot, ?_⟩
    rcases hbad with hnp | heql
    · obtain ⟨r', hr', _, f, hf, hN⟩ := hprime_over 𝔮 hpr hbot
      have hf2 : 2 ≤ f := by
        by_contra hlt; push Not at hlt
        have hf1 : f = 1 := by omega
        rw [hf1, pow_one] at hN; exact hnp (hN ▸ hr')
      have h4 : 4 ≤ r' ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ r' ^ 2 := Nat.pow_le_pow_left hr'.two_le 2
          _ ≤ r' ^ f := Nat.pow_le_pow_right hr'.pos hf2
      omega
    · have := hl.out.two_le; omega
  -- Lower bound `∏_{𝔮 ∈ BadSmall} (1 - 1 / absNorm 𝔮) ≥ exp(-(4*d + 2))`
  have hprod_lb : Real.exp (-(4 * (d : ℝ) + 2)) ≤
      ∏ 𝔮 ∈ BadSmall, (1 - (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)) := by
    -- First `1 - u ≥ exp(-2 u)` for `0 ≤ u ≤ 1 / 3`
    have hone_sub : ∀ 𝔮 ∈ BadSmall,
        Real.exp (-2 / (Ideal.absNorm 𝔮 : ℝ)) ≤ 1 - (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ) := by
      intro 𝔮 h𝔮
      have h3 : (3 : ℝ) ≤ (Ideal.absNorm 𝔮 : ℝ) := by exact_mod_cast (hBadSmall_prop 𝔮 h𝔮).2.2
      set u : ℝ := 1 / (Ideal.absNorm 𝔮 : ℝ)
      have hu_pos : 0 < u := by positivity
      have hu_le : u ≤ 1 / 3 := by dsimp [u]; rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
      have hexp : Real.exp (-2 * u) ≤ 1 - u := by
        rw [show -2 * u = -(2 * u) by ring, Real.exp_neg]
        have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
        have h4 : (Real.exp (2 * u))⁻¹ ≤ (1 + 2 * u)⁻¹ := inv_anti₀ (by linarith) h1
        have h2' : 1 ≤ (1 + 2 * u) * (1 - u) := by nlinarith
        have h3'' : (1 + 2 * u)⁻¹ ≤ 1 - u := (inv_le_iff_one_le_mul₀' (by linarith)).mpr h2'
        exact h4.trans h3''
      rw [show -2 / (Ideal.absNorm 𝔮 : ℝ) = -2 * u by dsimp [u]; ring]
      exact hexp
    have hsum_inv : ∑ 𝔮 ∈ BadSmall, (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ) ≤ 2 * (d : ℝ) + 1 := by
      -- Split `BadSmall` into `{span {lamR l}}` (norm `l ≥ 3`, contrib `≤ 1`) and `f ≥ 2` (norm `≥ r^2`, contrib `≤ 2 * d`)
      let BS_l := BadSmall.filter (fun 𝔮 => Ideal.absNorm 𝔮 = l)
      let BS_f2 := BadSmall.filter (fun 𝔮 => Ideal.absNorm 𝔮 ≠ l)
      rw [← sum_filter_add_sum_filter_not BadSmall (fun 𝔮 => Ideal.absNorm 𝔮 = l),
        show 2 * (d : ℝ) + 1 = 1 + 2 * (d : ℝ) by ring]
      apply add_le_add
      · -- Only `span {lamR l}` has `absNorm 𝔮 = l`!
        have hcard_l : BS_l.card ≤ 1 := by
          rw [Finset.card_le_one]
          intro 𝔮1 h1 𝔮2 h2
          obtain ⟨h1B, h1n⟩ := mem_filter.mp h1
          obtain ⟨h2B, h2n⟩ := mem_filter.mp h2
          obtain ⟨hpr1, _, _⟩ := hBadSmall_prop 𝔮1 h1B
          obtain ⟨hpr2, _, _⟩ := hBadSmall_prop 𝔮2 h2B
          have : 𝔮1.LiesOver (Ideal.span {(l : ℤ)}) := by
            rw [Ideal.liesOver_iff]
            refine (Int.ideal_span_isMaximal_of_prime l).eq_of_le (hpr1.comap _).ne_top ?_
            rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, algebraMap_int_eq, map_natCast]
            have hm := Ideal.absNorm_mem 𝔮1; rwa [h1n] at hm
          have : 𝔮2.LiesOver (Ideal.span {(l : ℤ)}) := by
            rw [Ideal.liesOver_iff]
            refine (Int.ideal_span_isMaximal_of_prime l).eq_of_le (hpr2.comap _).ne_top ?_
            rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, algebraMap_int_eq, map_natCast]
            have hm := Ideal.absNorm_mem 𝔮2; rwa [h2n] at hm
          rw [IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' l K (zetaK_spec l) 𝔮1,
            IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' l K (zetaK_spec l) 𝔮2]
        calc ∑ 𝔮 ∈ BS_l, (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)
            ≤ ∑ _𝔮 ∈ BS_l, (1 : ℝ) := sum_le_sum fun 𝔮 h𝔮 => by
              have h1 : (1 : ℝ) ≤ (Ideal.absNorm 𝔮 : ℝ) := by
                have := (hBadSmall_prop 𝔮 (mem_filter.mp h𝔮).1).2.2; exact_mod_cast (by omega : 1 ≤ Ideal.absNorm 𝔮)
              exact div_le_one_of_le₀ h1 (by positivity)
          _ = (BS_l.card : ℝ) := by simp
          _ ≤ 1 := by exact_mod_cast hcard_l
      · -- Every `𝔮 ∈ BS_f2` lies over some prime `r ≤ R₀` with `absNorm 𝔮 ≥ r^2`!
        have hsub : BS_f2 ⊆ (Nat.primesBelow (R₀ + 1)).biUnion fun r =>
            ((UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})).toFinset).filter
              (fun 𝔮 => r ^ 2 ≤ Ideal.absNorm 𝔮) := by
          intro 𝔮 h𝔮
          obtain ⟨h𝔮B, hnel⟩ := mem_filter.mp h𝔮
          obtain ⟨hbi, hbad⟩ := mem_filter.mp h𝔮B
          have hnp : ¬ (Ideal.absNorm 𝔮).Prime := hbad.resolve_right hnel
          obtain ⟨hpr, hbot, _⟩ := hBadSmall_prop 𝔮 h𝔮B
          obtain ⟨r, hr, hrfac, f, hf, hN⟩ := hprime_over 𝔮 hpr hbot
          have hf2 : 2 ≤ f := by
            by_contra hlt; push Not at hlt
            have hf1 : f = 1 := by omega
            rw [hf1, pow_one] at hN; exact hnp (hN ▸ hr)
          obtain ⟨r', hr'mem, h𝔮r'⟩ := mem_biUnion.mp hbi
          have hr'pr := Nat.prime_of_mem_primesBelow hr'mem
          obtain ⟨_, _, hle'⟩ := mem_normalizedFactors_prime (Multiset.mem_toFinset.mp h𝔮r')
          have hdvd_n : (Ideal.absNorm 𝔮 : ℤ) ∣ Algebra.norm ℤ (r' : R) :=
            Ideal.absNorm_dvd_norm_of_mem (hle' (Ideal.subset_span (Set.mem_singleton _)))
          rw [Algebra.norm_natCast, hN] at hdvd_n
          have hr_dvd_pow : r ∣ r ^ f := dvd_pow_self r (show f ≠ 0 by omega)
          have hrf_dvd : r ^ f ∣ r' ^ Module.finrank ℤ R := Int.ofNat_dvd.mp (by exact_mod_cast hdvd_n)
          have hr_eq : r = r' := (Nat.prime_dvd_prime_iff_eq hr hr'pr).mp
            (hr.dvd_of_dvd_pow (hr_dvd_pow.trans hrf_dvd))
          subst hr_eq
          refine mem_biUnion.mpr ⟨r, hr'mem, mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hrfac, ?_⟩⟩
          rw [hN]; exact Nat.pow_le_pow_right hr.pos hf2
        calc ∑ 𝔮 ∈ BS_f2, (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)
            ≤ ∑ 𝔮 ∈ (Nat.primesBelow (R₀ + 1)).biUnion (fun r =>
                ((UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})).toFinset).filter
                  (fun 𝔮 => r ^ 2 ≤ Ideal.absNorm 𝔮)), (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ) :=
              sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
          _ ≤ ∑ r ∈ Nat.primesBelow (R₀ + 1),
                ∑ 𝔮 ∈ ((UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})).toFinset).filter
                  (fun 𝔮 => r ^ 2 ≤ Ideal.absNorm 𝔮), (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ) :=
              sum_biUnion_le_nonneg fun _ => by positivity
          _ ≤ ∑ r ∈ Nat.primesBelow (R₀ + 1), (d : ℝ) / (r : ℝ) ^ 2 := by
              refine sum_le_sum fun r hr => ?_
              have hpr := Nat.prime_of_mem_primesBelow hr
              have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hpr.pos
              calc ∑ 𝔮 ∈ ((UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})).toFinset).filter
                      (fun 𝔮 => r ^ 2 ≤ Ideal.absNorm 𝔮), (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)
                  ≤ ∑ _𝔮 ∈ ((UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})).toFinset).filter
                      (fun 𝔮 => r ^ 2 ≤ Ideal.absNorm 𝔮), (1 : ℝ) / (r : ℝ) ^ 2 :=
                    sum_le_sum fun 𝔮 h𝔮 => by
                      have hle : (r : ℝ) ^ 2 ≤ (Ideal.absNorm 𝔮 : ℝ) := by
                        exact_mod_cast (mem_filter.mp h𝔮).2
                      exact div_le_div_of_nonneg_left zero_le_one (by positivity) hle
                _ = ((((UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})).toFinset).filter
                      (fun 𝔮 => r ^ 2 ≤ Ideal.absNorm 𝔮)).card : ℝ) * ((1 : ℝ) / (r : ℝ) ^ 2) := by simp
                _ ≤ (d : ℝ) * ((1 : ℝ) / (r : ℝ) ^ 2) := by
                    have h1 : (((UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})).toFinset).filter
                        (fun 𝔮 => r ^ 2 ≤ Ideal.absNorm 𝔮)).card ≤ d :=
                      (card_filter_le _ _).trans (hcard_over_le r hpr)
                    exact mul_le_mul_of_nonneg_right (by exact_mod_cast h1) (by positivity)
                _ = (d : ℝ) / (r : ℝ) ^ 2 := by ring
          _ ≤ ∑ n ∈ Ioc 1 (R₀ + 1), (d : ℝ) / (n : ℝ) ^ 2 := by
              refine sum_le_sum_of_subset_of_nonneg (fun r hr => ?_) (fun _ _ _ => by positivity)
              obtain ⟨hlt, hpr⟩ := Nat.mem_primesBelow.mp hr
              exact mem_Ioc.mpr ⟨hpr.one_lt, hlt.le⟩
          _ = (d : ℝ) * ∑ n ∈ Ioc 1 (R₀ + 1), (1 : ℝ) / (n : ℝ) ^ 2 := by
              rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
          _ ≤ (d : ℝ) * (1 / ((1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le 1 (R₀ + 1) le_rfl) (by positivity)
          _ ≤ 2 * (d : ℝ) := by norm_num; linarith [show (0 : ℝ) ≤ (d : ℝ) by positivity]
    calc Real.exp (-(4 * (d : ℝ) + 2))
        ≤ Real.exp (∑ 𝔮 ∈ BadSmall, (-2 / (Ideal.absNorm 𝔮 : ℝ))) := by
          apply Real.exp_le_exp.mpr
          have heq : ∑ 𝔮 ∈ BadSmall, (-2 / (Ideal.absNorm 𝔮 : ℝ)) =
              -2 * ∑ 𝔮 ∈ BadSmall, (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ) := by
            rw [mul_sum]; exact sum_congr rfl fun 𝔮 _ => by ring
          rw [heq]; linarith
      _ = ∏ 𝔮 ∈ BadSmall, Real.exp (-2 / (Ideal.absNorm 𝔮 : ℝ)) := Real.exp_sum BadSmall _
      _ ≤ ∏ 𝔮 ∈ BadSmall, (1 - (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)) :=
          prod_le_prod (fun _ _ => (Real.exp_pos _).le) hone_sub
  -- Inclusion-exclusion over `BadSmall`: for large `s`, count of `I` of class `C⁻¹` coprime to `BadSmall`
  -- divided by `s` tends to `cK * ∏_{𝔮 ∈ BadSmall} (1 - 1 / absNorm 𝔮) ≥ δ`!
  have hIE_tendsto := ie_good_count_tendsto C BadSmall (fun 𝔮 h𝔮 => ⟨(hBadSmall_prop 𝔮 h𝔮).1, (hBadSmall_prop 𝔮 h𝔮).2.1⟩)
  -- Pick `s ≥ 1` large enough that `IE_count(s) / s > δ / 2`!
  have hlim_ge : δ ≤ cK * ∏ 𝔮 ∈ BadSmall, (1 - (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)) := by
    calc δ = cK * Real.exp (-(4 * (d : ℝ) + 2)) := mul_comm _ _
      _ ≤ cK * ∏ 𝔮 ∈ BadSmall, (1 - (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)) :=
          mul_le_mul_of_nonneg_left hprod_lb hcK_pos.le
  have hev_large : ∀ᶠ s : ℝ in atTop,
      δ / 2 < (Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹ ∧
        ∀ 𝔮 ∈ BadSmall, ¬ 𝔮 ∣ I.1} : ℝ) / s :=
    (Filter.eventually_atTop.mpr (Metric.tendsto_atTop.mp hIE_tendsto (δ / 2) (by linarith))).mono fun s hs => by
      rw [Real.dist_eq] at hs; linarith [(abs_lt.mp hs).1, hlim_ge]
  obtain ⟨S₂, hS₂⟩ := eventually_atTop.mp hev_large
  let s : ℝ := max S₂ 10
  have hs_ge10 : 10 ≤ s := le_max_right _ _
  have hs_pos : 0 < s := by linarith
  have hIE_gt : (δ / 2) * s <
      (Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧ ClassGroup.mk0 I = C⁻¹ ∧
        ∀ 𝔮 ∈ BadSmall, ¬ 𝔮 ∣ I.1} : ℝ) :=
    (lt_div_iff₀ hs_pos).mp (hS₂ s (le_max_left _ _))
  -- Upper bound count of `I` of norm `≤ s` divisible by SOME bad prime `𝔮 ∉ BadSmall` by `≤ (δ / 4) * s`!
  have hfin_all : Finite {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s} := by
    have : Finite {I : (Ideal R)⁰ // Ideal.absNorm I.1 ≤ ⌊s⌋₊} := Ideal.finite_setOfPred_absNorm_le₀ ⌊s⌋₊
    exact Finite.of_injective (fun x : {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s} =>
      (⟨x.1, Nat.le_floor x.2⟩ : {I : (Ideal R)⁰ // Ideal.absNorm I.1 ≤ ⌊s⌋₊}))
      (fun a b h => Subtype.ext (Subtype.mk.inj h))
  let : Fintype {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s} := Fintype.ofFinite _
  let AllS : Finset {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s} := Finset.univ
  let GoodIE : Finset {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s} :=
    AllS.filter fun x => ClassGroup.mk0 x.1 = C⁻¹ ∧ ∀ 𝔮 ∈ BadSmall, ¬ 𝔮 ∣ x.1.1
  let TailBad : Finset {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s} :=
    AllS.filter fun x => ∃ 𝔮 ∈ UniqueFactorizationMonoid.normalizedFactors x.1.1,
      (¬ (Ideal.absNorm 𝔮).Prime ∨ Ideal.absNorm 𝔮 = l) ∧ 𝔮 ∉ BadSmall
  have hGoodIE_card : (δ / 2) * s < (GoodIE.card : ℝ) := by
    have heq : GoodIE.card = Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s ∧
        ClassGroup.mk0 I = C⁻¹ ∧ ∀ 𝔮 ∈ BadSmall, ¬ 𝔮 ∣ I.1} := by
      rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
      refine Nat.card_congr ?_
      exact
        { toFun := fun y => ⟨y.1.1, y.1.2, (mem_filter.mp y.2).2.1, (mem_filter.mp y.2).2.2⟩
          invFun := fun x => ⟨⟨x.1, x.2.1⟩, mem_filter.mpr ⟨mem_univ _, x.2.2.1, x.2.2.2⟩⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rwa [heq]
  -- Bound `TailBad.card ≤ C_all * s * (d / R₀) < (δ / 4) * s`!
  let M_s : ℕ := ⌊s⌋₊
  let BigBadPrimes : Finset (Ideal R) :=
    ((Ioc R₀ M_s).filter Nat.Prime).biUnion fun r =>
      ((UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})).toFinset).filter
        (fun 𝔮 => r ^ 2 ≤ Ideal.absNorm 𝔮)
  have hTail_sub : TailBad ⊆ BigBadPrimes.biUnion fun 𝔮 => AllS.filter (fun x => 𝔮 ∣ x.1.1) := by
    intro x hx
    obtain ⟨_, 𝔮, h𝔮_fac, h𝔮_bad, h𝔮_not⟩ := mem_filter.mp hx
    obtain ⟨hpr, hbot, hle⟩ := mem_normalizedFactors_prime h𝔮_fac
    obtain ⟨r, hr, hrfac, f, hf, hN⟩ := hprime_over 𝔮 hpr hbot
    have hr_gt : R₀ < r := by
      by_contra hleR; push Not at hleR
      apply h𝔮_not
      refine mem_filter.mpr ⟨mem_biUnion.mpr ⟨r, Nat.mem_primesBelow.mpr ⟨by omega, hr⟩,
        Multiset.mem_toFinset.mpr hrfac⟩, h𝔮_bad⟩
    have hrl : r ≠ l := by
      have : l + 10 ≤ R₀ := le_max_left _ _; omega
    have hnel : Ideal.absNorm 𝔮 ≠ l := by
      rw [hN]; intro heq
      have hrf : r ∣ r ^ f := dvd_pow_self r (show f ≠ 0 by omega)
      have : r = l := (Nat.prime_dvd_prime_iff_eq hr hl.out).mp (hrf.trans (heq ▸ dvd_refl l))
      exact hrl this
    have hnp : ¬ (Ideal.absNorm 𝔮).Prime := h𝔮_bad.resolve_right hnel
    have hf2 : 2 ≤ f := by
      by_contra hlt; push Not at hlt
      have hf1 : f = 1 := by omega
      rw [hf1, pow_one] at hN; exact hnp (hN ▸ hr)
    have h𝔮_le_s : Ideal.absNorm 𝔮 ≤ M_s := by
      have hdvd_x : 𝔮 ∣ x.1.1 := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h𝔮_fac
      have hle_n : Ideal.absNorm 𝔮 ≤ Ideal.absNorm x.1.1 := by
        obtain ⟨J, hJ⟩ := hdvd_x
        have hJ_pos : 0 < Ideal.absNorm J := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
          fun h0 => nonZeroDivisors.ne_zero x.1.2 (by rw [hJ, h0, Ideal.mul_bot]; rfl))
        rw [hJ, map_mul]; exact Nat.le_mul_of_pos_right _ hJ_pos
      exact hle_n.trans (Nat.le_floor x.2)
    have hr_le_Ms : r ≤ M_s := (Nat.le_self_pow (by omega : f ≠ 0) r).trans (hN ▸ h𝔮_le_s)
    refine mem_biUnion.mpr ⟨𝔮, mem_biUnion.mpr ⟨r, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hr_gt, hr_le_Ms⟩, hr⟩,
      mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hrfac, hN ▸ Nat.pow_le_pow_right hr.pos hf2⟩⟩,
      mem_filter.mpr ⟨mem_univ _, UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h𝔮_fac⟩⟩
  have hTail_card_le : (TailBad.card : ℝ) ≤ C_all * s * ((d : ℝ) / (R₀ : ℝ)) := by
    have h1 : TailBad.card ≤ ∑ 𝔮 ∈ BigBadPrimes, (AllS.filter (fun x => 𝔮 ∣ x.1.1)).card :=
      (card_le_card hTail_sub).trans card_biUnion_le
    have hper : ∀ 𝔮 ∈ BigBadPrimes,
        ((AllS.filter (fun x => 𝔮 ∣ x.1.1)).card : ℝ) ≤ C_all * s / (Ideal.absNorm 𝔮 : ℝ) := by
      intro 𝔮 h𝔮
      obtain ⟨r, hr, h𝔮f⟩ := mem_biUnion.mp h𝔮
      obtain ⟨h𝔮_in, _⟩ := mem_filter.mp h𝔮f
      obtain ⟨_, hbot, _⟩ := mem_normalizedFactors_prime (Multiset.mem_toFinset.mp h𝔮_in)
      let 𝔮0 : (Ideal R)⁰ := ⟨𝔮, mem_nonZeroDivisors_of_ne_zero hbot⟩
      have h𝔮_pos : (0 : ℝ) < (Ideal.absNorm 𝔮 : ℝ) :=
        Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hbot))
      by_cases hle1 : s / (Ideal.absNorm 𝔮 : ℝ) < 1
      · have hemp : AllS.filter (fun x => 𝔮 ∣ x.1.1) = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro x hx
          obtain ⟨J, hJ⟩ := (mem_filter.mp hx).2
          have hJ_pos : 1 ≤ Ideal.absNorm J := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
            fun h0 => nonZeroDivisors.ne_zero x.1.2 (by rw [hJ, h0, Ideal.mul_bot]; rfl))
          have hle_x : (Ideal.absNorm 𝔮 : ℝ) ≤ s := by
            have : Ideal.absNorm 𝔮 ≤ Ideal.absNorm x.1.1 := by
              rw [hJ, map_mul]; exact Nat.le_mul_of_pos_right _ hJ_pos
            exact (Nat.cast_le.mpr this).trans x.2
          have : 1 ≤ s / (Ideal.absNorm 𝔮 : ℝ) := (one_le_div h𝔮_pos).mpr hle_x
          linarith
        rw [hemp, card_empty, Nat.cast_zero]; positivity
      · push Not at hle1
        have hcard_le : (AllS.filter (fun x => 𝔮 ∣ x.1.1)).card ≤
            Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s / (Ideal.absNorm 𝔮 : ℝ)} := by
          rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
          have hfin' : Finite {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s / (Ideal.absNorm 𝔮 : ℝ)} := by
            have : Finite {I : (Ideal R)⁰ // Ideal.absNorm I.1 ≤ ⌊s / (Ideal.absNorm 𝔮 : ℝ)⌋₊} :=
              Ideal.finite_setOfPred_absNorm_le₀ ⌊s / (Ideal.absNorm 𝔮 : ℝ)⌋₊
            exact Finite.of_injective (fun y : {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s / (Ideal.absNorm 𝔮 : ℝ)} =>
              (⟨y.1, Nat.le_floor y.2⟩ : {I : (Ideal R)⁰ // Ideal.absNorm I.1 ≤ ⌊s / (Ideal.absNorm 𝔮 : ℝ)⌋₊}))
              (fun a b h => Subtype.ext (Subtype.mk.inj h))
          refine Nat.card_le_card_of_injective ?_ ?_
          · intro y
            let J := (mem_filter.mp y.2).2.choose
            have hJ : y.1.1.1 = 𝔮 * J := (mem_filter.mp y.2).2.choose_spec
            have hJ_ne : J ≠ ⊥ := fun h0 => nonZeroDivisors.ne_zero y.1.1.2 (by rw [hJ, h0, Ideal.mul_bot]; rfl)
            refine ⟨⟨J, mem_nonZeroDivisors_of_ne_zero hJ_ne⟩, ?_⟩
            rw [le_div_iff₀' h𝔮_pos, ← Nat.cast_mul, ← map_mul, ← hJ]; exact y.1.2
          · intro y1 y2 heq
            have h1 := (mem_filter.mp y1.2).2.choose_spec
            have h2 := (mem_filter.mp y2.2).2.choose_spec
            have hJeq : (mem_filter.mp y1.2).2.choose = (mem_filter.mp y2.2).2.choose :=
              congrArg (fun z => z.1.1) heq
            apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
            rw [h1, h2, hJeq]
        calc ((AllS.filter (fun x => 𝔮 ∣ x.1.1)).card : ℝ)
            ≤ (Nat.card {I : (Ideal R)⁰ // (Ideal.absNorm I.1 : ℝ) ≤ s / (Ideal.absNorm 𝔮 : ℝ)} : ℝ) := by
              exact_mod_cast hcard_le
          _ ≤ C_all * (s / (Ideal.absNorm 𝔮 : ℝ)) := hC_all _ hle1
          _ = C_all * s / (Ideal.absNorm 𝔮 : ℝ) := by ring
    have hsum_big : ∑ 𝔮 ∈ BigBadPrimes, (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ) ≤ (d : ℝ) / (R₀ : ℝ) := by
      calc ∑ 𝔮 ∈ BigBadPrimes, (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)
          ≤ ∑ r ∈ (Ioc R₀ M_s).filter Nat.Prime,
              ∑ 𝔮 ∈ ((UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})).toFinset).filter
                (fun 𝔮 => r ^ 2 ≤ Ideal.absNorm 𝔮), (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ) :=
            sum_biUnion_le_nonneg fun _ => by positivity
        _ ≤ ∑ r ∈ (Ioc R₀ M_s).filter Nat.Prime, (d : ℝ) / (r : ℝ) ^ 2 := by
            refine sum_le_sum fun r hr => ?_
            have hpr := (mem_filter.mp hr).2
            have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hpr.pos
            calc ∑ 𝔮 ∈ ((UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})).toFinset).filter
                    (fun 𝔮 => r ^ 2 ≤ Ideal.absNorm 𝔮), (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ)
                ≤ ∑ _𝔮 ∈ ((UniqueFactorizationMonoid.normalizedFactors (span {(r : R)})).toFinset).filter
                    (fun 𝔮 => r ^ 2 ≤ Ideal.absNorm 𝔮), (1 : ℝ) / (r : ℝ) ^ 2 :=
                  sum_le_sum fun 𝔮 h𝔮 => div_le_div_of_nonneg_left zero_le_one (by positivity)
                    (by exact_mod_cast (mem_filter.mp h𝔮).2)
              _ ≤ (d : ℝ) / (r : ℝ) ^ 2 := by
                  rw [sum_const, nsmul_eq_mul, show (d : ℝ) / (r : ℝ) ^ 2 = (d : ℝ) * (1 / (r : ℝ) ^ 2) by ring]
                  exact mul_le_mul_of_nonneg_right
                    (by exact_mod_cast (card_filter_le _ _).trans (hcard_over_le r hpr)) (by positivity)
        _ ≤ ∑ n ∈ Ioc R₀ M_s, (d : ℝ) / (n : ℝ) ^ 2 :=
            sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
        _ = (d : ℝ) * ∑ n ∈ Ioc R₀ M_s, (1 : ℝ) / (n : ℝ) ^ 2 := by
            rw [mul_sum]; exact sum_congr rfl fun n _ => by ring
        _ ≤ (d : ℝ) * (1 / (R₀ : ℝ)) := mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le R₀ M_s hR₀_ge1) (by positivity)
        _ = (d : ℝ) / (R₀ : ℝ) := by ring
    calc (TailBad.card : ℝ)
        ≤ ∑ 𝔮 ∈ BigBadPrimes, ((AllS.filter (fun x => 𝔮 ∣ x.1.1)).card : ℝ) := by exact_mod_cast h1
      _ ≤ ∑ 𝔮 ∈ BigBadPrimes, C_all * s / (Ideal.absNorm 𝔮 : ℝ) := sum_le_sum hper
      _ = C_all * s * ∑ 𝔮 ∈ BigBadPrimes, (1 : ℝ) / (Ideal.absNorm 𝔮 : ℝ) := by
          rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
      _ ≤ C_all * s * ((d : ℝ) / (R₀ : ℝ)) := mul_le_mul_of_nonneg_left hsum_big (by positivity)
  have hTail_lt : (TailBad.card : ℝ) < (GoodIE.card : ℝ) := by
    have h1 : C_all * s * ((d : ℝ) / (R₀ : ℝ)) < (δ / 4) * s := by
      have := mul_lt_mul_of_pos_right hR₀_tail hs_pos
      linarith [show C_all * s * ((d : ℝ) / (R₀ : ℝ)) = C_all * ((d : ℝ) / (R₀ : ℝ)) * s by ring]
    linarith
  have hne : (GoodIE \ TailBad).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : GoodIE ⊆ TailBad := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have hle : (GoodIE.card : ℝ) ≤ (TailBad.card : ℝ) := by exact_mod_cast card_le_card hsub
    linarith
  obtain ⟨x, hx⟩ := hne
  obtain ⟨hxG, hxT⟩ := mem_sdiff.mp hx
  obtain ⟨_, hcls, hno_small⟩ := mem_filter.mp hxG
  refine ⟨x.1, hcls, fun 𝔭 h𝔭 => ?_⟩
  by_contra hbad
  have hbad' : ¬ (Ideal.absNorm 𝔭).Prime ∨ Ideal.absNorm 𝔭 = l := by tauto
  by_cases hsm : 𝔭 ∈ BadSmall
  · exact hno_small 𝔭 hsm (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors h𝔭)
  · exact hxT (mem_filter.mpr ⟨mem_univ _, 𝔭, h𝔭, hbad', hsm⟩)

end IdealClassRepresentative

section PrimaryBoxBound

variable {l : ℕ} [hl : Fact l.Prime]

/-- Every ideal `𝔭` of class `C` coprime to `(l)` yields a primary generator `α` of `𝔭 * 𝔟`
    whose `coordR l` coordinates are bounded by `C_box * (absNorm 𝔭)^(1/(l-1))`. -/
theorem exists_primary_box_bound (hl2 : l ≠ 2) (C : ClassGroup (CycR l))
    (𝔟 : (Ideal (CycR l))⁰) (h𝔟_cls : ClassGroup.mk0 𝔟 = C⁻¹)
    (h𝔟_deg1 : ∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔟.1,
      (Ideal.absNorm 𝔭).Prime ∧ Ideal.absNorm 𝔭 ≠ l) :
    ∃ C_box : ℝ, 0 < C_box ∧
      ∀ (𝔭 : (Ideal (CycR l))⁰), ClassGroup.mk0 𝔭 = C → ¬ (𝔭.1 ≤ span {lamR l}) →
        ∃ α : CycR l, IsPrimary α ∧ span {α} = 𝔭.1 * 𝔟.1 ∧
          ∀ i : Fin (l - 1), |(coordR l α i : ℝ)| ≤
            C_box * (Ideal.absNorm 𝔭.1 : ℝ) ^ (1 / ((l - 1 : ℕ) : ℝ)) := by
  let K := CycK l
  let R := CycR l
  let d : ℕ := l - 1
  have hd_pos : 0 < d := by have := hl.out.two_le; omega
  have hfin_K : Module.finrank ℚ K = d := by
    rw [IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hl.out.pos),
      Nat.totient_prime hl.out]
  -- Bound on `normLeOne K`
  obtain ⟨M₁, hM₁⟩ := isBounded_iff_forall_norm_le.mp (NumberField.mixedEmbedding.fundamentalCone.isBounded_normLeOne K)
  let M : ℝ := max M₁ 1
  have hM_pos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  -- Build injective `ℝ`-linear map `L : (Fin d → ℝ) →ₗ[ℝ] mixedSpace K` agreeing with `mixedEmbedding ∘ (coordR l).symm`
  let L : (Fin d → ℝ) →ₗ[ℝ] NumberField.mixedEmbedding.mixedSpace K :=
    { toFun := fun v => ∑ i : Fin d, v i • NumberField.mixedEmbedding K (((coordR l).symm (Pi.single i 1) : R) : K)
      map_add' := fun u v => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c v => by simp [Finset.smul_sum, smul_smul] }
  have hL_coord : ∀ α : R, L (fun i => (coordR l α i : ℝ)) = NumberField.mixedEmbedding K (α : K) := by
    intro α
    dsimp [L]
    have hα_eq : α = ∑ i : Fin d, (coordR l α i) • (coordR l).symm (Pi.single i 1) := by
      apply (coordR l).injective
      ext j
      rw [map_sum, Finset.sum_apply]
      have hterm : ∀ i : Fin d, coordR l ((coordR l α i) • (coordR l).symm (Pi.single i 1)) j =
          if i = j then coordR l α i else 0 := fun i => by
        rw [map_zsmul, LinearEquiv.apply_symm_apply, Pi.smul_apply, zsmul_eq_mul, Pi.single_apply]
        by_cases h : j = i
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [sum_congr rfl fun i _ => hterm i]; simp
    conv_rhs => rw [hα_eq]
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_sum, map_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [map_zsmul, map_zsmul, ← NumberField.RingOfIntegers.coe_eq_algebraMap, ← Int.cast_smul_eq_zsmul ℝ]
  have hL_inj : Function.Injective L := by
    let bLat := NumberField.mixedEmbedding.latticeBasis K
    have hsurj : Function.Surjective L := by
      have hspan_top : LinearMap.range L = ⊤ := by
        rw [eq_top_iff, ← bLat.span_eq, Submodule.span_le]
        rintro y ⟨idx, rfl⟩
        have hy_lat : bLat idx ∈ NumberField.mixedEmbedding.integerLattice K := by
          rw [← NumberField.mixedEmbedding.mem_span_latticeBasis]
          exact Submodule.subset_span ⟨idx, rfl⟩
        obtain ⟨α, hα⟩ := hy_lat
        exact ⟨fun i => (coordR l α i : ℝ), (hL_coord α).trans hα⟩
      exact LinearMap.range_eq_top.mp hspan_top
    have hfin_eq : Module.finrank ℝ (Fin d → ℝ) = Module.finrank ℝ (NumberField.mixedEmbedding.mixedSpace K) := by
      rw [Module.finrank_fin_fun, Module.finrank_eq_card_basis bLat,
        ← Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := R),
        (zetaK_spec l).integralPowerBasis.finrank, integralPowerBasis_dim_eq l]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin_eq).mpr hsurj
  let L_linEquiv : (Fin d → ℝ) ≃ₗ[ℝ] NumberField.mixedEmbedding.mixedSpace K :=
    LinearEquiv.ofBijective L ⟨hL_inj, by
      have hfin_eq : Module.finrank ℝ (Fin d → ℝ) = Module.finrank ℝ (NumberField.mixedEmbedding.mixedSpace K) := by
        let bLat := NumberField.mixedEmbedding.latticeBasis K
        rw [Module.finrank_fin_fun, Module.finrank_eq_card_basis bLat,
          ← Module.finrank_eq_card_chooseBasisIndex (R := ℤ) (M := R),
          (zetaK_spec l).integralPowerBasis.finrank, integralPowerBasis_dim_eq l]
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin_eq).mp hL_inj⟩
  let L_inv : NumberField.mixedEmbedding.mixedSpace K →L[ℝ] (Fin d → ℝ) := L_linEquiv.symm.toContinuousLinearMap
  let K_L : ℝ := ‖L_inv‖ + 1
  have hKL_pos : 0 < K_L := by dsimp [K_L]; positivity
  have h𝔟_norm_pos : (0 : ℝ) < (Ideal.absNorm 𝔟.1 : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (nonZeroDivisors.ne_zero 𝔟.2)))
  let C_box : ℝ := K_L * M * (Ideal.absNorm 𝔟.1 : ℝ) ^ (1 / (d : ℝ))
  have hC_pos : 0 < C_box := by dsimp [C_box]; positivity
  refine ⟨C_box, hC_pos, fun 𝔭 h𝔭_cls hlam_𝔭 => ?_⟩
  -- `𝔭 * 𝔟` is principal since `ClassGroup.mk0 (𝔭 * 𝔟) = C * C⁻¹ = 1`
  have hprinc : Submodule.IsPrincipal (𝔭.1 * 𝔟.1) := by
    have hmk1 : ClassGroup.mk0 (𝔭 * 𝔟) = 1 := by rw [map_mul, h𝔭_cls, h𝔟_cls, mul_inv_cancel]
    have h1 := (ClassGroup.mk0_eq_one_iff (𝔭 * 𝔟).2).mp hmk1
    simpa using h1
  obtain ⟨α₀, hα₀⟩ := hprinc
  have hα₀_ne : α₀ ≠ 0 := fun h0 => by
    have hbot : 𝔭.1 * 𝔟.1 = ⊥ := by rw [hα₀, h0, Submodule.span_zero_singleton]
    exact mul_ne_zero (nonZeroDivisors.ne_zero 𝔭.2) (nonZeroDivisors.ne_zero 𝔟.2) hbot
  have hnorm_ne0 : NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding K (α₀ : K)) ≠ 0 := by
    rw [NumberField.mixedEmbedding.norm_eq_norm, Rat.cast_abs, abs_ne_zero, Rat.cast_ne_zero]
    intro h0
    have h1 : (α₀ : K) = 0 := Algebra.norm_eq_zero_iff.mp h0
    exact hα₀_ne (RingOfIntegers.ext (by rw [h1]; rfl))
  -- Move `α₀` into `fundamentalCone K` via a unit `u`
  obtain ⟨u, hu_cone⟩ := NumberField.mixedEmbedding.fundamentalCone.exists_unit_smul_mem hnorm_ne0
  let α₁ : R := (u : R) * α₀
  have hspan_α₁ : span {α₁} = 𝔭.1 * 𝔟.1 := by
    rw [show span {α₁} = span {α₀} from
      (Ideal.span_singleton_eq_span_singleton.mpr ⟨u, mul_comm α₀ (u : R)⟩).symm]
    exact hα₀.symm
  -- Check `¬ lamR l ∣ α₁`
  have hndvd_lam : ¬ lamR l ∣ α₁ := by
    intro hdvd
    have hle : span {α₁} ≤ span {lamR l} := Ideal.span_singleton_le_span_singleton.mpr hdvd
    rw [hspan_α₁] at hle
    have hpr_lam : (span {lamR l}).IsPrime := IsCyclotomicExtension.Rat.isPrime_span_zeta_sub_one' l (zetaK_spec l)
    rcases hpr_lam.mul_le.mp hle with h𝔭_le | h𝔟_le
    · exact absurd h𝔭_le hlam_𝔭
    · have hdvd_𝔟 : span {lamR l} ∣ 𝔟.1 := Ideal.dvd_iff_le.mpr h𝔟_le
      have hlam_bot : span {lamR l} ≠ ⊥ := by
        rw [ne_eq, Ideal.span_singleton_eq_bot]
        exact Prime.ne_zero (zetaK_spec l).zeta_sub_one_prime'
      obtain ⟨𝔮, h𝔮_mem, hassoc⟩ := UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
        (nonZeroDivisors.ne_zero 𝔟.2) (Ideal.prime_of_isPrime hlam_bot hpr_lam).irreducible hdvd_𝔟
      have h𝔮_eq : span {lamR l} = 𝔮 := associated_iff_eq.mp hassoc
      exact (h𝔟_deg1 𝔮 h𝔮_mem).2 (by rw [← h𝔮_eq, absNorm_span_lamR])
  -- Make `α = ζ^k * α₁` primary; it STILL stays in `fundamentalCone K`!
  obtain ⟨k, hk, hα_prim⟩ := exists_pow_zeta_mul_isPrimary hl2 hndvd_lam
  let α : R := zetaR l ^ k * α₁
  have huζ : IsUnit (zetaR l ^ k) := ((zetaR_spec l).isUnit hl.out.ne_zero).pow k
  have hspan_α : span {α} = 𝔭.1 * 𝔟.1 := by
    rw [show span {α} = span {α₁} from
      (Ideal.span_singleton_eq_span_singleton.mpr ⟨huζ.unit, mul_comm α₁ _⟩).symm, hspan_α₁]
  have hα_cone : NumberField.mixedEmbedding K (α : K) ∈ NumberField.mixedEmbedding.fundamentalCone K := by
    have hα₁_eq : NumberField.mixedEmbedding K (α₁ : K) = u • NumberField.mixedEmbedding K (α₀ : K) := by
      rw [NumberField.mixedEmbedding.unitSMul_smul, ← map_mul]; congr 1
    have hα₁_cone : NumberField.mixedEmbedding K (α₁ : K) ∈ NumberField.mixedEmbedding.fundamentalCone K := by
      rw [hα₁_eq]; exact hu_cone
    have htors_mem : huζ.unit ∈ NumberField.Units.torsion K := by
      rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      refine ⟨l, hl.out.pos, Units.ext ?_⟩
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one, ← pow_mul, mul_comm k l,
        pow_mul, (zetaR_spec l).pow_eq_one, one_pow]
    have h2 := NumberField.mixedEmbedding.fundamentalCone.torsion_smul_mem_of_mem hα₁_cone htors_mem
    have hα_eq : NumberField.mixedEmbedding K (α : K) = huζ.unit • NumberField.mixedEmbedding K (α₁ : K) := by
      rw [NumberField.mixedEmbedding.unitSMul_smul, ← map_mul]; congr 1
    rw [hα_eq]; exact h2
  -- Compute `mixedEmbedding.norm (mixedEmbedding K α) = absNorm 𝔭 * absNorm 𝔟`
  have hα_norm : NumberField.mixedEmbedding.norm (NumberField.mixedEmbedding K (α : K)) =
      (Ideal.absNorm 𝔭.1 : ℝ) * (Ideal.absNorm 𝔟.1 : ℝ) := by
    rw [NumberField.mixedEmbedding.norm_eq_norm, ← Algebra.coe_norm_int α, Rat.cast_abs, Rat.cast_intCast,
      ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast, ← Ideal.absNorm_span_singleton, hspan_α,
      map_mul, Nat.cast_mul]
  have h𝔭_norm_pos : (0 : ℝ) < (Ideal.absNorm 𝔭.1 : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (nonZeroDivisors.ne_zero 𝔭.2)))
  let Nα : ℝ := (Ideal.absNorm 𝔭.1 : ℝ) * (Ideal.absNorm 𝔟.1 : ℝ)
  have hNα_pos : 0 < Nα := mul_pos h𝔭_norm_pos h𝔟_norm_pos
  let t : ℝ := Nα ^ (-(1 / (d : ℝ)))
  have ht_pos : 0 < t := Real.rpow_pos_of_pos hNα_pos _
  have hscaled_mem : t • NumberField.mixedEmbedding K (α : K) ∈ NumberField.mixedEmbedding.fundamentalCone.normLeOne K := by
    refine ⟨NumberField.mixedEmbedding.fundamentalCone.smul_mem_of_mem hα_cone ht_pos.ne', ?_⟩
    change NumberField.mixedEmbedding.norm (t • NumberField.mixedEmbedding K (α : K)) ≤ 1
    rw [NumberField.mixedEmbedding.norm_smul, abs_of_pos ht_pos, hfin_K, hα_norm]
    have ht_pow : t ^ d = Nα⁻¹ := by
      dsimp [t]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNα_pos.le,
        show -(1 / (d : ℝ)) * (d : ℝ) = -1 by field_simp [(Nat.cast_pos.mpr hd_pos).ne'],
        Real.rpow_neg_one]
    rw [ht_pow, inv_mul_cancel₀ hNα_pos.ne']
  have hnorm_emb : ‖NumberField.mixedEmbedding K (α : K)‖ ≤ M * Nα ^ (1 / (d : ℝ)) := by
    have h1 : ‖t • NumberField.mixedEmbedding K (α : K)‖ ≤ M :=
      (hM₁ _ hscaled_mem).trans (le_max_left _ _)
    rw [norm_smul, Real.norm_of_nonneg ht_pos.le] at h1
    have ht_inv : t⁻¹ = Nα ^ (1 / (d : ℝ)) := by
      dsimp [t]; rw [Real.rpow_neg hNα_pos.le, inv_inv]
    calc ‖NumberField.mixedEmbedding K (α : K)‖
        = t⁻¹ * (t * ‖NumberField.mixedEmbedding K (α : K)‖) := by rw [inv_mul_cancel_left₀ ht_pos.ne']
      _ ≤ t⁻¹ * M := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr ht_pos.le)
      _ = M * Nα ^ (1 / (d : ℝ)) := by rw [ht_inv, mul_comm]
  refine ⟨α, hα_prim, hspan_α, fun i => ?_⟩
  have hv_eq : (fun j => (coordR l α j : ℝ)) = L_inv (NumberField.mixedEmbedding K (α : K)) := by
    rw [← hL_coord α]; exact (L_linEquiv.symm_apply_apply _).symm
  have hcoord_le : ‖(fun j => (coordR l α j : ℝ))‖ ≤ K_L * ‖NumberField.mixedEmbedding K (α : K)‖ := by
    rw [hv_eq]
    calc ‖L_inv (NumberField.mixedEmbedding K (α : K))‖
        ≤ ‖L_inv‖ * ‖NumberField.mixedEmbedding K (α : K)‖ := L_inv.le_opNorm _
      _ ≤ K_L * ‖NumberField.mixedEmbedding K (α : K)‖ :=
          mul_le_mul_of_nonneg_right (by dsimp [K_L]; linarith) (norm_nonneg _)
  have hi_le : |(coordR l α i : ℝ)| ≤ ‖(fun j => (coordR l α j : ℝ))‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (fun j => (coordR l α j : ℝ)) i
  calc |(coordR l α i : ℝ)|
      ≤ K_L * (M * Nα ^ (1 / (d : ℝ))) := hi_le.trans (hcoord_le.trans (mul_le_mul_of_nonneg_left hnorm_emb hKL_pos.le))
    _ = C_box * (Ideal.absNorm 𝔭.1 : ℝ) ^ (1 / (d : ℝ)) := by
        dsimp [C_box, Nα]
        rw [Real.mul_rpow h𝔭_norm_pos.le h𝔟_norm_pos.le]; ring

end PrimaryBoxBound

section LocalSieveDensities

variable (l : ℕ) [hl : Fact l.Prime]

/-- Residue classes mod `q` in `[0, q)^(l - 1)` forbidden by the `l`-th power residue condition
    `(α / (q))_l = w`. -/
noncomputable def forbiddenPowRes (q : ℕ) (w : CycR l) : Finset (Fin (l - 1) → ℕ) :=
  (Fintype.piFinset (fun _ : Fin (l - 1) => range q)).filter fun v =>
    ¬ (IsCoprime (span {(coordR l).symm (fun i => (v i : ℤ))}) (span {(q : CycR l)}) ∧
       powResIdeal ((coordR l).symm (fun i => (v i : ℤ))) (span {(q : CycR l)}) = w)

/-- Residue classes mod `r` in `[0, r)^(l - 1)` NOT coprime to `(r)`. -/
noncomputable def forbiddenSplit (r : ℕ) : Finset (Fin (l - 1) → ℕ) :=
  (Fintype.piFinset (fun _ : Fin (l - 1) => range r)).filter fun v =>
    ¬ IsCoprime (span {(coordR l).symm (fun i => (v i : ℤ))}) (span {(r : CycR l)})

omit hl in
lemma isCoprime_span_iff_isUnit_mk {q : ℕ} {α : CycR l} :
    IsCoprime (span {α}) (span {(q : CycR l)}) ↔
      IsUnit (Ideal.Quotient.mk (span {(q : CycR l)}) α) := by
  rw [Ideal.isCoprime_iff_exists]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton.mp ha
    refine isUnit_iff_exists_inv.mpr ⟨Ideal.Quotient.mk _ u, ?_⟩
    have hb0 : Ideal.Quotient.mk (span {(q : CycR l)}) b = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
    have h1 := congrArg (Ideal.Quotient.mk (span {(q : CycR l)})) hab
    rw [map_add, map_mul, map_one, hb0, add_zero] at h1
    exact h1
  · intro hu
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hu
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hmem : 1 - α * u ∈ span {(q : CycR l)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, hy, sub_self]
    exact ⟨α * u, Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _)),
      1 - α * u, hmem, by ring⟩

lemma not_mem_forbiddenPowRes_of_eq {q : ℕ} (hq : q.Prime) (hql : q ≠ l) {w α : CycR l}
    (hcop : IsCoprime (span {α}) (span {(q : CycR l)}))
    (heq : powResIdeal α (span {(q : CycR l)}) = w) :
    (fun i : Fin (l - 1) => (coordR l α i % (q : ℤ)).toNat) ∉ forbiddenPowRes l q w := by
  let v : Fin (l - 1) → ℕ := fun i => (coordR l α i % (q : ℤ)).toNat
  let α' : CycR l := (coordR l).symm (fun i => (v i : ℤ))
  have hsub : α - α' ∈ span {(q : CycR l)} := by
    rw [coordR_sub_mem_span_natCast]
    intro i
    simp only [α', LinearEquiv.apply_symm_apply, v]
    have hnn : 0 ≤ coordR l α i % (q : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hq.ne_zero)
    rw [Int.toNat_of_nonneg hnn]
    exact ⟨coordR l α i / (q : ℤ), by linarith [Int.emod_add_mul_ediv (coordR l α i) (q : ℤ)]⟩
  have hmk_eq : Ideal.Quotient.mk (span {(q : CycR l)}) α' = Ideal.Quotient.mk (span {(q : CycR l)}) α :=
    (Ideal.Quotient.eq.mpr hsub).symm
  have hcop' : IsCoprime (span {α'}) (span {(q : CycR l)}) := by
    rw [isCoprime_span_iff_isUnit_mk, hmk_eq, ← isCoprime_span_iff_isUnit_mk]; exact hcop
  have hres' : powResIdeal α' (span {(q : CycR l)}) = w := by
    rw [← powResIdeal_congr (isCoprime_lamR_span_prime hq hql) hcop hsub, heq]
  intro hm
  exact (mem_filter.mp hm).2 ⟨hcop', hres'⟩

lemma not_mem_forbiddenSplit_of_coprime {r : ℕ} (hr : r.Prime) {α : CycR l}
    (hcop : IsCoprime (span {α}) (span {(r : CycR l)})) :
    (fun i : Fin (l - 1) => (coordR l α i % (r : ℤ)).toNat) ∉ forbiddenSplit l r := by
  let v : Fin (l - 1) → ℕ := fun i => (coordR l α i % (r : ℤ)).toNat
  let α' : CycR l := (coordR l).symm (fun i => (v i : ℤ))
  have hsub : α - α' ∈ span {(r : CycR l)} := by
    rw [coordR_sub_mem_span_natCast]
    intro i
    simp only [α', LinearEquiv.apply_symm_apply, v]
    have hnn : 0 ≤ coordR l α i % (r : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hr.ne_zero)
    rw [Int.toNat_of_nonneg hnn]
    exact ⟨coordR l α i / (r : ℤ), by linarith [Int.emod_add_mul_ediv (coordR l α i) (r : ℤ)]⟩
  have hcop' : IsCoprime (span {α'}) (span {(r : CycR l)}) := by
    rw [isCoprime_span_iff_isUnit_mk, (Ideal.Quotient.eq.mpr hsub).symm, ← isCoprime_span_iff_isUnit_mk]
    exact hcop
  intro hm
  exact (mem_filter.mp hm).2 hcop'

/-- For prime `q ≠ l` and any `l`-th root of unity `w = ζ^k`, the allowed residue classes mod `q`
    form a coset of an index-`l` subgroup of `(R / q R)ˣ`, so `0 < q^d - |Ω q|` and
    `l * (q^d - |Ω q|) ≤ q^d`. -/
theorem forbiddenPowRes_card_bounds {q : ℕ} (hq : q.Prime) (hql : q ≠ l) {w : CycR l}
    (hw : ∃ k : ℕ, w = zetaR l ^ k) :
    (forbiddenPowRes l q w).card < q ^ (l - 1) ∧
    l * (q ^ (l - 1) - (forbiddenPowRes l q w).card) ≤ q ^ (l - 1) := by
  have : Fact q.Prime := ⟨hq⟩
  let A := CycR l ⧸ span {(q : CycR l)}
  have hq_bot : span {(q : CycR l)} ≠ ⊥ := by simp [hq.ne_zero]
  have : Finite A := Ring.HasFiniteQuotients.finiteQuotient hq_bot
  let : Fintype A := Fintype.ofFinite A
  have hcard_A : Fintype.card A = q ^ (l - 1) := by
    rw [← Nat.card_eq_fintype_card, ← absNorm_eq_card_quotient, Ideal.absNorm_span_natCast,
      (zetaK_spec l).integralPowerBasis.finrank, integralPowerBasis_dim_eq l]
  have hlam_cop := isCoprime_lamR_span_prime (l := l) hq hql
  -- Define group homomorphism `ψ : Aˣ →* (CycR l)ˣ` induced by `powResIdeal · (span {q})`
  have hres_unit : ∀ α : CycR l, IsUnit (powResIdeal α (span {(q : CycR l)})) := fun α => by
    refine isUnit_iff_exists_inv.mpr ⟨powResIdeal α (span {(q : CycR l)}) ^ (l - 1), ?_⟩
    rw [← pow_succ', show l - 1 + 1 = l by have := hl.out.one_lt; omega, powResIdeal_pow_l]
  have hψ_well : ∀ α β : CycR l, Ideal.Quotient.mk (span {(q : CycR l)}) α = Ideal.Quotient.mk _ β →
      IsUnit (Ideal.Quotient.mk (span {(q : CycR l)}) α) →
      powResIdeal α (span {(q : CycR l)}) = powResIdeal β (span {(q : CycR l)}) := fun α β heq hu =>
    powResIdeal_congr hlam_cop ((isCoprime_span_iff_isUnit_mk l).mpr hu) (Ideal.Quotient.eq.mp heq)
  let ψ : Aˣ →* (CycR l)ˣ :=
    { toFun := fun u =>
        let α := (Ideal.Quotient.mk_surjective u.val).choose
        (hres_unit α).unit
      map_one' := by
        apply Units.ext
        dsimp only; rw [IsUnit.unit_spec, Units.val_one]
        let α := (Ideal.Quotient.mk_surjective (1 : A)).choose
        have hα : Ideal.Quotient.mk (span {(q : CycR l)}) α = 1 :=
          (Ideal.Quotient.mk_surjective (1 : A)).choose_spec
        rw [hψ_well α 1 (by rw [hα, map_one]) (by rw [hα]; exact isUnit_one), powResIdeal_one hlam_cop]; rfl
      map_mul' := fun u v => by
        apply Units.ext
        dsimp only [Units.val_mul]; rw [IsUnit.unit_spec, IsUnit.unit_spec, IsUnit.unit_spec]
        let α := (Ideal.Quotient.mk_surjective u.val).choose
        let β := (Ideal.Quotient.mk_surjective v.val).choose
        let γ := (Ideal.Quotient.mk_surjective (u * v).val).choose
        have hα : Ideal.Quotient.mk (span {(q : CycR l)}) α = u.val := (Ideal.Quotient.mk_surjective u.val).choose_spec
        have hβ : Ideal.Quotient.mk (span {(q : CycR l)}) β = v.val := (Ideal.Quotient.mk_surjective v.val).choose_spec
        have hγ : Ideal.Quotient.mk (span {(q : CycR l)}) γ = (u * v).val := (Ideal.Quotient.mk_surjective (u * v).val).choose_spec
        have hαβ : Ideal.Quotient.mk (span {(q : CycR l)}) γ = Ideal.Quotient.mk _ (α * β) := by
          rw [map_mul, hα, hβ, hγ]; rfl
        rw [hψ_well γ (α * β) hαβ (by rw [hγ]; exact (u * v).isUnit),
          powResIdeal_mul_left hlam_cop ((isCoprime_span_iff_isUnit_mk l).mpr (by rw [hα]; exact u.isUnit))
            ((isCoprime_span_iff_isUnit_mk l).mpr (by rw [hβ]; exact v.isUnit))] }
  have hψ_apply : ∀ (u : Aˣ) (α : CycR l), Ideal.Quotient.mk (span {(q : CycR l)}) α = u.val →
      (ψ u : CycR l) = powResIdeal α (span {(q : CycR l)}) := by
    intro u α hα
    let α' := (Ideal.Quotient.mk_surjective u.val).choose
    have hα' : Ideal.Quotient.mk (span {(q : CycR l)}) α' = u.val := (Ideal.Quotient.mk_surjective u.val).choose_spec
    exact hψ_well α' α (hα'.trans hα.symm) (by rw [hα']; exact u.isUnit)
  -- `ψ` is nontrivial (hence `Im ψ` has cardinality `l` and contains `w`)!
  have hψ_nontriv : ∃ u : Aˣ, (ψ u : CycR l) ≠ 1 := by
    -- Pick a prime factor `𝔮` of `span {q}`
    have hfac_ne : (UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)})) ≠ 0 := by
      intro h0
      have h1 := Ideal.prod_normalizedFactors_eq_self hq_bot
      rw [h0, Multiset.prod_zero, Ideal.one_eq_top] at h1
      have hnorm := congrArg Ideal.absNorm h1
      rw [Ideal.absNorm_top, Ideal.absNorm_span_natCast, (zetaK_spec l).integralPowerBasis.finrank,
        integralPowerBasis_dim_eq l] at hnorm
      have : 1 < q ^ (l - 1) := one_lt_pow₀ hq.one_lt (by have := hl.out.two_le; omega)
      omega
    obtain ⟨𝔮₀, h𝔮₀_mem⟩ := Multiset.exists_mem_of_ne_zero hfac_ne
    -- Every prime factor of `span {q}` has multiplicity 1 since `q ≠ l` is unramified!
    have hnodup : (UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)})).Nodup := by
      rw [Multiset.nodup_iff_count_le_one]
      intro 𝔮
      by_cases hm : 𝔮 ∈ UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)})
      · obtain ⟨hpr, hbot, hle⟩ := mem_normalizedFactors_prime hm
        have : 𝔮.IsPrime := hpr
        have : 𝔮.LiesOver (Ideal.span {(q : ℤ)}) := by
          rw [Ideal.liesOver_iff]
          refine (Int.ideal_span_isMaximal_of_prime q).eq_of_le (hpr.comap _).ne_top ?_
          rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, algebraMap_int_eq, map_natCast]
          exact hle (Ideal.subset_span (Set.mem_singleton _))
        have hram : Ideal.ramificationIdx 𝔮 ℤ = 1 :=
          IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd q (CycK l) 𝔮
            (fun hd => hql ((Nat.prime_dvd_prime_iff_eq hq hl.out).mp hd))
        have hqZ_ne : (Ideal.span {(q : ℤ)}) ≠ ⊥ := by simp [hq.ne_zero]
        have hmap_q : Ideal.map (algebraMap ℤ (CycR l)) (Ideal.span {(q : ℤ)}) = span {(q : CycR l)} := by
          rw [Ideal.map_span, Set.image_singleton, algebraMap_int_eq, map_natCast]
        have hmult := IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {(q : ℤ)}) 𝔮 (by rwa [hmap_q])
        rw [hram, hmap_q] at hmult
        have hcnt_eq := UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors
          (Ideal.prime_of_isPrime hbot hpr).irreducible hq_bot
        have hnorm_𝔮 : normalize 𝔮 = 𝔮 := by simp
        rw [hnorm_𝔮, ← hmult] at hcnt_eq
        exact hcnt_eq.symm.le
      · rw [Multiset.count_eq_zero.mpr hm]; exact Nat.zero_le 1
    -- Pick a non-`l`-th power `g` in `(R ⧸ 𝔮₀)ˣ` and lift via CRT `Ideal.exists_forall_sub_mem_ideal`!
    obtain ⟨hpr0, hbot0, hle0⟩ := mem_normalizedFactors_prime h𝔮₀_mem
    have : 𝔮₀.IsPrime := hpr0; have : 𝔮₀.IsMaximal := hpr0.isMaximal hbot0
    let : Field (CycR l ⧸ 𝔮₀) := Ideal.Quotient.field 𝔮₀
    have : Finite (CycR l ⧸ 𝔮₀) := Ring.HasFiniteQuotients.finiteQuotient hbot0
    let : Fintype (CycR l ⧸ 𝔮₀) := Fintype.ofFinite _
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (CycR l ⧸ 𝔮₀)ˣ)
    obtain ⟨α_g, hα_g⟩ := Ideal.Quotient.mk_surjective (g.val)
    let S_q := (UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)})).toFinset
    have hpair : Pairwise (Function.onFun IsCoprime (fun x : S_q => x.1)) := by
      intro x1 x2 hne
      obtain ⟨h1, hb1, _⟩ := mem_normalizedFactors_prime (Multiset.mem_toFinset.mp x1.2)
      obtain ⟨h2, hb2, _⟩ := mem_normalizedFactors_prime (Multiset.mem_toFinset.mp x2.2)
      have hm1 := h1.isMaximal hb1; have hm2 := h2.isMaximal hb2
      dsimp only [Function.onFun]
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hnt
      exact hne (Subtype.ext ((hm1.eq_of_le hnt le_sup_left).trans (hm2.eq_of_le hnt le_sup_right).symm))
    obtain ⟨α, hα_crt⟩ := Ideal.exists_forall_sub_mem_ideal hpair
      (fun x : S_q => if x.1 = 𝔮₀ then α_g else 1)
    have hα_cop : IsCoprime (span {α}) (span {(q : CycR l)}) := by
      have hprod_S : S_q.val.prod = ∏ 𝔮 ∈ S_q, 𝔮 := by
        rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
      rw [← Ideal.prod_normalizedFactors_eq_self hq_bot,
        show (UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)})) = S_q.val from
          (Multiset.toFinset_val (UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)})) ▸ hnodup.dedup).symm,
        hprod_S]
      refine IsCoprime.prod_right fun 𝔮 h𝔮 => ?_
      obtain ⟨hpr, hbot, _⟩ := mem_normalizedFactors_prime (Multiset.mem_toFinset.mp h𝔮)
      have hm := hpr.isMaximal hbot
      have hnot_mem : α ∉ 𝔮 := by
        have hsub := hα_crt ⟨𝔮, h𝔮⟩
        by_cases h0 : 𝔮 = 𝔮₀
        · subst h0; simp only [↓reduceIte] at hsub
          intro hα0
          have h1 : Ideal.Quotient.mk 𝔮 α_g = 0 := by
            rw [← Ideal.Quotient.eq.mpr hsub, Ideal.Quotient.eq_zero_iff_mem.mpr hα0]
          rw [hα_g] at h1; exact g.ne_zero h1
        · simp only [h0, ↓reduceIte] at hsub
          intro hα0
          have h1 : (1 : CycR l) ∈ 𝔮 := by
            have : (1 : CycR l) = α - (α - 1) := by ring
            rw [this]; exact 𝔮.sub_mem hα0 hsub
          exact hpr.ne_top (Ideal.eq_top_of_isUnit_mem 𝔮 h1 isUnit_one)
      rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hnt
      have heq := hm.eq_of_le hnt le_sup_right
      exact hnot_mem (heq ▸ Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton _)))
    have hα_u : IsUnit (Ideal.Quotient.mk (span {(q : CycR l)}) α) :=
      (isCoprime_span_iff_isUnit_mk l).mp hα_cop
    refine ⟨hα_u.unit, ?_⟩
    have hψ_val : (ψ hα_u.unit : CycR l) = powResIdeal α (span {(q : CycR l)}) :=
      hψ_apply hα_u.unit α (by simp)
    rw [hψ_val]
    -- Compute `powResIdeal α (span {q}) = powResSymb α 𝔮₀ ≠ 1`!
    have hprod_eq : powResIdeal α (span {(q : CycR l)}) = powResSymb α 𝔮₀ := by
      unfold powResIdeal
      have hfac_val : UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)}) = S_q.val :=
        (Multiset.toFinset_val (UniqueFactorizationMonoid.normalizedFactors (span {(q : CycR l)})) ▸ hnodup.dedup).symm
      rw [hfac_val]
      change ∏ 𝔮 ∈ S_q, powResSymb α 𝔮 = powResSymb α 𝔮₀
      refine Finset.prod_eq_single 𝔮₀ (fun 𝔮 h𝔮 hne => ?_) (fun hnot => absurd (Multiset.mem_toFinset.mpr h𝔮₀_mem) hnot)
      obtain ⟨hpr, hbot, hle⟩ := mem_normalizedFactors_prime (Multiset.mem_toFinset.mp h𝔮)
      have : 𝔮.IsPrime := hpr
      have hlam𝔮 : lamR l ∉ 𝔮 := fun hm =>
        hpr.ne_top (eq_top_iff.mpr <| by rw [← hlam_cop.sup_eq]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hm) hle)
      have hsub := hα_crt ⟨𝔮, h𝔮⟩
      simp only [hne, ↓reduceIte] at hsub
      have h1_not : (1 : CycR l) ∉ 𝔮 := fun hm => hpr.ne_top (Ideal.eq_top_of_isUnit_mem 𝔮 hm isUnit_one)
      have hα_not : α ∉ 𝔮 := fun hm => h1_not (by
        have : (1 : CycR l) = α - (α - 1) := by ring
        rw [this]; exact 𝔮.sub_mem hm hsub)
      rw [powResSymb_congr hbot hlam𝔮 hα_not hsub, powResSymb_one hbot hlam𝔮]
    rw [hprod_eq]
    have hlam0 : lamR l ∉ 𝔮₀ := fun hm =>
      hpr0.ne_top (eq_top_iff.mpr <| by rw [← hlam_cop.sup_eq]; exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hm) hle0)
    have hsub0 := hα_crt ⟨𝔮₀, Multiset.mem_toFinset.mpr h𝔮₀_mem⟩
    simp only [↓reduceIte] at hsub0
    have hα0_not : α ∉ 𝔮₀ := fun hm => g.ne_zero (by
      rw [← hα_g, ← Ideal.Quotient.eq.mpr hsub0, Ideal.Quotient.eq_zero_iff_mem.mpr hm])
    intro h1
    obtain ⟨y, hy⟩ := (powResSymb_eq_one_iff_isPow hbot0 hlam0 hα0_not).mp h1
    rw [Ideal.Quotient.eq.mpr hsub0, hα_g] at hy
    have hy0 : y ≠ 0 := fun h0 => by rw [h0, zero_pow hl.out.ne_zero] at hy; exact g.ne_zero hy.symm
    let uy : (CycR l ⧸ 𝔮₀)ˣ := Units.mk0 y hy0
    have huy_pow : uy ^ l = g := Units.ext (by simpa [uy] using hy)
    -- Contradicts `g` generating `(R ⧸ 𝔮₀)ˣ` whose order is divisible by `l`!
    obtain ⟨m, hm⟩ : ∃ m : ℕ, g ^ m = uy := by
      obtain ⟨z, hz⟩ := hg uy; dsimp only at hz
      have hpos : 0 < orderOf g := orderOf_pos g
      refine ⟨(z % (orderOf g : ℤ)).toNat, ?_⟩
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg z (by exact_mod_cast hpos.ne')),
        zpow_mod_orderOf, hz]
    have hgm : g ^ (m * l) = g := by rw [pow_mul, hm, huy_pow]
    have hord_g : orderOf g = Ideal.absNorm 𝔮₀ - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units,
        ← Nat.card_eq_fintype_card, absNorm_eq_card_quotient]
    have hdvd_ml : (Ideal.absNorm 𝔮₀ - 1) ∣ (m * l - 1) := by
      have hm1 : 1 ≤ m * l := by
        by_contra h0; push Not at h0
        have : m * l = 0 := by omega
        rw [this, pow_zero] at hgm
        have : orderOf g = 1 := by rw [← hgm]; simp
        rw [hord_g] at this
        have hld := dvd_absNorm_sub_one hbot0 hlam0
        rw [this] at hld
        exact absurd (Nat.le_of_dvd zero_lt_one hld) (by have := hl.out.one_lt; omega)
      have hpow1 : g ^ (m * l - 1) = 1 := by
        apply mul_right_cancel (b := g)
        rw [← pow_succ, Nat.sub_add_cancel hm1, one_mul, hgm]
      exact hord_g ▸ orderOf_dvd_of_pow_eq_one hpow1
    have hl_dvd_1 : l ∣ (m * l - 1) := (dvd_absNorm_sub_one hbot0 hlam0).trans hdvd_ml
    have h1 : l ∣ 1 := by
      have hm1 : 1 ≤ m * l := by
        by_contra h0; push Not at h0
        have : m * l = 0 := by omega
        rw [this, pow_zero] at hgm
        have hord1 : orderOf g = 1 := by rw [← hgm]; simp
        rw [hord_g] at hord1
        exact absurd (Nat.le_of_dvd zero_lt_one (hord1 ▸ dvd_absNorm_sub_one hbot0 hlam0))
          (by have := hl.out.one_lt; omega)
      have hsub := Nat.dvd_sub (dvd_mul_left l m) hl_dvd_1
      rwa [Nat.sub_sub_self hm1] at hsub
    exact hl.out.not_dvd_one h1
  -- The image `ψ.range` is a subgroup of `μ_l` (card `l`) containing a non-identity element, so `Nat.card ψ.range = l`!
  let uζ : (CycR l)ˣ := ((zetaR_spec l).isUnit hl.out.ne_zero).unit
  have hrange_sub : ψ.range ≤ Subgroup.zpowers uζ := by
    rintro _ ⟨u, rfl⟩
    have hpowl : (ψ u : CycR l) ^ l = 1 := powResIdeal_pow_l _ _
    have hpowK : (((ψ u : CycR l) : CycK l)) ^ l = 1 := by
      rw [NumberField.RingOfIntegers.coe_eq_algebraMap, ← map_pow, hpowl, map_one]
    obtain ⟨k, _, hkeq⟩ := (zetaK_spec l).eq_pow_of_pow_eq_one hpowK
    refine ⟨(k : ℤ), Units.ext ?_⟩
    dsimp only
    rw [zpow_natCast, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    apply RingOfIntegers.ext
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap,
      map_pow, show algebraMap (CycR l) (CycK l) (zetaR l) = zetaK l from (zetaK_spec l).coe_toInteger]
    exact hkeq
  have hord_uζ : orderOf uζ = l := by
    rw [← orderOf_units, IsUnit.unit_spec]; exact (zetaR_spec l).eq_orderOf.symm
  have hcard_zpow : Nat.card (Subgroup.zpowers uζ) = l := by
    rw [Nat.card_zpowers, hord_uζ]
  have hrange_eq : ψ.range = Subgroup.zpowers uζ := by
    have hdvd := Subgroup.card_dvd_of_le hrange_sub
    rw [hcard_zpow] at hdvd
    rcases hl.out.eq_one_or_self_of_dvd _ hdvd with h1 | hl_eq
    · exfalso
      obtain ⟨u, hu⟩ := hψ_nontriv
      have : ψ u = 1 := by
        have hsub_sing : Subsingleton ψ.range := (Nat.card_eq_one_iff_unique.mp h1).1
        have := hsub_sing.elim ⟨ψ u, ⟨u, rfl⟩⟩ ⟨1, ψ.range.one_mem⟩
        exact congrArg Subtype.val this
      exact hu (by rw [this, Units.val_one])
    · have : Finite (Subgroup.zpowers uζ) := Nat.finite_of_card_ne_zero (by rw [hcard_zpow]; exact hl.out.ne_zero)
      exact Subgroup.eq_of_le_of_card_ge hrange_sub (by rw [hl_eq, hcard_zpow])
  -- Hence `w` is in `ψ.range` and `Fintype.card {u : Aˣ // (ψ u : CycR l) = w} = Fintype.card Aˣ / l`!
  obtain ⟨k, rfl⟩ := hw
  let uw : (CycR l)ˣ := uζ ^ k
  have huw_val : (uw : CycR l) = zetaR l ^ k := by simp [uw, uζ]
  have huw_mem : uw ∈ ψ.range := by rw [hrange_eq]; exact ⟨(k : ℤ), by simp [uw]⟩
  obtain ⟨u₀, hu₀⟩ := huw_mem
  have hfiber_card : Fintype.card {u : Aˣ // ψ u = uw} = Fintype.card ψ.ker := by
    refine Fintype.card_congr ?_
    exact
      { toFun := fun x => ⟨u₀⁻¹ * x.1, by simp [MonoidHom.mem_ker, x.2, hu₀]⟩
        invFun := fun y => ⟨u₀ * y.1, by simp [hu₀, MonoidHom.mem_ker.mp y.2]⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun y => Subtype.ext (by simp) }
  have hlag : Fintype.card Aˣ = Fintype.card ψ.ker * l := by
    have h1 := Subgroup.card_mul_index ψ.ker
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    have hidx : ψ.ker.index = Nat.card ψ.range := by
      rw [Subgroup.index, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    rw [hidx, hrange_eq, hcard_zpow] at h1
    exact h1.symm
  -- Connect `(Fintype.piFinset _ \ forbiddenPowRes l q w).card` to `Fintype.card {u : Aˣ // ψ u = uw}`!
  let Box := Fintype.piFinset (fun _ : Fin (l - 1) => range q)
  have hBox_card : Box.card = q ^ (l - 1) := by simp [Box]
  have hcompl_card : q ^ (l - 1) - (forbiddenPowRes l q (zetaR l ^ k)).card = Fintype.card {u : Aˣ // ψ u = uw} := by
    have hsub : forbiddenPowRes l q (zetaR l ^ k) ⊆ Box := filter_subset _ _
    rw [← hBox_card, ← Finset.card_sdiff_of_subset hsub]
    have hsdiff_eq : Box \ forbiddenPowRes l q (zetaR l ^ k) =
        Box.filter fun v => IsCoprime (span {(coordR l).symm (fun i => (v i : ℤ))}) (span {(q : CycR l)}) ∧
          powResIdeal ((coordR l).symm (fun i => (v i : ℤ))) (span {(q : CycR l)}) = zetaR l ^ k := by
      ext v; simp only [Finset.mem_sdiff, forbiddenPowRes, mem_filter, Box]; tauto
    rw [hsdiff_eq, ← Fintype.card_coe]
    let bij := Equiv.ofBijective _ (mod_box_bijective l hq.pos)
    refine Fintype.card_congr ?_
    refine
      { toFun := fun v =>
          let hv := mem_filter.mp v.2
          let hu : IsUnit (bij ⟨v.1, hv.1⟩) := (isCoprime_span_iff_isUnit_mk l).mp hv.2.1
          ⟨hu.unit, Units.ext ?_⟩
        invFun := fun u =>
          let v := bij.symm u.1.val
          ⟨v.1, mem_filter.mpr ⟨v.2, ?_, ?_⟩⟩
        left_inv := fun v => by
          apply Subtype.ext
          change (bij.symm (bij ⟨v.1, (mem_filter.mp v.2).1⟩)).1 = v.1
          exact congrArg Subtype.val (bij.symm_apply_apply ⟨v.1, (mem_filter.mp v.2).1⟩)
        right_inv := fun u => by
          apply Subtype.ext; apply Units.ext
          change bij (bij.symm u.1.val) = u.1.val
          exact bij.apply_symm_apply u.1.val }
    · rw [huw_val, hψ_apply hu.unit ((coordR l).symm (fun i => (v.1 i : ℤ))) (by simp [bij]), hv.2.2]
    · rw [isCoprime_span_iff_isUnit_mk]
      have hmk : Ideal.Quotient.mk (span {(q : CycR l)}) ((coordR l).symm (fun i => (v.1 i : ℤ))) = u.1.val :=
        bij.apply_symm_apply u.1.val
      rw [hmk]; exact u.1.isUnit
    · have hmk : Ideal.Quotient.mk (span {(q : CycR l)}) ((coordR l).symm (fun i => (v.1 i : ℤ))) = u.1.val :=
        bij.apply_symm_apply u.1.val
      have hu2 := congrArg Units.val u.2
      rw [huw_val] at hu2
      rw [← hu2, hψ_apply u.1 _ hmk]
  have hker_pos : 0 < Fintype.card ψ.ker := Fintype.card_pos
  have hA_ge : Fintype.card Aˣ ≤ q ^ (l - 1) := by
    rw [← hcard_A]; exact Fintype.card_le_of_injective Units.val (fun _ _ h => Units.ext h)
  constructor
  · omega
  · rw [hcompl_card, hfiber_card, mul_comm, ← hlag]; exact hA_ge

/-- For prime `r ≡ 1 (mod l)`, `(r^d - |forbiddenSplit l r|) = (r - 1)^d`. -/
theorem forbiddenSplit_card_compl {r : ℕ} (hr : r.Prime) (hr_mod : r % l = 1) :
    r ^ (l - 1) - (forbiddenSplit l r).card = (r - 1) ^ (l - 1) := by
  have : Fact r.Prime := ⟨hr⟩
  have hrl : r ≠ l := fun h => by rw [h, Nat.mod_self] at hr_mod; exact zero_ne_one hr_mod
  have hr_bot : span {(r : CycR l)} ≠ ⊥ := by simp [hr.ne_zero]
  let A := CycR l ⧸ span {(r : CycR l)}
  have : Finite A := Ring.HasFiniteQuotients.finiteQuotient hr_bot
  let : Fintype A := Fintype.ofFinite A
  -- Connect `r^d - |forbiddenSplit l r|` to `Fintype.card Aˣ`
  let Box := Fintype.piFinset (fun _ : Fin (l - 1) => range r)
  have hBox_card : Box.card = r ^ (l - 1) := by simp [Box]
  have hcompl_eq : r ^ (l - 1) - (forbiddenSplit l r).card = Fintype.card Aˣ := by
    have hsub : forbiddenSplit l r ⊆ Box := filter_subset _ _
    rw [← hBox_card, ← Finset.card_sdiff_of_subset hsub]
    have hsdiff : Box \ forbiddenSplit l r =
        Box.filter fun v => IsCoprime (span {(coordR l).symm (fun i => (v i : ℤ))}) (span {(r : CycR l)}) := by
      ext v; simp only [Finset.mem_sdiff, forbiddenSplit, mem_filter, Box]; tauto
    rw [hsdiff, ← Fintype.card_coe]
    let bij := Equiv.ofBijective _ (mod_box_bijective l hr.pos)
    refine Fintype.card_congr ?_
    exact
      { toFun := fun v => ((isCoprime_span_iff_isUnit_mk l).mp (mem_filter.mp v.2).2).unit
        invFun := fun u =>
          let v := bij.symm u.val
          ⟨v.1, mem_filter.mpr ⟨v.2, (isCoprime_span_iff_isUnit_mk l).mpr (by
            have h := bij.apply_symm_apply u.val; dsimp [bij] at h; rw [h]; exact u.isUnit)⟩⟩
        left_inv := fun v => by
          apply Subtype.ext
          change (bij.symm (bij ⟨v.1, (mem_filter.mp v.2).1⟩)).1 = v.1
          exact congrArg Subtype.val (bij.symm_apply_apply ⟨v.1, (mem_filter.mp v.2).1⟩)
        right_inv := fun u => by
          apply Units.ext
          change bij (bij.symm u.val) = u.val
          exact bij.apply_symm_apply u.val }
  rw [hcompl_eq]
  -- By CRT, `A ≃+* (∀ 𝔯 ∈ S_r, R ⧸ 𝔯)`, where each `𝔯` has `inertiaDeg = 1`, `ramificationIdx = 1`, `|S_r| = l - 1`!
  let fac := UniqueFactorizationMonoid.normalizedFactors (span {(r : CycR l)})
  have hper : ∀ 𝔯 ∈ fac, Ideal.absNorm 𝔯 = r ∧ Multiset.count 𝔯 fac = 1 := by
    intro 𝔯 h𝔯
    obtain ⟨hpr, hbot, hle⟩ := mem_normalizedFactors_prime h𝔯
    have : 𝔯.IsPrime := hpr; have : 𝔯.IsMaximal := hpr.isMaximal hbot
    have : 𝔯.LiesOver (Ideal.span {(r : ℤ)}) := by
      rw [Ideal.liesOver_iff]
      refine (Int.ideal_span_isMaximal_of_prime r).eq_of_le (hpr.comap _).ne_top ?_
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, algebraMap_int_eq, map_natCast]
      exact hle (Ideal.subset_span (Set.mem_singleton _))
    have hndvd : ¬ r ∣ l := fun hd => hrl ((Nat.prime_dvd_prime_iff_eq hr hl.out).mp hd)
    have hord1 : orderOf (r : ZMod l) = 1 := by
      rw [orderOf_eq_one_iff]
      have hmod : r ≡ 1 [MOD l] := by rw [Nat.ModEq, hr_mod, Nat.mod_eq_of_lt hl.out.one_lt]
      simpa using (ZMod.natCast_eq_natCast_iff r 1 l).mpr hmod
    have hdeg : Ideal.inertiaDeg 𝔯 ℤ = 1 := by
      rw [IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd r (CycK l) 𝔯 hndvd, hord1]
    have hram : Ideal.ramificationIdx 𝔯 ℤ = 1 :=
      IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd r (CycK l) 𝔯 hndvd
    have hN : Ideal.absNorm 𝔯 = r := by rw [← Ideal.pow_inertiaDeg r 𝔯, hdeg, pow_one]
    have hcnt : Multiset.count 𝔯 fac = 1 := by
      have hmap_r : Ideal.map (algebraMap ℤ (CycR l)) (Ideal.span {(r : ℤ)}) = span {(r : CycR l)} := by
        rw [Ideal.map_span, Set.image_singleton, algebraMap_int_eq, map_natCast]
      have hmult := IsDedekindDomain.ramificationIdx_eq_multiplicity (Ideal.span {(r : ℤ)}) 𝔯 (by rwa [hmap_r])
      rw [hram, hmap_r] at hmult
      have hcnt_eq := UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors
        (Ideal.prime_of_isPrime hbot hpr).irreducible hr_bot
      have hnorm_𝔯 : normalize 𝔯 = 𝔯 := by simp
      rw [hnorm_𝔯, ← hmult] at hcnt_eq
      exact hcnt_eq.symm
    exact ⟨hN, hcnt⟩
  have hnodup : fac.Nodup := Multiset.nodup_iff_count_le_one.mpr fun 𝔯 => by
    by_cases hm : 𝔯 ∈ fac
    · rw [(hper 𝔯 hm).2]
    · rw [Multiset.count_eq_zero.mpr hm]; exact Nat.zero_le 1
  let S_r := fac.toFinset
  have hSr_card : S_r.card = l - 1 := by
    have habs : Ideal.absNorm (span {(r : CycR l)}) = r ^ (l - 1) := by
      rw [Ideal.absNorm_span_natCast, (zetaK_spec l).integralPowerBasis.finrank, integralPowerBasis_dim_eq l]
    have habs2 : Ideal.absNorm (span {(r : CycR l)}) = r ^ S_r.card := by
      have hprod_S : S_r.val.prod = ∏ 𝔯 ∈ S_r, 𝔯 := by
        rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
      rw [← Ideal.prod_normalizedFactors_eq_self hr_bot]
      change Ideal.absNorm fac.prod = r ^ S_r.card
      rw [show fac = S_r.val from (Multiset.toFinset_val fac ▸ hnodup.dedup).symm, hprod_S,
        map_prod, prod_congr rfl fun 𝔯 h𝔯 => (hper 𝔯 (Multiset.mem_toFinset.mp h𝔯)).1, prod_const]
    rw [habs] at habs2
    exact (Nat.pow_right_injective hr.one_lt habs2).symm
  have hpair : Pairwise (Function.onFun IsCoprime (fun x : S_r => x.1)) := by
    intro x1 x2 hne
    obtain ⟨h1, hb1, _⟩ := mem_normalizedFactors_prime (Multiset.mem_toFinset.mp x1.2)
    obtain ⟨h2, hb2, _⟩ := mem_normalizedFactors_prime (Multiset.mem_toFinset.mp x2.2)
    have hm1 := h1.isMaximal hb1; have hm2 := h2.isMaximal hb2
    dsimp only [Function.onFun]
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hnt
    exact hne (Subtype.ext ((hm1.eq_of_le hnt le_sup_left).trans (hm2.eq_of_le hnt le_sup_right).symm))
  have hinf_eq : (⨅ x : S_r, x.1) = span {(r : CycR l)} := by
    have hprod_S : S_r.val.prod = ∏ 𝔯 ∈ S_r, 𝔯 := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [← Ideal.prod_normalizedFactors_eq_self hr_bot]
    change (⨅ x : S_r, x.1) = fac.prod
    rw [show fac = S_r.val from (Multiset.toFinset_val fac ▸ hnodup.dedup).symm, hprod_S,
      ← Finset.prod_attach S_r (fun 𝔯 => 𝔯)]
    have hinf_prod : (⨅ x ∈ (univ : Finset S_r), x.1) = ∏ x ∈ (univ : Finset S_r), x.1 :=
      (Ideal.prod_eq_iInf_of_pairwise_isCoprime (fun x _ y _ hne => hpair hne)).symm
    simpa [iInf_subtype'] using hinf_prod
  let crt : A ≃+* (∀ x : S_r, CycR l ⧸ x.1) :=
    (Ideal.quotEquivOfEq hinf_eq.symm).trans (Ideal.quotientInfRingEquivPiQuotient (fun x : S_r => x.1) hpair)
  have hu_equiv : Aˣ ≃ (∀ x : S_r, (CycR l ⧸ x.1)ˣ) :=
    (Units.mapEquiv crt.toMulEquiv).toEquiv.trans MulEquiv.piUnits.toEquiv
  have hcard_each : ∀ x : S_r, Nat.card (CycR l ⧸ x.1)ˣ = r - 1 := fun x => by
    obtain ⟨hpr, hbot, _⟩ := mem_normalizedFactors_prime (Multiset.mem_toFinset.mp x.2)
    have : x.1.IsMaximal := hpr.isMaximal hbot
    let : Field (CycR l ⧸ x.1) := Ideal.Quotient.field x.1
    have : Finite (CycR l ⧸ x.1) := Ring.HasFiniteQuotients.finiteQuotient hbot
    let : Fintype (CycR l ⧸ x.1) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
      ← absNorm_eq_card_quotient, (hper x.1 (Multiset.mem_toFinset.mp x.2)).1]
  rw [← Nat.card_eq_fintype_card, Nat.card_congr hu_equiv, Nat.card_pi,
    prod_congr rfl fun x _ => hcard_each x, prod_const, card_univ, Fintype.card_coe, hSr_card]

end LocalSieveDensities

end Erdos980Box

/-
# Proof of Elliott's Tail Estimate for Prime Exponents (`Erdos980.erdos_980.R1.H2`)

Combines:
- `M1`: reduction of `H2` to `SievePatternBound l`.
- `M2`: `d`-dimensional Montgomery arithmetic large sieve (`arith_large_sieve_nd`).
- `M3`: Rankin-truncated squarefree sieve-sum lower bound (`rankin_sieve_sum_lower`).
- `M4`: Cyclotomic arithmetic, Stickelberger elements, and Eisenstein reciprocity (`eisenstein_reciprocity_deg1`).
- `M5`: Degree-1 ideal class representatives, fundamental cone box bounds, and local sieve densities.
-/

namespace Erdos980Main

open Ideal NumberField RingOfIntegers Finset Filter Asymptotics
open Erdos980 Erdos980H2 Erdos980LS Erdos980Mertens Erdos980Eisenstein Erdos980Box
open scoped BigOperators Classical nonZeroDivisors Topology

section SharedSieveHelpers

/-- Product expansion `∏ q ∈ S, (1 + f q) = ∑ T ∈ S.powerset, ∏ q ∈ T, f q`. -/
private lemma prod_one_add_eq_powerset (S : Finset ℕ) (f : ℕ → ℝ) :
    ∏ q ∈ S, (1 + f q) = ∑ T ∈ S.powerset, ∏ q ∈ T, f q := by
  have h : ∏ q ∈ S, (1 + f q) = ∏ q ∈ S, (f q + 1) := prod_congr rfl fun _ _ => add_comm _ _
  rw [h, Finset.prod_add f (fun _ => (1 : ℝ)) S]
  refine sum_congr rfl fun T _ => by simp

/-- Splitting the squarefree large-sieve denominator into the product over `S`
    (prescribed primes) times the Rankin sum over squarefree `m ≤ Z` built from
    primes `r ≡ 1 (mod l)` outside `Bad` (with `S ⊆ Bad` and `(∏ S) * Z ≤ Q`). -/
lemma sieve_sum_split_of_prod {d l Q Z : ℕ} (_hZ : 1 ≤ Z)
    (Ω : ℕ → Finset (Fin d → ℕ))
    (hΩ : ∀ p, p.Prime → Ω p ⊆ Fintype.piFinset (fun _ : Fin d => range p))
    (S Bad : Finset ℕ) (hS_pr : ∀ q ∈ S, q.Prime) (hS_sub : S ⊆ Bad)
    (hMZ : (∏ q ∈ S, q) * Z ≤ Q)
    (hsplit_lb : ∀ r : ℕ, r.Prime → r % l = 1 → r ∉ Bad → r ≤ Z →
      (((l - 1 : ℕ) : ℝ) / (r : ℝ)) ≤ hfacND d Ω r) :
    (∏ q ∈ S, (1 + hfacND d Ω q)) *
      (∑ m ∈ (Icc 1 Z).filter (fun m => Squarefree m ∧ ∀ r ∈ m.primeFactors, r % l = 1 ∧ r ∉ Bad),
        ∏ r ∈ m.primeFactors, (((l - 1 : ℕ) : ℝ) / (r : ℝ))) ≤
    ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfacND d Ω p := by
  let Sm := (Icc 1 Z).filter (fun m => Squarefree m ∧ ∀ r ∈ m.primeFactors, r % l = 1 ∧ r ∉ Bad)
  have hprod_S_pos : 0 < ∏ q ∈ S, q := prod_pos fun q hq => (hS_pr q hq).pos
  have hstep1 :
      (∏ q ∈ S, (1 + hfacND d Ω q)) *
        (∑ m ∈ Sm, ∏ r ∈ m.primeFactors, (((l - 1 : ℕ) : ℝ) / (r : ℝ))) ≤
      (∏ q ∈ S, (1 + hfacND d Ω q)) *
        (∑ m ∈ Sm, ∏ r ∈ m.primeFactors, hfacND d Ω r) := by
    apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun q hq => by
      linarith [hfacND_nonneg Ω q (hΩ q (hS_pr q hq))])
    refine sum_le_sum fun m hm => prod_le_prod (fun _ _ => by positivity) fun r hr => ?_
    obtain ⟨hmIcc, _, hmpf⟩ := mem_filter.mp hm
    have hm1 : 1 ≤ m := (mem_Icc.mp hmIcc).1
    have hmZ : m ≤ Z := (mem_Icc.mp hmIcc).2
    have hr_pr : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hr_le : r ≤ Z := (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hr)).trans hmZ
    exact hsplit_lb r hr_pr (hmpf r hr).1 (hmpf r hr).2 hr_le
  refine hstep1.trans ?_
  rw [prod_one_add_eq_powerset, sum_mul_sum]
  let φ : Finset ℕ × ℕ → ℕ := fun x => (∏ q ∈ x.1, q) * x.2
  have hpf_T : ∀ T ∈ S.powerset, (∏ q ∈ T, q).primeFactors = T ∧ Squarefree (∏ q ∈ T, q) ∧ 0 < ∏ q ∈ T, q := by
    intro T hT
    have hTS : T ⊆ S := mem_powerset.mp hT
    have hTpr : ∀ q ∈ T, q.Prime := fun q hq => hS_pr q (hTS hq)
    have hpos : 0 < ∏ q ∈ T, q := prod_pos fun q hq => (hTpr q hq).pos
    have hpf : (∏ q ∈ T, q).primeFactors = T := by
      ext r
      rw [Nat.mem_primeFactors_of_ne_zero hpos.ne']
      constructor
      · rintro ⟨hr, hdvd⟩
        obtain ⟨q, hqT, hrq⟩ := (hr.prime.dvd_finsetProd_iff id).mp hdvd
        exact (Nat.prime_dvd_prime_iff_eq hr (hTpr q hqT)).mp hrq ▸ hqT
      · intro hrT; exact ⟨hTpr r hrT, dvd_prod_of_mem id hrT⟩
    have hsq : Squarefree (∏ q ∈ T, q) := by
      clear hT hTS hpos hpf
      induction T using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [prod_insert ha]
        have hapr : a.Prime := hTpr a (mem_insert_self a s)
        have hcop : Nat.Coprime a (∏ q ∈ s, q) := by
          refine Nat.Coprime.prod_right fun q hq => ?_
          have hqpr := hTpr q (mem_insert_of_mem hq)
          exact (Nat.coprime_primes hapr hqpr).mpr (fun heq => ha (heq ▸ hq))
        exact (Nat.squarefree_mul hcop).mpr ⟨hapr.squarefree,
          ih (fun b hb => hTpr b (mem_insert_of_mem hb))⟩
    exact ⟨hpf, hsq, hpos⟩
  have hcop_pair : ∀ x ∈ S.powerset ×ˢ Sm,
      Nat.Coprime (∏ q ∈ x.1, q) x.2 ∧ Disjoint x.1 x.2.primeFactors := by
    rintro ⟨T, m⟩ hx
    obtain ⟨hT, hm⟩ := mem_product.mp hx
    have hTS : T ⊆ S := mem_powerset.mp hT
    have hdisj : Disjoint T m.primeFactors := by
      rw [Finset.disjoint_left]
      intro r hrT hrm
      exact ((mem_filter.mp hm).2.2 r hrm).2 (hS_sub (hTS hrT))
    have hcop : Nat.Coprime (∏ q ∈ T, q) m := by
      refine Nat.Coprime.prod_left fun q hqT => ?_
      have hqpr := hS_pr q (hTS hqT)
      rw [hqpr.coprime_iff_not_dvd]
      intro hdvd
      have hm0 : m ≠ 0 := by have := (mem_Icc.mp (mem_filter.mp hm).1).1; omega
      exact Finset.disjoint_left.mp hdisj hqT (Nat.mem_primeFactors.mpr ⟨hqpr, hdvd, hm0⟩)
    exact ⟨hcop, hdisj⟩
  have hmap : ∀ x ∈ S.powerset ×ˢ Sm, φ x ∈ (Icc 1 Q).filter Squarefree := by
    rintro ⟨T, m⟩ hx
    obtain ⟨hT, hm⟩ := mem_product.mp hx
    obtain ⟨_, hsqT, hposT⟩ := hpf_T T hT
    obtain ⟨hmIcc, hsqm, _⟩ := mem_filter.mp hm
    obtain ⟨hcop, _⟩ := hcop_pair (T, m) hx
    have hT_le : ∏ q ∈ T, q ≤ ∏ q ∈ S, q := by
      have hTS : T ⊆ S := mem_powerset.mp hT
      rw [← Finset.prod_sdiff hTS]
      exact Nat.le_mul_of_pos_left _ (prod_pos fun q hq => (hS_pr q (mem_sdiff.mp hq).1).pos)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, (Nat.squarefree_mul hcop).mpr ⟨hsqT, hsqm⟩⟩
    · exact Nat.mul_pos hposT (by have := (mem_Icc.mp hmIcc).1; omega)
    · exact (Nat.mul_le_mul hT_le (mem_Icc.mp hmIcc).2).trans hMZ
  have hpf_phi : ∀ x ∈ S.powerset ×ˢ Sm, (φ x).primeFactors = x.1 ∪ x.2.primeFactors := by
    rintro ⟨T, m⟩ hx
    obtain ⟨hT, hm⟩ := mem_product.mp hx
    obtain ⟨hpfT, _, hposT⟩ := hpf_T T hT
    have hm0 : m ≠ 0 := by have := (mem_Icc.mp (mem_filter.mp hm).1).1; omega
    dsimp [φ]
    rw [Nat.primeFactors_mul hposT.ne' hm0, hpfT]
  have hinj : Set.InjOn φ ((S.powerset ×ˢ Sm : Finset _) : Set _) := by
    rintro ⟨T1, m1⟩ hx1 ⟨T2, m2⟩ hx2 heq
    have hx1' : (T1, m1) ∈ S.powerset ×ˢ Sm := hx1
    have hx2' : (T2, m2) ∈ S.powerset ×ˢ Sm := hx2
    have hT1_eq : (φ (T1, m1)).primeFactors ∩ S = T1 := by
      rw [hpf_phi _ hx1', Finset.union_inter_distrib_right]
      have h1 : T1 ∩ S = T1 := Finset.inter_eq_left.mpr (mem_powerset.mp (mem_product.mp hx1').1)
      have h2 : m1.primeFactors ∩ S = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro r hr
        obtain ⟨hrm, hrS⟩ := mem_inter.mp hr
        exact ((mem_filter.mp (mem_product.mp hx1').2).2.2 r hrm).2 (hS_sub hrS)
      rw [h1, h2, union_empty]
    have hT2_eq : (φ (T2, m2)).primeFactors ∩ S = T2 := by
      rw [hpf_phi _ hx2', Finset.union_inter_distrib_right]
      have h1 : T2 ∩ S = T2 := Finset.inter_eq_left.mpr (mem_powerset.mp (mem_product.mp hx2').1)
      have h2 : m2.primeFactors ∩ S = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro r hr
        obtain ⟨hrm, hrS⟩ := mem_inter.mp hr
        exact ((mem_filter.mp (mem_product.mp hx2').2).2.2 r hrm).2 (hS_sub hrS)
      rw [h1, h2, union_empty]
    have hTeq : T1 = T2 := by rw [← hT1_eq, ← hT2_eq, heq]
    subst hTeq
    have hposT := (hpf_T T1 (mem_product.mp hx1').1).2.2
    exact Prod.ext rfl (mul_left_cancel₀ hposT.ne' heq)
  have hval : ∀ x ∈ S.powerset ×ˢ Sm,
      (∏ q ∈ x.1, hfacND d Ω q) * (∏ r ∈ x.2.primeFactors, hfacND d Ω r) =
        ∏ p ∈ (φ x).primeFactors, hfacND d Ω p := fun x hx => by
    rw [hpf_phi x hx, Finset.prod_union (hcop_pair x hx).2]
  rw [← Finset.sum_product']
  calc ∑ x ∈ S.powerset ×ˢ Sm, (∏ q ∈ x.1, hfacND d Ω q) * (∏ r ∈ x.2.primeFactors, hfacND d Ω r)
      = ∑ x ∈ S.powerset ×ˢ Sm, ∏ p ∈ (φ x).primeFactors, hfacND d Ω p := sum_congr rfl hval
    _ = ∑ q ∈ (S.powerset ×ˢ Sm).image φ, ∏ p ∈ q.primeFactors, hfacND d Ω p :=
        (Finset.sum_image (f := fun q : ℕ => ∏ p ∈ q.primeFactors, hfacND d Ω p) hinj).symm
    _ ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfacND d Ω p :=
        sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr hmap) fun q _ _ =>
          prod_nonneg fun p hp => hfacND_nonneg Ω p (hΩ p (Nat.prime_of_mem_primeFactors hp))

/-- Asymptotic primorial and parameter bounds for `Q = ⌊x^(1/(2d))⌋` and `2^j ≤ (log x)^10`. -/
lemma primorial_params_eventually (d : ℕ) (hd : 1 ≤ d) :
    ∀ᶠ x : ℝ in atTop,
      100 ≤ x ∧
      1 ≤ ⌊x ^ (1 / (2 * (d : ℝ)))⌋₊ ∧
      (⌊x ^ (1 / (2 * (d : ℝ)))⌋₊ : ℝ) * (Real.log x / x) ≤ 1 / (Real.log x) ^ 10 ∧
      ∀ (j : ℕ), (2 : ℝ) ^ j ≤ (Real.log x) ^ 10 →
        ∀ S : Finset ℕ, S ⊆ (range j).image (Nat.nth Nat.Prime) →
          let Q := ⌊x ^ (1 / (2 * (d : ℝ)))⌋₊
          let M := ∏ q ∈ S, q
          let Z := Q / M
          10 ≤ Z ∧
          (1 / (5 * (d : ℝ))) * Real.log x ≤ Real.log (Z : ℝ) ∧
          (∀ q ∈ S, q < Q) := by
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨J₁, hJ₁⟩ := eventually_atTop.mp nth_prime_le_sq_eventually
  let C₁ : ℕ := max (Nat.nth Nat.Prime J₁) 1
  have hnth_le : ∀ i : ℕ, Nat.nth Nat.Prime i ≤ C₁ * (i + 1) ^ 2 := fun i => by
    by_cases hi : J₁ ≤ i
    · calc Nat.nth Nat.Prime i ≤ i ^ 2 := hJ₁ i hi
        _ ≤ 1 * (i + 1) ^ 2 := by nlinarith
        _ ≤ C₁ * (i + 1) ^ 2 := Nat.mul_le_mul_right _ (le_max_right _ _)
    · push Not at hi
      have hmono := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone hi.le
      calc Nat.nth Nat.Prime i ≤ Nat.nth Nat.Prime J₁ := hmono
        _ ≤ C₁ := le_max_left _ _
        _ = C₁ * 1 := (mul_one _).symm
        _ ≤ C₁ * (i + 1) ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
  -- Key little-o limits as `x → ∞`
  have hlog11 : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ 11 ≤ x ^ ((1 : ℝ) / 2) := by
    have h1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 22)).bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [h1, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hnn : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul] at hx
    calc (Real.log x) ^ 11 ≤ (x ^ ((1 : ℝ) / 22)) ^ 11 := pow_le_pow_left₀ hnn hx 11
      _ = x ^ ((1 : ℝ) / 22 * 11) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
      _ = x ^ ((1 : ℝ) / 2) := by norm_num
  have hlog_small : ∀ᶠ x : ℝ in atTop,
      20 * Real.log (Real.log x) * Real.log ((C₁ : ℝ) * (20 * Real.log (Real.log x) + 1) ^ 2) ≤
        (1 / (4 * (d : ℝ))) * Real.log x := by
    let K_c : ℝ := 20 * ((C₁ : ℝ) * 441 + 2)
    have hKc_pos : 0 < K_c := by dsimp [K_c]; positivity
    have h1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
      (show 0 < 1 / Real.sqrt (4 * (d : ℝ) * K_c) by positivity)
    have hcomp := Real.tendsto_log_atTop.eventually h1
    have h2 := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.exp 2))
    filter_upwards [hcomp, h2] with x hx1 hx2
    set L : ℝ := Real.log x
    have hL_ge : Real.exp 2 ≤ L := hx2
    have hL_pos : 0 < L := lt_of_lt_of_le (Real.exp_pos 2) hL_ge
    have hLL_ge2 : 2 ≤ Real.log L := by
      have := Real.log_le_log (Real.exp_pos 2) hL_ge; rwa [Real.log_exp] at this
    have hLL_pos : 0 < Real.log L := by linarith
    have hLL_le : Real.log L ≤ (1 / Real.sqrt (4 * (d : ℝ) * K_c)) * L ^ ((1 : ℝ) / 2) := by
      simpa [L, Real.norm_of_nonneg hLL_pos.le, Real.norm_of_nonneg (Real.rpow_nonneg hL_pos.le _)] using hx1
    have hLL_sq : (Real.log L) ^ 2 ≤ (1 / (4 * (d : ℝ) * K_c)) * L := by
      have hsq := pow_le_pow_left₀ hLL_pos.le hLL_le 2
      rw [mul_pow, div_pow, one_pow, Real.sq_sqrt (by positivity)] at hsq
      have hL_sq : (L ^ ((1 : ℝ) / 2)) ^ 2 = L := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le]; norm_num
      rwa [hL_sq] at hsq
    have hC1_ge1 : (1 : ℝ) ≤ C₁ := by exact_mod_cast le_max_right (Nat.nth Nat.Prime J₁) 1
    have hlog_arg : Real.log ((C₁ : ℝ) * (20 * Real.log L + 1) ^ 2) ≤ ((C₁ : ℝ) * 441 + 2) * Real.log L := by
      have harg_le : (C₁ : ℝ) * (20 * Real.log L + 1) ^ 2 ≤ ((C₁ : ℝ) * 441) * (Real.log L) ^ 2 := by
        have h1' : 20 * Real.log L + 1 ≤ 21 * Real.log L := by linarith
        have h2' : (20 * Real.log L + 1) ^ 2 ≤ (21 * Real.log L) ^ 2 := pow_le_pow_left₀ (by linarith) h1' 2
        nlinarith
      calc Real.log ((C₁ : ℝ) * (20 * Real.log L + 1) ^ 2)
          ≤ Real.log (((C₁ : ℝ) * 441) * (Real.log L) ^ 2) := Real.log_le_log (by positivity) harg_le
        _ = Real.log ((C₁ : ℝ) * 441) + Real.log ((Real.log L) ^ 2) := Real.log_mul (by positivity) (by positivity)
        _ = Real.log ((C₁ : ℝ) * 441) + 2 * Real.log (Real.log L) := by rw [Real.log_pow]; norm_num
        _ ≤ (C₁ : ℝ) * 441 + 2 * Real.log L := by
            have ha := Real.log_le_sub_one_of_pos (show 0 < (C₁ : ℝ) * 441 by positivity)
            have hb := Real.log_le_sub_one_of_pos hLL_pos
            linarith
        _ ≤ ((C₁ : ℝ) * 441 + 2) * Real.log L := by nlinarith
    calc 20 * Real.log L * Real.log ((C₁ : ℝ) * (20 * Real.log L + 1) ^ 2)
        ≤ 20 * Real.log L * (((C₁ : ℝ) * 441 + 2) * Real.log L) :=
          mul_le_mul_of_nonneg_left hlog_arg (by positivity)
      _ = K_c * (Real.log L) ^ 2 := by dsimp [K_c]; ring
      _ ≤ K_c * ((1 / (4 * (d : ℝ) * K_c)) * L) := mul_le_mul_of_nonneg_left hLL_sq hKc_pos.le
      _ = (1 / (4 * (d : ℝ))) * L := by field_simp [hKc_pos.ne', hd_pos.ne']
  have hx_pow : ∀ᶠ x : ℝ in atTop,
      20 ≤ x ^ (1 / (4 * (d : ℝ))) ∧ 4 ≤ x ^ (1 / (20 * (d : ℝ))) := by
    have ht1 : Tendsto (fun x : ℝ => x ^ (1 / (4 * (d : ℝ)))) atTop atTop :=
      tendsto_rpow_atTop (by positivity)
    have ht2 : Tendsto (fun x : ℝ => x ^ (1 / (20 * (d : ℝ)))) atTop atTop :=
      tendsto_rpow_atTop (by positivity)
    exact (ht1.eventually_ge_atTop 20).and (ht2.eventually_ge_atTop 4)
  filter_upwards [eventually_ge_atTop (100 : ℝ), hlog11, hlog_small, hx_pow] with x hx100 h11 hsm ⟨hp4, hp20⟩
  have hx_pos : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hL_pos : 0 < Real.log x := Real.log_pos hx1
  have hQ_ge20 : (20 : ℝ) ≤ x ^ (1 / (2 * (d : ℝ))) := by
    calc (20 : ℝ) ≤ x ^ (1 / (4 * (d : ℝ))) := hp4
      _ ≤ x ^ (1 / (2 * (d : ℝ))) := Real.rpow_le_rpow_of_exponent_le hx1.le
          (div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith))
  have hQ1 : 1 ≤ ⌊x ^ (1 / (2 * (d : ℝ)))⌋₊ := Nat.le_floor (by linarith)
  have hQ_small : (⌊x ^ (1 / (2 * (d : ℝ)))⌋₊ : ℝ) * (Real.log x / x) ≤ 1 / (Real.log x) ^ 10 := by
    have hfl : (⌊x ^ (1 / (2 * (d : ℝ)))⌋₊ : ℝ) ≤ x ^ ((1 : ℝ) / 2) := by
      calc (⌊x ^ (1 / (2 * (d : ℝ)))⌋₊ : ℝ) ≤ x ^ (1 / (2 * (d : ℝ))) := Nat.floor_le (by positivity)
        _ ≤ x ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hx1.le
            (div_le_div_of_nonneg_left zero_le_one (by norm_num) (by
              have : (1 : ℝ) ≤ d := by exact_mod_cast hd
              linarith))
    rw [← mul_div_assoc, div_le_div_iff₀ hx_pos (by positivity), one_mul]
    calc (⌊x ^ (1 / (2 * (d : ℝ)))⌋₊ : ℝ) * Real.log x * (Real.log x) ^ 10
        = (⌊x ^ (1 / (2 * (d : ℝ)))⌋₊ : ℝ) * (Real.log x) ^ 11 := by ring
      _ ≤ x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2) := mul_le_mul hfl h11 (by positivity) (by positivity)
      _ = x := by rw [← Real.rpow_add hx_pos]; norm_num
  refine ⟨hx100, hQ1, hQ_small, fun j hj S hS => ?_⟩
  let Q := ⌊x ^ (1 / (2 * (d : ℝ)))⌋₊
  let M := ∏ q ∈ S, q
  let Z := Q / M
  have hS_pr : ∀ q ∈ S, q.Prime := fun q hq => by
    obtain ⟨i, _, rfl⟩ := mem_image.mp (hS hq)
    exact Nat.prime_nth_prime i
  have hM_pos : 0 < M := prod_pos fun q hq => (hS_pr q hq).pos
  have hj_le : (j : ℝ) ≤ 20 * Real.log (Real.log x) := by
    have hlog_pow := Real.log_le_log (by positivity) hj
    rw [Real.log_pow, Real.log_pow] at hlog_pow
    push_cast at hlog_pow
    have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith
  have hM_le_rpow : (M : ℝ) ≤ x ^ (1 / (4 * (d : ℝ))) := by
    have hcard_S : S.card ≤ j := (card_le_card hS).trans (card_image_le.trans (by simp))
    have hq_bound : ∀ q ∈ S, (q : ℝ) ≤ (C₁ : ℝ) * (20 * Real.log (Real.log x) + 1) ^ 2 := fun q hq => by
      obtain ⟨i, hi, rfl⟩ := mem_image.mp (hS hq)
      have hil : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (mem_range.mp hi)
      calc (Nat.nth Nat.Prime i : ℝ) ≤ (C₁ : ℝ) * ((i : ℝ) + 1) ^ 2 := by exact_mod_cast hnth_le i
        _ ≤ (C₁ : ℝ) * (20 * Real.log (Real.log x) + 1) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    have harg_ge1 : (1 : ℝ) ≤ (C₁ : ℝ) * (20 * Real.log (Real.log x) + 1) ^ 2 := by
      have hC1 : (1 : ℝ) ≤ C₁ := by exact_mod_cast le_max_right (Nat.nth Nat.Prime J₁) 1
      have hLL_nn : 0 ≤ Real.log (Real.log x) := Real.log_nonneg (by
        have h1 : (1 : ℝ) ≤ Real.log 100 := by
          have : Real.exp 1 ≤ 100 := by linarith [Real.exp_one_lt_d9]
          have := Real.log_le_log (Real.exp_pos 1) this; rwa [Real.log_exp] at this
        exact h1.trans (Real.log_le_log (by norm_num) hx100))
      nlinarith
    have hM_pow : (M : ℝ) ≤ ((C₁ : ℝ) * (20 * Real.log (Real.log x) + 1) ^ 2) ^ j := by
      calc (M : ℝ) = ∏ q ∈ S, (q : ℝ) := by dsimp [M]; rw [Nat.cast_prod]
        _ ≤ ∏ _q ∈ S, ((C₁ : ℝ) * (20 * Real.log (Real.log x) + 1) ^ 2) :=
            prod_le_prod (fun _ _ => Nat.cast_nonneg _) hq_bound
        _ = ((C₁ : ℝ) * (20 * Real.log (Real.log x) + 1) ^ 2) ^ S.card := by rw [prod_const]
        _ ≤ ((C₁ : ℝ) * (20 * Real.log (Real.log x) + 1) ^ 2) ^ j := pow_le_pow_right₀ harg_ge1 hcard_S
    have hlogM : Real.log (M : ℝ) ≤ (1 / (4 * (d : ℝ))) * Real.log x := by
      calc Real.log (M : ℝ)
          ≤ Real.log (((C₁ : ℝ) * (20 * Real.log (Real.log x) + 1) ^ 2) ^ j) :=
            Real.log_le_log (Nat.cast_pos.mpr hM_pos) hM_pow
        _ = (j : ℝ) * Real.log ((C₁ : ℝ) * (20 * Real.log (Real.log x) + 1) ^ 2) := by rw [Real.log_pow]
        _ ≤ (20 * Real.log (Real.log x)) * Real.log ((C₁ : ℝ) * (20 * Real.log (Real.log x) + 1) ^ 2) :=
            mul_le_mul_of_nonneg_right hj_le (Real.log_nonneg harg_ge1)
        _ ≤ (1 / (4 * (d : ℝ))) * Real.log x := hsm
    have hexp := Real.exp_le_exp.mpr hlogM
    rw [Real.exp_log (Nat.cast_pos.mpr hM_pos), mul_comm (1 / (4 * (d : ℝ))) (Real.log x),
      ← Real.rpow_def_of_pos hx_pos] at hexp
    exact hexp
  have hQ_ge_half : (1 / 2 : ℝ) * x ^ (1 / (2 * (d : ℝ))) ≤ (Q : ℝ) := by
    have hlt := Nat.lt_floor_add_one (x ^ (1 / (2 * (d : ℝ))))
    linarith
  have hZ_real_ge : x ^ (1 / (5 * (d : ℝ))) ≤ (Z : ℝ) := by
    have hQM_ge : (1 / 2 : ℝ) * x ^ (1 / (4 * (d : ℝ))) ≤ (Q : ℝ) / (M : ℝ) := by
      rw [le_div_iff₀ (Nat.cast_pos.mpr hM_pos)]
      calc (1 / 2 : ℝ) * x ^ (1 / (4 * (d : ℝ))) * (M : ℝ)
          ≤ (1 / 2 : ℝ) * x ^ (1 / (4 * (d : ℝ))) * x ^ (1 / (4 * (d : ℝ))) :=
            mul_le_mul_of_nonneg_left hM_le_rpow (by positivity)
        _ = (1 / 2 : ℝ) * x ^ (1 / (2 * (d : ℝ))) := by
            rw [mul_assoc, ← Real.rpow_add hx_pos]
            congr 2; field_simp [hd_pos.ne']; ring
        _ ≤ (Q : ℝ) := hQ_ge_half
    have hdiv_fl : (Q : ℝ) / (M : ℝ) - 1 ≤ (Z : ℝ) := by
      have hrem : Q % M < M := Nat.mod_lt Q hM_pos
      have hdiv_eq : Q = M * Z + Q % M := (Nat.div_add_mod Q M).symm
      have hdiv_r : (Q : ℝ) = (M : ℝ) * (Z : ℝ) + ((Q % M : ℕ) : ℝ) := by exact_mod_cast hdiv_eq
      have hrem_r : ((Q % M : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast hrem
      have hMp : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
      rw [sub_le_iff_le_add, div_le_iff₀ hMp]
      nlinarith
    have hpow_split : x ^ (1 / (4 * (d : ℝ))) = x ^ (1 / (5 * (d : ℝ))) * x ^ (1 / (20 * (d : ℝ))) := by
      rw [← Real.rpow_add hx_pos]
      congr 1; field_simp [hd_pos.ne']; ring
    have hx5_ge1 : (1 : ℝ) ≤ x ^ (1 / (5 * (d : ℝ))) := Real.one_le_rpow hx1.le (by positivity)
    nlinarith
  have hZ10 : 10 ≤ Z := by
    have h10M : 10 * M ≤ Q := by
      have h10M_r : ((10 * M : ℕ) : ℝ) ≤ (Q : ℝ) := by
        push_cast
        calc (10 : ℝ) * (M : ℝ)
            ≤ ((1 / 2 : ℝ) * x ^ (1 / (4 * (d : ℝ)))) * x ^ (1 / (4 * (d : ℝ))) :=
              mul_le_mul (by linarith) hM_le_rpow (Nat.cast_nonneg _) (by positivity)
          _ = (1 / 2 : ℝ) * x ^ (1 / (2 * (d : ℝ))) := by
              rw [mul_assoc, ← Real.rpow_add hx_pos]
              congr 2; field_simp [hd_pos.ne']; ring
          _ ≤ (Q : ℝ) := hQ_ge_half
      exact_mod_cast h10M_r
    exact (Nat.le_div_iff_mul_le hM_pos).mpr (by linarith)
  have hlogZ : (1 / (5 * (d : ℝ))) * Real.log x ≤ Real.log (Z : ℝ) := by
    have := Real.log_le_log (by positivity) hZ_real_ge
    rwa [Real.log_rpow hx_pos] at this
  have hq_lt_Q : ∀ q ∈ S, q < Q := fun q hq => by
    have hq_le_M : q ≤ M := Nat.le_of_dvd hM_pos (dvd_prod_of_mem id hq)
    have hM_lt_Q : M < Q := by
      have h10M : 10 * M ≤ Q := (Nat.le_div_iff_mul_le hM_pos).mp hZ10
      omega
    omega
  exact ⟨hZ10, hlogZ, hq_lt_Q⟩

end SharedSieveHelpers

section CaseTwo

/-- For an odd prime `q` and `s ∈ {1, -1}`, the number of `a ∈ range q` with
    `legendreSym q a ≠ s` is `(q + 1) / 2`. -/
private lemma card_legendre_ne {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ((Fintype.piFinset (fun _ : Fin 1 => range q)).filter
      (fun v => legendreSym q (v 0 : ℤ) ≠ s)).card = (q + 1) / 2 := by
  have hq : q.Prime := Fact.out
  have hodd : q % 2 = 1 := by have := hq.eq_two_or_odd; omega
  have hcard_pi : (Fintype.piFinset (fun _ : Fin 1 => range q)).card = q := by simp
  let Box := Fintype.piFinset (fun _ : Fin 1 => range q)
  have hcompl : (Box.filter (fun v => legendreSym q (v 0 : ℤ) = s)).card = (q - 1) / 2 := by
    have hbij : (Box.filter (fun v => legendreSym q (v 0 : ℤ) = s)).card =
        (univ.filter (fun a : ZMod q => legendreSym q (a.val : ℤ) = s)).card := by
      refine Finset.card_bij (fun v _ => (v 0 : ZMod q)) ?_ ?_ ?_
      · intro v hv
        obtain ⟨hvB, hleg⟩ := mem_filter.mp hv
        have hvlt : v 0 < q := mem_range.mp (Fintype.mem_piFinset.mp hvB 0)
        refine mem_filter.mpr ⟨mem_univ _, ?_⟩
        rwa [ZMod.val_natCast_of_lt hvlt]
      · intro v1 hv1 v2 hv2 heq
        have h1 : v1 0 < q := mem_range.mp (Fintype.mem_piFinset.mp (mem_filter.mp hv1).1 0)
        have h2 : v2 0 < q := mem_range.mp (Fintype.mem_piFinset.mp (mem_filter.mp hv2).1 0)
        have hv0 : v1 0 = v2 0 := by
          have := congrArg ZMod.val heq
          rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at this
        funext i; fin_cases i; exact hv0
      · intro a ha
        refine ⟨fun _ => a.val, mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun _ => mem_range.mpr a.val_lt,
          (mem_filter.mp ha).2⟩, by simp⟩
    rw [hbij]
    let U := (ZMod q)ˣ
    have hcard_U : Fintype.card U = q - 1 := by rw [ZMod.card_units_eq_totient, Nat.totient_prime hq]
    have hnz_eq : univ.filter (fun a : ZMod q => legendreSym q (a.val : ℤ) = s) =
        (univ.filter (fun a : ZMod q => a ≠ 0)).filter (fun a => legendreSym q (a.val : ℤ) = s) := by
      ext a; simp only [mem_filter, mem_univ, true_and]
      constructor
      · intro h
        refine ⟨fun h0 => ?_, h⟩
        have hleg0 : legendreSym q (0 : ℤ) = 0 := (legendreSym.eq_zero_iff q 0).mpr (by simp)
        rw [h0, ZMod.val_zero, Nat.cast_zero, hleg0] at h
        rcases hs with rfl | rfl <;> omega
      · exact And.right
    have hcard_eq_U : (univ.filter (fun a : ZMod q => legendreSym q (a.val : ℤ) = s)).card =
        (univ.filter (fun u : U => legendreSym q (u.val.val : ℤ) = s)).card := by
      rw [hnz_eq]
      refine Finset.card_bij (fun a ha => Units.mk0 a (mem_filter.mp (mem_filter.mp ha).1).2) ?_ ?_ ?_
      · intro a ha; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2⟩
      · intro a1 _ a2 _ heq; exact congrArg Units.val heq
      · intro u hu
        refine ⟨u.val, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, u.ne_zero⟩, (mem_filter.mp hu).2⟩,
          Units.ext rfl⟩
    rw [hcard_eq_U]
    have hsq_iff : ∀ u : U, legendreSym q (u.val.val : ℤ) = 1 ↔ ∃ v : U, v ^ 2 = u := fun u => by
      have hcast : ((u.val.val : ℤ) : ZMod q) = u.val := by simp
      rw [legendreSym.eq_one_iff q (by rw [hcast]; exact u.ne_zero), hcast]
      constructor
      · rintro ⟨r, hr⟩
        have hr0 : r ≠ 0 := fun h0 => u.ne_zero (by rw [hr, h0, mul_zero])
        exact ⟨Units.mk0 r hr0, Units.ext (by rw [sq, Units.val_mul, Units.val_mk0, ← hr])⟩
      · rintro ⟨v, hv⟩
        exact ⟨v.val, by rw [← hv, Units.val_pow_eq_pow_val, sq]⟩
    have hnsq_iff : ∀ u : U, legendreSym q (u.val.val : ℤ) = -1 ↔ ¬ ∃ v : U, v ^ 2 = u := fun u => by
      have hcast : ((u.val.val : ℤ) : ZMod q) = u.val := by simp
      rw [legendreSym.eq_neg_one_iff, hcast]
      constructor
      · intro hnsq ⟨v, hv⟩; exact hnsq ⟨v.val, by rw [← hv, Units.val_pow_eq_pow_val, sq]⟩
      · intro hno ⟨r, hr⟩
        have hr0 : r ≠ 0 := fun h0 => u.ne_zero (by rw [hr, h0, mul_zero])
        exact hno ⟨Units.mk0 r hr0, Units.ext (by rw [sq, Units.val_mul, Units.val_mk0, ← hr])⟩
    let sqHom : U →* U := { toFun := fun v => v ^ 2, map_one' := by simp, map_mul' := fun a b => mul_pow a b 2 }
    have hker_card : Nat.card sqHom.ker = 2 := by
      have hne : (1 : ZMod q) ≠ -1 := by
        intro h
        have h2 : (2 : ZMod q) = 0 := by linear_combination h
        exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 q).mp h2))
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
      have hbij_ker : (univ : Finset sqHom.ker).card = ({(1 : ZMod q), -1} : Finset (ZMod q)).card := by
        refine Finset.card_bij (fun x _ => (x.1 : ZMod q)) ?_ ?_ ?_
        · intro x _
          have hx : (x.1 : ZMod q) ^ 2 = 1 := by
            have h1 : x.1 ^ 2 = 1 := x.2
            have := congrArg Units.val h1
            rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
          rcases sq_eq_one_iff.mp hx with h1 | h1 <;> simp [h1]
        · intro x1 _ x2 _ heq; exact Subtype.ext (Units.ext heq)
        · intro a ha
          have ha_sq : a ^ 2 = 1 := by
            rcases mem_insert.mp ha with rfl | h1
            · norm_num
            · rw [mem_singleton.mp h1]; norm_num
          have ha0 : a ≠ 0 := fun h0 => by rw [h0, zero_pow (by norm_num)] at ha_sq; exact zero_ne_one ha_sq
          refine ⟨⟨Units.mk0 a ha0, Units.ext (by
            change ((Units.mk0 a ha0 ^ 2 : U) : ZMod q) = (1 : ZMod q)
            rw [Units.val_pow_eq_pow_val, Units.val_mk0, ha_sq])⟩, mem_univ _, rfl⟩
      rw [hbij_ker, Finset.card_pair hne]
    have himg_card : (univ.filter (fun u : U => ∃ v : U, v ^ 2 = u)).card = (q - 1) / 2 := by
      have h1 : (univ.filter (fun u : U => ∃ v : U, v ^ 2 = u)).card = Nat.card sqHom.range := by
        rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
        refine Nat.card_congr ?_
        exact
          { toFun := fun x => ⟨x.1, (mem_filter.mp x.2).2⟩
            invFun := fun y => ⟨y.1, mem_filter.mpr ⟨mem_univ _, y.2⟩⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      rw [h1]
      have hlag := Subgroup.card_mul_index sqHom.ker
      have hind : sqHom.ker.index = Nat.card sqHom.range := by
        rw [Subgroup.index, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange sqHom).toEquiv]
      rw [hind, hker_card, Nat.card_eq_fintype_card (α := U), hcard_U] at hlag
      omega
    rcases hs with rfl | rfl
    · simpa only [hsq_iff] using himg_card
    · have hunion : univ.filter (fun u : U => ∃ v : U, v ^ 2 = u) ∪
          univ.filter (fun u : U => ¬ ∃ v : U, v ^ 2 = u) = univ := by
        ext u; simp only [mem_union, mem_filter, mem_univ, true_and]; exact iff_true_intro (em _)
      have hdisj : Disjoint (univ.filter (fun u : U => ∃ v : U, v ^ 2 = u))
          (univ.filter (fun u : U => ¬ ∃ v : U, v ^ 2 = u)) := by
        rw [Finset.disjoint_left]; intro u h1 h2; exact (mem_filter.mp h2).2 (mem_filter.mp h1).2
      have hpart : (univ.filter (fun u : U => ∃ v : U, v ^ 2 = u)).card +
          (univ.filter (fun u : U => ¬ ∃ v : U, v ^ 2 = u)).card = Fintype.card U := by
        rw [← card_union_of_disjoint hdisj, hunion, card_univ]
      rw [hcard_U, himg_card] at hpart
      have hrew : (univ.filter (fun u : U => legendreSym q (u.val.val : ℤ) = -1)).card =
          (univ.filter (fun u : U => ¬ ∃ v : U, v ^ 2 = u)).card := by
        congr 1; ext u; simp only [mem_filter, mem_univ, true_and, hnsq_iff]
      rw [hrew]; omega
  have hunion : Box.filter (fun v => legendreSym q (v 0 : ℤ) = s) ∪
      Box.filter (fun v => legendreSym q (v 0 : ℤ) ≠ s) = Box := by
    ext v; simp only [mem_union, mem_filter]; tauto
  have hdisj : Disjoint (Box.filter (fun v => legendreSym q (v 0 : ℤ) = s))
      (Box.filter (fun v => legendreSym q (v 0 : ℤ) ≠ s)) := by
    rw [Finset.disjoint_left]; intro v h1 h2; exact (mem_filter.mp h2).2 (mem_filter.mp h1).2
  have hpart : (Box.filter (fun v => legendreSym q (v 0 : ℤ) = s)).card +
      (Box.filter (fun v => legendreSym q (v 0 : ℤ) ≠ s)).card = Box.card := by
    rw [← card_union_of_disjoint hdisj, hunion]
  rw [show Box.card = q from hcard_pi, hcompl] at hpart
  change (Box.filter (fun v => legendreSym q (v 0 : ℤ) ≠ s)).card = (q + 1) / 2
  omega

/-- Uniform sieve pattern bound for `l = 2` via 1D large sieve and quadratic reciprocity. -/
theorem sieve_pattern_bound_two : SievePatternBound 2 := by
  obtain ⟨c₂, hc₂, hRankin⟩ := rankin_sieve_sum_lower Nat.prime_two
  let C : ℝ := 1 + 2 * (1000 / c₂)
  refine ⟨C, by dsimp [C]; positivity, 2, ?_⟩
  filter_upwards [primorial_params_eventually 1 le_rfl] with x ⟨hx100, hQ1, hQ_small, hprim⟩ j hj2 hj_pow
  let Q := ⌊x ^ (1 / (2 * ((1 : ℕ) : ℝ)))⌋₊
  have hx_pos : 0 < x := by linarith
  have hL_pos : 0 < Real.log x := Real.log_pos (by linarith)
  let P_all := (Nat.primesBelow ⌈x⌉₊).filter (fun p => p % 2 = 1 ∧
    ∀ i < j, ∃ y : ZMod p, y ^ 2 = (Nat.nth Nat.Prime i : ZMod p))
  -- Split `P_all` into `p ≤ Q`, `Q < p ∧ p % 4 = 1`, `Q < p ∧ p % 4 = 3`
  let P_lo := P_all.filter (fun p => p ≤ Q)
  let P_1 := P_all.filter (fun p => Q < p ∧ p % 4 = 1)
  let P_3 := P_all.filter (fun p => Q < p ∧ p % 4 = 3)
  have hsub_split : P_all ⊆ P_lo ∪ (P_1 ∪ P_3) := by
    intro p hp
    have hodd : p % 2 = 1 := (mem_filter.mp hp).2.1
    by_cases hle : p ≤ Q
    · exact mem_union_left _ (mem_filter.mpr ⟨hp, hle⟩)
    · push Not at hle
      have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
      rcases h4 with h | h
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hp, hle, h⟩))
      · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hp, hle, h⟩))
  have hcard_split : (P_all.card : ℝ) ≤ (P_lo.card : ℝ) + (P_1.card : ℝ) + (P_3.card : ℝ) := by
    have h1 : P_all.card ≤ P_lo.card + (P_1.card + P_3.card) :=
      (card_le_card hsub_split).trans ((card_union_le _ _).trans (Nat.add_le_add_left (card_union_le _ _) _))
    exact_mod_cast (show P_all.card ≤ P_lo.card + P_1.card + P_3.card by omega)
  have hlo_bound : (P_lo.card : ℝ) * (Real.log x / x) ≤ 1 / (2 : ℝ) ^ j := by
    have hleQ : P_lo.card ≤ Q := by
      have hsub : P_lo ⊆ Icc 1 Q := fun p hp =>
        mem_Icc.mpr ⟨(Nat.prime_of_mem_primesBelow (mem_filter.mp (mem_filter.mp hp).1).1).pos,
          (mem_filter.mp hp).2⟩
      exact (card_le_card hsub).trans (by simp)
    calc (P_lo.card : ℝ) * (Real.log x / x)
        ≤ (Q : ℝ) * (Real.log x / x) := mul_le_mul_of_nonneg_right (by exact_mod_cast hleQ) (by positivity)
      _ ≤ 1 / (Real.log x) ^ 10 := hQ_small
      _ ≤ 1 / (2 : ℝ) ^ j := div_le_div_of_nonneg_left zero_le_one (by positivity) hj_pow
  -- Bound both `P_1` and `P_3` with a single uniform lemma for `a ∈ {1, 3}`
  have hcls_bound : ∀ a : ℕ, a = 1 ∨ a = 3 →
      ((P_all.filter (fun p => Q < p ∧ p % 4 = a)).card : ℝ) * (Real.log x / x) ≤ (1000 / c₂) / (2 : ℝ) ^ j := by
    intro a ha
    let Pa := P_all.filter (fun p => Q < p ∧ p % 4 = a)
    let Sj := ((range j).image (Nat.nth Nat.Prime)).filter (fun q => q ≠ 2)
    have hSj_sub : Sj ⊆ (range j).image (Nat.nth Nat.Prime) := filter_subset _ _
    have hSj_pr : ∀ q ∈ Sj, q.Prime := fun q hq => by
      obtain ⟨i, _, rfl⟩ := mem_image.mp (hSj_sub hq)
      exact Nat.prime_nth_prime i
    have hSj_card : j - 1 ≤ Sj.card := by
      have himg : ((range j).image (Nat.nth Nat.Prime)).card = j := by
        rw [card_image_of_injective _ (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective, card_range]
      have hdiff : ((range j).image (Nat.nth Nat.Prime)) \ Sj ⊆ {2} := by
        intro q hq
        obtain ⟨h1, h2⟩ := mem_sdiff.mp hq
        simp only [Sj, mem_filter, h1, true_and, not_not] at h2
        exact mem_singleton.mpr h2
      have h1 := card_sdiff_add_card_eq_card hSj_sub
      have h2 : (((range j).image (Nat.nth Nat.Prime)) \ Sj).card ≤ 1 := (card_le_card hdiff).trans (by simp)
      omega
    obtain ⟨hZ10, hlogZ, hq_lt_Q⟩ := hprim j hj_pow Sj hSj_sub
    let M := ∏ q ∈ Sj, q
    let Z := Q / M
    have hM_pos : 0 < M := prod_pos fun q hq => (hSj_pr q hq).pos
    have hMZ_le : M * Z ≤ Q := Nat.mul_div_le Q M
    let sgn : ℕ → ℤ := fun q => (-1 : ℤ) ^ ((a / 2) * (q / 2))
    let Ω : ℕ → Finset (Fin 1 → ℕ) := fun q =>
      if hq : q ∈ Sj then
        letI : Fact q.Prime := ⟨hSj_pr q hq⟩
        (Fintype.piFinset (fun _ : Fin 1 => range q)).filter (fun v => legendreSym q (v 0 : ℤ) ≠ sgn q)
      else if q.Prime ∧ q % 2 = 1 ∧ q ≤ Z then {fun _ => 0}
      else ∅
    have hΩ : ∀ q, q.Prime → Ω q ⊆ Fintype.piFinset (fun _ : Fin 1 => range q) := fun q hq => by
      dsimp [Ω]; split_ifs
      · exact filter_subset _ _
      · exact singleton_subset_iff.mpr (Fintype.mem_piFinset.mpr fun _ => mem_range.mpr hq.pos)
      · exact empty_subset _
    let fA : ℕ → (Fin 1 → ℤ) := fun p _ => (p : ℤ)
    let A : Finset (Fin 1 → ℤ) := Pa.image fA
    have hA_card : A.card = Pa.card := card_image_of_injective Pa fun p1 p2 h => by
      have h0 : (p1 : ℤ) = (p2 : ℤ) := congrFun h 0
      exact_mod_cast h0
    have hA_box : A ⊆ intBox 1 0 ⌈x⌉₊ := by
      intro v hv
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hv
      have hp_lt : p < ⌈x⌉₊ := (Nat.mem_primesBelow.mp (mem_filter.mp (mem_filter.mp hp).1).1).1
      rw [intBox, Fintype.mem_piFinset]; intro i; rw [mem_Ico]; dsimp [fA]; omega
    have havoid : ∀ q, q.Prime → q ≤ Q → ∀ v ∈ A, vecMod q v ∉ Ω q := by
      intro q hq hqQ v hv
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hv
      obtain ⟨hp_all, hp_gtQ, hp_mod4⟩ := mem_filter.mp hp
      obtain ⟨hp_bel, hp_odd, hp_res⟩ := mem_filter.mp hp_all
      have hp_pr : p.Prime := Nat.prime_of_mem_primesBelow hp_bel
      have hp_ne2 : p ≠ 2 := by omega
      have hvec0 : vecMod q (fA p) 0 = p % q := by
        dsimp [vecMod, fA]; unfold Int.natMod; rw [← Int.natCast_emod, Int.toNat_natCast]
      dsimp [Ω]; split_ifs with hqSj hqSp
      · intro hmem
        have hne := (mem_filter.mp hmem).2
        rw [hvec0] at hne
        have hq2 : q ≠ 2 := (mem_filter.mp hqSj).2
        have hq_lt_p : q < p := (hq_lt_Q q hqSj).trans hp_gtQ
        have hndvd_pq : ¬ p ∣ q := fun hd => absurd (Nat.le_of_dvd hq.pos hd) (by omega)
        have hndvd_qp : ¬ q ∣ p := fun hd => absurd (Nat.prime_dvd_prime_iff_eq hq hp_pr |>.mp hd) (by omega)
        obtain ⟨i, hi, hqi⟩ := mem_image.mp (hSj_sub hqSj)
        obtain ⟨y, hy⟩ := hp_res i (mem_range.mp hi)
        rw [hqi] at hy
        have : Fact p.Prime := ⟨hp_pr⟩
        have : Fact q.Prime := ⟨hq⟩
        have hleg_pq : legendreSym p (q : ℤ) = 1 := by
          rw [legendreSym.eq_one_iff p (by
            rw [Int.cast_natCast]; exact fun h0 => hndvd_pq ((ZMod.natCast_eq_zero_iff q p).mp h0))]
          exact ⟨y, by rw [Int.cast_natCast, ← hy, sq]⟩
        have hqr := legendreSym.quadratic_reciprocity hp_ne2 hq2 hq_lt_p.ne'
        rw [hleg_pq, mul_one] at hqr
        have hleg_mod : legendreSym q ((p % q : ℕ) : ℤ) = legendreSym q (p : ℤ) := by
          rw [legendreSym.mod q (p : ℤ), show (p : ℤ) % (q : ℤ) = ((p % q : ℕ) : ℤ) by simp]
        have hexp_eq : ((-1 : ℤ) ^ ((p / 2) * (q / 2))) = sgn q := by
          dsimp [sgn]
          have hpar : (p / 2) % 2 = (a / 2) % 2 := by omega
          have hmod2 : ((p / 2) * (q / 2)) % 2 = ((a / 2) * (q / 2)) % 2 := by
            rw [Nat.mul_mod, hpar, ← Nat.mul_mod]
          rw [neg_one_pow_eq_pow_mod_two, hmod2, ← neg_one_pow_eq_pow_mod_two]
        exact hne (by rw [hleg_mod, hqr, hexp_eq])
      · intro hmem
        have h0 := congrFun (mem_singleton.mp hmem) 0
        rw [hvec0] at h0
        have hq_lt_p : q < p := (hqSp.2.2.trans (Nat.le_mul_of_pos_left Z hM_pos)).trans_lt (hMZ_le.trans_lt hp_gtQ)
        have hdvd : q ∣ p := Nat.dvd_of_mod_eq_zero h0
        exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp_pr).mp hdvd) (by omega)
      · exact notMem_empty _
    have hls := arith_large_sieve_nd Q hQ1 0 ⌈x⌉₊ A hA_box Ω hΩ havoid
    rw [hA_card, pow_one] at hls
    have hnum_le : 2 * (⌈x⌉₊ : ℝ) + 6 * (Q : ℝ) ^ 2 ≤ 10 * x := by
      have hceil : (⌈x⌉₊ : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx_pos.le).le
      have hQsq : (Q : ℝ) ^ 2 ≤ x := by
        have hfl : (Q : ℝ) ≤ x ^ ((1 : ℝ) / 2) := by
          simpa [Q] using Nat.floor_le (show 0 ≤ x ^ (1 / (2 * ((1 : ℕ) : ℝ))) by positivity)
        calc (Q : ℝ) ^ 2 ≤ (x ^ ((1 : ℝ) / 2)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hfl 2
          _ = x := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]; norm_num
      linarith
    -- Lower bound the sieve sum using `sieve_sum_split_of_prod` + `hRankin`
    have hsplit_lb : ∀ r : ℕ, r.Prime → r % 2 = 1 → r ∉ Sj → r ≤ Z →
        (((2 - 1 : ℕ) : ℝ) / (r : ℝ)) ≤ hfacND 1 Ω r := by
      intro r hr hr2 hrSj hrZ
      have hΩr : Ω r = {fun _ => 0} := by
        dsimp [Ω]; rw [dif_neg hrSj, if_pos ⟨hr, hr2, hrZ⟩]
      unfold hfacND
      rw [hΩr, card_singleton, Nat.cast_one, pow_one]
      have hr1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast hr.one_lt
      simpa using div_le_div_of_nonneg_left zero_le_one (by linarith) (by linarith : (r : ℝ) - 1 ≤ (r : ℝ))
    have hZ1 : 1 ≤ Z := le_trans (by norm_num) hZ10
    have hdenom_split := sieve_sum_split_of_prod hZ1 Ω hΩ Sj Sj hSj_pr subset_rfl hMZ_le hsplit_lb
    have hrank := hRankin Z hZ10 Sj
    have hSj_factor : ∀ q ∈ Sj, 2 * (1 + (((2 - 1 : ℕ) : ℝ) / (q : ℝ))) ≤ 1 + hfacND 1 Ω q := by
      intro q hqSj
      have hq := hSj_pr q hqSj
      have hq2 : q ≠ 2 := (mem_filter.mp hqSj).2
      have : Fact q.Prime := ⟨hq⟩
      have hΩq : Ω q = (Fintype.piFinset (fun _ : Fin 1 => range q)).filter
          (fun v => legendreSym q (v 0 : ℤ) ≠ sgn q) := by dsimp [Ω]; rw [dif_pos hqSj]
      have hsgn : sgn q = 1 ∨ sgn q = -1 := by
        dsimp [sgn]
        rcases Nat.even_or_odd ((a / 2) * (q / 2)) with hev | hodd
        · left; exact hev.neg_one_pow
        · right; exact hodd.neg_one_pow
      have hcard := card_legendre_ne (q := q) hq2 hsgn
      have hqodd : q % 2 = 1 := by have := hq.eq_two_or_odd; omega
      have hq_ge3 : (3 : ℝ) ≤ (q : ℝ) := by have := hq.two_le; exact_mod_cast (by omega : 3 ≤ q)
      have hcard_r : ((Ω q).card : ℝ) = ((q : ℝ) + 1) / 2 := by
        rw [hΩq, hcard]
        have : 2 * ((q + 1) / 2) = q + 1 := by omega
        have h2r : (2 : ℝ) * (((q + 1) / 2 : ℕ) : ℝ) = (q : ℝ) + 1 := by exact_mod_cast this
        linarith
      unfold hfacND
      rw [pow_one, hcard_r]
      have hsub : (q : ℝ) - ((q : ℝ) + 1) / 2 = ((q : ℝ) - 1) / 2 := by ring
      rw [hsub]
      have hq1_pos : (0 : ℝ) < (q : ℝ) - 1 := by linarith
      have hlhs_eq : 1 + ((q : ℝ) + 1) / 2 / (((q : ℝ) - 1) / 2) = 2 * (q : ℝ) / ((q : ℝ) - 1) := by
        field_simp [hq1_pos.ne']; ring
      rw [hlhs_eq]
      norm_num
      rw [le_div_iff₀ hq1_pos]
      have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
      have : 2 * (1 + (q : ℝ)⁻¹) * ((q : ℝ) - 1) = 2 * (q : ℝ) - 2 / (q : ℝ) := by
        field_simp [hq_pos.ne']; ring
      linarith [show (0 : ℝ) ≤ 2 / (q : ℝ) by positivity]
    let D := ∏ r ∈ Sj.filter (fun r => r.Prime ∧ r % 2 = 1), (1 + ((2 - 1 : ℕ) : ℝ) / (r : ℝ))
    have hD_pos : 0 < D := prod_pos fun r _ => by positivity
    have hSj_filter_eq : Sj.filter (fun r => r.Prime ∧ r % 2 = 1) = Sj := by
      ext r; simp only [mem_filter, and_iff_left_iff_imp]
      intro hr; have hpr := hSj_pr r hr; have hne2 := (mem_filter.mp hr).2
      exact ⟨hpr, by have := hpr.eq_two_or_odd; omega⟩
    have hprod_ge : (2 : ℝ) ^ Sj.card * D ≤ ∏ q ∈ Sj, (1 + hfacND 1 Ω q) := by
      dsimp [D]; rw [hSj_filter_eq, ← prod_const, ← Finset.prod_mul_distrib]
      exact prod_le_prod (fun _ _ => by positivity) hSj_factor
    have h2Sj : (1 / 2 : ℝ) * (2 : ℝ) ^ j ≤ (2 : ℝ) ^ Sj.card := by
      have h1 : (2 : ℝ) ^ (j - 1) ≤ (2 : ℝ) ^ Sj.card := pow_le_pow_right₀ (by norm_num) hSj_card
      have h2 : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ (j - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      linarith
    have hdenom_lb : (c₂ / 100) * (2 : ℝ) ^ j * Real.log x ≤
        ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfacND 1 Ω p := by
      have hlogZ' : (1 / 5 : ℝ) * Real.log x ≤ Real.log (Z : ℝ) := by
        have h5 : (1 / (5 * ((1 : ℕ) : ℝ))) = (1 / 5 : ℝ) := by norm_num
        rw [← h5]; exact hlogZ
      calc (c₂ / 100) * (2 : ℝ) ^ j * Real.log x
          ≤ (1 / 2 : ℝ) * (2 : ℝ) ^ j * (c₂ * ((1 / 5 : ℝ) * Real.log x)) := by
            have : (0 : ℝ) ≤ c₂ * (2 : ℝ) ^ j * Real.log x := by positivity
            nlinarith
        _ ≤ (2 : ℝ) ^ Sj.card * (c₂ * Real.log (Z : ℝ)) :=
            mul_le_mul h2Sj (mul_le_mul_of_nonneg_left hlogZ' hc₂.le) (by positivity) (by positivity)
        _ = ((2 : ℝ) ^ Sj.card * D) * ((c₂ * Real.log (Z : ℝ)) / D) := by field_simp [hD_pos.ne']
        _ ≤ (∏ q ∈ Sj, (1 + hfacND 1 Ω q)) *
            (∑ m ∈ (Icc 1 Z).filter (fun m => Squarefree m ∧ ∀ r ∈ m.primeFactors, r % 2 = 1 ∧ r ∉ Sj),
              ∏ r ∈ m.primeFactors, (((2 - 1 : ℕ) : ℝ) / (r : ℝ))) :=
            mul_le_mul hprod_ge hrank (by positivity) (prod_nonneg fun q hq => by
              linarith [hfacND_nonneg Ω q (hΩ q (hSj_pr q hq))])
        _ ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfacND 1 Ω p := hdenom_split
    have hcomb : (Pa.card : ℝ) * ((c₂ / 100) * (2 : ℝ) ^ j * Real.log x) ≤ 10 * x :=
      (mul_le_mul_of_nonneg_left hdenom_lb (Nat.cast_nonneg _)).trans (hls.trans hnum_le)
    rw [← mul_div_assoc, div_le_div_iff₀ hx_pos (by positivity)]
    have : (Pa.card : ℝ) * Real.log x * (2 : ℝ) ^ j ≤ (1000 / c₂) * x := by
      have hc2_pos : 0 < c₂ / 100 := by positivity
      have h1 : (Pa.card : ℝ) * Real.log x * (2 : ℝ) ^ j * (c₂ / 100) ≤ 10 * x := by linarith
      rw [show (1000 / c₂) * x = (10 * x) / (c₂ / 100) by field_simp [hc₂.ne']; ring]
      exact (le_div_iff₀ hc2_pos).mpr h1
    exact this
  have h1 := hcls_bound 1 (Or.inl rfl)
  have h3 := hcls_bound 3 (Or.inr rfl)
  calc (P_all.card : ℝ) * (Real.log x / x)
      ≤ ((P_lo.card : ℝ) + (P_1.card : ℝ) + (P_3.card : ℝ)) * (Real.log x / x) :=
        mul_le_mul_of_nonneg_right hcard_split (by positivity)
    _ = (P_lo.card : ℝ) * (Real.log x / x) + (P_1.card : ℝ) * (Real.log x / x) +
        (P_3.card : ℝ) * (Real.log x / x) := by ring
    _ ≤ 1 / (2 : ℝ) ^ j + (1000 / c₂) / (2 : ℝ) ^ j + (1000 / c₂) / (2 : ℝ) ^ j := by linarith
    _ = C / (2 : ℝ) ^ j := by dsimp [C]; ring

end CaseTwo

section CaseOddPrime

/-- For an odd prime `l` and `x ∈ CycR l` with `x^l = 1`, `x = zetaR l ^ k` for some `k : ℕ`. -/
private lemma eq_pow_zetaR_of_pow_l_eq_one {l : ℕ} [Fact l.Prime] {x : CycR l} (hx : x ^ l = 1) :
    ∃ k : ℕ, x = zetaR l ^ k := by
  have hxK : (x : CycK l) ^ l = 1 := by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, ← map_pow, hx, map_one]
  obtain ⟨k, _, hk⟩ := (zetaK_spec l).eq_pow_of_pow_eq_one hxK
  refine ⟨k, RingOfIntegers.ext ?_⟩
  rw [NumberField.RingOfIntegers.coe_eq_algebraMap, NumberField.RingOfIntegers.coe_eq_algebraMap,
    map_pow, show algebraMap (CycR l) (CycK l) (zetaR l) = zetaK l from (zetaK_spec l).coe_toInteger]
  exact hk.symm

/-- If `I` is a nonzero ideal of `CycR l` and `r` is a prime not dividing `absNorm I`,
    then `IsCoprime I (span {r})`. -/
private lemma isCoprime_of_not_dvd_absNorm {l : ℕ} [Fact l.Prime] {I : Ideal (CycR l)}
    {r : ℕ} (hr : r.Prime) (hndvd : ¬ r ∣ Ideal.absNorm I) :
    IsCoprime I (span {(r : CycR l)}) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hnt
  obtain ⟨𝔪, hm_max, hle⟩ := Ideal.exists_le_maximal _ hnt
  have hI_le : I ≤ 𝔪 := le_sup_left.trans hle
  have hr_le : span {(r : CycR l)} ≤ 𝔪 := le_sup_right.trans hle
  have h1 : Ideal.absNorm 𝔪 ∣ Ideal.absNorm I := Ideal.absNorm_dvd_absNorm_of_le hI_le
  have h2 : Ideal.absNorm 𝔪 ∣ Ideal.absNorm (span {(r : CycR l)}) := Ideal.absNorm_dvd_absNorm_of_le hr_le
  have hbot : 𝔪 ≠ ⊥ := fun h0 => by
    have : (r : CycR l) = 0 := Ideal.mem_bot.mp (h0 ▸ hr_le (Ideal.subset_span (Set.mem_singleton _)))
    exact hr.ne_zero (Nat.cast_eq_zero.mp this)
  have hN_gt1 : 1 < Ideal.absNorm 𝔪 := by
    rw [absNorm_eq_card_quotient]
    have : Finite (CycR l ⧸ 𝔪) := Ring.HasFiniteQuotients.finiteQuotient hbot
    let : Fintype (CycR l ⧸ 𝔪) := Fintype.ofFinite _
    let : Field (CycR l ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hN_gt1.ne'
  rw [Ideal.absNorm_span_natCast] at h2
  have hqr : q = r := (Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow (hqm.trans h2))
  exact hndvd (hqr ▸ hqm.trans h1)

set_option maxHeartbeats 1200000 in
/-- Uniform sieve pattern bound for every odd prime `l` via the `(l-1)`-dimensional large sieve,
    Eisenstein reciprocity, and Rankin-truncated Mertens in AP. -/
theorem sieve_pattern_bound_odd_l {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) : SievePatternBound l := by
  have : Fact l.Prime := ⟨hl⟩
  let d : ℕ := l - 1
  have hd_ge2 : 2 ≤ d := by have := hl.two_le; omega
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨c_l, hc_l, hRankin⟩ := rankin_sieve_sum_lower hl
  -- For every ideal class `C`, fix a degree-1 representative `𝔟_C` of `C⁻¹` and a box constant `C_box_C`
  have hcls_data : ∀ C : ClassGroup (CycR l),
      ∃ (𝔟 : (Ideal (CycR l))⁰) (C_box : ℝ),
        ClassGroup.mk0 𝔟 = C⁻¹ ∧
        (∀ 𝔭 ∈ UniqueFactorizationMonoid.normalizedFactors 𝔟.1,
          (Ideal.absNorm 𝔭).Prime ∧ Ideal.absNorm 𝔭 ≠ l) ∧
        0 < C_box ∧
        (∀ 𝔭 : (Ideal (CycR l))⁰, ClassGroup.mk0 𝔭 = C → ¬ (𝔭.1 ≤ span {lamR l}) →
          ∃ α : CycR l, IsPrimary α ∧ span {α} = 𝔭.1 * 𝔟.1 ∧
            ∀ i : Fin d, |(coordR l α i : ℝ)| ≤ C_box * (Ideal.absNorm 𝔭.1 : ℝ) ^ (1 / (d : ℝ))) := fun C => by
    obtain ⟨𝔟, h𝔟_cls, h𝔟_deg1⟩ := exists_deg1_class_rep (l := l) hl2 C
    obtain ⟨C_box, hC_box, hbox⟩ := exists_primary_box_bound (l := l) hl2 C 𝔟 h𝔟_cls h𝔟_deg1
    exact ⟨𝔟, C_box, h𝔟_cls, h𝔟_deg1, hC_box, hbox⟩
  choose 𝔟_of C_box_of h𝔟_cls h𝔟_deg1 hC_box_pos hbox_of using hcls_data
  -- Per-class constant `K_cls C`
  let D_const : ClassGroup (CycR l) → ℝ := fun C =>
    ∏ r ∈ ((l * Ideal.absNorm (𝔟_of C).1).primeFactors).filter (fun r => r.Prime ∧ r % l = 1),
      (1 + (d : ℝ) / (r : ℝ))
  let E_cls : ClassGroup (CycR l) → ℕ := fun C => 1 + (Ideal.absNorm (𝔟_of C).1).primeFactors.card
  let K_cls : ClassGroup (CycR l) → ℝ := fun C =>
    (8 * C_box_of C + 16) ^ d * (5 * (d : ℝ) / c_l) * D_const C * (2 : ℝ) ^ (E_cls C)
  have hK_pos : ∀ C, 0 < K_cls C := fun C => by
    dsimp [K_cls, D_const]
    have hD : 0 < ∏ r ∈ ((l * Ideal.absNorm (𝔟_of C).1).primeFactors).filter (fun r => r.Prime ∧ r % l = 1),
        (1 + (d : ℝ) / (r : ℝ)) := prod_pos fun _ _ => by positivity
    have hCb := hC_box_pos C
    positivity
  let C_tot : ℝ := 1 + ∑ C : ClassGroup (CycR l), K_cls C
  have hC_tot_pos : 0 < C_tot := by
    dsimp [C_tot]; linarith [sum_nonneg fun C (_ : C ∈ univ) => (hK_pos C).le]
  refine ⟨C_tot, hC_tot_pos, 1, ?_⟩
  filter_upwards [primorial_params_eventually d (by omega : 1 ≤ d)] with x ⟨hx100, hQ1, hQ_small, hprim⟩ j hj1 hj_pow
  let Q := ⌊x ^ (1 / (2 * (d : ℝ)))⌋₊
  have hx_pos : 0 < x := by linarith
  have hL_pos : 0 < Real.log x := Real.log_pos (by linarith)
  let P_all := (Nat.primesBelow ⌈x⌉₊).filter (fun p => p % l = 1 ∧
    ∀ i < j, ∃ y : ZMod p, y ^ l = (Nat.nth Nat.Prime i : ZMod p))
  let P_lo := P_all.filter (fun p => p ≤ Q)
  let P_hi := P_all.filter (fun p => Q < p)
  have hlo_bound : (P_lo.card : ℝ) * (Real.log x / x) ≤ 1 / (2 : ℝ) ^ j := by
    have hleQ : P_lo.card ≤ Q := by
      have hsub : P_lo ⊆ Icc 1 Q := fun p hp =>
        mem_Icc.mpr ⟨(Nat.prime_of_mem_primesBelow (mem_filter.mp (mem_filter.mp hp).1).1).pos,
          (mem_filter.mp hp).2⟩
      exact (card_le_card hsub).trans (by simp)
    calc (P_lo.card : ℝ) * (Real.log x / x)
        ≤ (Q : ℝ) * (Real.log x / x) := mul_le_mul_of_nonneg_right (by exact_mod_cast hleQ) (by positivity)
      _ ≤ 1 / (Real.log x) ^ 10 := hQ_small
      _ ≤ 1 / (2 : ℝ) ^ j := div_le_div_of_nonneg_left zero_le_one (by positivity) hj_pow
  -- Choose for each `p ∈ P_hi` a degree-1 prime ideal `𝔭_of p` of norm `p`
  have hex_𝔭 : ∀ p : ℕ, p.Prime → p % l = 1 →
      ∃ 𝔭 : Ideal (CycR l), 𝔭.IsPrime ∧ Ideal.absNorm 𝔭 = p ∧
        (∀ q : ℕ, ¬ p ∣ q → ((∃ y : ZMod p, y ^ l = (q : ZMod p)) ↔ powResSymb (q : CycR l) 𝔭 = 1)) :=
    fun p hp hmod => exists_deg1_prime_of_mod_eq_one l hp hmod
  let 𝔭_of : ∀ p : ℕ, p ∈ P_hi → (Ideal (CycR l))⁰ := fun p hp =>
    let hp_all := (mem_filter.mp hp).1
    let hp_pr := Nat.prime_of_mem_primesBelow (mem_filter.mp hp_all).1
    let hp_mod := (mem_filter.mp hp_all).2.1
    let 𝔭 := (hex_𝔭 p hp_pr hp_mod).choose
    ⟨𝔭, mem_nonZeroDivisors_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mp (by
      rw [(hex_𝔭 p hp_pr hp_mod).choose_spec.2.1]; exact hp_pr.ne_zero))⟩
  have h𝔭_spec : ∀ (p : ℕ) (hp : p ∈ P_hi),
      (𝔭_of p hp).1.IsPrime ∧ Ideal.absNorm (𝔭_of p hp).1 = p ∧
      (∀ q : ℕ, ¬ p ∣ q → ((∃ y : ZMod p, y ^ l = (q : ZMod p)) ↔ powResSymb (q : CycR l) (𝔭_of p hp).1 = 1)) :=
    fun p hp => (hex_𝔭 p (Nat.prime_of_mem_primesBelow (mem_filter.mp (mem_filter.mp hp).1).1)
      (mem_filter.mp (mem_filter.mp hp).1).2.1).choose_spec
  -- Partition `P_hi` by ideal class `C : ClassGroup (CycR l)`
  let clsOf : ℕ → ClassGroup (CycR l) := fun p =>
    if hp : p ∈ P_hi then ClassGroup.mk0 (𝔭_of p hp) else 1
  have hhi_sum : (P_hi.card : ℝ) = ∑ C : ClassGroup (CycR l), ((P_hi.filter (fun p => clsOf p = C)).card : ℝ) := by
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise (f := clsOf) (s := P_hi) (t := univ)
      (fun _ _ => mem_univ _))
  -- Per-class sieve bound: `|(P_hi.filter (clsOf · = C))| * (log x / x) ≤ K_cls C / 2^j`
  have hper_cls : ∀ C : ClassGroup (CycR l),
      ((P_hi.filter (fun p => clsOf p = C)).card : ℝ) * (Real.log x / x) ≤ K_cls C / (2 : ℝ) ^ j := by
    intro C
    let PC := P_hi.filter (fun p => clsOf p = C)
    let 𝔟 := 𝔟_of C
    let C_box := C_box_of C
    have h𝔟_norm_pos : 0 < Ideal.absNorm 𝔟.1 :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (nonZeroDivisors.ne_zero 𝔟.2))
    let B : ℕ := ⌈C_box * (⌈x⌉₊ : ℝ) ^ (1 / (d : ℝ))⌉₊ + 1
    -- For each `p ∈ PC`, extract primary `α_p` with `span {α_p} = 𝔭_p * 𝔟` and `coordR l α_p ∈ intBox d (-B) (2B + 1)`
    have hα_ex : ∀ p ∈ PC, ∃ α : CycR l, IsPrimary α ∧
        (∃ hp : p ∈ P_hi, span {α} = (𝔭_of p hp).1 * 𝔟.1) ∧
        coordR l α ∈ intBox d (-(B : ℤ)) (2 * B + 1) := by
      intro p hpC
      have hp_hi : p ∈ P_hi := (mem_filter.mp hpC).1
      have hcls_eq : ClassGroup.mk0 (𝔭_of p hp_hi) = C := by
        have h := (mem_filter.mp hpC).2; simp only [clsOf, hp_hi, ↓reduceDIte] at h; exact h
      have h𝔭_pr := (h𝔭_spec p hp_hi).1
      have h𝔭_norm := (h𝔭_spec p hp_hi).2.1
      have hp_mod : p % l = 1 := (mem_filter.mp (mem_filter.mp hp_hi).1).2.1
      have hpl : p ≠ l := fun h => by rw [h, Nat.mod_self] at hp_mod; exact zero_ne_one hp_mod
      have hnot_le : ¬ ((𝔭_of p hp_hi).1 ≤ span {lamR l}) := by
        intro hle
        have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
        rw [absNorm_span_lamR, h𝔭_norm] at hdvd
        exact hpl ((Nat.prime_dvd_prime_iff_eq hl
          (Nat.prime_of_mem_primesBelow (mem_filter.mp (mem_filter.mp hp_hi).1).1)).mp hdvd).symm
      obtain ⟨α, hα_prim, hα_span, hα_box⟩ := hbox_of C (𝔭_of p hp_hi) hcls_eq hnot_le
      refine ⟨α, hα_prim, ⟨hp_hi, hα_span⟩, ?_⟩
      rw [intBox, Fintype.mem_piFinset]; intro i; rw [mem_Ico]
      have hp_lt : p < ⌈x⌉₊ := (Nat.mem_primesBelow.mp (mem_filter.mp (mem_filter.mp hp_hi).1).1).1
      have hcoord_le : |(coordR l α i : ℝ)| < (B : ℝ) := by
        calc |(coordR l α i : ℝ)|
            ≤ C_box * (p : ℝ) ^ (1 / (d : ℝ)) := by simpa [h𝔭_norm] using hα_box i
          _ ≤ C_box * (⌈x⌉₊ : ℝ) ^ (1 / (d : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ (hC_box_pos C).le
              exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hp_lt.le) (by positivity)
          _ < (B : ℝ) := by
              dsimp [B]; push_cast
              linarith [Nat.le_ceil (C_box * (⌈x⌉₊ : ℝ) ^ (1 / (d : ℝ)))]
      have hlo : -((B : ℤ) : ℝ) ≤ (coordR l α i : ℝ) := by
        push_cast; linarith [(abs_lt.mp hcoord_le).1]
      have hhi : (coordR l α i : ℝ) < (-(B : ℤ) + ((2 * B + 1 : ℕ) : ℤ) : ℝ) := by
        push_cast; linarith [(abs_lt.mp hcoord_le).2]
      exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
    let α_of : ℕ → CycR l := fun p => if hp : p ∈ PC then (hα_ex p hp).choose else 0
    let A : Finset (Fin d → ℤ) := PC.image (fun p => coordR l (α_of p))
    have hA_card : A.card = PC.card := by
      refine card_image_of_injOn fun p1 hp1 p2 hp2 heq => ?_
      have hα_eq : α_of p1 = α_of p2 := (coordR l).injective heq
      have h1 : α_of p1 = (hα_ex p1 hp1).choose := dif_pos hp1
      have h2 : α_of p2 = (hα_ex p2 hp2).choose := dif_pos hp2
      obtain ⟨hp1_hi, hspan1⟩ := (hα_ex p1 hp1).choose_spec.2.1
      obtain ⟨hp2_hi, hspan2⟩ := (hα_ex p2 hp2).choose_spec.2.1
      have hnorm_eq : Ideal.absNorm (span {α_of p1}) = Ideal.absNorm (span {α_of p2}) := by rw [hα_eq]
      rw [h1, hspan1, map_mul, (h𝔭_spec p1 hp1_hi).2.1, h2, hspan2, map_mul, (h𝔭_spec p2 hp2_hi).2.1] at hnorm_eq
      exact Nat.eq_of_mul_eq_mul_right h𝔟_norm_pos hnorm_eq
    have hA_box : A ⊆ intBox d (-(B : ℤ)) (2 * B + 1) := by
      intro v hv
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hv
      have h1 : α_of p = (hα_ex p hp).choose := dif_pos hp
      rw [h1]; exact (hα_ex p hp).choose_spec.2.2
    -- Define `Sj` (prescribed primes coprime to `l * absNorm 𝔟`) and `Bad`
    let Sj := ((range j).image (Nat.nth Nat.Prime)).filter (fun q => q ≠ l ∧ ¬ q ∣ Ideal.absNorm 𝔟.1)
    have hSj_sub : Sj ⊆ (range j).image (Nat.nth Nat.Prime) := filter_subset _ _
    have hSj_pr : ∀ q ∈ Sj, q.Prime := fun q hq => by
      obtain ⟨i, _, rfl⟩ := mem_image.mp (hSj_sub hq)
      exact Nat.prime_nth_prime i
    have hSj_card : j ≤ Sj.card + E_cls C := by
      have himg : ((range j).image (Nat.nth Nat.Prime)).card = j := by
        rw [card_image_of_injective _ (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective, card_range]
      have hdiff : ((range j).image (Nat.nth Nat.Prime)) \ Sj ⊆
          insert l (Ideal.absNorm 𝔟.1).primeFactors := by
        intro q hq
        obtain ⟨h1, h2⟩ := mem_sdiff.mp hq
        obtain ⟨i, _, rfl⟩ := mem_image.mp h1
        have hqpr := Nat.prime_nth_prime i
        simp only [Sj, mem_filter, h1, true_and, not_and_or, not_not] at h2
        rcases h2 with rfl | hdvd
        · exact mem_insert_self _ _
        · exact mem_insert_of_mem (Nat.mem_primeFactors.mpr ⟨hqpr, hdvd, h𝔟_norm_pos.ne'⟩)
      have h1 := card_sdiff_add_card_eq_card hSj_sub
      have hE : E_cls C = 1 + (Ideal.absNorm 𝔟.1).primeFactors.card := rfl
      have h2 : (((range j).image (Nat.nth Nat.Prime)) \ Sj).card ≤ E_cls C :=
        (card_le_card hdiff).trans ((card_insert_le _ _).trans (by omega))
      omega
    obtain ⟨hZ10, hlogZ, hq_lt_Q⟩ := hprim j hj_pow Sj hSj_sub
    let M := ∏ q ∈ Sj, q
    let Z := Q / M
    have hM_pos : 0 < M := prod_pos fun q hq => (hSj_pr q hq).pos
    have hMZ_le : M * Z ≤ Q := Nat.mul_div_le Q M
    let Bad : Finset ℕ := Sj ∪ (l * Ideal.absNorm 𝔟.1).primeFactors
    let Ω : ℕ → Finset (Fin d → ℕ) := fun q =>
      if q ∈ Sj then forbiddenPowRes l q (powResIdeal (q : CycR l) 𝔟.1)
      else if q.Prime ∧ q % l = 1 ∧ q ∉ Bad ∧ q ≤ Z then forbiddenSplit l q
      else ∅
    have hΩ : ∀ q, q.Prime → Ω q ⊆ Fintype.piFinset (fun _ : Fin d => range q) := fun q _ => by
      dsimp [Ω]; split_ifs
      · exact filter_subset _ _
      · exact filter_subset _ _
      · exact empty_subset _
    have havoid : ∀ q, q.Prime → q ≤ Q → ∀ v ∈ A, vecMod q v ∉ Ω q := by
      intro q hq hqQ v hv
      obtain ⟨p, hpC, rfl⟩ := mem_image.mp hv
      have hα_def : α_of p = (hα_ex p hpC).choose := dif_pos hpC
      have hα_prim : IsPrimary (α_of p) := hα_def ▸ (hα_ex p hpC).choose_spec.1
      obtain ⟨hp_hi, hα_span⟩ := (hα_ex p hpC).choose_spec.2.1
      rw [← hα_def] at hα_span
      have hp_gtQ : Q < p := (mem_filter.mp hp_hi).2
      have hp_all := (mem_filter.mp hp_hi).1
      have hp_pr := Nat.prime_of_mem_primesBelow (mem_filter.mp hp_all).1
      have hp_mod := (mem_filter.mp hp_all).2.1
      have hp_res := (mem_filter.mp hp_all).2.2
      have h𝔭_pr := (h𝔭_spec p hp_hi).1
      have h𝔭_norm := (h𝔭_spec p hp_hi).2.1
      have hvec_eq : vecMod q (coordR l (α_of p)) =
          fun i : Fin d => (coordR l (α_of p) i % (q : ℤ)).toNat := rfl
      rw [hvec_eq]
      dsimp [Ω]; split_ifs with hqSj hqSp
      · have hql : q ≠ l := (mem_filter.mp hqSj).2.1
        have hq_ndvd_𝔟 : ¬ q ∣ Ideal.absNorm 𝔟.1 := (mem_filter.mp hqSj).2.2
        have hq_lt_p : q < p := (hq_lt_Q q hqSj).trans hp_gtQ
        have hq_ndvd_p : ¬ q ∣ p := fun hd => absurd ((Nat.prime_dvd_prime_iff_eq hq hp_pr).mp hd) (by omega)
        have hq_ndvd_α : ¬ q ∣ Ideal.absNorm (span {α_of p}) := by
          rw [hα_span, map_mul, h𝔭_norm]
          intro hd; rcases hq.dvd_mul.mp hd with h1 | h2
          · exact hq_ndvd_p h1
          · exact hq_ndvd_𝔟 h2
        have hcop_αq : IsCoprime (span {α_of p}) (span {(q : CycR l)}) :=
          isCoprime_of_not_dvd_absNorm hq hq_ndvd_α
        -- Every prime factor of `span {α_of p} = 𝔭_p * 𝔟` is degree-1 and `≠ (l)`!
        have hdeg1_α : ∀ 𝔮 ∈ UniqueFactorizationMonoid.normalizedFactors (span {α_of p}),
            (Ideal.absNorm 𝔮).Prime ∧ Ideal.absNorm 𝔮 ≠ l := by
          intro 𝔮 h𝔮
          rw [hα_span] at h𝔮
          have h𝔭_bot : (𝔭_of p hp_hi).1 ≠ ⊥ := nonZeroDivisors.ne_zero (𝔭_of p hp_hi).2
          have h𝔟_bot : 𝔟.1 ≠ ⊥ := nonZeroDivisors.ne_zero 𝔟.2
          have hrel := UniqueFactorizationMonoid.normalizedFactors_mul h𝔭_bot h𝔟_bot
          rw [hrel, Multiset.mem_add] at h𝔮
          rcases h𝔮 with h1 | h2
          · have h𝔭_irr := (Ideal.prime_of_isPrime h𝔭_bot h𝔭_pr).irreducible
            have hfac1 : UniqueFactorizationMonoid.normalizedFactors (𝔭_of p hp_hi).1 = {(𝔭_of p hp_hi).1} := by
              rw [UniqueFactorizationMonoid.normalizedFactors_irreducible h𝔭_irr, normalize_eq]
            rw [hfac1, Multiset.mem_singleton] at h1
            rw [h1, h𝔭_norm]
            exact ⟨hp_pr, fun he => by rw [he, Nat.mod_self] at hp_mod; exact zero_ne_one hp_mod⟩
          · exact h𝔟_deg1 C 𝔮 h2
        -- Eisenstein reciprocity!
        have heis := eisenstein_reciprocity_deg1 hl2 hq hql hα_prim hcop_αq hdeg1_α
        -- Split `powResIdeal q (𝔭_p * 𝔟) = powResSymb q 𝔭_p * powResIdeal q 𝔟 = 1 * powResIdeal q 𝔟`!
        have h𝔭_bot : (𝔭_of p hp_hi).1 ≠ ⊥ := nonZeroDivisors.ne_zero (𝔭_of p hp_hi).2
        have h𝔟_bot : 𝔟.1 ≠ ⊥ := nonZeroDivisors.ne_zero 𝔟.2
        have hres_split : powResIdeal (q : CycR l) (span {α_of p}) =
            powResSymb (q : CycR l) (𝔭_of p hp_hi).1 * powResIdeal (q : CycR l) 𝔟.1 := by
          rw [hα_span, powResIdeal_mul h𝔭_bot h𝔟_bot,
            powResIdeal_prime (h𝔭_pr) h𝔭_bot]
        obtain ⟨i, hi, hqi⟩ := mem_image.mp (hSj_sub hqSj)
        have hres_p1 : powResSymb (q : CycR l) (𝔭_of p hp_hi).1 = 1 := by
          have hp_ndvd_q : ¬ p ∣ q := fun hd => absurd (Nat.le_of_dvd hq.pos hd) (by omega)
          exact ((h𝔭_spec p hp_hi).2.2 q hp_ndvd_q).mp (hqi ▸ hp_res i (mem_range.mp hi))
        have hres_eq : powResIdeal (α_of p) (span {(q : CycR l)}) = powResIdeal (q : CycR l) 𝔟.1 := by
          rw [← heis, hres_split, hres_p1, one_mul]
        exact not_mem_forbiddenPowRes_of_eq l hq hql hcop_αq hres_eq
      · have hq_not_Bad : q ∉ Bad := hqSp.2.2.1
        have hq_ndvd_𝔟 : ¬ q ∣ Ideal.absNorm 𝔟.1 := fun hd =>
          hq_not_Bad (mem_union_right _ (Nat.mem_primeFactors.mpr
            ⟨hq, dvd_mul_of_dvd_right hd l, (Nat.mul_pos hl.pos h𝔟_norm_pos).ne'⟩))
        have hq_lt_p : q < p := hqQ.trans_lt hp_gtQ
        have hq_ndvd_p : ¬ q ∣ p := fun hd => absurd ((Nat.prime_dvd_prime_iff_eq hq hp_pr).mp hd) (by omega)
        have hq_ndvd_α : ¬ q ∣ Ideal.absNorm (span {α_of p}) := by
          rw [hα_span, map_mul, h𝔭_norm]
          intro hd; rcases hq.dvd_mul.mp hd with h1 | h2
          · exact hq_ndvd_p h1
          · exact hq_ndvd_𝔟 h2
        exact not_mem_forbiddenSplit_of_coprime l hq (isCoprime_of_not_dvd_absNorm hq hq_ndvd_α)
      · exact notMem_empty _
    -- Apply `arith_large_sieve_nd`
    have hls := arith_large_sieve_nd Q hQ1 (-(B : ℤ)) (2 * B + 1) A hA_box Ω hΩ havoid
    rw [hA_card] at hls
    -- Upper bound numerator `(2 * (2*B + 1) + 6 * Q^2)^d ≤ (8 * C_box + 16)^d * x`
    have hnum_le : (2 * ((2 * B + 1 : ℕ) : ℝ) + 6 * (Q : ℝ) ^ 2) ^ d ≤ (8 * C_box + 16) ^ d * x := by
      have hx_d_ge1 : (1 : ℝ) ≤ x ^ (1 / (d : ℝ)) := Real.one_le_rpow (by linarith) (by positivity)
      have hceil_x : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
        have := (Nat.ceil_lt_add_one hx_pos.le).le; linarith
      have h2_d : (2 : ℝ) ^ (1 / (d : ℝ)) ≤ 2 := by
        calc (2 : ℝ) ^ (1 / (d : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (div_le_one_of_le₀ (by exact_mod_cast (by omega : 1 ≤ d)) (by positivity))
          _ = 2 := Real.rpow_one 2
      have hCb_pos : 0 < C_box := hC_box_pos C
      have hB_le : (B : ℝ) ≤ (2 * C_box + 2) * x ^ (1 / (d : ℝ)) := by
        dsimp [B]; push_cast
        have hcb := (Nat.ceil_lt_add_one (show 0 ≤ C_box * (⌈x⌉₊ : ℝ) ^ (1 / (d : ℝ)) by positivity)).le
        have hcx : (⌈x⌉₊ : ℝ) ^ (1 / (d : ℝ)) ≤ 2 * x ^ (1 / (d : ℝ)) := by
          calc (⌈x⌉₊ : ℝ) ^ (1 / (d : ℝ))
              ≤ (2 * x) ^ (1 / (d : ℝ)) := Real.rpow_le_rpow (Nat.cast_nonneg _) hceil_x (by positivity)
            _ = (2 : ℝ) ^ (1 / (d : ℝ)) * x ^ (1 / (d : ℝ)) := Real.mul_rpow (by norm_num) hx_pos.le
            _ ≤ 2 * x ^ (1 / (d : ℝ)) := mul_le_mul_of_nonneg_right h2_d (by positivity)
        nlinarith
      have hQ_sq : (Q : ℝ) ^ 2 ≤ x ^ (1 / (d : ℝ)) := by
        have hfl : (Q : ℝ) ≤ x ^ (1 / (2 * (d : ℝ))) := Nat.floor_le (by positivity)
        calc (Q : ℝ) ^ 2 ≤ (x ^ (1 / (2 * (d : ℝ)))) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hfl 2
          _ = x ^ (1 / (d : ℝ)) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]
              congr 1; field_simp [hd_pos.ne']; ring
      have hbase_le : 2 * ((2 * B + 1 : ℕ) : ℝ) + 6 * (Q : ℝ) ^ 2 ≤
          (8 * C_box + 16) * x ^ (1 / (d : ℝ)) := by
        push_cast; nlinarith
      have hxd_pow : (x ^ (1 / (d : ℝ))) ^ d = x := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le,
          show 1 / (d : ℝ) * (d : ℝ) = 1 by field_simp [hd_pos.ne'], Real.rpow_one]
      calc (2 * ((2 * B + 1 : ℕ) : ℝ) + 6 * (Q : ℝ) ^ 2) ^ d
          ≤ ((8 * C_box + 16) * x ^ (1 / (d : ℝ))) ^ d := pow_le_pow_left₀ (by positivity) hbase_le d
        _ = (8 * C_box + 16) ^ d * (x ^ (1 / (d : ℝ))) ^ d := mul_pow _ _ d
        _ = (8 * C_box + 16) ^ d * x := by rw [hxd_pow]
    -- Lower bound `hfacND d Ω r ≥ d / r` for `r ≡ 1 (mod l)`, `r ∉ Bad`, `r ≤ Z`
    have hsplit_lb : ∀ r : ℕ, r.Prime → r % l = 1 → r ∉ Bad → r ≤ Z →
        ((d : ℝ) / (r : ℝ)) ≤ hfacND d Ω r := by
      intro r hr hr_mod hrBad hrZ
      have hrSj : r ∉ Sj := fun h => hrBad (mem_union_left _ h)
      have hΩr : Ω r = forbiddenSplit l r := by
        dsimp [Ω]; rw [if_neg hrSj, if_pos ⟨hr, hr_mod, hrBad, hrZ⟩]
      have hcompl := forbiddenSplit_card_compl l hr hr_mod
      have hcard_le : (forbiddenSplit l r).card ≤ r ^ d := by
        have h1 : (forbiddenSplit l r).card ≤ (Fintype.piFinset (fun _ : Fin d => range r)).card :=
          card_le_card (filter_subset _ _)
        simpa using h1
      have hsub_r : (r : ℝ) ^ d - ((Ω r).card : ℝ) = ((r - 1 : ℕ) : ℝ) ^ d := by
        rw [hΩr]
        have : (r ^ d - (forbiddenSplit l r).card : ℕ) = (r - 1) ^ d := hcompl
        have h2 : (((r ^ d - (forbiddenSplit l r).card : ℕ) : ℝ)) = (((r - 1) ^ d : ℕ) : ℝ) := by
          exact_mod_cast this
        rw [Nat.cast_sub hcard_le, Nat.cast_pow, Nat.cast_pow] at h2
        exact h2
      have hcard_r : ((Ω r).card : ℝ) = (r : ℝ) ^ d - ((r - 1 : ℕ) : ℝ) ^ d := by linarith
      unfold hfacND
      rw [hsub_r, hcard_r]
      have hr1_pos : (0 : ℝ) < ((r - 1 : ℕ) : ℝ) := by
        have := hr.two_le; exact_mod_cast (by omega : 0 < r - 1)
      have hbern : 1 + (d : ℝ) / ((r - 1 : ℕ) : ℝ) ≤ ((r : ℝ) / ((r - 1 : ℕ) : ℝ)) ^ d := by
        have hr_eq : (r : ℝ) / ((r - 1 : ℕ) : ℝ) = 1 + 1 / ((r - 1 : ℕ) : ℝ) := by
          have : (r : ℝ) = ((r - 1 : ℕ) : ℝ) + 1 := by
            have := hr.two_le; exact_mod_cast (by omega : r = r - 1 + 1)
          rw [this]; field_simp [hr1_pos.ne']
        rw [hr_eq]
        have h1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / ((r - 1 : ℕ) : ℝ) by
          linarith [show (0 : ℝ) ≤ 1 / ((r - 1 : ℕ) : ℝ) by positivity]) d
        rwa [mul_one_div] at h1
      have hrew : ((r : ℝ) ^ d - ((r - 1 : ℕ) : ℝ) ^ d) / ((r - 1 : ℕ) : ℝ) ^ d =
          ((r : ℝ) / ((r - 1 : ℕ) : ℝ)) ^ d - 1 := by
        rw [sub_div, div_self (pow_ne_zero d hr1_pos.ne'), div_pow]
      rw [hrew]
      have hle_r : (d : ℝ) / (r : ℝ) ≤ (d : ℝ) / ((r - 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left hd_pos.le hr1_pos (by
          have := hr.two_le; exact_mod_cast (by omega : r - 1 ≤ r))
      linarith
    have hZ1 : 1 ≤ Z := le_trans (by norm_num) hZ10
    have hdenom_split := sieve_sum_split_of_prod hZ1 Ω hΩ Sj Bad hSj_pr
      subset_union_left hMZ_le hsplit_lb
    have hrank := hRankin Z hZ10 Bad
    -- Lower bound `1 + hfacND d Ω q ≥ l` for every `q ∈ Sj`
    have hSj_ge_l : ∀ q ∈ Sj, (l : ℝ) ≤ 1 + hfacND d Ω q := fun q hqSj => by
      have hq := hSj_pr q hqSj
      have hql : q ≠ l := (mem_filter.mp hqSj).2.1
      have hΩq : Ω q = forbiddenPowRes l q (powResIdeal (q : CycR l) 𝔟.1) := by dsimp [Ω]; rw [if_pos hqSj]
      have hw : ∃ k : ℕ, powResIdeal (q : CycR l) 𝔟.1 = zetaR l ^ k :=
        eq_pow_zetaR_of_pow_l_eq_one (powResIdeal_pow_l _ _)
      obtain ⟨hlt, hl_le⟩ := forbiddenPowRes_card_bounds l hq hql hw
      have hrem_pos : (0 : ℝ) < (q : ℝ) ^ d - ((Ω q).card : ℝ) := by
        rw [hΩq]; exact sub_pos.mpr (by exact_mod_cast hlt)
      have hl_le_r : (l : ℝ) * ((q : ℝ) ^ d - ((Ω q).card : ℝ)) ≤ (q : ℝ) ^ d := by
        rw [hΩq]
        have h1 : ((l * (q ^ d - (forbiddenPowRes l q (powResIdeal (q : CycR l) 𝔟.1)).card) : ℕ) : ℝ) ≤
            ((q ^ d : ℕ) : ℝ) := by exact_mod_cast hl_le
        rw [Nat.cast_mul, Nat.cast_sub hlt.le, Nat.cast_pow] at h1
        exact h1
      unfold hfacND
      rw [show 1 + ((Ω q).card : ℝ) / ((q : ℝ) ^ d - ((Ω q).card : ℝ)) =
          (q : ℝ) ^ d / ((q : ℝ) ^ d - ((Ω q).card : ℝ)) by field_simp [hrem_pos.ne']; ring]
      exact (le_div_iff₀ hrem_pos).mpr hl_le_r
    -- Compare `∏_{q ∈ Sj} l` against `D_Bad = ∏_{r ∈ Bad, r ≡ 1 (mod l)} (1 + d / r)`
    let D_Bad := ∏ r ∈ Bad.filter (fun r => r.Prime ∧ r % l = 1), (1 + (d : ℝ) / (r : ℝ))
    have hD_Bad_pos : 0 < D_Bad := prod_pos fun _ _ => by positivity
    have hD_Bad_le : D_Bad ≤
        (∏ r ∈ Sj.filter (fun r => r % l = 1), (1 + (d : ℝ) / (r : ℝ))) * D_const C := by
      have hsub : Bad.filter (fun r => r.Prime ∧ r % l = 1) ⊆
          (Sj.filter (fun r => r % l = 1)) ∪
          (((l * Ideal.absNorm 𝔟.1).primeFactors).filter (fun r => r.Prime ∧ r % l = 1)) := by
        intro r hr
        obtain ⟨hrBad, hrpr, hrmod⟩ := mem_filter.mp hr
        rcases mem_union.mp hrBad with h1 | h2
        · exact mem_union_left _ (mem_filter.mpr ⟨h1, hrmod⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨h2, hrpr, hrmod⟩)
      have h1 : D_Bad ≤ ∏ r ∈ (Sj.filter (fun r => r % l = 1)) ∪
          (((l * Ideal.absNorm 𝔟.1).primeFactors).filter (fun r => r.Prime ∧ r % l = 1)),
          (1 + (d : ℝ) / (r : ℝ)) := by
        dsimp [D_Bad]
        rw [← Finset.prod_sdiff hsub]
        have hge1 : (1 : ℝ) ≤ ∏ r ∈ (((Sj.filter (fun r => r % l = 1)) ∪
            (((l * Ideal.absNorm 𝔟.1).primeFactors).filter (fun r => r.Prime ∧ r % l = 1))) \
            Bad.filter (fun r => r.Prime ∧ r % l = 1)), (1 + (d : ℝ) / (r : ℝ)) :=
          one_le_prod fun r _ => by linarith [show (0 : ℝ) ≤ (d : ℝ) / (r : ℝ) by positivity]
        nlinarith
      have hdisj : Disjoint (Sj.filter (fun r => r % l = 1))
          (((l * Ideal.absNorm 𝔟.1).primeFactors).filter (fun r => r.Prime ∧ r % l = 1)) := by
        rw [Finset.disjoint_left]
        intro r hr1 hr2
        have hrSj := (mem_filter.mp hr1).1
        have hr_l := (mem_filter.mp hrSj).2.1
        have hr_𝔟 := (mem_filter.mp hrSj).2.2
        have hr_pr := (mem_filter.mp hr2).2.1
        have hr_dvd := Nat.dvd_of_mem_primeFactors (mem_filter.mp hr2).1
        rcases hr_pr.dvd_mul.mp hr_dvd with h1' | h2'
        · exact hr_l ((Nat.prime_dvd_prime_iff_eq hr_pr hl).mp h1')
        · exact hr_𝔟 h2'
      rw [Finset.prod_union hdisj] at h1
      exact h1
    have hratio_ge : (2 : ℝ) ^ Sj.card * (∏ r ∈ Sj.filter (fun r => r % l = 1), (1 + (d : ℝ) / (r : ℝ))) ≤
        ∏ q ∈ Sj, (1 + hfacND d Ω q) := by
      have hfactor_le : ∏ r ∈ Sj.filter (fun r => r % l = 1), (1 + (d : ℝ) / (r : ℝ)) ≤
          ∏ r ∈ Sj, (3 / 2 : ℝ) := by
        have hsub : Sj.filter (fun r => r % l = 1) ⊆ Sj := filter_subset _ _
        calc ∏ r ∈ Sj.filter (fun r => r % l = 1), (1 + (d : ℝ) / (r : ℝ))
            ≤ ∏ _r ∈ Sj.filter (fun r => r % l = 1), (3 / 2 : ℝ) := by
              refine prod_le_prod (fun _ _ => by positivity) fun r hr => ?_
              have hrpr := hSj_pr r (mem_filter.mp hr).1
              have hrmod := (mem_filter.mp hr).2
              -- Since `l` is odd prime and `r` is prime with `r ≡ 1 (mod l)`, `r ≥ 2 * l + 1`!
              have hr_ge : 2 * l + 1 ≤ r := by
                set q_rl : ℕ := r / l
                have hdiv : r = l * q_rl + 1 := by
                  have h := Nat.div_add_mod r l
                  rw [hrmod] at h; exact h.symm
                have hq0 : q_rl ≠ 0 := fun h0 => by
                  rw [h0, mul_zero, zero_add] at hdiv; have := hrpr.two_le; omega
                have hq1 : q_rl ≠ 1 := fun h1 => by
                  have hr_eq : r = l + 1 := by rw [h1, mul_one] at hdiv; exact hdiv
                  have hl_odd : l % 2 = 1 := by have := hl.eq_two_or_odd; omega
                  have hr_even : 2 ∣ r := ⟨(l + 1) / 2, by omega⟩
                  have hr2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hrpr).mp hr_even
                  omega
                have hq2 : 2 ≤ q_rl := Nat.lt_of_le_of_ne (Nat.pos_of_ne_zero hq0) (Ne.symm hq1)
                nlinarith
              have h1 : (2 * (d : ℝ)) ≤ (r : ℝ) := by exact_mod_cast (by omega : 2 * d ≤ r)
              have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpr.pos
              have hhalf : (d : ℝ) / (r : ℝ) ≤ 1 / 2 :=
                (div_le_div_iff₀ hr_pos (by norm_num : (0 : ℝ) < 2)).mpr (by linarith)
              linarith
          _ ≤ ∏ _r ∈ Sj, (3 / 2 : ℝ) := by
              rw [prod_const, prod_const]
              exact pow_le_pow_right₀ (by norm_num) (card_le_card hsub)
      have hl3 : (3 : ℝ) ≤ (l : ℝ) := by have := hl.two_le; exact_mod_cast (by omega : 3 ≤ l)
      calc (2 : ℝ) ^ Sj.card * (∏ r ∈ Sj.filter (fun r => r % l = 1), (1 + (d : ℝ) / (r : ℝ)))
          ≤ (2 : ℝ) ^ Sj.card * (∏ _r ∈ Sj, (3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hfactor_le (by positivity)
        _ = (3 : ℝ) ^ Sj.card := by rw [prod_const, ← mul_pow]; norm_num
        _ ≤ (l : ℝ) ^ Sj.card := pow_le_pow_left₀ (by norm_num) hl3 _
        _ = ∏ _q ∈ Sj, (l : ℝ) := (prod_const _).symm
        _ ≤ ∏ q ∈ Sj, (1 + hfacND d Ω q) := prod_le_prod (fun _ _ => by positivity) hSj_ge_l
    have h2Sj : (2 : ℝ) ^ j / (2 : ℝ) ^ (E_cls C) ≤ (2 : ℝ) ^ Sj.card := by
      rw [div_le_iff₀ (by positivity), ← pow_add]
      exact pow_le_pow_right₀ (by norm_num) hSj_card
    have hD_const_pos : 0 < D_const C := prod_pos fun _ _ => by positivity
    have hdenom_lb : (c_l / (5 * (d : ℝ))) * (2 : ℝ) ^ j / (D_const C * (2 : ℝ) ^ (E_cls C)) * Real.log x ≤
        ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfacND d Ω p := by
      have hfac_ratio : (2 : ℝ) ^ j / (D_const C * (2 : ℝ) ^ (E_cls C)) ≤
          (∏ q ∈ Sj, (1 + hfacND d Ω q)) / D_Bad := by
        rw [le_div_iff₀ hD_Bad_pos]
        calc (2 : ℝ) ^ j / (D_const C * (2 : ℝ) ^ (E_cls C)) * D_Bad
            ≤ (2 : ℝ) ^ j / (D_const C * (2 : ℝ) ^ (E_cls C)) *
              ((∏ r ∈ Sj.filter (fun r => r % l = 1), (1 + (d : ℝ) / (r : ℝ))) * D_const C) :=
              mul_le_mul_of_nonneg_left hD_Bad_le (by positivity)
          _ = ((2 : ℝ) ^ j / (2 : ℝ) ^ (E_cls C)) *
              (∏ r ∈ Sj.filter (fun r => r % l = 1), (1 + (d : ℝ) / (r : ℝ))) := by
              field_simp [hD_const_pos.ne']
          _ ≤ (2 : ℝ) ^ Sj.card * (∏ r ∈ Sj.filter (fun r => r % l = 1), (1 + (d : ℝ) / (r : ℝ))) :=
              mul_le_mul_of_nonneg_right h2Sj (prod_nonneg fun _ _ => by positivity)
          _ ≤ ∏ q ∈ Sj, (1 + hfacND d Ω q) := hratio_ge
      calc (c_l / (5 * (d : ℝ))) * (2 : ℝ) ^ j / (D_const C * (2 : ℝ) ^ (E_cls C)) * Real.log x
          = ((2 : ℝ) ^ j / (D_const C * (2 : ℝ) ^ (E_cls C))) * (c_l * ((1 / (5 * (d : ℝ))) * Real.log x)) := by ring
        _ ≤ ((∏ q ∈ Sj, (1 + hfacND d Ω q)) / D_Bad) * (c_l * Real.log (Z : ℝ)) :=
            mul_le_mul hfac_ratio (mul_le_mul_of_nonneg_left hlogZ hc_l.le)
              (by positivity) (div_nonneg (prod_nonneg fun q hq => by
                linarith [hfacND_nonneg Ω q (hΩ q (hSj_pr q hq))]) hD_Bad_pos.le)
        _ = (∏ q ∈ Sj, (1 + hfacND d Ω q)) * ((c_l * Real.log (Z : ℝ)) / D_Bad) := by ring
        _ ≤ (∏ q ∈ Sj, (1 + hfacND d Ω q)) *
            (∑ m ∈ (Icc 1 Z).filter (fun m => Squarefree m ∧ ∀ r ∈ m.primeFactors, r % l = 1 ∧ r ∉ Bad),
              ∏ r ∈ m.primeFactors, ((d : ℝ) / (r : ℝ))) :=
            mul_le_mul_of_nonneg_left hrank (prod_nonneg fun q hq => by
              linarith [hfacND_nonneg Ω q (hΩ q (hSj_pr q hq))])
        _ ≤ ∑ q ∈ (Icc 1 Q).filter Squarefree, ∏ p ∈ q.primeFactors, hfacND d Ω p := hdenom_split
    have hcomb : (PC.card : ℝ) *
        ((c_l / (5 * (d : ℝ))) * (2 : ℝ) ^ j / (D_const C * (2 : ℝ) ^ (E_cls C)) * Real.log x) ≤
        (8 * C_box + 16) ^ d * x :=
      (mul_le_mul_of_nonneg_left hdenom_lb (Nat.cast_nonneg _)).trans (hls.trans hnum_le)
    rw [← mul_div_assoc, div_le_div_iff₀ hx_pos (by positivity)]
    have hcoeff_pos : 0 < (c_l / (5 * (d : ℝ))) / (D_const C * (2 : ℝ) ^ (E_cls C)) := by positivity
    have hcomb' : ((PC.card : ℝ) * Real.log x * (2 : ℝ) ^ j) *
        ((c_l / (5 * (d : ℝ))) / (D_const C * (2 : ℝ) ^ (E_cls C))) ≤ (8 * C_box + 16) ^ d * x := by
      calc ((PC.card : ℝ) * Real.log x * (2 : ℝ) ^ j) *
            ((c_l / (5 * (d : ℝ))) / (D_const C * (2 : ℝ) ^ (E_cls C)))
          = (PC.card : ℝ) *
            ((c_l / (5 * (d : ℝ))) * (2 : ℝ) ^ j / (D_const C * (2 : ℝ) ^ (E_cls C)) * Real.log x) := by ring
        _ ≤ (8 * C_box + 16) ^ d * x := hcomb
    have hfinal := (le_div_iff₀ hcoeff_pos).mpr hcomb'
    have hrew_rhs : (8 * C_box + 16) ^ d * x /
        ((c_l / (5 * (d : ℝ))) / (D_const C * (2 : ℝ) ^ (E_cls C))) = K_cls C * x := by
      dsimp [K_cls, C_box]
      field_simp [hc_l.ne', hd_pos.ne', hD_const_pos.ne']
    linarith
  have hsub_all : P_all ⊆ P_lo ∪ P_hi := fun p hp => by
    by_cases hle : p ≤ Q
    · exact mem_union_left _ (mem_filter.mpr ⟨hp, hle⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hp, by omega⟩)
  have hcard_all : (P_all.card : ℝ) ≤ (P_lo.card : ℝ) + (P_hi.card : ℝ) := by
    exact_mod_cast (card_le_card hsub_all).trans (card_union_le P_lo P_hi)
  calc (P_all.card : ℝ) * (Real.log x / x)
      ≤ ((P_lo.card : ℝ) + (P_hi.card : ℝ)) * (Real.log x / x) :=
        mul_le_mul_of_nonneg_right hcard_all (by positivity)
    _ = (P_lo.card : ℝ) * (Real.log x / x) +
        ∑ C : ClassGroup (CycR l), ((P_hi.filter (fun p => clsOf p = C)).card : ℝ) * (Real.log x / x) := by
        rw [add_mul, hhi_sum, sum_mul]
    _ ≤ 1 / (2 : ℝ) ^ j + ∑ C : ClassGroup (CycR l), K_cls C / (2 : ℝ) ^ j :=
        add_le_add hlo_bound (sum_le_sum fun C _ => hper_cls C)
    _ = C_tot / (2 : ℝ) ^ j := by dsimp [C_tot]; rw [← sum_div, add_div]

end CaseOddPrime

end Erdos980Main

/-- Elliott's 1967/68 tail estimate for prime exponents `l`:
    `OMA.R_Erdos980_erdos_980_R1.H2`. -/
theorem OMA.solution : OMA.R_Erdos980_erdos_980_R1.H2 := by
  intro l hl
  by_cases hl2 : l = 2
  · subst hl2
    exact Erdos980H2.tail_of_sieve_pattern_bound Nat.prime_two Erdos980Main.sieve_pattern_bound_two
  · exact Erdos980H2.tail_of_sieve_pattern_bound hl (Erdos980Main.sieve_pattern_bound_odd_l hl hl2)
