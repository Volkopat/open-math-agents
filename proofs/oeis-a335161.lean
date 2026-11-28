import OMAStatements.S_oeis_a335161

-- Problem: A335161: a(n) = nim-product of 2^4 and 2^n.
-- Credit: @ceejcake
-- Proof:
-- 1. Establish Conway's Fermat 2-power scaling for F = 16:
--      ∀ a < 16, ∀ b, nimMul a b = 16 * nimMul a (b / 16) ^^^ nimMul a (b % 16),
--    hence also nimMul a b = 256 * nimMul a (b / 256) ^^^ nimMul a (b % 256) for a < 16.
-- 2. Define the explicit GF(256) nim-multiplication formula `nm256` from `nm16` and prove
--    `nimMul 16 r = nm256 16 r` for all r < 256 (using the explicit inverse `inv16Shift` of
--    `16 ^^^ a'` in GF(256) for a' < 16).
-- 3. By strong induction on b, prove Conway's F = 256 scaling for a = 16:
--      ∀ b, nimMul 16 b = 256 * nimMul 16 (b / 256) ^^^ nimMul 16 (b % 256).
-- 4. Specializing to b = 2^n (n > 7) gives a(n) = 256 * a(n - 8), and base cases
--    a(0..7) = 16, 32, 64, 128, 24, 44, 75, 141 yield the rational generating function.

namespace ProofA335161

open OMA.S_oeis_a335161 PowerSeries

-- Part 1: Computable GF(16) and GF(256) nim-multiplication (before Classical)
private def nm4 (a b : ℕ) : ℕ :=
  let a1 := a / 2; let a0 := a % 2
  let b1 := b / 2; let b0 := b % 2
  let c1 := (a1 * b0) ^^^ (a0 * b1) ^^^ (a1 * b1)
  let c0 := (a0 * b0) ^^^ (a1 * b1)
  2 * c1 + c0

private def nm16 (a b : ℕ) : ℕ :=
  let a1 := a / 4; let a0 := a % 4
  let b1 := b / 4; let b0 := b % 4
  let c1 := nm4 a1 b0 ^^^ nm4 a0 b1 ^^^ nm4 a1 b1
  let c0 := nm4 a0 b0 ^^^ nm4 2 (nm4 a1 b1)
  4 * c1 + c0

private def nm256 (a b : ℕ) : ℕ :=
  let a1 := a / 16; let a0 := a % 16
  let b1 := b / 16; let b0 := b % 16
  let c1 := nm16 a1 b0 ^^^ nm16 a0 b1 ^^^ nm16 a1 b1
  let c0 := nm16 a0 b0 ^^^ nm16 8 (nm16 a1 b1)
  16 * c1 + c0

private lemma nm16_lt : ∀ a b : Fin 16, nm16 a.1 b.1 < 16 := by decide
private lemma nm16_comm : ∀ a b : Fin 16, nm16 a.1 b.1 = nm16 b.1 a.1 := by decide
private lemma nm16_assoc : ∀ a b c : Fin 16, nm16 (nm16 a.1 b.1) c.1 = nm16 a.1 (nm16 b.1 c.1) := by decide
private lemma nm16_distrib_left : ∀ a b c : Fin 16,
    nm16 (a.1 ^^^ b.1) c.1 = nm16 a.1 c.1 ^^^ nm16 b.1 c.1 := by decide
private lemma nm16_no_zero_div : ∀ a b : Fin 16, nm16 a.1 b.1 = 0 → a.1 = 0 ∨ b.1 = 0 := by decide
private lemma nm16_surj : ∀ d : Fin 16, d.1 ≠ 0 → ∀ v : Fin 16, ∃ r : Fin 16, nm16 d.1 r.1 = v.1 := by decide
private lemma nm16_mex_lt : ∀ a b m : Fin 16, m.1 < nm16 a.1 b.1 →
    ∃ a' : Fin 16, a'.1 < a.1 ∧ ∃ b' : Fin 16, b'.1 < b.1 ∧
      m.1 = nm16 a'.1 b.1 ^^^ nm16 a.1 b'.1 ^^^ nm16 a'.1 b'.1 := by decide +kernel
private lemma xor_lt_16 : ∀ a b : Fin 16, (a.1 ^^^ b.1) < 16 := by decide
private lemma nm16_one_left : ∀ x : Fin 16, nm16 1 x.1 = x.1 := by decide
private lemma nm16_zero_right : ∀ x : Fin 16, nm16 x.1 0 = 0 := by decide
private lemma nm16_norm_ne_zero : ∀ a : Fin 16, (nm16 a.1 (a.1 ^^^ 1) ^^^ 8) ≠ 0 := by decide
private lemma nm16_sq_surj : ∀ d : Fin 16, d.1 ≠ 0 → ∀ v : Fin 16,
    ∃ a : Fin 16, nm16 (nm16 a.1 a.1) d.1 = v.1 := by decide
private lemma xor_lt_split16 : ∀ r1 r0 m1 : Fin 16, m1.1 < (r1.1 ^^^ r0.1) →
    (r1.1 ^^^ m1.1) < r0.1 ∨ (r0.1 ^^^ m1.1) < r1.1 := by decide
private lemma nm16_case2_wit : ∀ r1 m0 : Fin 16, m0.1 < nm16 8 r1.1 →
    ∃ a' r1' : Fin 16, r1'.1 < r1.1 ∧
      nm16 (nm16 a'.1 (a'.1 ^^^ 1) ^^^ 8) (r1.1 ^^^ r1'.1) = nm16 8 r1.1 ^^^ m0.1 := by decide
private lemma nm256_base :
    nm256 16 1 = 16 ∧ nm256 16 2 = 32 ∧ nm256 16 4 = 64 ∧ nm256 16 8 = 128 ∧
    nm256 16 16 = 24 ∧ nm256 16 32 = 44 ∧ nm256 16 64 = 75 ∧ nm256 16 128 = 141 := by decide

section
open scoped Classical

-- Bitwise XOR helpers for F = 16 = 2^4 and F = 256 = 2^8
private lemma xor_div16 (x y : ℕ) : (x ^^^ y) / 16 = x / 16 ^^^ y / 16 := by
  have h : (16 : ℕ) = 2 ^ 4 := rfl
  rw [h, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_xor_distrib]

private lemma xor_mod16 (x y : ℕ) : (x ^^^ y) % 16 = x % 16 ^^^ y % 16 := by
  have h : (16 : ℕ) = 2 ^ 4 := rfl
  rw [h, Nat.xor_mod_two_pow]

private lemma xor_div256 (x y : ℕ) : (x ^^^ y) / 256 = x / 256 ^^^ y / 256 := by
  have h : (256 : ℕ) = 2 ^ 8 := rfl
  rw [h, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_xor_distrib]

private lemma xor_mod256 (x y : ℕ) : (x ^^^ y) % 256 = x % 256 ^^^ y % 256 := by
  have h : (256 : ℕ) = 2 ^ 8 := rfl
  rw [h, Nat.xor_mod_two_pow]

private lemma mul_pow2_xor_add (K q r : ℕ) (hr : r < 2 ^ K) : 2 ^ K * q ^^^ r = 2 ^ K * q + r := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [Nat.testBit_xor]
  by_cases hk : k < K
  · have hq : (2 ^ K * q).testBit k = false := by
      have : 2 ^ K * q = q <<< K := by rw [Nat.shiftLeft_eq]; ring
      rw [this, Nat.testBit_shiftLeft]; simp [show ¬ (K ≤ k) by omega]
    have hadd : (2 ^ K * q + r).testBit k = r.testBit k := by
      have h1 := Nat.testBit_mod_two_pow (2 ^ K * q + r) K k
      have hmod : (2 ^ K * q + r) % 2 ^ K = r := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
      simp [hk, hmod] at h1
      exact h1.symm
    rw [hq, Bool.false_xor, hadd]
  · have hpow_le : 2 ^ K ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    have hr0 : r.testBit k = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hr hpow_le)
    have hadd : (2 ^ K * q + r).testBit k = (2 ^ K * q).testBit k := by
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : (2 ^ K * q + r) / 2 ^ k = (2 ^ K * q) / 2 ^ k := by
        have hpow : 2 ^ k = 2 ^ K * 2 ^ (k - K) := by
          have hkK : k = K + (k - K) := by omega
          conv_lhs => rw [hkK]
          rw [pow_add]
        rw [hpow, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
        congr 1
        have hpos : 0 < 2 ^ K := Nat.pos_of_ne_zero (by positivity)
        rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hr, add_zero, Nat.mul_div_right q hpos]
      rw [hdiv]
    rw [hr0, Bool.xor_false, hadd]

private lemma mul16_xor_add (q r : ℕ) (hr : r < 16) : 16 * q ^^^ r = 16 * q + r :=
  mul_pow2_xor_add 4 q r hr

private lemma div16_mul16_xor (q r : ℕ) (hr : r < 16) : (16 * q ^^^ r) / 16 = q := by
  rw [mul16_xor_add q r hr]; omega

private lemma mod16_mul16_xor (q r : ℕ) (hr : r < 16) : (16 * q ^^^ r) % 16 = r := by
  rw [mul16_xor_add q r hr]; omega

private lemma mul256_xor_add (q r : ℕ) (hr : r < 256) : 256 * q ^^^ r = 256 * q + r :=
  mul_pow2_xor_add 8 q r hr

private lemma div256_mul256_xor (q r : ℕ) (hr : r < 256) : (256 * q ^^^ r) / 256 = q := by
  rw [mul256_xor_add q r hr]; omega

private lemma mod256_mul256_xor (q r : ℕ) (hr : r < 256) : (256 * q ^^^ r) % 256 = r := by
  rw [mul256_xor_add q r hr]; omega

private lemma xor_eq_zero_imp {a b : ℕ} (h : a ^^^ b = 0) : a = b := by
  apply Nat.eq_of_testBit_eq; intro k
  have hk := congr_arg (fun x => x.testBit k) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at hk
  cases ha : a.testBit k <;> cases hb : b.testBit k <;> simp [ha, hb] at hk ⊢

private lemma xor_lt_256 {a b : ℕ} (ha : a < 256) (hb : b < 256) : (a ^^^ b) < 256 := by
  have hd : (a ^^^ b) / 256 = 0 := by rw [xor_div256, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb]; simp
  omega

private lemma nimMul_eq_sInf (a b : ℕ) :
    nimMul a b = sInf {m : ℕ | ∀ a' < a, ∀ b' < b, m ≠ nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b'} := by
  rw [nimMul]

private lemma nimMul_mem_set (a b : ℕ) :
    ∀ a' < a, ∀ b' < b, nimMul a b ≠ nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b' := by
  let S := {m : ℕ | ∀ a' < a, ∀ b' < b, m ≠ nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b'}
  have hne : S.Nonempty := by
    let bad := (Finset.range a ×ˢ Finset.range b).image (fun p => nimMul p.1 b ^^^ nimMul a p.2 ^^^ nimMul p.1 p.2)
    obtain ⟨m, hm⟩ := Infinite.exists_notMem_finset bad
    refine ⟨m, fun a' ha' b' hb' heq => hm ?_⟩
    exact Finset.mem_image.mpr ⟨(a', b'), Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha', Finset.mem_range.mpr hb'⟩, heq.symm⟩
  have hmem : sInf S ∈ S := Nat.sInf_mem hne
  rw [← nimMul_eq_sInf] at hmem
  exact hmem

private lemma nimMul_lt_witness {a b m : ℕ} (hm : m < nimMul a b) :
    ∃ a' < a, ∃ b' < b, m = nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b' := by
  by_contra h
  push Not at h
  have hmem : m ∈ {m : ℕ | ∀ a' < a, ∀ b' < b, m ≠ nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b'} := h
  have hle : nimMul a b ≤ m := by rw [nimMul_eq_sInf]; exact Nat.sInf_le hmem
  omega

private lemma nimMul_eq_of_mex {a b M : ℕ}
    (h1 : ∀ a' < a, ∀ b' < b, M ≠ nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b')
    (h2 : ∀ m < M, ∃ a' < a, ∃ b' < b, m = nimMul a' b ^^^ nimMul a b' ^^^ nimMul a' b') :
    nimMul a b = M := by
  apply le_antisymm
  · rw [nimMul_eq_sInf]; exact Nat.sInf_le h1
  · by_contra hlt; push Not at hlt
    rcases h2 (nimMul a b) hlt with ⟨a', ha', b', hb', heq⟩
    exact nimMul_mem_set a b a' ha' b' hb' heq

private lemma nimMul_zero_right (a : ℕ) : nimMul a 0 = 0 := by
  apply nimMul_eq_of_mex
  · intro _ _ _ hb; omega
  · intro _ hm; omega

-- Part 2: F = 16 agreement & scaling
private lemma nm16_mex_ne {a b a' b' : ℕ} (ha : a < 16) (hb : b < 16) (ha' : a' < a) (hb' : b' < b) :
    nm16 a b ≠ nm16 a' b ^^^ nm16 a b' ^^^ nm16 a' b' := by
  intro heq
  have hx : (a ^^^ a') < 16 := xor_lt_16 ⟨a, ha⟩ ⟨a', by omega⟩
  have hy : (b ^^^ b') < 16 := xor_lt_16 ⟨b, hb⟩ ⟨b', by omega⟩
  have hdist1 : nm16 (a ^^^ a') b = nm16 a b ^^^ nm16 a' b := nm16_distrib_left ⟨a, ha⟩ ⟨a', by omega⟩ ⟨b, hb⟩
  have hdist2 : nm16 (a ^^^ a') b' = nm16 a b' ^^^ nm16 a' b' := nm16_distrib_left ⟨a, ha⟩ ⟨a', by omega⟩ ⟨b', by omega⟩
  have hdist3 : nm16 (a ^^^ a') (b ^^^ b') = nm16 (a ^^^ a') b ^^^ nm16 (a ^^^ a') b' := by
    rw [nm16_comm ⟨a ^^^ a', hx⟩ ⟨b ^^^ b', hy⟩, nm16_distrib_left ⟨b, hb⟩ ⟨b', by omega⟩ ⟨a ^^^ a', hx⟩,
      nm16_comm ⟨b, hb⟩ ⟨a ^^^ a', hx⟩, nm16_comm ⟨b', by omega⟩ ⟨a ^^^ a', hx⟩]
  have hzero : nm16 (a ^^^ a') (b ^^^ b') = 0 := by
    rw [hdist3, hdist1, hdist2, heq]
    simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
  rcases nm16_no_zero_div ⟨a ^^^ a', hx⟩ ⟨b ^^^ b', hy⟩ hzero with h0 | h0
  · dsimp only at h0; have := xor_eq_zero_imp h0; omega
  · dsimp only at h0; have := xor_eq_zero_imp h0; omega

private lemma nimMul_eq_nm16 : ∀ s a b : ℕ, a + b = s → a < 16 → b < 16 → nimMul a b = nm16 a b := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro a b hsum ha hb
    apply nimMul_eq_of_mex
    · intro a' ha' b' hb'
      rw [ih (a' + b) (by omega) a' b rfl (by omega) hb,
          ih (a + b') (by omega) a b' rfl ha (by omega),
          ih (a' + b') (by omega) a' b' rfl (by omega) (by omega)]
      exact nm16_mex_ne ha hb ha' hb'
    · intro m hm
      have hm16 : m < 16 := lt_trans hm (nm16_lt ⟨a, ha⟩ ⟨b, hb⟩)
      rcases nm16_mex_lt ⟨a, ha⟩ ⟨b, hb⟩ ⟨m, hm16⟩ hm with ⟨a', ha', b', hb', heq⟩
      dsimp only at ha' hb'
      refine ⟨a'.1, ha', b'.1, hb', ?_⟩
      rw [ih (a'.1 + b) (by omega) a'.1 b rfl a'.2 hb,
          ih (a + b'.1) (by omega) a b'.1 rfl ha b'.2,
          ih (a'.1 + b'.1) (by omega) a'.1 b'.1 rfl a'.2 b'.2]
      exact heq

private lemma nimMul_scale16 : ∀ s a b : ℕ, a + b = s → a < 16 →
    nimMul a b = 16 * nimMul a (b / 16) ^^^ nimMul a (b % 16) := by
  intro s
  induction s using Nat.strong_induction_on with
  | h s ih =>
    intro a b hsum ha
    let q := b / 16
    let r := b % 16
    have hr16 : r < 16 := Nat.mod_lt b (by omega)
    have hnr16 : nimMul a r < 16 := by
      rw [nimMul_eq_nm16 (a + r) a r rfl ha hr16]; exact nm16_lt ⟨a, ha⟩ ⟨r, hr16⟩
    apply nimMul_eq_of_mex
    · intro a' ha' b' hb' heq
      let q' := b' / 16
      let r' := b' % 16
      have hr'16 : r' < 16 := Nat.mod_lt b' (by omega)
      have ha'16 : a' < 16 := by omega
      rw [ih (a' + b) (by omega) a' b rfl ha'16,
          ih (a + b') (by omega) a b' rfl ha,
          ih (a' + b') (by omega) a' b' rfl ha'16] at heq
      have hdiv := congr_arg (· / 16) heq
      have hmod := congr_arg (· % 16) heq
      have hna'r : nimMul a' r < 16 := by rw [nimMul_eq_nm16 (a' + r) a' r rfl ha'16 hr16]; exact nm16_lt ⟨a', ha'16⟩ ⟨r, hr16⟩
      have hnar' : nimMul a r' < 16 := by rw [nimMul_eq_nm16 (a + r') a r' rfl ha hr'16]; exact nm16_lt ⟨a, ha⟩ ⟨r', hr'16⟩
      have hna'r' : nimMul a' r' < 16 := by rw [nimMul_eq_nm16 (a' + r') a' r' rfl ha'16 hr'16]; exact nm16_lt ⟨a', ha'16⟩ ⟨r', hr'16⟩
      rw [div16_mul16_xor _ _ hnr16, xor_div16, xor_div16,
          div16_mul16_xor _ _ hna'r, div16_mul16_xor _ _ hnar', div16_mul16_xor _ _ hna'r'] at hdiv
      rw [mod16_mul16_xor _ _ hnr16, xor_mod16, xor_mod16,
          mod16_mul16_xor _ _ hna'r, mod16_mul16_xor _ _ hnar', mod16_mul16_xor _ _ hna'r'] at hmod
      by_cases hq : q' < q
      · exact nimMul_mem_set a q a' ha' q' hq hdiv
      · have hqeq : q' = q := by omega
        have hrlt : r' < r := by omega
        exact nimMul_mem_set a r a' ha' r' hrlt hmod
    · intro m hm
      rw [mul16_xor_add _ _ hnr16] at hm
      have hdiv_mod : ∀ x y : ℕ, x / 16 = y / 16 → x % 16 = y % 16 → x = y := fun x y h1 h2 => by omega
      have hv16 : m % 16 < 16 := Nat.mod_lt m (by omega)
      by_cases hu : m / 16 < nimMul a (b / 16)
      · rcases nimMul_lt_witness hu with ⟨a', ha', q', hq', hu_eq⟩
        have ha'16 : a' < 16 := by omega
        have hdiff_lt : (a ^^^ a') < 16 := xor_lt_16 ⟨a, ha⟩ ⟨a', ha'16⟩
        have hdiff_ne : (a ^^^ a') ≠ 0 := fun h => by have := xor_eq_zero_imp h; omega
        have hna'r : nimMul a' (b % 16) < 16 := by rw [nimMul_eq_nm16 (a' + b % 16) a' (b % 16) rfl ha'16 hr16]; exact nm16_lt ⟨a', ha'16⟩ ⟨b % 16, hr16⟩
        have htarget_lt : (m % 16 ^^^ nm16 a' (b % 16)) < 16 :=
          xor_lt_16 ⟨m % 16, hv16⟩ ⟨nm16 a' (b % 16), nm16_lt ⟨a', ha'16⟩ ⟨b % 16, hr16⟩⟩
        rcases nm16_surj ⟨a ^^^ a', hdiff_lt⟩ hdiff_ne ⟨m % 16 ^^^ nm16 a' (b % 16), htarget_lt⟩ with ⟨r', hr'_eq⟩
        let b' := 16 * q' + r'.1
        have hb' : b' < b := by have := r'.2; omega
        refine ⟨a', ha', b', hb', ?_⟩
        rw [ih (a' + b) (by omega) a' b rfl ha'16,
            ih (a + b') (by omega) a b' rfl ha,
            ih (a' + b') (by omega) a' b' rfl ha'16]
        have hb'd : b' / 16 = q' := by have := r'.2; omega
        have hb'm : b' % 16 = r'.1 := by have := r'.2; omega
        rw [hb'd, hb'm]
        have hlow : nimMul a' (b % 16) ^^^ nimMul a r'.1 ^^^ nimMul a' r'.1 = m % 16 := by
          rw [nimMul_eq_nm16 (a' + b % 16) a' (b % 16) rfl ha'16 hr16,
              nimMul_eq_nm16 (a + r'.1) a r'.1 rfl ha r'.2,
              nimMul_eq_nm16 (a' + r'.1) a' r'.1 rfl ha'16 r'.2]
          have hdist := nm16_distrib_left ⟨a, ha⟩ ⟨a', ha'16⟩ r'
          rw [Nat.xor_assoc, ← hdist, hr'_eq]; simp
        have hnar' : nimMul a r'.1 < 16 := by rw [nimMul_eq_nm16 (a + r'.1) a r'.1 rfl ha r'.2]; exact nm16_lt ⟨a, ha⟩ r'
        have hna'r' : nimMul a' r'.1 < 16 := by rw [nimMul_eq_nm16 (a' + r'.1) a' r'.1 rfl ha'16 r'.2]; exact nm16_lt ⟨a', ha'16⟩ r'
        apply hdiv_mod
        · rw [xor_div16, xor_div16, div16_mul16_xor _ _ hna'r, div16_mul16_xor _ _ hnar', div16_mul16_xor _ _ hna'r']
          exact hu_eq
        · rw [xor_mod16, xor_mod16, mod16_mul16_xor _ _ hna'r, mod16_mul16_xor _ _ hnar', mod16_mul16_xor _ _ hna'r']
          exact hlow.symm
      · have hu_eq : m / 16 = nimMul a (b / 16) := by omega
        have hv_lt : m % 16 < nimMul a (b % 16) := by dsimp only [r] at hm; omega
        rcases nimMul_lt_witness hv_lt with ⟨a', ha', r', hr', hv_eq⟩
        have ha'16 : a' < 16 := by omega
        have hr'16 : r' < 16 := by omega
        let b' := 16 * (b / 16) + r'
        have hb' : b' < b := by omega
        refine ⟨a', ha', b', hb', ?_⟩
        rw [ih (a' + b) (by omega) a' b rfl ha'16,
            ih (a + b') (by omega) a b' rfl ha,
            ih (a' + b') (by omega) a' b' rfl ha'16]
        have hb'd : b' / 16 = b / 16 := by omega
        have hb'm : b' % 16 = r' := by omega
        rw [hb'd, hb'm]
        have hna'r : nimMul a' (b % 16) < 16 := by rw [nimMul_eq_nm16 (a' + b % 16) a' (b % 16) rfl ha'16 hr16]; exact nm16_lt ⟨a', ha'16⟩ ⟨b % 16, hr16⟩
        have hnar' : nimMul a r' < 16 := by rw [nimMul_eq_nm16 (a + r') a r' rfl ha hr'16]; exact nm16_lt ⟨a, ha⟩ ⟨r', hr'16⟩
        have hna'r' : nimMul a' r' < 16 := by rw [nimMul_eq_nm16 (a' + r') a' r' rfl ha'16 hr'16]; exact nm16_lt ⟨a', ha'16⟩ ⟨r', hr'16⟩
        apply hdiv_mod
        · rw [xor_div16, xor_div16, div16_mul16_xor _ _ hna'r, div16_mul16_xor _ _ hnar', div16_mul16_xor _ _ hna'r']
          rw [hu_eq]; simp
        · rw [xor_mod16, xor_mod16, mod16_mul16_xor _ _ hna'r, mod16_mul16_xor _ _ hnar', mod16_mul16_xor _ _ hna'r']
          exact hv_eq

-- Corollary: F = 256 scaling for a < 16 (by applying F = 16 scaling twice)
private lemma nimMul_scale256_lt16 {a : ℕ} (ha : a < 16) (b : ℕ) :
    nimMul a b = 256 * nimMul a (b / 256) ^^^ nimMul a (b % 256) := by
  have h1 := nimMul_scale16 (a + b) a b rfl ha
  have h2 := nimMul_scale16 (a + b / 16) a (b / 16) rfl ha
  have h3 := nimMul_scale16 (a + b % 256) a (b % 256) rfl ha
  have hr0 : nimMul a (b % 16) < 16 := by
    rw [nimMul_eq_nm16 (a + b % 16) a (b % 16) rfl ha (Nat.mod_lt b (by omega))]
    exact nm16_lt ⟨a, ha⟩ ⟨b % 16, Nat.mod_lt b (by omega)⟩
  have hr1 : nimMul a (b / 16 % 16) < 16 := by
    rw [nimMul_eq_nm16 (a + b / 16 % 16) a (b / 16 % 16) rfl ha (Nat.mod_lt _ (by omega))]
    exact nm16_lt ⟨a, ha⟩ ⟨b / 16 % 16, Nat.mod_lt _ (by omega)⟩
  have e1 : b / 16 / 16 = b / 256 := by omega
  have e2 : b % 256 / 16 = b / 16 % 16 := by omega
  have e3 : b % 256 % 16 = b % 16 := by omega
  rw [h1, h2, e1, h3, e2, e3]
  rw [mul16_xor_add _ _ hr1, mul16_xor_add _ _ hr0, mul16_xor_add _ _ hr0]
  have hlt256 : 16 * nimMul a (b / 16 % 16) + nimMul a (b % 16) < 256 := by omega
  rw [mul256_xor_add _ _ hlt256]
  ring

private lemma nimMul_lt256_of_lt16 {a r : ℕ} (ha : a < 16) (hr : r < 256) : nimMul a r < 256 := by
  rw [nimMul_scale16 (a + r) a r rfl ha]
  have hq : nimMul a (r / 16) < 16 := by
    rw [nimMul_eq_nm16 (a + r / 16) a (r / 16) rfl ha (by omega)]; exact nm16_lt ⟨a, ha⟩ ⟨r / 16, by omega⟩
  have hmod : nimMul a (r % 16) < 16 := by
    rw [nimMul_eq_nm16 (a + r % 16) a (r % 16) rfl ha (by omega)]; exact nm16_lt ⟨a, ha⟩ ⟨r % 16, by omega⟩
  rw [mul16_xor_add _ _ hmod]; omega

-- Part 3: nm256 algebraic properties and agreement with nimMul 16 r for r < 256
private lemma nm256_lt {a b : ℕ} (ha : a < 256) (hb : b < 256) : nm256 a b < 256 := by
  unfold nm256
  have ha1 : a / 16 < 16 := by omega
  have ha0 : a % 16 < 16 := by omega
  have hb1 : b / 16 < 16 := by omega
  have hb0 : b % 16 < 16 := by omega
  have h1 := nm16_lt ⟨a / 16, ha1⟩ ⟨b % 16, hb0⟩
  have h2 := nm16_lt ⟨a % 16, ha0⟩ ⟨b / 16, hb1⟩
  have h3 := nm16_lt ⟨a / 16, ha1⟩ ⟨b / 16, hb1⟩
  have h4 := nm16_lt ⟨a % 16, ha0⟩ ⟨b % 16, hb0⟩
  have h5 := nm16_lt ⟨8, by omega⟩ ⟨nm16 (a / 16) (b / 16), h3⟩
  have hc1 : (nm16 (a / 16) (b % 16) ^^^ nm16 (a % 16) (b / 16) ^^^ nm16 (a / 16) (b / 16)) < 16 :=
    xor_lt_16 ⟨_, xor_lt_16 ⟨_, h1⟩ ⟨_, h2⟩⟩ ⟨_, h3⟩
  have hc0 : (nm16 (a % 16) (b % 16) ^^^ nm16 8 (nm16 (a / 16) (b / 16))) < 16 :=
    xor_lt_16 ⟨_, h4⟩ ⟨_, h5⟩
  dsimp only
  omega

private lemma nm256_eq_nimMul_lt16 {a r : ℕ} (ha : a < 16) (hr : r < 256) : nm256 a r = nimMul a r := by
  rw [nimMul_scale16 (a + r) a r rfl ha]
  have hq : nimMul a (r / 16) = nm16 a (r / 16) := nimMul_eq_nm16 _ _ _ rfl ha (by omega)
  have hm : nimMul a (r % 16) = nm16 a (r % 16) := nimMul_eq_nm16 _ _ _ rfl ha (by omega)
  have hmlt : nm16 a (r % 16) < 16 := nm16_lt ⟨a, ha⟩ ⟨r % 16, by omega⟩
  rw [hq, hm, mul16_xor_add _ _ hmlt]
  unfold nm256; dsimp only
  have ha1 : a / 16 = 0 := by omega
  have ha0 : a % 16 = a := by omega
  have hz : ∀ x : Fin 16, nm16 0 x.1 = 0 := by decide
  rw [ha1, ha0, hz ⟨r % 16, by omega⟩, hz ⟨r / 16, by omega⟩,
      show nm16 8 0 = 0 by decide]
  simp

private lemma nm256_distrib_left {a b c : ℕ} (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    nm256 (a ^^^ b) c = nm256 a c ^^^ nm256 b c := by
  have hmul : ∀ x y : ℕ, x < 256 → y < 256 →
      nm256 x y = 16 * (nm16 (x / 16) (y % 16) ^^^ nm16 (x % 16) (y / 16) ^^^ nm16 (x / 16) (y / 16)) ^^^
        (nm16 (x % 16) (y % 16) ^^^ nm16 8 (nm16 (x / 16) (y / 16))) := by
    intro x y hx hy
    unfold nm256
    have h4 := nm16_lt ⟨x % 16, by omega⟩ ⟨y % 16, by omega⟩
    have h3 := nm16_lt ⟨x / 16, by omega⟩ ⟨y / 16, by omega⟩
    have h5 := nm16_lt ⟨8, by omega⟩ ⟨nm16 (x / 16) (y / 16), h3⟩
    have hc0 : (nm16 (x % 16) (y % 16) ^^^ nm16 8 (nm16 (x / 16) (y / 16))) < 16 := xor_lt_16 ⟨_, h4⟩ ⟨_, h5⟩
    exact (mul16_xor_add _ _ hc0).symm
  have hab : (a ^^^ b) < 256 := xor_lt_256 ha hb
  rw [hmul (a ^^^ b) c hab hc, hmul a c ha hc, hmul b c hb hc]
  have hd : ∀ x y : ℕ, x / 16 = y / 16 → x % 16 = y % 16 → x = y := fun x y h1 h2 => by omega
  have hc0_ab : (nm16 ((a ^^^ b) % 16) (c % 16) ^^^ nm16 8 (nm16 ((a ^^^ b) / 16) (c / 16))) < 16 :=
    xor_lt_16 ⟨_, nm16_lt ⟨_, by omega⟩ ⟨_, by omega⟩⟩ ⟨_, nm16_lt ⟨8, by omega⟩ ⟨_, nm16_lt ⟨_, by omega⟩ ⟨_, by omega⟩⟩⟩
  have hc0_a : (nm16 (a % 16) (c % 16) ^^^ nm16 8 (nm16 (a / 16) (c / 16))) < 16 :=
    xor_lt_16 ⟨_, nm16_lt ⟨_, by omega⟩ ⟨_, by omega⟩⟩ ⟨_, nm16_lt ⟨8, by omega⟩ ⟨_, nm16_lt ⟨_, by omega⟩ ⟨_, by omega⟩⟩⟩
  have hc0_b : (nm16 (b % 16) (c % 16) ^^^ nm16 8 (nm16 (b / 16) (c / 16))) < 16 :=
    xor_lt_16 ⟨_, nm16_lt ⟨_, by omega⟩ ⟨_, by omega⟩⟩ ⟨_, nm16_lt ⟨8, by omega⟩ ⟨_, nm16_lt ⟨_, by omega⟩ ⟨_, by omega⟩⟩⟩
  apply hd
  · rw [div16_mul16_xor _ _ hc0_ab]
    have hR := xor_div16
      (16 * (nm16 (a / 16) (c % 16) ^^^ nm16 (a % 16) (c / 16) ^^^ nm16 (a / 16) (c / 16)) ^^^
        (nm16 (a % 16) (c % 16) ^^^ nm16 8 (nm16 (a / 16) (c / 16))))
      (16 * (nm16 (b / 16) (c % 16) ^^^ nm16 (b % 16) (c / 16) ^^^ nm16 (b / 16) (c / 16)) ^^^
        (nm16 (b % 16) (c % 16) ^^^ nm16 8 (nm16 (b / 16) (c / 16))))
    rw [hR, div16_mul16_xor _ _ hc0_a, div16_mul16_xor _ _ hc0_b, xor_div16, xor_mod16,
        nm16_distrib_left ⟨a / 16, by omega⟩ ⟨b / 16, by omega⟩ ⟨c % 16, by omega⟩,
        nm16_distrib_left ⟨a % 16, by omega⟩ ⟨b % 16, by omega⟩ ⟨c / 16, by omega⟩,
        nm16_distrib_left ⟨a / 16, by omega⟩ ⟨b / 16, by omega⟩ ⟨c / 16, by omega⟩]
    simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
  · rw [mod16_mul16_xor _ _ hc0_ab]
    have hR := xor_mod16
      (16 * (nm16 (a / 16) (c % 16) ^^^ nm16 (a % 16) (c / 16) ^^^ nm16 (a / 16) (c / 16)) ^^^
        (nm16 (a % 16) (c % 16) ^^^ nm16 8 (nm16 (a / 16) (c / 16))))
      (16 * (nm16 (b / 16) (c % 16) ^^^ nm16 (b % 16) (c / 16) ^^^ nm16 (b / 16) (c / 16)) ^^^
        (nm16 (b % 16) (c % 16) ^^^ nm16 8 (nm16 (b / 16) (c / 16))))
    rw [hR, mod16_mul16_xor _ _ hc0_a, mod16_mul16_xor _ _ hc0_b, xor_div16, xor_mod16,
        nm16_distrib_left ⟨a % 16, by omega⟩ ⟨b % 16, by omega⟩ ⟨c % 16, by omega⟩,
        nm16_distrib_left ⟨a / 16, by omega⟩ ⟨b / 16, by omega⟩ ⟨c / 16, by omega⟩]
    have h8 : nm16 8 (nm16 (a / 16) (c / 16) ^^^ nm16 (b / 16) (c / 16)) =
        nm16 8 (nm16 (a / 16) (c / 16)) ^^^ nm16 8 (nm16 (b / 16) (c / 16)) := by
      have xlt := nm16_lt ⟨a / 16, by omega⟩ ⟨c / 16, by omega⟩
      have ylt := nm16_lt ⟨b / 16, by omega⟩ ⟨c / 16, by omega⟩
      have xylt := xor_lt_16 ⟨_, xlt⟩ ⟨_, ylt⟩
      rw [nm16_comm ⟨8, by omega⟩ ⟨_, xylt⟩, nm16_distrib_left ⟨_, xlt⟩ ⟨_, ylt⟩ ⟨8, by omega⟩,
        nm16_comm ⟨_, xlt⟩ ⟨8, by omega⟩, nm16_comm ⟨_, ylt⟩ ⟨8, by omega⟩]
    rw [h8]
    simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]

private lemma nm256_comm {a b : ℕ} (ha : a < 256) (hb : b < 256) : nm256 a b = nm256 b a := by
  unfold nm256; dsimp only
  rw [nm16_comm ⟨a / 16, by omega⟩ ⟨b % 16, by omega⟩,
      nm16_comm ⟨a % 16, by omega⟩ ⟨b / 16, by omega⟩,
      nm16_comm ⟨a / 16, by omega⟩ ⟨b / 16, by omega⟩,
      nm16_comm ⟨a % 16, by omega⟩ ⟨b % 16, by omega⟩]
  simp [Nat.xor_comm]

private lemma nm256_distrib_right {a b c : ℕ} (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    nm256 a (b ^^^ c) = nm256 a b ^^^ nm256 a c := by
  rw [nm256_comm ha (xor_lt_256 hb hc), nm256_distrib_left hb hc ha, nm256_comm hb ha, nm256_comm hc ha]

private lemma nm256_16_xor_eq {a d : ℕ} (ha : a < 16) (hd : d < 256) :
    nm256 (16 ^^^ a) d =
      16 * (d % 16 ^^^ nm16 a (d / 16) ^^^ d / 16) +
        (nm16 a (d % 16) ^^^ nm16 8 (d / 16)) := by
  unfold nm256; dsimp only
  have h16a : 16 ^^^ a = 16 * 1 + a := by
    have := mul16_xor_add 1 a ha; simpa using this
  have hdiv : (16 ^^^ a) / 16 = 1 := by omega
  have hmod : (16 ^^^ a) % 16 = a := by omega
  rw [hdiv, hmod, nm16_one_left ⟨d % 16, by omega⟩, nm16_one_left ⟨d / 16, by omega⟩]

private lemma nm256_16_eq {r : ℕ} (hr : r < 256) :
    nm256 16 r = 16 * (r / 16 ^^^ r % 16) + nm16 8 (r / 16) := by
  have h := nm256_16_xor_eq (a := 0) (by omega) hr
  simp only [Nat.xor_zero] at h
  have hz : ∀ x : Fin 16, nm16 0 x.1 = 0 := by decide
  rw [h, hz ⟨r / 16, by omega⟩, hz ⟨r % 16, by omega⟩]
  simp [Nat.xor_comm]

private lemma nm256_16_no_zero_div_fast {a d : ℕ} (ha : a < 16) (hd : d < 256)
    (h0 : nm256 (16 ^^^ a) d = 0) : d = 0 := by
  rw [nm256_16_xor_eq ha hd] at h0
  have hd1 : d / 16 < 16 := by omega
  have hd0 : d % 16 < 16 := by omega
  have hc1 : d % 16 ^^^ nm16 a (d / 16) ^^^ d / 16 = 0 := by omega
  have hc0 : nm16 a (d % 16) ^^^ nm16 8 (d / 16) = 0 := by omega
  have ha1 : (a ^^^ 1) < 16 := xor_lt_16 ⟨a, ha⟩ ⟨1, by omega⟩
  have hd0_eq : d % 16 = nm16 (a ^^^ 1) (d / 16) := by
    have hc1' : d % 16 ^^^ (nm16 a (d / 16) ^^^ d / 16) = 0 := by rw [← Nat.xor_assoc]; exact hc1
    have h1 := xor_eq_zero_imp hc1'
    rw [h1, nm16_distrib_left ⟨a, ha⟩ ⟨1, by omega⟩ ⟨d / 16, hd1⟩, nm16_one_left ⟨d / 16, hd1⟩]
  rw [hd0_eq, ← nm16_assoc ⟨a, ha⟩ ⟨a ^^^ 1, ha1⟩ ⟨d / 16, hd1⟩,
      ← nm16_distrib_left ⟨nm16 a (a ^^^ 1), nm16_lt ⟨a, ha⟩ ⟨a ^^^ 1, ha1⟩⟩ ⟨8, by omega⟩ ⟨d / 16, hd1⟩] at hc0
  have hnorm_lt : (nm16 a (a ^^^ 1) ^^^ 8) < 16 := xor_lt_16 ⟨_, nm16_lt ⟨a, ha⟩ ⟨a ^^^ 1, ha1⟩⟩ ⟨8, by omega⟩
  have hzero := nm16_no_zero_div ⟨_, hnorm_lt⟩ ⟨d / 16, hd1⟩ hc0
  have hne := nm16_norm_ne_zero ⟨a, ha⟩
  dsimp only at hzero hne
  have hd1_zero : d / 16 = 0 := by tauto
  rw [hd1_zero, nm16_zero_right ⟨a ^^^ 1, ha1⟩] at hd0_eq
  omega

private lemma nm256_16_surj {a v : ℕ} (ha : a < 16) (hv : v < 256) :
    ∃ r < 256, nm256 (16 ^^^ a) r = v := by
  have hv1 : v / 16 < 16 := by omega
  have hv0 : v % 16 < 16 := by omega
  have ha1 : (a ^^^ 1) < 16 := xor_lt_16 ⟨a, ha⟩ ⟨1, by omega⟩
  have hnorm_lt : (nm16 a (a ^^^ 1) ^^^ 8) < 16 :=
    xor_lt_16 ⟨_, nm16_lt ⟨a, ha⟩ ⟨a ^^^ 1, ha1⟩⟩ ⟨8, by omega⟩
  have hrhs_lt : (v % 16 ^^^ nm16 a (v / 16)) < 16 :=
    xor_lt_16 ⟨_, hv0⟩ ⟨_, nm16_lt ⟨a, ha⟩ ⟨_, hv1⟩⟩
  rcases nm16_surj ⟨_, hnorm_lt⟩ (nm16_norm_ne_zero ⟨a, ha⟩) ⟨_, hrhs_lt⟩ with ⟨r1, hr1eq⟩
  dsimp only at hr1eq
  let r0 := v / 16 ^^^ nm16 (a ^^^ 1) r1.1
  have hr0_lt : r0 < 16 := xor_lt_16 ⟨_, hv1⟩ ⟨_, nm16_lt ⟨a ^^^ 1, ha1⟩ r1⟩
  let r := 16 * r1.1 + r0
  have hr256 : r < 256 := by omega
  refine ⟨r, hr256, ?_⟩
  rw [nm256_16_xor_eq ha hr256]
  have hrd : r / 16 = r1.1 := by omega
  have hrm : r % 16 = r0 := by omega
  rw [hrd, hrm]
  have hc1 : r0 ^^^ nm16 a r1.1 ^^^ r1.1 = v / 16 := by
    dsimp only [r0]
    rw [nm16_distrib_left ⟨a, ha⟩ ⟨1, by omega⟩ r1, nm16_one_left r1]
    simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
  have hc0 : nm16 a r0 ^^^ nm16 8 r1.1 = v % 16 := by
    dsimp only [r0]
    have hdist : nm16 a (v / 16 ^^^ nm16 (a ^^^ 1) r1.1) =
        nm16 a (v / 16) ^^^ nm16 a (nm16 (a ^^^ 1) r1.1) := by
      have ylt := nm16_lt ⟨a ^^^ 1, ha1⟩ r1
      have xylt := xor_lt_16 ⟨_, hv1⟩ ⟨_, ylt⟩
      rw [nm16_comm ⟨a, ha⟩ ⟨_, xylt⟩, nm16_distrib_left ⟨_, hv1⟩ ⟨_, ylt⟩ ⟨a, ha⟩,
          nm16_comm ⟨_, hv1⟩ ⟨a, ha⟩, nm16_comm ⟨_, ylt⟩ ⟨a, ha⟩]
    rw [hdist, ← nm16_assoc ⟨a, ha⟩ ⟨a ^^^ 1, ha1⟩ r1, Nat.xor_assoc,
        ← nm16_distrib_left ⟨_, nm16_lt ⟨a, ha⟩ ⟨a ^^^ 1, ha1⟩⟩ ⟨8, by omega⟩ r1, hr1eq]
    simp [Nat.xor_comm, Nat.xor_left_comm]
  rw [hc1, hc0]; omega

private lemma nimMul_16_eq_nm256 : ∀ r : ℕ, r < 256 → nimMul 16 r = nm256 16 r := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr
    apply nimMul_eq_of_mex
    · intro a' ha' r' hr' heq
      rw [ih r' hr' (by omega), ← nm256_eq_nimMul_lt16 ha' hr, ← nm256_eq_nimMul_lt16 ha' (by omega)] at heq
      have hrr : (r ^^^ r') < 256 := xor_lt_256 hr (by omega)
      have hzero : nm256 (16 ^^^ a') (r ^^^ r') = 0 := by
        rw [nm256_distrib_left (by omega) (by omega) hrr,
            nm256_distrib_right (by omega) hr (by omega),
            nm256_distrib_right (by omega) hr (by omega), heq]
        simp [Nat.xor_comm, Nat.xor_left_comm]
      have hrr0 := nm256_16_no_zero_div_fast ha' hrr hzero
      have := xor_eq_zero_imp hrr0; omega
    · intro m hm
      have hm256 : m < 256 := lt_trans hm (nm256_lt (by omega) hr)
      have hr1 : r / 16 < 16 := by omega
      have hr0 : r % 16 < 16 := by omega
      have hm1 : m / 16 < 16 := by omega
      have hm0 : m % 16 < 16 := by omega
      have hnm16_r : nm256 16 r = 16 * (r / 16 ^^^ r % 16) + nm16 8 (r / 16) := nm256_16_eq hr
      have hlow_r : nm16 8 (r / 16) < 16 := nm16_lt ⟨8, by omega⟩ ⟨r / 16, hr1⟩
      -- Helper: to finish once we have a' < 16 and r' < r with nm256 (16 ^^^ a') (r ^^^ r') = nm256 16 r ^^^ m
      have finish : ∀ a' r' : ℕ, a' < 16 → r' < r →
          nm256 (16 ^^^ a') (r ^^^ r') = nm256 16 r ^^^ m →
          ∃ a' < 16, ∃ r' < r, m = nimMul a' r ^^^ nimMul 16 r' ^^^ nimMul a' r' := by
        intro a' r' ha' hr' hprod
        refine ⟨a', ha', r', hr', ?_⟩
        rw [ih r' hr' (by omega), ← nm256_eq_nimMul_lt16 ha' hr, ← nm256_eq_nimMul_lt16 ha' (by omega)]
        have hr'256 : r' < 256 := by omega
        have hprod' : (nm256 16 r ^^^ nm256 16 r') ^^^ (nm256 a' r ^^^ nm256 a' r') = nm256 16 r ^^^ m := by
          rw [← hprod, nm256_distrib_left (by omega) (by omega) (xor_lt_256 hr hr'256),
              nm256_distrib_right (by omega) hr hr'256,
              nm256_distrib_right (by omega) hr hr'256]
        have hcancel := congr_arg (nm256 16 r ^^^ ·) hprod'
        have hlhs : nm256 16 r ^^^ ((nm256 16 r ^^^ nm256 16 r') ^^^ (nm256 a' r ^^^ nm256 a' r')) =
            nm256 a' r ^^^ nm256 16 r' ^^^ nm256 a' r' := by
          simp [Nat.xor_assoc, Nat.xor_comm, Nat.xor_left_comm]
        have hrhs : nm256 16 r ^^^ (nm256 16 r ^^^ m) = m := by
          simp [Nat.xor_comm]
        rw [hlhs, hrhs] at hcancel
        exact hcancel.symm
      have hd_eq : nm256 16 r ^^^ m =
          16 * ((r / 16 ^^^ r % 16) ^^^ m / 16) + (nm16 8 (r / 16) ^^^ m % 16) := by
        have hm_split : m = 16 * (m / 16) + m % 16 := by omega
        have h1 := mul16_xor_add (r / 16 ^^^ r % 16) (nm16 8 (r / 16)) hlow_r
        have h2 := mul16_xor_add (m / 16) (m % 16) hm0
        have h3 := mul16_xor_add ((r / 16 ^^^ r % 16) ^^^ m / 16) (nm16 8 (r / 16) ^^^ m % 16)
          (xor_lt_16 ⟨_, hlow_r⟩ ⟨_, hm0⟩)
        have hL : nm256 16 r ^^^ m =
            (16 * (r / 16 ^^^ r % 16) ^^^ nm16 8 (r / 16)) ^^^ (16 * (m / 16) ^^^ m % 16) := by
          rw [hnm16_r, ← h1, h2, ← hm_split]
        rw [hL, ← h3]
        have : ∀ x y : ℕ, x / 16 = y / 16 → x % 16 = y % 16 → x = y := fun x y a b => by omega
        apply this
        · simp only [xor_div16, div16_mul16_xor _ _ hlow_r, div16_mul16_xor _ _ hm0,
            div16_mul16_xor _ _ (xor_lt_16 ⟨_, hlow_r⟩ ⟨_, hm0⟩)]
        · simp only [xor_mod16, mod16_mul16_xor _ _ hlow_r, mod16_mul16_xor _ _ hm0,
            mod16_mul16_xor _ _ (xor_lt_16 ⟨_, hlow_r⟩ ⟨_, hm0⟩)]
      by_cases hcase : m / 16 < (r / 16 ^^^ r % 16)
      · rcases xor_lt_split16 ⟨r / 16, hr1⟩ ⟨r % 16, hr0⟩ ⟨m / 16, hm1⟩ hcase with h1a | h1b
        · -- Subcase 1a: r' = 16 * (r / 16) + (r / 16 ^^^ m / 16) < r
          dsimp only at h1a
          let r' := 16 * (r / 16) + (r / 16 ^^^ m / 16)
          have hr' : r' < r := by omega
          have hr'lt : (r / 16 ^^^ m / 16) < 16 := xor_lt_16 ⟨_, hr1⟩ ⟨_, hm1⟩
          have hd1_zero : (r ^^^ r') / 16 = 0 := by
            rw [xor_div16]; have : r' / 16 = r / 16 := by omega
            rw [this, Nat.xor_self]
          have hd0_val : (r ^^^ r') % 16 = (r / 16 ^^^ r % 16) ^^^ m / 16 := by
            rw [xor_mod16]; have : r' % 16 = r / 16 ^^^ m / 16 := by omega
            rw [this]; simp [Nat.xor_comm, Nat.xor_left_comm]
          have hd0_ne : (r ^^^ r') % 16 ≠ 0 := by
            intro h0; rw [hd0_val] at h0; have := xor_eq_zero_imp h0; omega
          have hd0_lt : (r ^^^ r') % 16 < 16 := Nat.mod_lt _ (by omega)
          rcases nm16_surj ⟨(r ^^^ r') % 16, hd0_lt⟩ hd0_ne
            ⟨nm16 8 (r / 16) ^^^ m % 16, xor_lt_16 ⟨_, hlow_r⟩ ⟨_, hm0⟩⟩ with ⟨a', ha'eq⟩
          dsimp only at ha'eq
          apply finish a'.1 r' a'.2 hr'
          rw [nm256_16_xor_eq a'.2 (xor_lt_256 hr (by omega)), hd_eq, hd1_zero,
              nm16_zero_right a', nm16_zero_right ⟨8, by omega⟩,
              nm16_comm a' ⟨_, hd0_lt⟩, ha'eq, hd0_val]
          simp
        · -- Subcase 1b: r1' = r % 16 ^^^ m / 16 < r / 16
          dsimp only at h1b
          let r1' := r % 16 ^^^ m / 16
          let d1 := (r / 16 ^^^ r % 16) ^^^ m / 16
          have hd1_lt : d1 < 16 := xor_lt_16 ⟨_, xor_lt_16 ⟨_, hr1⟩ ⟨_, hr0⟩⟩ ⟨_, hm1⟩
          have hd1_ne : d1 ≠ 0 := by
            intro h0; have := xor_eq_zero_imp h0; omega
          have hv_lt : ((nm16 8 (r / 16) ^^^ m % 16) ^^^ nm16 8 d1) < 16 :=
            xor_lt_16 ⟨_, xor_lt_16 ⟨_, hlow_r⟩ ⟨_, hm0⟩⟩ ⟨_, nm16_lt ⟨8, by omega⟩ ⟨d1, hd1_lt⟩⟩
          rcases nm16_sq_surj ⟨d1, hd1_lt⟩ hd1_ne ⟨_, hv_lt⟩ with ⟨a', ha'eq⟩
          dsimp only at ha'eq
          let d0 := nm16 a'.1 d1
          have hd0_lt : d0 < 16 := nm16_lt a' ⟨d1, hd1_lt⟩
          let r0' := r % 16 ^^^ d0
          have hr0'_lt : r0' < 16 := xor_lt_16 ⟨_, hr0⟩ ⟨d0, hd0_lt⟩
          let r' := 16 * r1' + r0'
          have hr' : r' < r := by omega
          apply finish a'.1 r' a'.2 hr'
          have hdiv : (r ^^^ r') / 16 = d1 := by
            rw [xor_div16]; have : r' / 16 = r1' := by omega
            rw [this]; dsimp only [r1', d1]; simp [Nat.xor_assoc]
          have hmod : (r ^^^ r') % 16 = d0 := by
            rw [xor_mod16]; have : r' % 16 = r0' := by omega
            rw [this]; dsimp only [r0']; simp [Nat.xor_comm, Nat.xor_left_comm]
          rw [nm256_16_xor_eq a'.2 (xor_lt_256 hr (by omega)), hd_eq, hdiv, hmod]
          have hc1 : d0 ^^^ nm16 a'.1 d1 ^^^ d1 = d1 := by dsimp only [d0]; simp
          have hc0 : nm16 a'.1 d0 ^^^ nm16 8 d1 = nm16 8 (r / 16) ^^^ m % 16 := by
            dsimp only [d0]
            rw [← nm16_assoc a' a' ⟨d1, hd1_lt⟩, ha'eq]
            simp [Nat.xor_comm, Nat.xor_left_comm]
          rw [hc1, hc0]
      · -- Case 2: m / 16 = r / 16 ^^^ r % 16, m % 16 < nm16 8 (r / 16)
        have hm1_eq : m / 16 = r / 16 ^^^ r % 16 := by omega
        have hm0_lt : m % 16 < nm16 8 (r / 16) := by omega
        rcases nm16_case2_wit ⟨r / 16, hr1⟩ ⟨m % 16, hm0⟩ hm0_lt with ⟨a', r1', hr1'lt, hnorm_eq⟩
        dsimp only at hr1'lt hnorm_eq
        let d1 := r / 16 ^^^ r1'.1
        have hd1_lt : d1 < 16 := xor_lt_16 ⟨_, hr1⟩ r1'
        have ha1_lt : (a'.1 ^^^ 1) < 16 := xor_lt_16 a' ⟨1, by omega⟩
        let d0 := nm16 (a'.1 ^^^ 1) d1
        have hd0_lt : d0 < 16 := nm16_lt ⟨_, ha1_lt⟩ ⟨d1, hd1_lt⟩
        let r0' := r % 16 ^^^ d0
        have hr0'_lt : r0' < 16 := xor_lt_16 ⟨_, hr0⟩ ⟨d0, hd0_lt⟩
        let r' := 16 * r1'.1 + r0'
        have hr' : r' < r := by omega
        apply finish a'.1 r' a'.2 hr'
        have hdiv : (r ^^^ r') / 16 = d1 := by
          rw [xor_div16]; have : r' / 16 = r1'.1 := by omega
          rw [this]
        have hmod : (r ^^^ r') % 16 = d0 := by
          rw [xor_mod16]; have : r' % 16 = r0' := by omega
          rw [this]; dsimp only [r0']; simp [Nat.xor_comm, Nat.xor_left_comm]
        rw [nm256_16_xor_eq a'.2 (xor_lt_256 hr (by omega)), hd_eq, hdiv, hmod, hm1_eq, Nat.xor_self]
        have hc1 : d0 ^^^ nm16 a'.1 d1 ^^^ d1 = 0 := by
          dsimp only [d0]
          rw [nm16_distrib_left a' ⟨1, by omega⟩ ⟨d1, hd1_lt⟩, nm16_one_left ⟨d1, hd1_lt⟩]
          simp [Nat.xor_comm, Nat.xor_left_comm]
        have hc0 : nm16 a'.1 d0 ^^^ nm16 8 d1 = nm16 8 (r / 16) ^^^ m % 16 := by
          dsimp only [d0]
          rw [← nm16_assoc a' ⟨_, ha1_lt⟩ ⟨d1, hd1_lt⟩,
              ← nm16_distrib_left ⟨_, nm16_lt a' ⟨_, ha1_lt⟩⟩ ⟨8, by omega⟩ ⟨d1, hd1_lt⟩]
          exact hnorm_eq
        rw [hc1, hc0]

-- Part 4: Conway's F = 256 scaling theorem for a = 16
private lemma nimMul_scale256_16 : ∀ b : ℕ,
    nimMul 16 b = 256 * nimMul 16 (b / 256) ^^^ nimMul 16 (b % 256) := by
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    have hr256 : b % 256 < 256 := Nat.mod_lt b (by omega)
    have hnr256 : nimMul 16 (b % 256) < 256 := by
      rw [nimMul_16_eq_nm256 (b % 256) hr256]; exact nm256_lt (by omega) hr256
    apply nimMul_eq_of_mex
    · intro a' ha' b' hb' heq
      rw [nimMul_scale256_lt16 ha' b, ih b' hb', nimMul_scale256_lt16 ha' b'] at heq
      have hdiv := congr_arg (· / 256) heq
      have hmod := congr_arg (· % 256) heq
      have hr'256 : b' % 256 < 256 := Nat.mod_lt b' (by omega)
      have hna'r : nimMul a' (b % 256) < 256 := nimMul_lt256_of_lt16 ha' hr256
      have hnar' : nimMul 16 (b' % 256) < 256 := by rw [nimMul_16_eq_nm256 _ hr'256]; exact nm256_lt (by omega) hr'256
      have hna'r' : nimMul a' (b' % 256) < 256 := nimMul_lt256_of_lt16 ha' hr'256
      rw [div256_mul256_xor _ _ hnr256, xor_div256, xor_div256,
          div256_mul256_xor _ _ hna'r, div256_mul256_xor _ _ hnar', div256_mul256_xor _ _ hna'r'] at hdiv
      rw [mod256_mul256_xor _ _ hnr256, xor_mod256, xor_mod256,
          mod256_mul256_xor _ _ hna'r, mod256_mul256_xor _ _ hnar', mod256_mul256_xor _ _ hna'r'] at hmod
      by_cases hq : b' / 256 < b / 256
      · exact nimMul_mem_set 16 (b / 256) a' ha' (b' / 256) hq hdiv
      · have hqeq : b' / 256 = b / 256 := by omega
        have hrlt : b' % 256 < b % 256 := by omega
        exact nimMul_mem_set 16 (b % 256) a' ha' (b' % 256) hrlt hmod
    · intro m hm
      rw [mul256_xor_add _ _ hnr256] at hm
      have hdiv_mod : ∀ x y : ℕ, x / 256 = y / 256 → x % 256 = y % 256 → x = y := fun x y h1 h2 => by omega
      have hv256 : m % 256 < 256 := Nat.mod_lt m (by omega)
      by_cases hu : m / 256 < nimMul 16 (b / 256)
      · rcases nimMul_lt_witness hu with ⟨a', ha', q', hq', hu_eq⟩
        have hna'r : nimMul a' (b % 256) < 256 := nimMul_lt256_of_lt16 ha' hr256
        let target := m % 256 ^^^ nimMul a' (b % 256)
        have htarget256 : target < 256 := xor_lt_256 hv256 hna'r
        rcases nm256_16_surj ha' htarget256 with ⟨r', hr'256, hinv⟩
        let b' := 256 * q' + r'
        have hb' : b' < b := by omega
        refine ⟨a', ha', b', hb', ?_⟩
        rw [nimMul_scale256_lt16 ha' b, ih b' hb', nimMul_scale256_lt16 ha' b']
        have hb'd : b' / 256 = q' := by omega
        have hb'm : b' % 256 = r' := by omega
        rw [hb'd, hb'm]
        have hlow : nimMul a' (b % 256) ^^^ nimMul 16 r' ^^^ nimMul a' r' = m % 256 := by
          rw [nimMul_16_eq_nm256 r' hr'256, ← nm256_eq_nimMul_lt16 ha' hr'256]
          have hdist := nm256_distrib_left (by omega : 16 < 256) (by omega : a' < 256) hr'256
          rw [Nat.xor_assoc, ← hdist, hinv]
          dsimp only [target]; simp
        have hnar' : nimMul 16 r' < 256 := by rw [nimMul_16_eq_nm256 r' hr'256]; exact nm256_lt (by omega) hr'256
        have hna'r' : nimMul a' r' < 256 := nimMul_lt256_of_lt16 ha' hr'256
        apply hdiv_mod
        · rw [xor_div256, xor_div256, div256_mul256_xor _ _ hna'r, div256_mul256_xor _ _ hnar', div256_mul256_xor _ _ hna'r']
          exact hu_eq
        · rw [xor_mod256, xor_mod256, mod256_mul256_xor _ _ hna'r, mod256_mul256_xor _ _ hnar', mod256_mul256_xor _ _ hna'r']
          exact hlow.symm
      · have hu_eq : m / 256 = nimMul 16 (b / 256) := by omega
        have hv_lt : m % 256 < nimMul 16 (b % 256) := by omega
        rcases nimMul_lt_witness hv_lt with ⟨a', ha', r', hr', hv_eq⟩
        have hr'256 : r' < 256 := by omega
        let b' := 256 * (b / 256) + r'
        have hb' : b' < b := by omega
        refine ⟨a', ha', b', hb', ?_⟩
        rw [nimMul_scale256_lt16 ha' b, ih b' hb', nimMul_scale256_lt16 ha' b']
        have hb'd : b' / 256 = b / 256 := by omega
        have hb'm : b' % 256 = r' := by omega
        rw [hb'd, hb'm]
        have hna'r : nimMul a' (b % 256) < 256 := nimMul_lt256_of_lt16 ha' hr256
        have hnar' : nimMul 16 r' < 256 := by rw [nimMul_16_eq_nm256 r' hr'256]; exact nm256_lt (by omega) hr'256
        have hna'r' : nimMul a' r' < 256 := nimMul_lt256_of_lt16 ha' hr'256
        apply hdiv_mod
        · rw [xor_div256, xor_div256, div256_mul256_xor _ _ hna'r, div256_mul256_xor _ _ hnar', div256_mul256_xor _ _ hna'r']
          rw [hu_eq]; simp
        · rw [xor_mod256, xor_mod256, mod256_mul256_xor _ _ hna'r, mod256_mul256_xor _ _ hnar', mod256_mul256_xor _ _ hna'r']
          exact hv_eq

-- Part 5: Main theorem for A335161
theorem main :
    (∀ n : ℕ, 7 < n → a n = 256 * a (n - 8)) ∧
    ((1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2) * (1 + 16 * X ^ 4) *
      PowerSeries.mk (fun n => (a n : ℤ)) =
      (16 + 32 * X + 64 * X ^ 2 + 128 * X ^ 3 +
        24 * X ^ 4 + 44 * X ^ 5 + 75 * X ^ 6 + 141 * X ^ 7 : PowerSeries ℤ)) := by
  have hrec : ∀ n : ℕ, 7 < n → a n = 256 * a (n - 8) := by
    intro n hn
    unfold a
    have hpow : 2 ^ n = 256 * 2 ^ (n - 8) := by
      have : n = 8 + (n - 8) := by omega
      conv_lhs => rw [this]
      rw [pow_add]; norm_num
    have h16 : (2 ^ 4 : ℕ) = 16 := rfl
    rw [h16, nimMul_scale256_16 (2 ^ n), hpow]
    have hd : 256 * 2 ^ (n - 8) / 256 = 2 ^ (n - 8) := by omega
    have hm : 256 * 2 ^ (n - 8) % 256 = 0 := by omega
    rw [hd, hm, nimMul_zero_right, Nat.xor_zero]
  refine ⟨hrec, ?_⟩
  have ha0 : a 0 = 16 := by unfold a; rw [show (2 ^ 4 : ℕ) = 16 from rfl, nimMul_16_eq_nm256 _ (by norm_num)]; exact nm256_base.1
  have ha1 : a 1 = 32 := by unfold a; rw [show (2 ^ 4 : ℕ) = 16 from rfl, nimMul_16_eq_nm256 _ (by norm_num)]; exact nm256_base.2.1
  have ha2 : a 2 = 64 := by unfold a; rw [show (2 ^ 4 : ℕ) = 16 from rfl, nimMul_16_eq_nm256 _ (by norm_num)]; exact nm256_base.2.2.1
  have ha3 : a 3 = 128 := by unfold a; rw [show (2 ^ 4 : ℕ) = 16 from rfl, nimMul_16_eq_nm256 _ (by norm_num)]; exact nm256_base.2.2.2.1
  have ha4 : a 4 = 24 := by unfold a; rw [show (2 ^ 4 : ℕ) = 16 from rfl, nimMul_16_eq_nm256 _ (by norm_num)]; exact nm256_base.2.2.2.2.1
  have ha5 : a 5 = 44 := by unfold a; rw [show (2 ^ 4 : ℕ) = 16 from rfl, nimMul_16_eq_nm256 _ (by norm_num)]; exact nm256_base.2.2.2.2.2.1
  have ha6 : a 6 = 75 := by unfold a; rw [show (2 ^ 4 : ℕ) = 16 from rfl, nimMul_16_eq_nm256 _ (by norm_num)]; exact nm256_base.2.2.2.2.2.2.1
  have ha7 : a 7 = 141 := by unfold a; rw [show (2 ^ 4 : ℕ) = 16 from rfl, nimMul_16_eq_nm256 _ (by norm_num)]; exact nm256_base.2.2.2.2.2.2.2
  let f : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))
  have hlhs : (1 - 2 * X) * (1 + 2 * X) * (1 + 4 * X ^ 2) * (1 + 16 * X ^ 4) * f =
      f - PowerSeries.C 256 * (X ^ 8 * f) := by
    simp only [map_ofNat]; ring
  have hrhs : (16 + 32 * X + 64 * X ^ 2 + 128 * X ^ 3 +
        24 * X ^ 4 + 44 * X ^ 5 + 75 * X ^ 6 + 141 * X ^ 7 : PowerSeries ℤ) =
      PowerSeries.C 16 + PowerSeries.C 32 * X ^ 1 + PowerSeries.C 64 * X ^ 2 +
        PowerSeries.C 128 * X ^ 3 + PowerSeries.C 24 * X ^ 4 + PowerSeries.C 44 * X ^ 5 +
        PowerSeries.C 75 * X ^ 6 + PowerSeries.C 141 * X ^ 7 := by
    simp only [map_ofNat]; ring
  rw [hlhs, hrhs]
  ext k
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_C, PowerSeries.coeff_X_pow, f, PowerSeries.coeff_mk]
  match k with
  | 0 => simp [ha0]
  | 1 => simp [ha1]
  | 2 => simp [ha2]
  | 3 => simp [ha3]
  | 4 => simp [ha4]
  | 5 => simp [ha5]
  | 6 => simp [ha6]
  | 7 => simp [ha7]
  | m + 8 =>
    have hr := hrec (m + 8) (by omega)
    simp only [show m + 8 ≠ 0 by omega, show m + 8 ≠ 1 by omega, show m + 8 ≠ 2 by omega,
      show m + 8 ≠ 3 by omega, show m + 8 ≠ 4 by omega, show m + 8 ≠ 5 by omega,
      show m + 8 ≠ 6 by omega, show m + 8 ≠ 7 by omega, show 8 ≤ m + 8 by omega,
      ↓reduceIte, mul_zero, add_zero]
    have hsub : m + 8 - 8 = m := by omega
    rw [hsub] at hr ⊢
    exact_mod_cast (by omega : (a (m + 8) : ℤ) - 256 * (a m : ℤ) = 0)

end
end ProofA335161

theorem OMA.solution : type_of% @OMA.S_oeis_a335161.main :=
  ProofA335161.main
