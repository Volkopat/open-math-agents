import OMAStatements.S_oeis_a335159
import Mathlib

private def mul4 (a b : ℕ) : ℕ :=
  match a, b with
  | 1, b => b
  | a, 1 => a
  | 2, 2 => 3
  | 2, 3 => 1
  | 3, 2 => 1
  | 3, 3 => 2
  | _, _ => 0

private def mul16 (a b : ℕ) : ℕ :=
  let a1 := a / 4
  let a0 := a % 4
  let b1 := b / 4
  let b0 := b % 4
  let p11 := mul4 a1 b1
  let hi := p11 ^^^ mul4 a1 b0 ^^^ mul4 a0 b1
  let lo := mul4 a0 b0 ^^^ mul4 2 p11
  4 * hi + lo

private lemma mul16_lt (x y : Fin 16) : mul16 x.1 y.1 < 16 := by
  revert x y
  decide

private lemma mul16_avoid (x y : Fin 16) :
    ∀ x' : Fin 16, x'.1 < x.1 → ∀ y' : Fin 16, y'.1 < y.1 →
      mul16 x.1 y.1 ≠ mul16 x'.1 y.1 ^^^ mul16 x.1 y'.1 ^^^ mul16 x'.1 y'.1 := by
  revert x y
  decide

private lemma mul16_min (x y m : Fin 16) :
    m.1 < mul16 x.1 y.1 →
      ∃ x' : Fin 16, x'.1 < x.1 ∧ ∃ y' : Fin 16, y'.1 < y.1 ∧
        m.1 = mul16 x'.1 y.1 ^^^ mul16 x.1 y'.1 ^^^ mul16 x'.1 y'.1 := by
  revert x y m
  decide

private lemma mul16_xor_left (x y z : Fin 16) :
    mul16 (x.1 ^^^ y.1) z.1 = mul16 x.1 z.1 ^^^ mul16 y.1 z.1 := by
  revert x y z
  decide

private lemma mul16_surj (c R : Fin 16) :
    c.1 ≠ 0 → ∃ r' : Fin 16, mul16 c.1 r'.1 = R.1 := by
  revert c R
  decide

private lemma xor_ne_zero_of_lt (a a' : Fin 16) : a'.1 < a.1 → a.1 ^^^ a'.1 ≠ 0 := by
  revert a a'
  decide

private lemma mul16_comb_surj {a a' r R : ℕ}
    (ha : a < 16) (ha' : a' < a) (hr : r < 16) (hR : R < 16) :
    ∃ r' < 16, mul16 a' r ^^^ mul16 a r' ^^^ mul16 a' r' = R := by
  have ha'16 : a' < 16 := ha'.trans ha
  let fa : Fin 16 := ⟨a, ha⟩
  let fa' : Fin 16 := ⟨a', ha'16⟩
  let fr : Fin 16 := ⟨r, hr⟩
  let fR : Fin 16 := ⟨R, hR⟩
  have hcxor : fa.1 ^^^ fa'.1 < 16 := Nat.xor_lt_two_pow (n := 4) ha ha'16
  let fc : Fin 16 := ⟨fa.1 ^^^ fa'.1, hcxor⟩
  have hcne : fc.1 ≠ 0 := xor_ne_zero_of_lt fa fa' ha'
  have hTlt : fR.1 ^^^ mul16 fa'.1 fr.1 < 16 :=
    Nat.xor_lt_two_pow (n := 4) hR (mul16_lt fa' fr)
  let fT : Fin 16 := ⟨fR.1 ^^^ mul16 fa'.1 fr.1, hTlt⟩
  obtain ⟨fr', hfr'⟩ := mul16_surj fc fT hcne
  refine ⟨fr'.1, fr'.2, ?_⟩
  have hdist := mul16_xor_left fa fa' fr'
  change mul16 fc.1 fr'.1 = fT.1 at hfr'
  change mul16 (fa.1 ^^^ fa'.1) fr'.1 = mul16 fa.1 fr'.1 ^^^ mul16 fa'.1 fr'.1 at hdist
  have hlin : mul16 a fr'.1 ^^^ mul16 a' fr'.1 = R ^^^ mul16 a' r := by
    dsimp [fc, fT] at hfr' hdist
    exact hdist.symm.trans hfr'
  rw [Nat.xor_assoc, hlin]
  change mul16 a' r ^^^ (R ^^^ mul16 a' r) = R
  rw [Nat.xor_comm R (mul16 a' r), ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

private lemma nimMul_eq_mul16_aux :
    ∀ n a b : ℕ, a + b = n → a < 16 → b < 16 →
      OMA.S_oeis_a335159.nimMul a b = mul16 a b := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b hab ha hb
    rw [OMA.S_oeis_a335159.nimMul]
    let S : Set ℕ :=
      {m : ℕ | ∀ a' < a, ∀ b' < b,
        m ≠ OMA.S_oeis_a335159.nimMul a' b ^^^ OMA.S_oeis_a335159.nimMul a b' ^^^
          OMA.S_oeis_a335159.nimMul a' b'}
    have hmem : mul16 a b ∈ S := by
      intro a' ha' b' hb'
      have ha'16 : a' < 16 := ha'.trans ha
      have hb'16 : b' < 16 := hb'.trans hb
      rw [ih (a' + b) (by omega) a' b rfl ha'16 hb,
        ih (a + b') (by omega) a b' rfl ha hb'16,
        ih (a' + b') (by omega) a' b' rfl ha'16 hb'16]
      exact mul16_avoid ⟨a, ha⟩ ⟨b, hb⟩ ⟨a', ha'16⟩ ha' ⟨b', hb'16⟩ hb'
    have hmin : ∀ m < mul16 a b, m ∉ S := by
      intro m hm hms
      have hm16 : m < 16 := hm.trans (mul16_lt ⟨a, ha⟩ ⟨b, hb⟩)
      obtain ⟨a', ha', b', hb', hmeq⟩ := mul16_min ⟨a, ha⟩ ⟨b, hb⟩ ⟨m, hm16⟩ hm
      change a'.1 < a at ha'
      change b'.1 < b at hb'
      have hne := hms a'.1 ha' b'.1 hb'
      rw [ih (a'.1 + b) (by omega) a'.1 b rfl a'.2 hb,
        ih (a + b'.1) (by omega) a b'.1 rfl ha b'.2,
        ih (a'.1 + b'.1) (by omega) a'.1 b'.1 rfl a'.2 b'.2] at hne
      exact hne hmeq
    refine le_antisymm (Nat.sInf_le hmem) ?_
    by_contra hlt
    have hlt' : sInf S < mul16 a b := lt_of_not_ge hlt
    exact hmin (sInf S) hlt' (Nat.sInf_mem ⟨mul16 a b, hmem⟩)

private lemma nimMul_eq_mul16 {a b : ℕ} (ha : a < 16) (hb : b < 16) :
    OMA.S_oeis_a335159.nimMul a b = mul16 a b :=
  nimMul_eq_mul16_aux (a + b) a b rfl ha hb

private lemma testBit_sixteen_mul_add (x y : ℕ) (hy : y < 16) (k : ℕ) :
    (16 * x + y).testBit k = if k < 4 then y.testBit k else x.testBit (k - 4) := by
  simp only [Nat.testBit, Nat.and_comm 1, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  split_ifs with hk
  · have hpow : 16 = 2 * 2 ^ (3 - k) * 2 ^ k := by
      calc
        16 = 2 ^ 4 := by norm_num
        _ = 2 ^ (1 + (3 - k) + k) := by rw [show 1 + (3 - k) + k = 4 by omega]
        _ = 2 ^ 1 * 2 ^ (3 - k) * 2 ^ k := by rw [pow_add, pow_add]
        _ = 2 * 2 ^ (3 - k) * 2 ^ k := by rw [pow_one]
    have hdiv : (16 * x + y) / 2 ^ k = 2 * (2 ^ (3 - k) * x) + y / 2 ^ k := by
      rw [hpow]
      have hre : 2 * 2 ^ (3 - k) * 2 ^ k * x + y =
          2 ^ k * (2 * (2 ^ (3 - k) * x)) + y := by ring
      rw [hre, Nat.mul_add_div (Nat.two_pow_pos k)]
    rw [hdiv, Nat.mul_add_mod]
  · have hpow : 2 ^ k = 16 * 2 ^ (k - 4) := by
      have h1 : 16 * 2 ^ (k - 4) = 2 ^ 4 * 2 ^ (k - 4) := by norm_num
      rw [h1, ← pow_add, show 4 + (k - 4) = k by omega]
    have hdiv1 : (16 * x + y) / 16 = x := by
      rw [Nat.mul_add_div (by decide : 0 < 16), Nat.div_eq_of_lt hy, add_zero]
    rw [hpow, ← Nat.div_div_eq_div_mul, hdiv1]

private lemma xor_split {x₁ x₂ y₁ y₂ : ℕ} (hy₁ : y₁ < 16) (hy₂ : y₂ < 16) :
    (16 * x₁ + y₁) ^^^ (16 * x₂ + y₂) = 16 * (x₁ ^^^ x₂) + (y₁ ^^^ y₂) := by
  apply Nat.eq_of_testBit_eq
  intro k
  have hyxor : y₁ ^^^ y₂ < 16 := Nat.xor_lt_two_pow (n := 4) hy₁ hy₂
  simp only [Nat.testBit_xor, testBit_sixteen_mul_add _ _ hy₁,
    testBit_sixteen_mul_add _ _ hy₂, testBit_sixteen_mul_add _ _ hyxor]
  split_ifs <;> rfl

private lemma nimMul_split_aux :
    ∀ n a b : ℕ, a + b = n → a < 16 →
      OMA.S_oeis_a335159.nimMul a b =
        16 * OMA.S_oeis_a335159.nimMul a (b / 16) + OMA.S_oeis_a335159.nimMul a (b % 16) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b hab ha
    set q := b / 16
    set r := b % 16
    have hr16 : r < 16 := Nat.mod_lt b (by decide)
    have hbq : 16 * q + r = b := Nat.div_add_mod b 16
    set Q₀ := OMA.S_oeis_a335159.nimMul a q
    set R₀ := OMA.S_oeis_a335159.nimMul a r
    have hR₀16 : R₀ < 16 := by
      dsimp [R₀]
      rw [nimMul_eq_mul16 ha hr16]
      exact mul16_lt ⟨a, ha⟩ ⟨r, hr16⟩
    let M := 16 * Q₀ + R₀
    rw [OMA.S_oeis_a335159.nimMul]
    let S : Set ℕ :=
      {m : ℕ | ∀ a' < a, ∀ b' < b,
        m ≠ OMA.S_oeis_a335159.nimMul a' b ^^^ OMA.S_oeis_a335159.nimMul a b' ^^^
          OMA.S_oeis_a335159.nimMul a' b'}
    have hsplit_val : ∀ a' b', a' < a → b' < b →
        OMA.S_oeis_a335159.nimMul a' b ^^^ OMA.S_oeis_a335159.nimMul a b' ^^^
            OMA.S_oeis_a335159.nimMul a' b' =
          16 * (OMA.S_oeis_a335159.nimMul a' q ^^^ OMA.S_oeis_a335159.nimMul a (b' / 16) ^^^
              OMA.S_oeis_a335159.nimMul a' (b' / 16)) +
            (OMA.S_oeis_a335159.nimMul a' r ^^^ OMA.S_oeis_a335159.nimMul a (b' % 16) ^^^
              OMA.S_oeis_a335159.nimMul a' (b' % 16)) := by
      intro a' b' ha' hb'
      have ha'16 : a' < 16 := ha'.trans ha
      have hr'16 : b' % 16 < 16 := Nat.mod_lt b' (by decide)
      rw [ih (a' + b) (by omega) a' b rfl ha'16,
        ih (a + b') (by omega) a b' rfl ha,
        ih (a' + b') (by omega) a' b' rfl ha'16]
      have h1 : OMA.S_oeis_a335159.nimMul a' r < 16 := by
        rw [nimMul_eq_mul16 ha'16 hr16]; exact mul16_lt ⟨a', ha'16⟩ ⟨r, hr16⟩
      have h2 : OMA.S_oeis_a335159.nimMul a (b' % 16) < 16 := by
        rw [nimMul_eq_mul16 ha hr'16]; exact mul16_lt ⟨a, ha⟩ ⟨b' % 16, hr'16⟩
      have h3 : OMA.S_oeis_a335159.nimMul a' (b' % 16) < 16 := by
        rw [nimMul_eq_mul16 ha'16 hr'16]; exact mul16_lt ⟨a', ha'16⟩ ⟨b' % 16, hr'16⟩
      have h12 : OMA.S_oeis_a335159.nimMul a' r ^^^ OMA.S_oeis_a335159.nimMul a (b' % 16) < 16 :=
        Nat.xor_lt_two_pow (n := 4) h1 h2
      rw [xor_split h1 h2, xor_split h12 h3]
    have hmem : M ∈ S := by
      intro a' ha' b' hb'
      rw [hsplit_val a' b' ha' hb']
      have ha'16 : a' < 16 := ha'.trans ha
      have hr'16 : b' % 16 < 16 := Nat.mod_lt b' (by decide)
      have hlo16 : OMA.S_oeis_a335159.nimMul a' r ^^^ OMA.S_oeis_a335159.nimMul a (b' % 16) ^^^
          OMA.S_oeis_a335159.nimMul a' (b' % 16) < 16 := by
        have h1 : OMA.S_oeis_a335159.nimMul a' r < 16 := by
          rw [nimMul_eq_mul16 ha'16 hr16]; exact mul16_lt ⟨a', ha'16⟩ ⟨r, hr16⟩
        have h2 : OMA.S_oeis_a335159.nimMul a (b' % 16) < 16 := by
          rw [nimMul_eq_mul16 ha hr'16]; exact mul16_lt ⟨a, ha⟩ ⟨b' % 16, hr'16⟩
        have h3 : OMA.S_oeis_a335159.nimMul a' (b' % 16) < 16 := by
          rw [nimMul_eq_mul16 ha'16 hr'16]; exact mul16_lt ⟨a', ha'16⟩ ⟨b' % 16, hr'16⟩
        exact Nat.xor_lt_two_pow (n := 4) (Nat.xor_lt_two_pow (n := 4) h1 h2) h3
      have hqle : b' / 16 ≤ q := Nat.div_le_div_right hb'.le
      intro heq
      have heq_div : Q₀ = OMA.S_oeis_a335159.nimMul a' q ^^^ OMA.S_oeis_a335159.nimMul a (b' / 16) ^^^
          OMA.S_oeis_a335159.nimMul a' (b' / 16) := by
        omega
      have heq_mod : R₀ = OMA.S_oeis_a335159.nimMul a' r ^^^ OMA.S_oeis_a335159.nimMul a (b' % 16) ^^^
          OMA.S_oeis_a335159.nimMul a' (b' % 16) := by
        omega
      rcases lt_or_eq_of_le hqle with hqlt | hqeq
      · have hqmem : Q₀ ∈ {m : ℕ | ∀ a'' < a, ∀ q' < q,
            m ≠ OMA.S_oeis_a335159.nimMul a'' q ^^^ OMA.S_oeis_a335159.nimMul a q' ^^^
              OMA.S_oeis_a335159.nimMul a'' q'} := by
          have hne_sInf : ∃ m, m ∈ {m : ℕ | ∀ a'' < a, ∀ q' < q,
              m ≠ OMA.S_oeis_a335159.nimMul a'' q ^^^ OMA.S_oeis_a335159.nimMul a q' ^^^
                OMA.S_oeis_a335159.nimMul a'' q'} := by
            let F := (Finset.range a).product (Finset.range q)
            let g : ℕ × ℕ → ℕ := fun p ↦
              OMA.S_oeis_a335159.nimMul p.1 q ^^^ OMA.S_oeis_a335159.nimMul a p.2 ^^^
                OMA.S_oeis_a335159.nimMul p.1 p.2
            refine ⟨(F.image g).sup id + 1, fun a'' ha'' q' hq' hcol ↦ ?_⟩
            have hle : g (a'', q') ≤ (F.image g).sup id :=
              Finset.le_sup (f := id) (Finset.mem_image_of_mem g
                (Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha'', Finset.mem_range.mpr hq'⟩))
            change (F.image g).sup id + 1 = g (a'', q') at hcol
            omega
          dsimp [Q₀]
          rw [OMA.S_oeis_a335159.nimMul]
          exact Nat.sInf_mem hne_sInf
        exact hqmem a' ha' (b' / 16) hqlt heq_div
      · have hrlt : b' % 16 < r := by
          have hb'eq : 16 * (b' / 16) + b' % 16 = b' := Nat.div_add_mod b' 16
          omega
        have hrmem : R₀ ∈ {m : ℕ | ∀ a'' < a, ∀ r' < r,
            m ≠ OMA.S_oeis_a335159.nimMul a'' r ^^^ OMA.S_oeis_a335159.nimMul a r' ^^^
              OMA.S_oeis_a335159.nimMul a'' r'} := by
          have hne_sInf : ∃ m, m ∈ {m : ℕ | ∀ a'' < a, ∀ r' < r,
              m ≠ OMA.S_oeis_a335159.nimMul a'' r ^^^ OMA.S_oeis_a335159.nimMul a r' ^^^
                OMA.S_oeis_a335159.nimMul a'' r'} := by
            let F := (Finset.range a).product (Finset.range r)
            let g : ℕ × ℕ → ℕ := fun p ↦
              OMA.S_oeis_a335159.nimMul p.1 r ^^^ OMA.S_oeis_a335159.nimMul a p.2 ^^^
                OMA.S_oeis_a335159.nimMul p.1 p.2
            refine ⟨(F.image g).sup id + 1, fun a'' ha'' r' hr' hcol ↦ ?_⟩
            have hle : g (a'', r') ≤ (F.image g).sup id :=
              Finset.le_sup (f := id) (Finset.mem_image_of_mem g
                (Finset.mem_product.mpr ⟨Finset.mem_range.mpr ha'', Finset.mem_range.mpr hr'⟩))
            change (F.image g).sup id + 1 = g (a'', r') at hcol
            omega
          dsimp [R₀]
          rw [OMA.S_oeis_a335159.nimMul]
          exact Nat.sInf_mem hne_sInf
        exact hrmem a' ha' (b' % 16) hrlt heq_mod
    have hmin : ∀ m < M, m ∉ S := by
      intro m hm hms
      set Q := m / 16
      set R := m % 16
      have hR16 : R < 16 := Nat.mod_lt m (by decide)
      have hm_eq : 16 * Q + R = m := Nat.div_add_mod m 16
      have hQle : Q ≤ Q₀ := by
        dsimp [M] at hm
        omega
      rcases lt_or_eq_of_le hQle with hQlt | hQeq
      · have hQnot : Q ∉ {k : ℕ | ∀ a' < a, ∀ q' < q,
            k ≠ OMA.S_oeis_a335159.nimMul a' q ^^^ OMA.S_oeis_a335159.nimMul a q' ^^^
              OMA.S_oeis_a335159.nimMul a' q'} := by
          intro hmemQ
          have hle : Q₀ ≤ Q := by
            dsimp [Q₀]
            rw [OMA.S_oeis_a335159.nimMul]
            exact Nat.sInf_le hmemQ
          omega
        simp only [Set.mem_ofPred_eq, not_forall, not_not] at hQnot
        rcases hQnot with ⟨a', ha', q', hq', hQhit⟩
        obtain ⟨r', hr'16, hRhit⟩ := mul16_comb_surj ha ha' hr16 hR16
        have ha'16 : a' < 16 := ha'.trans ha
        let b' := 16 * q' + r'
        have hb'lt : b' < b := by omega
        have hdiv : b' / 16 = q' := by omega
        have hmod : b' % 16 = r' := by omega
        have hne := hms a' ha' b' hb'lt
        rw [hsplit_val a' b' ha' hb'lt, hdiv, hmod, ← hQhit] at hne
        rw [nimMul_eq_mul16 ha'16 hr16, nimMul_eq_mul16 ha hr'16,
          nimMul_eq_mul16 ha'16 hr'16, hRhit, hm_eq] at hne
        exact hne rfl
      · have hRlt : R < R₀ := by
          dsimp [M] at hm
          omega
        have hRnot : R ∉ {k : ℕ | ∀ a' < a, ∀ r' < r,
            k ≠ OMA.S_oeis_a335159.nimMul a' r ^^^ OMA.S_oeis_a335159.nimMul a r' ^^^
              OMA.S_oeis_a335159.nimMul a' r'} := by
          intro hmemR
          have hle : R₀ ≤ R := by
            dsimp [R₀]
            rw [OMA.S_oeis_a335159.nimMul]
            exact Nat.sInf_le hmemR
          omega
        simp only [Set.mem_ofPred_eq, not_forall, not_not] at hRnot
        rcases hRnot with ⟨a', ha', r', hr', hRhit⟩
        let b' := 16 * q + r'
        have hb'lt : b' < b := by omega
        have hr'16 : r' < 16 := hr'.trans hr16
        have hdiv : b' / 16 = q := by omega
        have hmod : b' % 16 = r' := by omega
        have hne := hms a' ha' b' hb'lt
        rw [hsplit_val a' b' ha' hb'lt, hdiv, hmod, ← hRhit] at hne
        have hhi : OMA.S_oeis_a335159.nimMul a' q ^^^ OMA.S_oeis_a335159.nimMul a q ^^^
            OMA.S_oeis_a335159.nimMul a' q = Q₀ := by
          rw [Nat.xor_comm (OMA.S_oeis_a335159.nimMul a' q) (OMA.S_oeis_a335159.nimMul a q),
            Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        rw [hhi, ← hQeq, hm_eq] at hne
        exact hne rfl
    refine le_antisymm (Nat.sInf_le hmem) ?_
    by_contra hlt
    have hlt' : sInf S < M := lt_of_not_ge hlt
    exact hmin (sInf S) hlt' (Nat.sInf_mem ⟨M, hmem⟩)

private lemma nimMul_split {a b : ℕ} (ha : a < 16) :
    OMA.S_oeis_a335159.nimMul a b =
      16 * OMA.S_oeis_a335159.nimMul a (b / 16) + OMA.S_oeis_a335159.nimMul a (b % 16) :=
  nimMul_split_aux (a + b) a b rfl ha

private lemma a_rec (n : ℕ) (hn : 3 < n) :
    OMA.S_oeis_a335159.a n = 16 * OMA.S_oeis_a335159.a (n - 4) := by
  rw [OMA.S_oeis_a335159.a, OMA.S_oeis_a335159.a]
  have hpow : 2 ^ n = 16 * 2 ^ (n - 4) := by
    have h1 : 16 * 2 ^ (n - 4) = 2 ^ 4 * 2 ^ (n - 4) := by norm_num
    rw [h1, ← pow_add, show 4 + (n - 4) = n by omega]
  rw [nimMul_split (by decide : 2 ^ 2 < 16), hpow, Nat.mul_div_right _ (by decide),
    Nat.mul_mod_right, nimMul_eq_mul16 (by decide : 2 ^ 2 < 16) (by decide : 0 < 16)]
  have hm0 : mul16 (2 ^ 2) 0 = 0 := by decide
  rw [hm0, add_zero]

private lemma a_zero : OMA.S_oeis_a335159.a 0 = 4 := by
  rw [OMA.S_oeis_a335159.a, nimMul_eq_mul16 (by decide) (by decide)]
  decide

private lemma a_one : OMA.S_oeis_a335159.a 1 = 8 := by
  rw [OMA.S_oeis_a335159.a, nimMul_eq_mul16 (by decide) (by decide)]
  decide

private lemma a_two : OMA.S_oeis_a335159.a 2 = 6 := by
  rw [OMA.S_oeis_a335159.a, nimMul_eq_mul16 (by decide) (by decide)]
  decide

private lemma a_three : OMA.S_oeis_a335159.a 3 = 11 := by
  rw [OMA.S_oeis_a335159.a, nimMul_eq_mul16 (by decide) (by decide)]
  decide

theorem OMA.solution : type_of% @OMA.S_oeis_a335159.main := by
  refine ⟨a_rec, ?_⟩
  have hpoly :
      ((1 - 2 * PowerSeries.X) * (1 + 2 * PowerSeries.X) * (1 + 4 * PowerSeries.X ^ 2) :
          PowerSeries ℤ) =
        1 - 16 * PowerSeries.X ^ 4 := by
    ring
  rw [hpoly]
  ext n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_mk]
  have hcoeff16 :
      PowerSeries.coeff n
          ((16 * PowerSeries.X ^ 4 : PowerSeries ℤ) *
            PowerSeries.mk fun n ↦ (OMA.S_oeis_a335159.a n : ℤ)) =
        if n < 4 then 0 else 16 * (OMA.S_oeis_a335159.a (n - 4) : ℤ) := by
    have h16 : (16 * PowerSeries.X ^ 4 : PowerSeries ℤ) =
        PowerSeries.C 16 * PowerSeries.X ^ 4 := by
      simp
    rw [h16, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    by_cases hn : n < 4
    · have : ¬ 4 ≤ n := by omega
      simp [hn, this]
    · have hge : 4 ≤ n := by omega
      simp [hn, hge]
  rw [hcoeff16]
  have hrhs :
      (4 + 8 * PowerSeries.X + 6 * PowerSeries.X ^ 2 + 11 * PowerSeries.X ^ 3 : PowerSeries ℤ) =
        PowerSeries.C 4 * PowerSeries.X ^ 0 + PowerSeries.C 8 * PowerSeries.X ^ 1 +
          PowerSeries.C 6 * PowerSeries.X ^ 2 + PowerSeries.C 11 * PowerSeries.X ^ 3 := by
    simp
  rw [hrhs]
  simp only [map_add, PowerSeries.coeff_C_mul_X_pow]
  rcases lt_or_ge n 4 with hn | hn
  · interval_cases n <;> simp [a_zero, a_one, a_two, a_three]
  · have hnot : ¬ n < 4 := by omega
    rw [if_neg hnot, a_rec n (by omega)]
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    have h2 : n ≠ 2 := by omega
    have h3 : n ≠ 3 := by omega
    simp [h0, h1, h2, h3]
