import OMAStatements.S_oeis_a364114

/-!
Proof of Peter Bala's four supercongruences for row 3 of Bala's Legendre array (OEIS A364114).
-/

namespace OMA.S_oeis_a364114.Proof

open Finset BigOperators Polynomial

-- ============================================================================
-- Block B: p-Local Valuation Library, Wolstenholme, and Kazandzidis (Lemma 2)
-- ============================================================================

/-- Elementary p-local predicate: q lies in p^e * Z_(p). -/
private def PVal (p e : ℕ) (q : ℚ) : Prop :=
  ∃ (a : ℤ) (d : ℕ), ¬ p ∣ d ∧ q = (p : ℚ) ^ e * (a : ℚ) / (d : ℚ)

/-- Elementary p-adic valuation on natural numbers. -/
private noncomputable def vp (p n : ℕ) : ℕ := n.factorization p

private lemma vp_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) : p ^ vp p n ∣ n :=
  (hp.pow_dvd_iff_le_factorization hn).mpr le_rfl

private lemma vp_succ_not_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ¬ p ^ (vp p n + 1) ∣ n := by
  intro h
  have hle := (hp.pow_dvd_iff_le_factorization hn).mp h
  dsimp [vp] at hle
  omega

private lemma vp_le_of_dvd {p n k : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h : p ^ k ∣ n) :
    k ≤ vp p n :=
  (hp.pow_dvd_iff_le_factorization hn).mp h

private lemma pow_vp_le {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) : p ^ vp p n ≤ n :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (vp_dvd hp hn)

private lemma vp_split {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    ∃ m : ℕ, ¬ p ∣ m ∧ n = p ^ vp p n * m := by
  obtain ⟨m, hm⟩ := vp_dvd hp hn
  refine ⟨m, ?_, hm⟩
  intro ⟨k, hk⟩
  apply vp_succ_not_dvd hp hn
  refine ⟨k, ?_⟩
  calc n = p ^ vp p n * m := hm
    _ = p ^ vp p n * (p * k) := by rw [hk]
    _ = p ^ (vp p n + 1) * k := by rw [pow_succ]; ring

private lemma vp_add_of_lt {p a b : ℕ} (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0)
    (hlt : vp p a < vp p b) : vp p (a + b) = vp p a := by
  have hab : a + b ≠ 0 := by omega
  have h1 : p ^ vp p a ∣ a + b := by
    have ha1 := vp_dvd hp ha
    have hb1 : p ^ vp p a ∣ b := dvd_trans (Nat.pow_dvd_pow p (Nat.le_of_lt hlt)) (vp_dvd hp hb)
    exact dvd_add ha1 hb1
  have hle : vp p a ≤ vp p (a + b) := vp_le_of_dvd hp hab h1
  have hlt2 : ¬ vp p a + 1 ≤ vp p (a + b) := by
    intro hge
    have hdab : p ^ (vp p a + 1) ∣ a + b :=
      dvd_trans (Nat.pow_dvd_pow p hge) (vp_dvd hp hab)
    have hdb : p ^ (vp p a + 1) ∣ b :=
      dvd_trans (Nat.pow_dvd_pow p hlt) (vp_dvd hp hb)
    have hda : p ^ (vp p a + 1) ∣ a := (Nat.dvd_add_left hdb).mp hdab
    exact vp_succ_not_dvd hp ha hda
  omega

private lemma vp_mul_two {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : n ≠ 0) :
    vp p (2 * n) = vp p n := by
  have h2n : 2 * n ≠ 0 := by omega
  have hcop : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr (by intro h; have := Nat.le_of_dvd (by decide) h; omega)
  apply le_antisymm
  · apply vp_le_of_dvd hp hn
    have h1 := vp_dvd hp h2n
    exact (hcop.pow_left _).dvd_of_dvd_mul_left h1
  · exact vp_le_of_dvd hp h2n (dvd_mul_of_dvd_right (vp_dvd hp hn) 2)

private lemma PVal.zero {p e : ℕ} (hp : p.Prime) : PVal p e 0 :=
  ⟨0, 1, hp.not_dvd_one, by simp⟩

private lemma PVal.int {p : ℕ} (hp : p.Prime) (a : ℤ) : PVal p 0 (a : ℚ) :=
  ⟨a, 1, hp.not_dvd_one, by simp⟩

private lemma PVal.nat {p : ℕ} (hp : p.Prime) (a : ℕ) : PVal p 0 (a : ℚ) :=
  ⟨(a : ℤ), 1, hp.not_dvd_one, by simp⟩

private lemma PVal.of_dvd_int {p e : ℕ} (hp : p.Prime) {z : ℤ} (h : (p : ℤ) ^ e ∣ z) :
    PVal p e (z : ℚ) := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c, 1, hp.not_dvd_one, by push_cast; ring⟩

private lemma PVal.of_dvd_nat {p e : ℕ} (hp : p.Prime) {n : ℕ} (h : p ^ e ∣ n) :
    PVal p e (n : ℚ) := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨(c : ℤ), 1, hp.not_dvd_one, by push_cast; ring⟩

private lemma PVal.of_pow_p {p e : ℕ} (hp : p.Prime) : PVal p e ((p : ℚ) ^ e) :=
  ⟨1, 1, hp.not_dvd_one, by simp⟩

private lemma PVal.mono {p e₁ e₂ : ℕ} {q : ℚ} (hle : e₁ ≤ e₂) (hq : PVal p e₂ q) :
    PVal p e₁ q := by
  obtain ⟨a, d, hd, rfl⟩ := hq
  refine ⟨(p : ℤ) ^ (e₂ - e₁) * a, d, hd, ?_⟩
  have hadd : e₁ + (e₂ - e₁) = e₂ := by omega
  push_cast
  rw [← mul_assoc, ← pow_add, hadd]

private lemma PVal.neg {p e : ℕ} {q : ℚ} (hq : PVal p e q) : PVal p e (-q) := by
  obtain ⟨a, d, hd, rfl⟩ := hq
  exact ⟨-a, d, hd, by push_cast; ring⟩

private lemma PVal.add {p e : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h1 : PVal p e q₁) (h2 : PVal p e q₂) : PVal p e (q₁ + q₂) := by
  obtain ⟨a₁, d₁, hd₁, rfl⟩ := h1
  obtain ⟨a₂, d₂, hd₂, rfl⟩ := h2
  have hd₁0 : (d₁ : ℚ) ≠ 0 := by
    exact_mod_cast (show d₁ ≠ 0 by intro h; subst h; exact hd₁ (dvd_zero p))
  have hd₂0 : (d₂ : ℚ) ≠ 0 := by
    exact_mod_cast (show d₂ ≠ 0 by intro h; subst h; exact hd₂ (dvd_zero p))
  refine ⟨a₁ * (d₂ : ℤ) + a₂ * (d₁ : ℤ), d₁ * d₂, ?_, ?_⟩
  · intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact hd₁ h
    · exact hd₂ h
  · push_cast
    field_simp [hd₁0, hd₂0]

private lemma PVal.sub {p e : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h1 : PVal p e q₁) (h2 : PVal p e q₂) : PVal p e (q₁ - q₂) := by
  rw [sub_eq_add_neg]
  exact h1.add hp h2.neg

private lemma PVal.mul {p e₁ e₂ : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h1 : PVal p e₁ q₁) (h2 : PVal p e₂ q₂) : PVal p (e₁ + e₂) (q₁ * q₂) := by
  obtain ⟨a₁, d₁, hd₁, rfl⟩ := h1
  obtain ⟨a₂, d₂, hd₂, rfl⟩ := h2
  refine ⟨a₁ * a₂, d₁ * d₂, ?_, ?_⟩
  · intro h
    rcases hp.dvd_mul.mp h with h | h
    · exact hd₁ h
    · exact hd₂ h
  · push_cast
    rw [pow_add]
    ring

private lemma PVal.mul_zero {p e : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h1 : PVal p e q₁) (h2 : PVal p 0 q₂) : PVal p e (q₁ * q₂) := by
  simpa using h1.mul hp h2

private lemma PVal.zero_mul {p e : ℕ} (hp : p.Prime) {q₁ q₂ : ℚ}
    (h1 : PVal p 0 q₁) (h2 : PVal p e q₂) : PVal p e (q₁ * q₂) := by
  simpa using h1.mul hp h2

private lemma PVal.inv_nat {p d : ℕ} (hd : ¬ p ∣ d) : PVal p 0 ((d : ℚ)⁻¹) :=
  ⟨1, d, hd, by simp [div_eq_mul_inv]⟩

private lemma PVal.div_nat {p e : ℕ} (hp : p.Prime) {q : ℚ} {d : ℕ}
    (hq : PVal p e q) (hd : ¬ p ∣ d) : PVal p e (q / (d : ℚ)) := by
  rw [div_eq_mul_inv]
  exact hq.mul_zero hp (PVal.inv_nat hd)

private lemma PVal.div_int {p e : ℕ} (hp : p.Prime) {q : ℚ} {m : ℤ}
    (hq : PVal p e q) (hm : ¬ (p : ℤ) ∣ m) : PVal p e (q / (m : ℚ)) := by
  have hna : ¬ p ∣ m.natAbs := by
    intro h
    apply hm
    exact Int.natCast_dvd.mpr h
  rcases Int.natAbs_eq m with h | h
  · have hq' : (m : ℚ) = (m.natAbs : ℚ) := by
      have := congrArg (Int.cast : ℤ → ℚ) h; simpa using this
    rw [hq']
    exact hq.div_nat hp hna
  · have hq' : (m : ℚ) = - (m.natAbs : ℚ) := by
      have := congrArg (Int.cast : ℤ → ℚ) h; simpa using this
    rw [hq', div_neg]
    exact (hq.div_nat hp hna).neg

private lemma PVal.div_pow_p {p e m : ℕ} (hp : p.Prime) {q : ℚ}
    (hq : PVal p (e + m) q) : PVal p e (q / (p : ℚ) ^ m) := by
  obtain ⟨a, d, hd, rfl⟩ := hq
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨a, d, hd, ?_⟩
  rw [pow_add]
  field_simp [hp0]

private lemma PVal.div_nat_vp {p e m : ℕ} (hp : p.Prime) {q : ℚ} {d : ℕ}
    (hd0 : d ≠ 0) (hm : vp p d ≤ m) (hq : PVal p (e + m) q) :
    PVal p e (q / (d : ℚ)) := by
  obtain ⟨u, hu, hdu⟩ := vp_split hp hd0
  have hq' : PVal p (e + vp p d) q := hq.mono (by omega)
  have h1 : PVal p e (q / (p : ℚ) ^ vp p d) := hq'.div_pow_p hp
  have h2 : PVal p e ((q / (p : ℚ) ^ vp p d) / (u : ℚ)) := h1.div_nat hp hu
  have heq : q / (d : ℚ) = (q / (p : ℚ) ^ vp p d) / (u : ℚ) := by
    conv_lhs => rw [hdu]
    push_cast; rw [div_div]
  rwa [heq]

private lemma PVal.sum {ι : Type*} {s : Finset ι} {p e : ℕ} (hp : p.Prime) {f : ι → ℚ}
    (h : ∀ i ∈ s, PVal p e (f i)) : PVal p e (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PVal.zero hp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (mem_insert_self a s)).add hp (ih fun i hi => h i (mem_insert_of_mem hi))

private lemma PVal.prod_zero {ι : Type*} {s : Finset ι} {p : ℕ} (hp : p.Prime) {f : ι → ℚ}
    (h : ∀ i ∈ s, PVal p 0 (f i)) : PVal p 0 (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PVal.nat hp 1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (mem_insert_self a s)).mul_zero hp (ih fun i hi => h i (mem_insert_of_mem hi))

private lemma PVal.pow {p e : ℕ} (hp : p.Prime) {q : ℚ} (hq : PVal p e q) (m : ℕ) :
    PVal p (m * e) (q ^ m) := by
  induction m with
  | zero => simpa using PVal.nat hp 1
  | succ m ih =>
    rw [pow_succ, show (m + 1) * e = m * e + e by ring]
    exact ih.mul hp hq

private lemma PVal.prod_one_add {ι : Type*} {s : Finset ι} {p e : ℕ} (hp : p.Prime) {f : ι → ℚ}
    (h : ∀ i ∈ s, PVal p e (f i)) : PVal p e ((∏ i ∈ s, (1 + f i)) - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PVal.zero hp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hfa : PVal p e (f a) := h a (mem_insert_self a s)
    have hP : PVal p e ((∏ i ∈ s, (1 + f i)) - 1) := ih fun i hi => h i (mem_insert_of_mem hi)
    have heq : (1 + f a) * (∏ i ∈ s, (1 + f i)) - 1 =
        f a * ((∏ i ∈ s, (1 + f i)) - 1) + f a + ((∏ i ∈ s, (1 + f i)) - 1) := by ring
    rw [heq]
    have hmul : PVal p e (f a * ((∏ i ∈ s, (1 + f i)) - 1)) :=
      (hfa.mul hp hP).mono (by omega)
    exact (hmul.add hp hfa).add hp hP

private lemma PVal.one_add_ne_zero {p e : ℕ} (_hp : p.Prime) (he : 1 ≤ e) {z : ℚ}
    (hz : PVal p e z) : 1 + z ≠ 0 := by
  obtain ⟨a, d, hd, rfl⟩ := hz
  have hd0 : (d : ℚ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by intro h; subst h; exact hd (dvd_zero p))
  intro h0
  have hm : ((d : ℤ) + (p : ℤ) ^ e * a : ℚ) = 0 := by
    have : (1 + (p : ℚ) ^ e * (a : ℚ) / (d : ℚ)) * (d : ℚ) = 0 := by simp [h0]
    have h2 : (d : ℚ) + (p : ℚ) ^ e * (a : ℚ) = 0 := by
      have h3 : (1 + (p : ℚ) ^ e * (a : ℚ) / (d : ℚ)) * (d : ℚ) = (d : ℚ) + (p : ℚ) ^ e * (a : ℚ) := by
        field_simp [hd0]
      linarith
    exact_mod_cast h2
  have hmi : (d : ℤ) + (p : ℤ) ^ e * a = 0 := by exact_mod_cast hm
  have hpd : (p : ℤ) ∣ (d : ℤ) := by
    have hpe : (p : ℤ) ∣ (p : ℤ) ^ e := dvd_pow_self (p : ℤ) (by omega)
    have h1 : (p : ℤ) ∣ (p : ℤ) ^ e * a := dvd_mul_of_dvd_left hpe a
    have h2 : (d : ℤ) = -((p : ℤ) ^ e * a) := by linarith
    rw [h2]; exact dvd_neg.mpr h1
  exact hd (Int.natCast_dvd_natCast.mp hpd)

private lemma PVal.inv_one_add {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) {z : ℚ}
    (hz : PVal p e z) : PVal p e ((1 + z)⁻¹ - 1) := by
  obtain ⟨a, d, hd, rfl⟩ := hz
  have hd0 : (d : ℚ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by intro h; subst h; exact hd (dvd_zero p))
  set m : ℤ := (d : ℤ) + (p : ℤ) ^ e * a
  have hpm : ¬ (p : ℤ) ∣ m := by
    intro hm
    have hpe : (p : ℤ) ∣ (p : ℤ) ^ e * a := dvd_mul_of_dvd_left (dvd_pow_self (p : ℤ) (by omega)) a
    have hpd : (p : ℤ) ∣ (d : ℤ) := by
      have : (d : ℤ) = m - (p : ℤ) ^ e * a := by simp [m]
      rw [this]; exact dvd_sub hm hpe
    exact hd (Int.natCast_dvd_natCast.mp hpd)
  have hm0 : (m : ℚ) ≠ 0 := by
    intro h
    have : m = 0 := by exact_mod_cast h
    rw [this] at hpm; exact hpm (dvd_zero _)
  have heq : (1 + (p : ℚ) ^ e * (a : ℚ) / (d : ℚ))⁻¹ - 1 =
      (-((p : ℚ) ^ e * (a : ℚ))) / (m : ℚ) := by
    have h1 : 1 + (p : ℚ) ^ e * (a : ℚ) / (d : ℚ) = (m : ℚ) / (d : ℚ) := by
      simp only [m]; push_cast; field_simp [hd0]
    rw [h1, inv_div]
    field_simp [hm0]
    simp only [m]; push_cast; ring
  rw [heq]
  have hnum : PVal p e (-((p : ℚ) ^ e * (a : ℚ))) :=
    (PVal.of_pow_p hp |>.mul_zero hp (PVal.int hp a)).neg
  exact hnum.div_int hp hpm

private lemma PVal.int_dvd {p e : ℕ} (hp : p.Prime) {z : ℤ} (h : PVal p e (z : ℚ)) :
    (p : ℤ) ^ e ∣ z := by
  obtain ⟨a, d, hd, hq⟩ := h
  have hd0 : (d : ℚ) ≠ 0 := by
    exact_mod_cast (show d ≠ 0 by intro h0; subst h0; exact hd (dvd_zero p))
  have hmul_q : (z : ℚ) * (d : ℚ) = (p : ℚ) ^ e * (a : ℚ) := by
    rw [hq]; field_simp [hd0]
  have hmul : z * (d : ℤ) = (p : ℤ) ^ e * a := by exact_mod_cast hmul_q
  have hdvd : (p : ℤ) ^ e ∣ z * (d : ℤ) := ⟨a, hmul⟩
  have hcop_nat : Nat.Coprime (p ^ e) d := (hp.coprime_iff_not_dvd.mpr hd).pow_left e
  have hcop : IsCoprime ((p : ℤ) ^ e) (d : ℤ) := by
    have h := (Nat.coprime_iff_gcd_eq_one.mp hcop_nat)
    exact_mod_cast Nat.Coprime.isCoprime hcop_nat
  exact hcop.dvd_of_dvd_mul_right hdvd

private lemma PVal.modEq_of_sub {p e : ℕ} (hp : p.Prime) {x y : ℤ}
    (h : PVal p e ((x : ℚ) - (y : ℚ))) : x ≡ y [ZMOD (p : ℤ) ^ e] := by
  have h' : PVal p e (((y - x : ℤ) : ℚ)) := by
    have : ((y - x : ℤ) : ℚ) = -((x : ℚ) - (y : ℚ)) := by push_cast; ring
    rw [this]; exact h.neg
  exact Int.modEq_iff_dvd.mpr (PVal.int_dvd hp h')

/-- L2.1(a): For every prime p >= 5, sum_{i=1}^{p-1} i^{-2} lies in p * Z_(p). -/
private lemma sum_inv_sq_mod_p (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    PVal p 1 (∑ i ∈ Ico 1 p, ((i : ℚ) ^ 2)⁻¹) := by
  have : Fact p.Prime := ⟨hp⟩
  -- Work in ZMod p via the bijection i |-> (2 * i) % p on Ico 1 p
  set S : ZMod p := ∑ i ∈ Ico 1 p, ((i : ZMod p) ^ 2)⁻¹
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by decide) hd
    omega
  have h3ne : (3 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by decide) hd
    omega
  have hbij : S = ∑ i ∈ Ico 1 p, ((((2 * i) % p : ℕ) : ZMod p) ^ 2)⁻¹ := by
    symm
    refine Finset.sum_bij (fun i _ => (2 * i) % p) ?_ ?_ ?_ ?_
    · intro i hi
      rw [mem_Ico] at hi ⊢
      refine ⟨?_, Nat.mod_lt _ hp.pos⟩
      by_contra hlt
      have h0 : (2 * i) % p = 0 := by omega
      have hd : p ∣ 2 * i := Nat.dvd_of_mod_eq_zero h0
      rcases hp.dvd_mul.mp hd with h2 | hi'
      · have := Nat.le_of_dvd (by decide) h2; omega
      · have := Nat.le_of_dvd (by omega) hi'; omega
    · intro i hi j hj heq
      rw [mem_Ico] at hi hj
      have hmod : ((2 * i : ℕ) : ZMod p) = ((2 * j : ℕ) : ZMod p) := by
        rw [← ZMod.natCast_mod (2 * i) p, ← ZMod.natCast_mod (2 * j) p, heq]
      push_cast at hmod
      have hij : (i : ZMod p) = (j : ZMod p) := mul_left_cancel₀ h2ne hmod
      have hval : i % p = j % p := by
        have h1 := congrArg ZMod.val hij
        simpa [ZMod.val_natCast] using h1
      rwa [Nat.mod_eq_of_lt hi.2, Nat.mod_eq_of_lt hj.2] at hval
    · intro b hb
      rw [mem_Ico] at hb
      have hinv_ne : ((2 : ZMod p)⁻¹ * (b : ZMod p)).val ≠ 0 := by
        intro h0
        have hz : (2 : ZMod p)⁻¹ * (b : ZMod p) = 0 := by
          rw [← ZMod.natCast_zmod_val ((2 : ZMod p)⁻¹ * (b : ZMod p)), h0]; simp
        have hb0 : (b : ZMod p) = 0 := by
          have h := congrArg (fun x => (2 : ZMod p) * x) hz
          rw [← mul_assoc, mul_inv_cancel₀ h2ne, one_mul, mul_zero] at h
          exact h
        have hd : p ∣ b := (ZMod.natCast_eq_zero_iff b p).mp hb0
        have := Nat.le_of_dvd (by omega) hd
        omega
      refine ⟨((2 : ZMod p)⁻¹ * (b : ZMod p)).val, ?_, ?_⟩
      · rw [mem_Ico]
        exact ⟨Nat.pos_of_ne_zero hinv_ne, ZMod.val_lt _⟩
      · have hcast : (((2 * ((2 : ZMod p)⁻¹ * (b : ZMod p)).val) % p : ℕ) : ZMod p) = (b : ZMod p) := by
          rw [ZMod.natCast_mod]; push_cast; rw [ZMod.natCast_zmod_val]
          rw [← mul_assoc, mul_inv_cancel₀ h2ne, one_mul]
        have hv := congrArg ZMod.val hcast
        rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.mod_lt _ hp.pos),
          Nat.mod_eq_of_lt hb.2] at hv
        exact hv
    · intro i _; rfl
  have hS_scale : S = ((2 : ZMod p) ^ 2)⁻¹ * S := by
    calc S = ∑ i ∈ Ico 1 p, ((((2 * i) % p : ℕ) : ZMod p) ^ 2)⁻¹ := hbij
      _ = ∑ i ∈ Ico 1 p, (((2 : ZMod p) * (i : ZMod p)) ^ 2)⁻¹ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ZMod.natCast_mod]; push_cast; rfl
      _ = ∑ i ∈ Ico 1 p, ((2 : ZMod p) ^ 2)⁻¹ * ((i : ZMod p) ^ 2)⁻¹ := by
          refine Finset.sum_congr rfl fun i _ => by rw [mul_pow, mul_inv]
      _ = ((2 : ZMod p) ^ 2)⁻¹ * S := by rw [← Finset.mul_sum]
  have hS0 : S = 0 := by
    have h4 : (2 : ZMod p) ^ 2 * S = S := by
      have h := congrArg (fun x => (2 : ZMod p) ^ 2 * x) hS_scale
      have h22 : (2 : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 h2ne
      rw [← mul_assoc, mul_inv_cancel₀ h22, one_mul] at h
      exact h
    have h3 : (3 : ZMod p) * S = 0 := by
      have : ((2 : ZMod p) ^ 2 - 1) * S = 0 := by rw [sub_mul, one_mul, h4, sub_self]
      have h21 : (2 : ZMod p) ^ 2 - 1 = (3 : ZMod p) := by ring
      rwa [h21] at this
    exact (mul_eq_zero.mp h3).resolve_left h3ne
  -- Lift S = 0 in ZMod p to PVal p 1 in Q via common denominator ((p - 1)!)^2
  set F : ℕ := (p - 1).factorial ^ 2
  set N : ℕ := ∑ i ∈ Ico 1 p, F / i ^ 2
  have hF_ndvd : ¬ p ∣ F := by
    intro h
    have hf : p ∣ (p - 1).factorial := hp.dvd_of_dvd_pow h
    have hle := hp.dvd_factorial.mp hf
    omega
  have hi_dvd : ∀ i ∈ Ico 1 p, i ^ 2 ∣ F := by
    intro i hi
    rw [mem_Ico] at hi
    exact pow_dvd_pow_of_dvd (Nat.dvd_factorial hi.1 (by omega)) 2
  have hN_zmod : (N : ZMod p) = 0 := by
    have hsum_z : (N : ZMod p) = (F : ZMod p) * S := by
      simp only [N, S, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [mem_Ico] at hi
      have hine : (i : ZMod p) ≠ 0 := by
        intro h0
        have hd := (ZMod.natCast_eq_zero_iff i p).mp h0
        have := Nat.le_of_dvd hi.1 hd
        omega
      have hi2ne : (i : ZMod p) ^ 2 ≠ 0 := pow_ne_zero 2 hine
      have hmul : (F / i ^ 2) * i ^ 2 = F := Nat.div_mul_cancel (hi_dvd i (mem_Ico.mpr hi))
      have hmul_z : ((F / i ^ 2 : ℕ) : ZMod p) * (i : ZMod p) ^ 2 = (F : ZMod p) := by
        have h := congrArg (Nat.cast : ℕ → ZMod p) hmul; push_cast at h; exact h
      rw [← hmul_z, mul_assoc, mul_inv_cancel₀ hi2ne, mul_one]
    rw [hsum_z, hS0, mul_zero]
  have hpN : p ∣ N := (ZMod.natCast_eq_zero_iff N p).mp hN_zmod
  have hq : ∑ i ∈ Ico 1 p, ((i : ℚ) ^ 2)⁻¹ = (N : ℚ) / (F : ℚ) := by
    have hF0 : (F : ℚ) ≠ 0 := by
      exact_mod_cast (show F ≠ 0 by intro h; rw [h] at hF_ndvd; exact hF_ndvd (dvd_zero p))
    rw [eq_div_iff hF0, Finset.sum_mul]
    simp only [N, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mem_Ico] at hi
    have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hi20 : ((i : ℚ) ^ 2) ≠ 0 := pow_ne_zero 2 hi0
    have hmul : ((F / i ^ 2 : ℕ) : ℚ) * (i : ℚ) ^ 2 = (F : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel (hi_dvd i (mem_Ico.mpr hi))
    rw [← hmul, mul_comm (((F / i ^ 2 : ℕ) : ℚ)), ← mul_assoc, inv_mul_cancel₀ hi20, one_mul]
  rw [hq]
  exact (PVal.of_dvd_nat hp (by simpa using hpN)).div_nat hp hF_ndvd

/-- L2.1(b): Paired inverse sum sum_{i=1}^{(p-1)/2} 1 / (i * (p - i)) lies in p * Z_(p). -/
private lemma sum_pair_inv_mod_p (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    PVal p 1 (∑ i ∈ Ico 1 ((p - 1) / 2 + 1),
      (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ)))) := by
  set m := (p - 1) / 2
  obtain ⟨m', hm'⟩ := hp.odd_of_ne_two (by omega)
  have hm2 : 2 * m + 1 = p := by omega
  have hfull : 2 * ∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))) =
      ∑ i ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))) := by
    have hunion : Ico 1 p = Ico 1 (m + 1) ∪ Ico (m + 1) p := by
      rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
    have hdisj : Disjoint (Ico 1 (m + 1)) (Ico (m + 1) p) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2; rw [mem_Ico] at hx1 hx2; omega
    rw [hunion, Finset.sum_union hdisj]
    have hsym : ∑ i ∈ Ico (m + 1) p, (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))) =
        ∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))) := by
      refine Finset.sum_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
      · intro i hi; rw [mem_Ico] at hi ⊢; omega
      · intro i hi j hj heq; rw [mem_Ico] at hi hj; omega
      · intro b hb; rw [mem_Ico] at hb; exact ⟨p - b, by rw [mem_Ico]; omega, by omega⟩
      · intro i hi
        rw [mem_Ico] at hi
        have hsub : ((p - i : ℕ) : ℚ) = (p : ℚ) - (i : ℚ) := by
          rw [Nat.cast_sub (by omega)]
        rw [hsub]; ring
    rw [hsym]; ring
  have hdiff : PVal p 1
      (∑ i ∈ Ico 1 p, ((1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))) + ((i : ℚ) ^ 2)⁻¹)) := by
    refine PVal.sum hp fun i hi => ?_
    rw [mem_Ico] at hi
    have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpi0 : (p : ℚ) - (i : ℚ) ≠ 0 := by
      have : (i : ℚ) < (p : ℚ) := by exact_mod_cast hi.2
      linarith
    have heq : (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))) + ((i : ℚ) ^ 2)⁻¹ =
        (p : ℚ) / (((i ^ 2 * (p - i) : ℕ) : ℚ)) := by
      push_cast
      rw [Nat.cast_sub (by omega)]
      field_simp [hi0, hpi0]
      ring
    rw [heq]
    have hnd : ¬ p ∣ i ^ 2 * (p - i) := by
      intro h
      rcases hp.dvd_mul.mp h with h1 | h2
      · have := Nat.le_of_dvd hi.1 (hp.dvd_of_dvd_pow h1); omega
      · have := Nat.le_of_dvd (by omega) h2; omega
    have hp1 : PVal p 1 (p : ℚ) := by simpa using PVal.of_pow_p (e := 1) hp
    exact hp1.div_nat hp hnd
  have hsum_full : PVal p 1 (∑ i ∈ Ico 1 p, (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ)))) := by
    rw [Finset.sum_add_distrib] at hdiff
    have hinv := sum_inv_sq_mod_p p hp hp5
    have hsub := hdiff.sub hp hinv
    simpa using hsub
  have hnd2 : ¬ p ∣ 2 := by
    intro h; have := Nat.le_of_dvd (by decide) h; omega
  have hres := (hsum_full.div_nat hp hnd2)
  rw [← hfull] at hres
  have h2ne : (2 : ℚ) ≠ 0 := by norm_num
  simpa [mul_div_cancel_left₀ _ h2ne] using hres

/-- L2.2: Factor u(x) = prod_{i=1}^{p-1} (x*p + i)/i and its paired form. -/
private def uFactor (p x : ℕ) : ℚ :=
  ∏ i ∈ Ico 1 p, ((x : ℚ) * (p : ℚ) + (i : ℚ)) / (i : ℚ)

private lemma uFactor_pair (p x : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    uFactor p x = ∏ i ∈ Ico 1 ((p - 1) / 2 + 1),
      (1 + (p : ℚ) ^ 2 * ((x : ℚ) * ((x : ℚ) + 1)) / ((i : ℚ) * ((p : ℚ) - (i : ℚ)))) := by
  set m := (p - 1) / 2
  obtain ⟨m', hm'⟩ := hp.odd_of_ne_two (by omega)
  have hm2 : 2 * m + 1 = p := by omega
  unfold uFactor
  have hunion : Ico 1 p = Ico 1 (m + 1) ∪ Ico (m + 1) p := by
    rw [Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  have hdisj : Disjoint (Ico 1 (m + 1)) (Ico (m + 1) p) := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2; rw [mem_Ico] at ha1 ha2; omega
  rw [hunion, Finset.prod_union hdisj]
  have hsecond : ∏ i ∈ Ico (m + 1) p, ((x : ℚ) * (p : ℚ) + (i : ℚ)) / (i : ℚ) =
      ∏ i ∈ Ico 1 (m + 1), ((x : ℚ) * (p : ℚ) + ((p : ℚ) - (i : ℚ))) / ((p : ℚ) - (i : ℚ)) := by
    refine Finset.prod_bij (fun i _ => p - i) ?_ ?_ ?_ ?_
    · intro i hi; rw [mem_Ico] at hi ⊢; omega
    · intro i hi j hj heq; rw [mem_Ico] at hi hj; omega
    · intro b hb; rw [mem_Ico] at hb; exact ⟨p - b, by rw [mem_Ico]; omega, by omega⟩
    · intro i hi
      rw [mem_Ico] at hi
      have hsub : ((p - i : ℕ) : ℚ) = (p : ℚ) - (i : ℚ) := Nat.cast_sub (by omega)
      rw [hsub]; ring
  rw [hsecond, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [mem_Ico] at hi
  have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpi0 : (p : ℚ) - (i : ℚ) ≠ 0 := by
    have : (i : ℚ) < (p : ℚ) := by exact_mod_cast (show i < p by omega)
    linarith
  field_simp [hi0, hpi0]
  ring

private lemma uFactor_sub_one_pval (p x : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    PVal p 2 (uFactor p x - 1) := by
  rw [uFactor_pair p x hp hp5]
  refine PVal.prod_one_add hp fun i hi => ?_
  rw [mem_Ico] at hi
  have hnd : ¬ p ∣ i * (p - i) := by
    intro h
    rcases hp.dvd_mul.mp h with h1 | h2
    · have := Nat.le_of_dvd hi.1 h1; omega
    · have := Nat.le_of_dvd (by omega) h2; omega
  have heq : (p : ℚ) ^ 2 * ((x : ℚ) * ((x : ℚ) + 1)) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))) =
      ((p : ℚ) ^ 2 * ((x * (x + 1) : ℕ) : ℚ)) / (((i * (p - i) : ℕ) : ℚ)) := by
    push_cast; rw [Nat.cast_sub (by omega)]
  rw [heq]
  exact ((PVal.of_pow_p hp).mul_zero hp (PVal.nat hp _)).div_nat hp hnd

/-- L2.3: Truncated logarithm Log_E(1 + z) = sum_{r=0}^{E-1} (-1)^r * z^(r+1) / (r+1). -/
private def truncLog (E : ℕ) (z : ℚ) : ℚ :=
  ∑ r ∈ range E, (-1 : ℚ) ^ r * z ^ (r + 1) / ((r + 1 : ℕ) : ℚ)

private noncomputable def logPoly (E : ℕ) : ℚ[X] :=
  ∑ r ∈ range E, C ((-1 : ℚ) ^ r / ((r + 1 : ℕ) : ℚ)) * X ^ (r + 1)

private lemma logPoly_eval (E : ℕ) (z : ℚ) : (logPoly E).eval z = truncLog E z := by
  simp only [logPoly, truncLog, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  refine Finset.sum_congr rfl fun r _ => by ring

private lemma logPoly_derivative (E : ℕ) :
    Polynomial.derivative (logPoly E) = ∑ r ∈ range E, (-X : ℚ[X]) ^ r := by
  simp only [logPoly, map_sum, derivative_mul, derivative_C, zero_mul, zero_add, derivative_X_pow]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr : ((r + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  rw [← mul_assoc, ← C_mul, Nat.add_sub_cancel]
  have hc : (-1 : ℚ) ^ r / ((r + 1 : ℕ) : ℚ) * ((r + 1 : ℕ) : ℚ) = (-1 : ℚ) ^ r := by
    field_simp [hr]
  rw [hc]
  have hneg : (-X : ℚ[X]) ^ r = C ((-1 : ℚ) ^ r) * X ^ r := by
    rw [show (-X : ℚ[X]) = C (-1 : ℚ) * X by simp, mul_pow, ← map_pow]
  rw [hneg]

private lemma vp_lt_self {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) : vp p n < n := by
  have hle := pow_vp_le hp hn
  have h2 : vp p n < 2 ^ vp p n := Nat.lt_two_pow_self
  have hp2 : 2 ^ vp p n ≤ p ^ vp p n := Nat.pow_le_pow_left hp.two_le _
  omega

/-- L2.3(a): Additivity of truncLog modulo p^E for z1, z2 in p^2 Z_(p). -/
private lemma truncLog_mul_sub (p E : ℕ) (hp : p.Prime) {z₁ z₂ : ℚ}
    (hz₁ : PVal p 2 z₁) (hz₂ : PVal p 2 z₂) :
    PVal p E (truncLog E (z₁ + z₂ + z₁ * z₂) - truncLog E z₁ - truncLog E z₂) := by
  cases E with
  | zero =>
    simp only [truncLog, range_zero, sum_empty, sub_self]
    exact PVal.zero hp
  | succ E' =>
    set E := E' + 1
    set U : ℚ[X] := C z₂ + C (1 + z₂) * X
    set Q : ℚ[X] := (logPoly E).comp U - logPoly E - C (truncLog E z₂)
    have hU_eq : U = X + C z₂ + C z₂ * X := by
      simp only [U, map_add, map_one]; ring
    have hQ_eval : Q.eval z₁ = truncLog E (z₁ + z₂ + z₁ * z₂) - truncLog E z₁ - truncLog E z₂ := by
      simp only [Q, eval_sub, eval_comp, eval_C, logPoly_eval]
      have hU_ev : U.eval z₁ = z₁ + z₂ + z₁ * z₂ := by
        simp only [U, eval_add, eval_mul, eval_C, eval_X]; ring
      rw [hU_ev]
    have hQ0 : Q.eval 0 = 0 := by
      simp only [Q, eval_sub, eval_comp, eval_C, logPoly_eval]
      have hU0 : U.eval 0 = z₂ := by simp [U]
      have hl0 : truncLog E 0 = 0 := by
        simp [truncLog]
      rw [hU0, hl0]; ring
    have hQcoeff0 : Q.coeff 0 = 0 := by
      rw [coeff_zero_eq_eval_zero, hQ0]
    -- Compute derivative Q explicitly via (1 + X) * derivative Q = (-X)^E - (-U)^E
    set R : ℚ[X] := C z₂ * ∑ t ∈ range E, (-X : ℚ[X]) ^ t * (-U) ^ (E - 1 - t)
    have hderiv : Polynomial.derivative Q = R := by
      have h1X_ne : (1 + X : ℚ[X]) ≠ 0 := by
        intro h
        have := congrArg (fun P : ℚ[X] => P.eval 0) h
        simp at this
      apply mul_left_cancel₀ h1X_ne
      have hU_der : Polynomial.derivative U = C (1 + z₂) := by
        simp [U, derivative_add, derivative_mul, derivative_C, derivative_X]
      have hdQ : Polynomial.derivative Q =
          (∑ r ∈ range E, (-U) ^ r) * C (1 + z₂) - ∑ r ∈ range E, (-X : ℚ[X]) ^ r := by
        simp only [Q, derivative_sub, derivative_C, sub_zero, derivative_comp, logPoly_derivative, hU_der]
        congr 1
        rw [mul_comm]
        congr 1
        simp only [Polynomial.sum_comp, Polynomial.pow_comp, Polynomial.neg_comp, Polynomial.X_comp]
      have h1U : (1 + X : ℚ[X]) * C (1 + z₂) = 1 + U := by
        simp only [U, map_add, map_one]; ring
      have hg1 : (1 + U) * ∑ r ∈ range E, (-U) ^ r = 1 - (-U) ^ E := by
        have h := geom_sum_mul (-U) E
        -- (∑ r < E, (-U)^r) * (-U - 1) = (-U)^E - 1
        have h2 : (1 + U) = -((-U) - 1) := by ring
        rw [h2, neg_mul, mul_comm _ (∑ r ∈ range E, (-U) ^ r), h]; ring
      have hg2 : (1 + X : ℚ[X]) * ∑ r ∈ range E, (-X : ℚ[X]) ^ r = 1 - (-X : ℚ[X]) ^ E := by
        have h := geom_sum_mul (-X : ℚ[X]) E
        have h2 : (1 + X : ℚ[X]) = -((-X : ℚ[X]) - 1) := by ring
        rw [h2, neg_mul, mul_comm _ (∑ r ∈ range E, (-X : ℚ[X]) ^ r), h]; ring
      have hLHS : (1 + X : ℚ[X]) * Polynomial.derivative Q = (-X : ℚ[X]) ^ E - (-U) ^ E := by
        rw [hdQ, mul_sub]
        have hpart : (1 + X : ℚ[X]) * ((∑ r ∈ range E, (-U) ^ r) * C (1 + z₂)) =
            (1 + U) * ∑ r ∈ range E, (-U) ^ r := by
          calc (1 + X : ℚ[X]) * ((∑ r ∈ range E, (-U) ^ r) * C (1 + z₂))
              = ((1 + X : ℚ[X]) * C (1 + z₂)) * ∑ r ∈ range E, (-U) ^ r := by ring
            _ = (1 + U) * ∑ r ∈ range E, (-U) ^ r := by rw [h1U]
        rw [hpart, hg1, hg2]; ring
      have hRHS : (1 + X : ℚ[X]) * R = (-X : ℚ[X]) ^ E - (-U) ^ E := by
        have hsub : (-X : ℚ[X]) - (-U) = (1 + X : ℚ[X]) * C z₂ := by
          rw [hU_eq]; ring
        have hg := geom_sum₂_mul (-X : ℚ[X]) (-U) E
        -- (∑ t < E, (-X)^t * (-U)^(E-1-t)) * (-X - -U) = (-X)^E - (-U)^E
        calc (1 + X : ℚ[X]) * R
            = (∑ t ∈ range E, (-X : ℚ[X]) ^ t * (-U) ^ (E - 1 - t)) * ((1 + X : ℚ[X]) * C z₂) := by
                simp only [R]; ring
          _ = (∑ t ∈ range E, (-X : ℚ[X]) ^ t * (-U) ^ (E - 1 - t)) * ((-X : ℚ[X]) - (-U)) := by
                rw [hsub]
          _ = (-X : ℚ[X]) ^ E - (-U) ^ E := hg
      rw [hLHS, hRHS]
    -- Show R.coeff k = 0 for k >= E and PVal p (2 * (E - k)) (R.coeff k) for k < E
    have hR_coeff : ∀ k : ℕ,
        (E ≤ k → R.coeff k = 0) ∧ (k < E → PVal p (2 * (E - k)) (R.coeff k)) := by
      intro k
      have hR_form : R.coeff k =
          z₂ * ∑ t ∈ range E, (-1 : ℚ) ^ (E - 1) * (X ^ t * U ^ (E - 1 - t)).coeff k := by
        simp only [R, coeff_C_mul, finsetSum_coeff]
        congr 1
        refine Finset.sum_congr rfl fun t ht => ?_
        have htE : t < E := mem_range.mp ht
        have hneg1 : (-X : ℚ[X]) ^ t * (-U) ^ (E - 1 - t) =
            C ((-1 : ℚ) ^ (E - 1)) * (X ^ t * U ^ (E - 1 - t)) := by
          rw [show (-X : ℚ[X]) = C (-1 : ℚ) * X by simp,
              show (-U : ℚ[X]) = C (-1 : ℚ) * U by simp,
              mul_pow, mul_pow, ← map_pow, ← map_pow]
          have hexp : t + (E - 1 - t) = E - 1 := by omega
          calc C ((-1 : ℚ) ^ t) * X ^ t * (C ((-1 : ℚ) ^ (E - 1 - t)) * U ^ (E - 1 - t))
              = (C ((-1 : ℚ) ^ t) * C ((-1 : ℚ) ^ (E - 1 - t))) * (X ^ t * U ^ (E - 1 - t)) := by ring
            _ = C ((-1 : ℚ) ^ (t + (E - 1 - t))) * (X ^ t * U ^ (E - 1 - t)) := by
                rw [← C_mul, ← pow_add]
            _ = C ((-1 : ℚ) ^ (E - 1)) * (X ^ t * U ^ (E - 1 - t)) := by rw [hexp]
        rw [hneg1, coeff_C_mul]
      have hterm_coeff : ∀ t ∈ range E,
          (X ^ t * U ^ (E - 1 - t)).coeff k =
            if t ≤ k ∧ k < E then
              ((Nat.choose (E - 1 - t) (k - t) : ℚ) * (1 + z₂) ^ (k - t) * z₂ ^ (E - 1 - k))
            else 0 := by
        intro t ht
        have htE : t < E := mem_range.mp ht
        set m := E - 1 - t
        have hpow : U ^ m = ∑ j ∈ range (m + 1),
            C ((Nat.choose m j : ℚ) * (1 + z₂) ^ j * z₂ ^ (m - j)) * X ^ j := by
          have hadd := add_pow (C (1 + z₂) * X) (C z₂) m
          have hU' : U = C (1 + z₂) * X + C z₂ := by simp only [U]; ring
          rw [hU', hadd]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [map_mul, map_pow, map_natCast, mul_pow]
          ring
        rw [hpow, Finset.mul_sum, finsetSum_coeff]
        by_cases hcond : t ≤ k ∧ k < E
        · simp only [hcond, and_self, ↓reduceIte]
          have hkt : k - t ∈ range (m + 1) := by rw [mem_range]; omega
          rw [Finset.sum_eq_single (k - t)]
          · have hre : X ^ t * (C ((Nat.choose m (k - t) : ℚ) * (1 + z₂) ^ (k - t) * z₂ ^ (m - (k - t))) * X ^ (k - t)) =
                C ((Nat.choose m (k - t) : ℚ) * (1 + z₂) ^ (k - t) * z₂ ^ (m - (k - t))) * X ^ k := by
              have hX : (X : ℚ[X]) ^ t * X ^ (k - t) = X ^ k := by
                rw [← pow_add, Nat.add_sub_of_le hcond.1]
              rw [← hX]; ring
            rw [hre, coeff_C_mul, coeff_X_pow_self, mul_one]
            rw [show m - (k - t) = E - 1 - k by omega]
          · intro j hj hne
            have hre : X ^ t * (C ((Nat.choose m j : ℚ) * (1 + z₂) ^ j * z₂ ^ (m - j)) * X ^ j) =
                C ((Nat.choose m j : ℚ) * (1 + z₂) ^ j * z₂ ^ (m - j)) * X ^ (t + j) := by
              rw [pow_add]; ring
            rw [hre, coeff_C_mul, coeff_X_pow]
            have hneq : k ≠ t + j := by omega
            simp [hneq]
          · intro h; exact absurd hkt h
        · simp only [hcond, ↓reduceIte]
          refine Finset.sum_eq_zero fun j hj => ?_
          have hjm : j < m + 1 := mem_range.mp hj
          have hre : X ^ t * (C ((Nat.choose m j : ℚ) * (1 + z₂) ^ j * z₂ ^ (m - j)) * X ^ j) =
              C ((Nat.choose m j : ℚ) * (1 + z₂) ^ j * z₂ ^ (m - j)) * X ^ (t + j) := by
            rw [pow_add]; ring
          rw [hre, coeff_C_mul, coeff_X_pow]
          have hneq : k ≠ t + j := by omega
          simp [hneq]
      constructor
      · intro hEk
        rw [hR_form]
        have hzero : ∀ t ∈ range E, (-1 : ℚ) ^ (E - 1) * (X ^ t * U ^ (E - 1 - t)).coeff k = 0 := by
          intro t ht
          rw [hterm_coeff t ht]
          have : ¬ (t ≤ k ∧ k < E) := by omega
          simp [this]
        rw [Finset.sum_eq_zero hzero, mul_zero]
      · intro hkE
        rw [hR_form]
        have hz2_pow : PVal p (2 * (E - 1 - k)) (z₂ ^ (E - 1 - k)) := by
          simpa [mul_comm] using hz₂.pow hp (E - 1 - k)
        have hsum_pv : PVal p (2 * (E - 1 - k))
            (∑ t ∈ range E, (-1 : ℚ) ^ (E - 1) * (X ^ t * U ^ (E - 1 - t)).coeff k) := by
          refine PVal.sum hp fun t ht => ?_
          rw [hterm_coeff t ht]
          split_ifs with hcond
          · have h1z : PVal p 0 (1 + z₂) := (PVal.nat hp 1).add hp (hz₂.mono (by omega))
            have hcoef : PVal p 0
                ((-1 : ℚ) ^ (E - 1) * ((Nat.choose (E - 1 - t) (k - t) : ℚ) * (1 + z₂) ^ (k - t))) := by
              have hm1 : PVal p 0 ((-1 : ℚ) ^ (E - 1)) := by
                simpa using (PVal.int hp (-1)).pow hp (E - 1)
              have hch : PVal p 0 (Nat.choose (E - 1 - t) (k - t) : ℚ) := PVal.nat hp _
              have hp1z : PVal p 0 ((1 + z₂) ^ (k - t)) := by simpa using h1z.pow hp (k - t)
              exact hm1.mul_zero hp (hch.mul_zero hp hp1z)
            have hre : (-1 : ℚ) ^ (E - 1) *
                ((Nat.choose (E - 1 - t) (k - t) : ℚ) * (1 + z₂) ^ (k - t) * z₂ ^ (E - 1 - k)) =
                ((-1 : ℚ) ^ (E - 1) * ((Nat.choose (E - 1 - t) (k - t) : ℚ) * (1 + z₂) ^ (k - t))) *
                  z₂ ^ (E - 1 - k) := by ring
            rw [hre]
            exact hcoef.zero_mul hp hz2_pow
          · rw [mul_zero]; exact PVal.zero hp
        have hmul := hz₂.mul hp hsum_pv
        have hexp : 2 + 2 * (E - 1 - k) = 2 * (E - k) := by omega
        rwa [hexp] at hmul
    -- Relate Q.eval z₁ to sum of Q.coeff (k + 1) * z₁^(k + 1) for k < E
    have hQ_coeff : ∀ k : ℕ, Q.coeff (k + 1) = R.coeff k / ((k + 1 : ℕ) : ℚ) := by
      intro k
      have hd := Polynomial.coeff_derivative Q k
      rw [hderiv] at hd
      have hk0 : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      rw [eq_div_iff hk0]
      push_cast; exact hd.symm
    have hQ_deg : ∀ m : ℕ, E < m → Q.coeff m = 0 := by
      intro m hm
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [hQ_coeff k, (hR_coeff k).1 (by omega), zero_div]
    have hQ_expand : Q.eval z₁ = ∑ k ∈ range E, Q.coeff (k + 1) * z₁ ^ (k + 1) := by
      rw [Polynomial.eval_eq_sum_range' (n := E + 1)]
      · rw [Finset.sum_range_succ', hQcoeff0, zero_mul, add_zero]
      · by_contra hge
        have hlt : E < Q.natDegree := by omega
        have hne : Q ≠ 0 := by
          intro h0; rw [h0, natDegree_zero] at hlt; omega
        exact (Polynomial.leadingCoeff_ne_zero.mpr hne) (by rw [Polynomial.leadingCoeff]; exact hQ_deg Q.natDegree hlt)
    rw [← hQ_eval, hQ_expand]
    refine PVal.sum hp fun k hk => ?_
    have hkE : k < E := mem_range.mp hk
    rw [hQ_coeff k]
    have hRk : PVal p (2 * (E - k)) (R.coeff k) := (hR_coeff k).2 hkE
    have hz1k : PVal p (2 * (k + 1)) (z₁ ^ (k + 1)) := by
      simpa [mul_comm] using hz₁.pow hp (k + 1)
    have hnum : PVal p (2 * E + 2) (R.coeff k * z₁ ^ (k + 1)) := by
      have hm := hRk.mul hp hz1k
      have hexp : 2 * (E - k) + 2 * (k + 1) = 2 * E + 2 := by omega
      rwa [hexp] at hm
    have hre : R.coeff k / ((k + 1 : ℕ) : ℚ) * z₁ ^ (k + 1) =
        (R.coeff k * z₁ ^ (k + 1)) / ((k + 1 : ℕ) : ℚ) := by ring
    rw [hre]
    have hvp : vp p (k + 1) ≤ E := by
      have := vp_lt_self hp (by omega : k + 1 ≠ 0)
      omega
    exact (hnum.mono (by omega : E + E ≤ 2 * E + 2)).div_nat_vp hp (by omega : k + 1 ≠ 0) hvp

private lemma truncLog_inv_add (p E : ℕ) (hp : p.Prime) {z : ℚ} (hz : PVal p 2 z) :
    PVal p E (truncLog E ((1 + z)⁻¹ - 1) + truncLog E z) := by
  have h1z : 1 + z ≠ 0 := hz.one_add_ne_zero hp (by omega)
  have hinv : PVal p 2 ((1 + z)⁻¹ - 1) := hz.inv_one_add hp (by omega)
  have hmul := truncLog_mul_sub p E hp hz hinv
  have hcomb : z + ((1 + z)⁻¹ - 1) + z * ((1 + z)⁻¹ - 1) = 0 := by
    have : z + ((1 + z)⁻¹ - 1) + z * ((1 + z)⁻¹ - 1) = (1 + z) * (1 + z)⁻¹ - 1 := by ring
    rw [this, mul_inv_cancel₀ h1z, sub_self]
  have h0 : truncLog E 0 = 0 := by simp [truncLog]
  rw [hcomb, h0] at hmul
  have heq : truncLog E ((1 + z)⁻¹ - 1) + truncLog E z =
      -(0 - truncLog E z - truncLog E ((1 + z)⁻¹ - 1)) := by ring
  rw [heq]
  exact hmul.neg

private lemma truncLog_prod {ι : Type*} (s : Finset ι) (p E : ℕ) (hp : p.Prime) (f : ι → ℚ)
    (hf : ∀ i ∈ s, PVal p 2 (f i)) :
    PVal p E (truncLog E ((∏ i ∈ s, (1 + f i)) - 1) - ∑ i ∈ s, truncLog E (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [prod_empty, sub_self, sum_empty, sub_zero]
    have h0 : truncLog E 0 = 0 := by simp [truncLog]
    rw [h0]; exact PVal.zero hp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa : PVal p 2 (f a) := hf a (mem_insert_self a s)
    have hPs : PVal p 2 ((∏ i ∈ s, (1 + f i)) - 1) :=
      PVal.prod_one_add hp fun i hi => hf i (mem_insert_of_mem hi)
    have hih := ih fun i hi => hf i (mem_insert_of_mem hi)
    have hmul := truncLog_mul_sub p E hp hfa hPs
    have hcomb : f a + ((∏ i ∈ s, (1 + f i)) - 1) + f a * ((∏ i ∈ s, (1 + f i)) - 1) =
        (1 + f a) * (∏ i ∈ s, (1 + f i)) - 1 := by ring
    rw [hcomb] at hmul
    have hadd := hmul.add hp hih
    have heq : (truncLog E ((1 + f a) * (∏ i ∈ s, (1 + f i)) - 1) - truncLog E (f a) -
          truncLog E ((∏ i ∈ s, (1 + f i)) - 1)) +
        (truncLog E ((∏ i ∈ s, (1 + f i)) - 1) - ∑ i ∈ s, truncLog E (f i)) =
        truncLog E ((1 + f a) * (∏ i ∈ s, (1 + f i)) - 1) - (truncLog E (f a) + ∑ i ∈ s, truncLog E (f i)) := by
      ring
    rwa [heq] at hadd

private lemma truncLog_div_sub (p E : ℕ) (hp : p.Prime) {A B : ℚ}
    (hA : PVal p 2 (A - 1)) (hB : PVal p 2 (B - 1)) :
    PVal p E (truncLog E (A / B - 1) - (truncLog E (A - 1) - truncLog E (B - 1))) := by
  have hB0 : B ≠ 0 := by
    have := hB.one_add_ne_zero hp (by omega)
    simpa using this
  have hBinv : PVal p 2 (B⁻¹ - 1) := by
    have := hB.inv_one_add hp (by omega)
    simpa using this
  have h1 := truncLog_mul_sub p E hp hA hBinv
  have h2 := truncLog_inv_add p E hp hB
  have hcomb : (A - 1) + (B⁻¹ - 1) + (A - 1) * (B⁻¹ - 1) = A / B - 1 := by
    rw [div_eq_mul_inv]; ring
  rw [hcomb] at h1
  have h2' : PVal p E (truncLog E (B⁻¹ - 1) + truncLog E (B - 1)) := by simpa using h2
  have h3 := h1.add hp h2'
  have heq : (truncLog E (A / B - 1) - truncLog E (A - 1) - truncLog E (B⁻¹ - 1)) +
      (truncLog E (B⁻¹ - 1) + truncLog E (B - 1)) =
      truncLog E (A / B - 1) - (truncLog E (A - 1) - truncLog E (B - 1)) := by ring
  rwa [heq] at h3

/-- L2.3(b): Valuation preservation (injectivity) of truncLog on p^2 Z_(p). -/
private lemma truncLog_inj (p E : ℕ) (hp : p.Prime) {z : ℚ}
    (hz : PVal p 2 z) (hlog : PVal p E (truncLog E z)) : PVal p E z := by
  have hstep : ∀ v : ℕ, 2 ≤ v → v ≤ E → PVal p v z := by
    intro v hv hvE
    induction v with
    | zero => omega
    | succ v ih =>
      by_cases hv2 : v < 2
      · have heq : v + 1 = 2 := by omega
        rw [heq]; exact hz
      · have ihv : PVal p v z := ih (by omega) (by omega)
        have hEpos : 1 ≤ E := by omega
        have hlogv : PVal p (v + 1) (truncLog E z) := hlog.mono hvE
        have hsplit : truncLog E z = z + ∑ r ∈ range (E - 1),
            (-1 : ℚ) ^ (r + 1) * z ^ (r + 2) / ((r + 2 : ℕ) : ℚ) := by
          unfold truncLog
          rw [show E = (E - 1) + 1 by omega, Finset.sum_range_succ', add_comm]
          simp only [pow_zero, one_mul, zero_add, pow_one, Nat.cast_one, div_one]
          congr 1
        have htail : PVal p (v + 1)
            (∑ r ∈ range (E - 1), (-1 : ℚ) ^ (r + 1) * z ^ (r + 2) / ((r + 2 : ℕ) : ℚ)) := by
          refine PVal.sum hp fun r _ => ?_
          have hpow : PVal p ((r + 2) * v) (z ^ (r + 2)) := ihv.pow hp (r + 2)
          have hsign : PVal p 0 ((-1 : ℚ) ^ (r + 1)) := by
            simpa using (PVal.int hp (-1)).pow hp (r + 1)
          have hnum : PVal p ((r + 2) * v) ((-1 : ℚ) ^ (r + 1) * z ^ (r + 2)) :=
            hsign.zero_mul hp hpow
          have hvp : vp p (r + 2) ≤ r + 1 := by
            have := vp_lt_self hp (by omega : r + 2 ≠ 0)
            omega
          have hge : (v + 1) + (r + 1) ≤ (r + 2) * v := by
            have hv2' : 2 ≤ v := by omega
            nlinarith
          exact (hnum.mono hge).div_nat_vp hp (by omega : r + 2 ≠ 0) hvp
        have hz' : z = truncLog E z -
            ∑ r ∈ range (E - 1), (-1 : ℚ) ^ (r + 1) * z ^ (r + 2) / ((r + 2 : ℕ) : ℚ) := by
          linarith
        rw [hz']
        exact hlogv.sub hp htail
  by_cases hE2 : E ≤ 2
  · exact hz.mono hE2
  · exact hstep E (by omega) le_rfl

/-- L2.4: Falling-factorial polynomial basis and oddness/denominator bound for F_r(N). -/
private noncomputable def fallPoly (m : ℕ) : ℤ[X] :=
  ∏ i ∈ range m, (X - C (i : ℤ))

private lemma fallPoly_monic (m : ℕ) : (fallPoly m).Monic := by
  unfold fallPoly
  exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (i : ℤ)

private lemma fallPoly_natDegree (m : ℕ) : (fallPoly m).natDegree = m := by
  induction m with
  | zero => simp [fallPoly]
  | succ m ih =>
    have hstep : fallPoly (m + 1) = fallPoly m * (X - C (m : ℤ)) := by
      unfold fallPoly; rw [Finset.prod_range_succ]
    rw [hstep]
    have hmon1 : (fallPoly m).Monic := fallPoly_monic m
    have hmon2 : (X - C (m : ℤ)).Monic := Polynomial.monic_X_sub_C (m : ℤ)
    rw [Polynomial.Monic.natDegree_mul hmon1 hmon2, ih, Polynomial.natDegree_X_sub_C]

private lemma poly_eq_sum_fallPoly :
    ∀ (d : ℕ) (P : ℤ[X]), P.natDegree ≤ d →
      ∃ c : ℕ → ℤ, P = ∑ m ∈ range (d + 1), C (c m) * fallPoly m := by
  intro d
  induction d with
  | zero =>
    intro P hP
    refine ⟨fun _ => P.coeff 0, ?_⟩
    simp only [Nat.reduceAdd, range_one, sum_singleton, fallPoly, range_zero, prod_empty, mul_one]
    exact Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp hP)
  | succ d ih =>
    intro P hP
    set a := P.coeff (d + 1)
    set P' := P - C a * fallPoly (d + 1)
    have hdeg' : P'.natDegree ≤ d := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro k hk
      simp only [P', coeff_sub, coeff_C_mul]
      by_cases hk1 : k = d + 1
      · subst hk1
        have hlc : (fallPoly (d + 1)).coeff (d + 1) = 1 := by
          simpa [Polynomial.leadingCoeff, fallPoly_natDegree] using (fallPoly_monic (d + 1)).leadingCoeff
        rw [hlc, mul_one, sub_self]
      · have hgt : d + 1 < k := by omega
        have h1 : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        have h2 : (fallPoly (d + 1)).coeff k = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [fallPoly_natDegree]; omega)
        rw [h1, h2, mul_zero, sub_zero]
    obtain ⟨c', hc'⟩ := ih P' hdeg'
    refine ⟨fun m => if m = d + 1 then a else c' m, ?_⟩
    rw [Finset.sum_range_succ]
    simp only [↓reduceIte]
    have hsum' : ∑ m ∈ range (d + 1), C (if m = d + 1 then a else c' m) * fallPoly m =
        ∑ m ∈ range (d + 1), C (c' m) * fallPoly m := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have hne : m ≠ d + 1 := by rw [mem_range] at hm; omega
      simp [hne]
    rw [hsum', ← hc']
    simp [P']

private lemma fallPoly_diff (m : ℕ) :
    (fallPoly (m + 1)).comp (X + 1) - fallPoly (m + 1) = C ((m + 1 : ℕ) : ℤ) * fallPoly m := by
  have h1 : (fallPoly (m + 1)).comp (X + 1) = (X + 1) * fallPoly m := by
    unfold fallPoly
    rw [Polynomial.prod_comp, Finset.prod_range_succ']
    simp only [Nat.cast_zero, map_zero, sub_zero, Polynomial.sub_comp, Polynomial.X_comp,
      Polynomial.C_comp, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]; ring
  have h2 : fallPoly (m + 1) = fallPoly m * (X - C (m : ℤ)) := by
    unfold fallPoly
    rw [Finset.prod_range_succ]
  rw [h1, h2]
  have hsub : (X + 1 : ℤ[X]) - (X - C (m : ℤ)) = C ((m + 1 : ℕ) : ℤ) := by
    simp only [Nat.cast_add, Nat.cast_one, map_add, map_one]; ring
  calc (X + 1) * fallPoly m - fallPoly m * (X - C (m : ℤ))
      = ((X + 1) - (X - C (m : ℤ))) * fallPoly m := by ring
    _ = C ((m + 1 : ℕ) : ℤ) * fallPoly m := by rw [hsub]

private lemma fallPoly_eval_zero (m : ℕ) : (fallPoly (m + 1)).eval 0 = 0 := by
  unfold fallPoly
  rw [Polynomial.eval_prod, Finset.prod_range_succ']
  simp

private lemma two_mul_add_one_lt_five_pow (r : ℕ) (hr : 1 ≤ r) : 2 * r + 1 < 5 ^ r := by
  induction r with
  | zero => omega
  | succ r ih =>
    by_cases hr0 : r = 0
    · subst hr0; decide
    · have ih' := ih (by omega)
      rw [pow_succ]; omega

private lemma lt_five_pow_sub_one (r : ℕ) (hr : 2 ≤ r) : r < 5 ^ (r - 1) := by
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  simp only [Nat.succ_sub_one]
  have h := two_mul_add_one_lt_five_pow r' (by omega)
  omega

private lemma poly_eq_zero_of_eval_nat (G : ℚ[X]) (hG : ∀ N : ℕ, G.eval (N : ℚ) = 0) : G = 0 := by
  by_contra hne
  set S : Finset ℚ := (range (G.natDegree + 1)).image (fun n : ℕ => (n : ℚ))
  have hcardS : S.card = G.natDegree + 1 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hsub : S ⊆ G.roots.toFinset := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨n, _, rfl⟩ := hq
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def]
    exact hG n
  have h1 : S.card ≤ G.roots.toFinset.card := Finset.card_le_card hsub
  have h2 : G.roots.toFinset.card ≤ G.roots.card := Multiset.toFinset_card_le _
  have h3 : G.roots.card ≤ G.natDegree := Polynomial.card_roots' G
  omega

private lemma coeff_comp_neg_X_q (P : ℚ[X]) (t : ℕ) :
    (P.comp (-X)).coeff t = (-1 : ℚ) ^ t * P.coeff t := by
  conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow P]
  rw [Polynomial.sum_comp, Polynomial.finsetSum_coeff]
  have hterm : ∀ i : ℕ, ((C (P.coeff i) * X ^ i).comp (-X)).coeff t =
      if t = i then (-1 : ℚ) ^ t * P.coeff t else 0 := by
    intro i
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]
    rw [show (-X : ℚ[X]) = C (-1 : ℚ) * X by simp, mul_pow, ← map_pow, ← mul_assoc, ← C_mul]
    rw [coeff_C_mul, coeff_X_pow]
    split_ifs with h
    · subst h; ring
    · ring
  simp_rw [hterm]
  by_cases ht : t ∈ range (P.natDegree + 1)
  · rw [Finset.sum_eq_single t]
    · simp
    · intro i _ hne; simp [Ne.symm hne]
    · intro h; exact absurd ht h
  · rw [Finset.sum_eq_zero]
    · have hlt : P.natDegree < t := by rw [mem_range] at ht; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, mul_zero]
    · intro i hi
      have hne : t ≠ i := by intro h; subst h; exact ht hi
      simp [hne]

private lemma power_sum_odd_poly (r : ℕ) (hr : 1 ≤ r) :
    ∃ F : ℚ[X],
      (∀ N : ℕ, F.eval (N : ℚ) = ∑ j ∈ range N, ((j : ℚ) * ((j : ℚ) + 1)) ^ r) ∧
      (∀ t : ℕ, Even t → F.coeff t = 0) ∧
      (∀ t : ℕ, 2 * r + 1 < t → F.coeff t = 0) ∧
      (∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ t : ℕ,
        PVal p 0 ((p : ℚ) ^ (r - 1) * F.coeff t)) := by
  set P : ℤ[X] := (X * (X + 1)) ^ r
  have hdegP : P.natDegree ≤ 2 * r := by
    have h1 : (X * (X + 1) : ℤ[X]).natDegree ≤ 2 := by
      calc (X * (X + 1) : ℤ[X]).natDegree
          ≤ (X : ℤ[X]).natDegree + (X + 1 : ℤ[X]).natDegree := Polynomial.natDegree_mul_le
        _ ≤ 1 + 1 := by
            have hX : (X : ℤ[X]).natDegree ≤ 1 := by simp
            have hX1 : (X + 1 : ℤ[X]).natDegree ≤ 1 := by
              calc (X + 1 : ℤ[X]).natDegree
                  ≤ max (X : ℤ[X]).natDegree (1 : ℤ[X]).natDegree := Polynomial.natDegree_add_le _ _
                _ ≤ 1 := by simp
            omega
        _ = 2 := rfl
    calc P.natDegree ≤ r * (X * (X + 1) : ℤ[X]).natDegree := Polynomial.natDegree_pow_le
      _ ≤ r * 2 := Nat.mul_le_mul_left r h1
      _ = 2 * r := by ring
  obtain ⟨c, hc⟩ := poly_eq_sum_fallPoly (2 * r) P hdegP
  set φ : ℤ →+* ℚ := Int.castRingHom ℚ
  set F : ℚ[X] := ∑ m ∈ range (2 * r + 1),
    C ((c m : ℚ) / ((m + 1 : ℕ) : ℚ)) * (fallPoly (m + 1)).map φ
  have hF0 : F.eval 0 = 0 := by
    simp only [F, eval_finsetSum, eval_mul, eval_C]
    refine Finset.sum_eq_zero fun m _ => ?_
    have hm0 : ((fallPoly (m + 1)).map φ).eval 0 = 0 := by
      rw [show (0 : ℚ) = φ 0 by simp, Polynomial.eval_map, Polynomial.eval₂_at_apply,
          fallPoly_eval_zero, map_zero]
    rw [hm0, mul_zero]
  have hF_diff : F.comp (X + 1) - F = (X * (X + 1)) ^ r := by
    simp only [F, Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp, ← Finset.sum_sub_distrib]
    have hterm : ∀ m ∈ range (2 * r + 1),
        C ((c m : ℚ) / ((m + 1 : ℕ) : ℚ)) * ((fallPoly (m + 1)).map φ).comp (X + 1) -
          C ((c m : ℚ) / ((m + 1 : ℕ) : ℚ)) * (fallPoly (m + 1)).map φ =
        C (c m : ℚ) * (fallPoly m).map φ := by
      intro m _
      rw [← mul_sub]
      have hmap_diff : ((fallPoly (m + 1)).map φ).comp (X + 1) - (fallPoly (m + 1)).map φ =
          C ((m + 1 : ℕ) : ℚ) * (fallPoly m).map φ := by
        have h := congrArg (Polynomial.map φ) (fallPoly_diff m)
        rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C] at h
        have hcomp : ((fallPoly (m + 1)).comp (X + 1)).map φ =
            ((fallPoly (m + 1)).map φ).comp (X + 1) := by
          rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_one]
        rw [hcomp] at h
        simpa [φ] using h
      rw [hmap_diff, ← mul_assoc, ← C_mul]
      have hm0 : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      congr 2
      field_simp [hm0]
    rw [Finset.sum_congr rfl hterm]
    have hmapP := congrArg (Polynomial.map φ) hc
    simp only [P, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_X,
      Polynomial.map_one, Polynomial.map_sum, Polynomial.map_C] at hmapP
    simpa [φ] using hmapP.symm
  have hF_eval : ∀ N : ℕ, F.eval (N : ℚ) = ∑ j ∈ range N, ((j : ℚ) * ((j : ℚ) + 1)) ^ r := by
    intro N
    induction N with
    | zero => simpa using hF0
    | succ N ih =>
      rw [Finset.sum_range_succ, ← ih]
      have hstep := congrArg (fun Q : ℚ[X] => Q.eval (N : ℚ)) hF_diff
      simp only [eval_sub, eval_comp, eval_add, eval_X, eval_one, eval_pow, eval_mul] at hstep
      push_cast
      linarith
  -- Oddness: G = F + F.comp (-X) has G(X+1) - G(X) = 0 and G(0) = 0
  have hF_odd : F.comp (-X) = -F := by
    set G : ℚ[X] := F + F.comp (-X)
    have hG_diff : G.comp (X + 1) - G = 0 := by
      have h1 : F.comp (X + 1) - F = (X * (X + 1)) ^ r := hF_diff
      have h2 := congrArg (fun Q : ℚ[X] => Q.comp (-X - 1)) hF_diff
      simp only [Polynomial.sub_comp, Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.X_comp,
        Polynomial.one_comp, Polynomial.pow_comp, Polynomial.mul_comp] at h2
      have hsim1 : (-X - 1 + 1 : ℚ[X]) = -X := by ring
      have hsim2 : ((-X - 1) * (-X) : ℚ[X]) = X * (X + 1) := by ring
      rw [hsim1, hsim2] at h2
      have hsim3 : (-(X + 1) : ℚ[X]) = -X - 1 := by ring
      calc G.comp (X + 1) - G
          = (F.comp (X + 1) - F) + (F.comp (-X - 1) - F.comp (-X)) := by
              simp only [G, Polynomial.add_comp, Polynomial.comp_assoc, Polynomial.neg_comp,
                Polynomial.X_comp, hsim3]; ring
        _ = (X * (X + 1)) ^ r - (F.comp (-X) - F.comp (-X - 1)) := by rw [h1]; ring
        _ = (X * (X + 1)) ^ r - (X * (X + 1)) ^ r := by rw [h2]
        _ = 0 := sub_self _
    have hG_nat : ∀ N : ℕ, G.eval (N : ℚ) = 0 := by
      intro N
      induction N with
      | zero =>
        simp only [G, Nat.cast_zero, eval_add, eval_comp, eval_neg, eval_X, neg_zero, hF0, add_zero]
      | succ N ih =>
        have hstep := congrArg (fun Q : ℚ[X] => Q.eval (N : ℚ)) hG_diff
        simp only [eval_sub, eval_comp, eval_add, eval_X, eval_one, eval_zero] at hstep
        push_cast; linarith
    have hG0 : G = 0 := poly_eq_zero_of_eval_nat G hG_nat
    exact eq_neg_of_add_eq_zero_right hG0
  refine ⟨F, hF_eval, ?_, ?_, ?_⟩
  · intro t ht
    have h := congrArg (fun Q : ℚ[X] => Q.coeff t) hF_odd
    rw [coeff_comp_neg_X_q, Polynomial.coeff_neg] at h
    rcases ht with ⟨k, rfl⟩
    have hpow : (-1 : ℚ) ^ (k + k) = 1 := by
      rw [show k + k = 2 * k by ring, pow_mul]; norm_num
    rw [hpow, one_mul] at h
    linarith
  · intro t ht
    simp only [F, finsetSum_coeff, coeff_C_mul]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hm' : m < 2 * r + 1 := mem_range.mp hm
    have hdegm : ((fallPoly (m + 1)).map φ).natDegree ≤ m + 1 :=
      le_trans Polynomial.natDegree_map_le (by rw [fallPoly_natDegree])
    have hc0 : ((fallPoly (m + 1)).map φ).coeff t = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hc0, mul_zero]
  · intro p hp hp5 t
    simp only [F, finsetSum_coeff, coeff_C_mul, Finset.mul_sum]
    refine PVal.sum hp fun m hm => ?_
    have hm' : m < 2 * r + 1 := mem_range.mp hm
    have hre : (p : ℚ) ^ (r - 1) * ((c m : ℚ) / ((m + 1 : ℕ) : ℚ) *
        ((fallPoly (m + 1)).map φ).coeff t) =
        ((p : ℚ) ^ (r - 1) * ((c m : ℚ) * ((fallPoly (m + 1)).coeff t : ℚ))) /
          ((m + 1 : ℕ) : ℚ) := by
      rw [Polynomial.coeff_map]; simp only [φ, Int.coe_castRingHom]; ring
    rw [hre]
    have hvp_le : vp p (m + 1) ≤ r - 1 := by
      have h1 : p ^ vp p (m + 1) ≤ m + 1 := pow_vp_le hp (Nat.succ_ne_zero m)
      have h2 : m + 1 ≤ 2 * r + 1 := by omega
      have h3 : 2 * r + 1 < 5 ^ r := two_mul_add_one_lt_five_pow r hr
      have h4 : 5 ^ r ≤ p ^ r := Nat.pow_le_pow_left hp5 r
      have hlt : p ^ vp p (m + 1) < p ^ r := by omega
      have hlt' : vp p (m + 1) < r := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
      omega
    have hnum : PVal p (0 + (r - 1))
        ((p : ℚ) ^ (r - 1) * ((c m : ℚ) * ((fallPoly (m + 1)).coeff t : ℚ))) := by
      rw [zero_add]
      exact (PVal.of_pow_p hp).mul_zero hp ((PVal.int hp (c m)).mul_zero hp (PVal.int hp _))
    exact hnum.div_nat_vp hp (Nat.succ_ne_zero m) hvp_le

/-- L2.5: For every odd t >= 3, b * c * (b + c) divides (b + c)^t - b^t - c^t in Z. -/
private lemma odd_pow_sub_dvd (b c : ℤ) (t : ℕ) (hodd : Odd t) (ht : 3 ≤ t) :
    b * c * (b + c) ∣ (b + c) ^ t - b ^ t - c ^ t := by
  obtain ⟨s, rfl⟩ := hodd
  obtain ⟨s', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  clear ht
  induction s' with
  | zero =>
    refine ⟨3, ?_⟩
    ring
  | succ s' ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨(b ^ 2 + b * c + c ^ 2) * q + ((b + c) ^ (2 * s' + 2) + b ^ (2 * s' + 2) + c ^ (2 * s' + 2)), ?_⟩
    have hid : (b + c) ^ (2 * (s' + 1 + 1) + 1) - b ^ (2 * (s' + 1 + 1) + 1) - c ^ (2 * (s' + 1 + 1) + 1) =
        (b ^ 2 + b * c + c ^ 2) * ((b + c) ^ (2 * (s' + 1) + 1) - b ^ (2 * (s' + 1) + 1) - c ^ (2 * (s' + 1) + 1)) +
        b * c * (b + c) * ((b + c) ^ (2 * s' + 2) + b ^ (2 * s' + 2) + c ^ (2 * s' + 2)) := by
      have h1 : 2 * (s' + 1 + 1) + 1 = (2 * s' + 2) + 3 := by omega
      have h2 : 2 * (s' + 1) + 1 = (2 * s' + 2) + 1 := by omega
      rw [h1, h2]
      ring
    rw [hid, hq]
    ring

/-- Auxiliary exact factorial factorization of C((b+c)*p, b*p) / C(b+c, b). -/
private lemma factorial_step_uFactor (p a : ℕ) (hp : p.Prime) :
    (((a * p + p).factorial : ℚ) / ((a * p).factorial : ℚ)) =
      ((a + 1 : ℕ) : ℚ) * (p : ℚ) * ((p - 1).factorial : ℚ) * uFactor p a := by
  have hprod : ∀ m : ℕ, ((a * p + m).factorial : ℚ) / ((a * p).factorial : ℚ) =
      ∏ i ∈ range m, ((a * p + 1 + i : ℕ) : ℚ) := by
    intro m
    induction m with
    | zero =>
      have hne : ((a * p).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (a * p)
      simp [div_self hne]
    | succ m ih =>
      rw [Finset.prod_range_succ, ← ih]
      have hfac : (a * p + (m + 1)).factorial = (a * p + m + 1) * (a * p + m).factorial := by
        rw [show a * p + (m + 1) = (a * p + m) + 1 by omega, Nat.factorial_succ]
      rw [hfac]; push_cast; ring
  rw [hprod p]
  have hp1 : 1 ≤ p := hp.one_le
  have hsplit : ∏ i ∈ range p, ((a * p + 1 + i : ℕ) : ℚ) =
      ((a + 1 : ℕ) : ℚ) * (p : ℚ) * ∏ i ∈ Ico 1 p, ((a : ℚ) * (p : ℚ) + (i : ℚ)) := by
    rw [show p = (p - 1) + 1 by omega, Finset.prod_range_succ]
    have hlast : ((a * ((p - 1) + 1) + 1 + (p - 1) : ℕ) : ℚ) = ((a + 1 : ℕ) : ℚ) * (((p - 1) + 1 : ℕ) : ℚ) := by
      have : a * ((p - 1) + 1) + 1 + (p - 1) = (a + 1) * ((p - 1) + 1) := by ring
      exact_mod_cast this
    rw [hlast, mul_comm]
    congr 1
    refine Finset.prod_bij (fun i _ => i + 1) ?_ ?_ ?_ ?_
    · intro i hi; rw [mem_range] at hi; rw [mem_Ico]; omega
    · intro i _ j _ heq; omega
    · intro b hb; rw [mem_Ico] at hb; refine ⟨b - 1, ?_, by omega⟩; rw [mem_range]; omega
    · intro i _; push_cast; ring
  have hfac_prod : ((p - 1).factorial : ℚ) = ∏ i ∈ Ico 1 p, (i : ℚ) := by
    have h : ∀ m : ℕ, (m.factorial : ℚ) = ∏ i ∈ Ico 1 (m + 1), (i : ℚ) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Nat.factorial_succ, Nat.cast_mul, ih]
        have hunion : Ico 1 (m + 1 + 1) = insert (m + 1) (Ico 1 (m + 1)) := by
          ext x; simp only [mem_Ico, mem_insert]; omega
        rw [hunion, Finset.prod_insert (by simp)]
    simpa [Nat.sub_add_cancel hp1] using h (p - 1)
  rw [hsplit, hfac_prod]
  unfold uFactor
  rw [Finset.prod_div_distrib]
  have hne : (∏ i ∈ Ico 1 p, (i : ℚ)) ≠ 0 := by
    rw [← hfac_prod]
    exact_mod_cast Nat.factorial_ne_zero (p - 1)
  field_simp [hne]

private lemma choose_mul_p_ratio (p b c : ℕ) (hp : p.Prime) :
    (Nat.choose ((b + c) * p) (b * p) : ℚ) / (Nat.choose (b + c) b : ℚ) =
      ∏ j ∈ range b, (uFactor p (c + j) / uFactor p j) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.prod_range_succ, ← ih]
    have hch_ne1 : (Nat.choose (b + c) b : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : b ≤ b + c)).ne'
    have hch_ne2 : (Nat.choose ((b + c) * p) (b * p) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.mul_le_mul_right p (by omega : b ≤ b + c))).ne'
    have hch_ne3 : (Nat.choose (b + 1 + c) (b + 1) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : b + 1 ≤ b + 1 + c)).ne'
    have hstep_base : (Nat.choose (b + 1 + c) (b + 1) : ℚ) / (Nat.choose (b + c) b : ℚ) =
        ((b + 1 + c : ℕ) : ℚ) / ((b + 1 : ℕ) : ℚ) := by
      have hnat : (b + 1) * Nat.choose (b + 1 + c) (b + 1) = (b + 1 + c) * Nat.choose (b + c) b := by
        have h := Nat.add_one_mul_choose_eq (b + c) b
        rw [show b + c + 1 = b + 1 + c by omega] at h
        linarith
      have hq : ((b + 1 : ℕ) : ℚ) * (Nat.choose (b + 1 + c) (b + 1) : ℚ) =
          ((b + 1 + c : ℕ) : ℚ) * (Nat.choose (b + c) b : ℚ) := by exact_mod_cast hnat
      have hb1 : ((b + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      rw [div_eq_div_iff hch_ne1 hb1]
      linarith
    have hstep_p : (Nat.choose ((b + 1 + c) * p) ((b + 1) * p) : ℚ) /
        (Nat.choose ((b + c) * p) (b * p) : ℚ) =
        (((b + c + 1 : ℕ) : ℚ) / ((b + 1 : ℕ) : ℚ)) * (uFactor p (c + b) / uFactor p b) := by
      have hf1 : (Nat.choose ((b + 1 + c) * p) ((b + 1) * p) : ℚ) *
          (((b + 1) * p).factorial : ℚ) * ((c * p).factorial : ℚ) =
          (((b + 1 + c) * p).factorial : ℚ) := by
        have h := Nat.choose_mul_factorial_mul_factorial (Nat.mul_le_mul_right p (by omega : b + 1 ≤ b + 1 + c))
        rw [show (b + 1 + c) * p - (b + 1) * p = c * p by
          rw [← Nat.sub_mul]; congr 1; omega] at h
        exact_mod_cast h
      have hf2 : (Nat.choose ((b + c) * p) (b * p) : ℚ) *
          ((b * p).factorial : ℚ) * ((c * p).factorial : ℚ) =
          (((b + c) * p).factorial : ℚ) := by
        have h := Nat.choose_mul_factorial_mul_factorial (Nat.mul_le_mul_right p (by omega : b ≤ b + c))
        rw [show (b + c) * p - b * p = c * p by
          rw [← Nat.sub_mul]; congr 1; omega] at h
        exact_mod_cast h
      have hfac1 := factorial_step_uFactor p (c + b) hp
      have hfac2 := factorial_step_uFactor p b hp
      have heq1 : (c + b) * p + p = (b + 1 + c) * p := by ring
      have heq2 : (c + b) * p = (b + c) * p := by ring
      have heq3 : b * p + p = (b + 1) * p := by ring
      rw [heq1, heq2] at hfac1
      rw [heq3] at hfac2
      have hfa : ((b * p).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hfb : (((b + 1) * p).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hfc : ((c * p).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hfd : (((b + c) * p).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hpm1 : ((p - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hub : uFactor p b ≠ 0 := by
        unfold uFactor
        rw [Finset.prod_ne_zero_iff]
        intro i hi; rw [mem_Ico] at hi
        have hi0 : (0 : ℚ) < (i : ℚ) := by exact_mod_cast hi.1
        exact div_ne_zero (by positivity) (by positivity)
      have hb1 : ((b + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      have hratio : (Nat.choose ((b + 1 + c) * p) ((b + 1) * p) : ℚ) /
          (Nat.choose ((b + c) * p) (b * p) : ℚ) =
          ((((b + 1 + c) * p).factorial : ℚ) / (((b + c) * p).factorial : ℚ)) /
          ((((b + 1) * p).factorial : ℚ) / ((b * p).factorial : ℚ)) := by
        have h1 : (Nat.choose ((b + 1 + c) * p) ((b + 1) * p) : ℚ) =
            (((b + 1 + c) * p).factorial : ℚ) / ((((b + 1) * p).factorial : ℚ) * ((c * p).factorial : ℚ)) := by
          rw [eq_div_iff (mul_ne_zero hfb hfc)]; linarith
        have h2 : (Nat.choose ((b + c) * p) (b * p) : ℚ) =
            (((b + c) * p).factorial : ℚ) / (((b * p).factorial : ℚ) * ((c * p).factorial : ℚ)) := by
          rw [eq_div_iff (mul_ne_zero hfa hfc)]; linarith
        rw [h1, h2]; field_simp [hfa, hfb, hfc, hfd]
      rw [hratio, hfac1, hfac2]
      have hcb : ((c + b + 1 : ℕ) : ℚ) = ((b + c + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [hcb]
      field_simp [hp0, hpm1, hub, hb1]
    have hcb2 : ((b + 1 + c : ℕ) : ℚ) = ((b + c + 1 : ℕ) : ℚ) := by push_cast; ring
    have hb1 : ((b + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hcbne : ((b + c + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hLHS : (Nat.choose ((b + 1 + c) * p) ((b + 1) * p) : ℚ) / (Nat.choose (b + 1 + c) (b + 1) : ℚ) =
        ((Nat.choose ((b + c) * p) (b * p) : ℚ) / (Nat.choose (b + c) b : ℚ)) *
        (((Nat.choose ((b + 1 + c) * p) ((b + 1) * p) : ℚ) / (Nat.choose ((b + c) * p) (b * p) : ℚ)) /
         ((Nat.choose (b + 1 + c) (b + 1) : ℚ) / (Nat.choose (b + c) b : ℚ))) := by
      field_simp [hch_ne1, hch_ne2, hch_ne3]
    rw [hLHS, hstep_p, hstep_base, hcb2]
    field_simp [hb1, hcbne]

/-- L2.6: Kazandzidis ratio supercongruence for prime p >= 5 and b, c >= 1. -/
private lemma kazandzidis_ratio (p b c : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hb : 1 ≤ b) (hc : 1 ≤ c) :
    PVal p (3 + vp p b + vp p c + vp p (b + c))
      ((Nat.choose ((b + c) * p) (b * p) : ℚ) / (Nat.choose (b + c) b : ℚ) - 1) := by
  set E := 3 + vp p b + vp p c + vp p (b + c)
  set R := (Nat.choose ((b + c) * p) (b * p) : ℚ) / (Nat.choose (b + c) b : ℚ)
  have hR_eq : R = ∏ j ∈ range b, (uFactor p (c + j) / uFactor p j) := choose_mul_p_ratio p b c hp
  have hu_pv : ∀ x : ℕ, PVal p 2 (uFactor p x - 1) := fun x => uFactor_sub_one_pval p x hp hp5
  have hdiv_pv : ∀ j : ℕ, PVal p 2 (uFactor p (c + j) / uFactor p j - 1) := by
    intro j
    have h1 := hu_pv (c + j)
    have h2 := hu_pv j
    have h2inv : PVal p 2 ((uFactor p j)⁻¹ - 1) := by
      simpa using h2.inv_one_add hp (by omega)
    have heq : uFactor p (c + j) / uFactor p j - 1 =
        (uFactor p (c + j) - 1) * ((uFactor p j)⁻¹ - 1) +
        (uFactor p (c + j) - 1) + ((uFactor p j)⁻¹ - 1) := by
      rw [div_eq_mul_inv]; ring
    rw [heq]
    exact (((h1.mul hp h2inv).mono (by omega)).add hp h1).add hp h2inv
  have hR_pv2 : PVal p 2 (R - 1) := by
    rw [hR_eq]
    have h := PVal.prod_one_add hp (s := range b) (f := fun j => uFactor p (c + j) / uFactor p j - 1)
      (fun j _ => hdiv_pv j)
    simpa using h
  -- Apply truncLog_inj: it suffices to show PVal p E (truncLog E (R - 1))
  refine truncLog_inj p E hp hR_pv2 ?_
  -- Step 1: truncLog E (R - 1) == sum_{j < b} (truncLog E (u(c+j)-1) - truncLog E (u(j)-1))
  have hlogR : PVal p E (truncLog E (R - 1) -
      ∑ j ∈ range b, (truncLog E (uFactor p (c + j) - 1) - truncLog E (uFactor p j - 1))) := by
    have hprod := truncLog_prod (range b) p E hp
      (fun j => uFactor p (c + j) / uFactor p j - 1) (fun j _ => hdiv_pv j)
    have hprod' : PVal p E (truncLog E (R - 1) -
        ∑ j ∈ range b, truncLog E (uFactor p (c + j) / uFactor p j - 1)) := by
      simpa [hR_eq] using hprod
    have hterm : PVal p E (∑ j ∈ range b,
        (truncLog E (uFactor p (c + j) / uFactor p j - 1) -
          (truncLog E (uFactor p (c + j) - 1) - truncLog E (uFactor p j - 1)))) :=
      PVal.sum hp fun j _ => truncLog_div_sub p E hp (hu_pv (c + j)) (hu_pv j)
    rw [Finset.sum_sub_distrib] at hterm
    have hadd := hprod'.add hp hterm
    have heq : (truncLog E (R - 1) - ∑ j ∈ range b, truncLog E (uFactor p (c + j) / uFactor p j - 1)) +
        (∑ j ∈ range b, truncLog E (uFactor p (c + j) / uFactor p j - 1) -
          ∑ j ∈ range b, (truncLog E (uFactor p (c + j) - 1) - truncLog E (uFactor p j - 1))) =
        truncLog E (R - 1) -
          ∑ j ∈ range b, (truncLog E (uFactor p (c + j) - 1) - truncLog E (uFactor p j - 1)) := by
      ring
    rwa [heq] at hadd
  -- Step 2: Expand each truncLog E (u(x) - 1) into sum over i in Ico 1 (m + 1)
  set m := (p - 1) / 2
  set g : ℕ → ℕ → ℚ := fun x i =>
    (p : ℚ) ^ 2 * ((x : ℚ) * ((x : ℚ) + 1)) / ((i : ℚ) * ((p : ℚ) - (i : ℚ)))
  have hg_pv2 : ∀ x : ℕ, ∀ i ∈ Ico 1 (m + 1), PVal p 2 (g x i) := by
    intro x i hi
    rw [mem_Ico] at hi
    have hnd : ¬ p ∣ i * (p - i) := by
      intro h
      rcases hp.dvd_mul.mp h with h1 | h2
      · have := Nat.le_of_dvd hi.1 h1; omega
      · have := Nat.le_of_dvd (by omega) h2; omega
    have heq : g x i = ((p : ℚ) ^ 2 * ((x * (x + 1) : ℕ) : ℚ)) / (((i * (p - i) : ℕ) : ℚ)) := by
      simp only [g]; push_cast; rw [Nat.cast_sub (by omega)]
    rw [heq]
    exact ((PVal.of_pow_p hp).mul_zero hp (PVal.nat hp _)).div_nat hp hnd
  have hlog_u : ∀ x : ℕ, PVal p E (truncLog E (uFactor p x - 1) -
      ∑ i ∈ Ico 1 (m + 1), truncLog E (g x i)) := by
    intro x
    have h := truncLog_prod (Ico 1 (m + 1)) p E hp (g x) (hg_pv2 x)
    rwa [← uFactor_pair p x hp hp5] at h
  -- Define double sum L(x) = sum_{i=1}^m truncLog E (g x i)
  set L : ℕ → ℚ := fun x => ∑ i ∈ Ico 1 (m + 1), truncLog E (g x i)
  have hlogR2 : PVal p E (truncLog E (R - 1) - ∑ j ∈ range b, (L (c + j) - L j)) := by
    have hdiff : PVal p E (∑ j ∈ range b,
        ((truncLog E (uFactor p (c + j) - 1) - L (c + j)) -
         (truncLog E (uFactor p j - 1) - L j))) :=
      PVal.sum hp fun j _ => (hlog_u (c + j)).sub hp (hlog_u j)
    have hcomb := hlogR.add hp hdiff
    have heq : (truncLog E (R - 1) -
          ∑ j ∈ range b, (truncLog E (uFactor p (c + j) - 1) - truncLog E (uFactor p j - 1))) +
        ∑ j ∈ range b, ((truncLog E (uFactor p (c + j) - 1) - L (c + j)) -
          (truncLog E (uFactor p j - 1) - L j)) =
        truncLog E (R - 1) - ∑ j ∈ range b, (L (c + j) - L j) := by
      have hsub : ∑ j ∈ range b, ((truncLog E (uFactor p (c + j) - 1) - L (c + j)) -
            (truncLog E (uFactor p j - 1) - L j)) -
          ∑ j ∈ range b, (truncLog E (uFactor p (c + j) - 1) - truncLog E (uFactor p j - 1)) =
          -(∑ j ∈ range b, (L (c + j) - L j)) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      linarith
    rwa [heq] at hcomb
  -- Step 3: Show sum_{j < b} (L(c+j) - L(j)) lies in PVal p E
  have hsumL_eq : ∑ j ∈ range b, (L (c + j) - L j) =
      ∑ r ∈ range E,
        ((-1 : ℚ) ^ r / ((r + 1 : ℕ) : ℚ)) * (p : ℚ) ^ (2 * (r + 1)) *
        (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ (r + 1))) *
        ((∑ j ∈ range (b + c), ((j : ℚ) * ((j : ℚ) + 1)) ^ (r + 1)) -
         (∑ j ∈ range b, ((j : ℚ) * ((j : ℚ) + 1)) ^ (r + 1)) -
         (∑ j ∈ range c, ((j : ℚ) * ((j : ℚ) + 1)) ^ (r + 1))) := by
    have hL_exp : ∀ x : ℕ, L x = ∑ r ∈ range E,
        ((-1 : ℚ) ^ r / ((r + 1 : ℕ) : ℚ)) * (p : ℚ) ^ (2 * (r + 1)) *
        (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ (r + 1))) *
        (((x : ℚ) * ((x : ℚ) + 1)) ^ (r + 1)) := by
      intro x
      simp only [L, truncLog]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [g, div_pow, mul_pow, ← pow_mul]
      ring
    simp only [hL_exp, ← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hinner : ∑ j ∈ range b,
        ((((c + j : ℕ) : ℚ) * (((c + j : ℕ) : ℚ) + 1)) ^ (r + 1) -
          ((j : ℚ) * ((j : ℚ) + 1)) ^ (r + 1)) =
        (∑ j ∈ range (b + c), ((j : ℚ) * ((j : ℚ) + 1)) ^ (r + 1)) -
        (∑ j ∈ range b, ((j : ℚ) * ((j : ℚ) + 1)) ^ (r + 1)) -
        (∑ j ∈ range c, ((j : ℚ) * ((j : ℚ) + 1)) ^ (r + 1)) := by
      rw [Finset.sum_sub_distrib, show b + c = c + b by omega, Finset.sum_range_add]
      ring
    rw [← hinner]
    rw [Finset.mul_sum (s := range b)]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hsumL_pv : PVal p E (∑ j ∈ range b, (L (c + j) - L j)) := by
    rw [hsumL_eq]
    refine PVal.sum hp fun r _ => ?_
    set r1 := r + 1
    obtain ⟨F, hFeval, hFeven, hFdeg, hFden⟩ := power_sum_odd_poly r1 (by omega)
    have hFdiff_eq : (∑ j ∈ range (b + c), ((j : ℚ) * ((j : ℚ) + 1)) ^ r1) -
        (∑ j ∈ range b, ((j : ℚ) * ((j : ℚ) + 1)) ^ r1) -
        (∑ j ∈ range c, ((j : ℚ) * ((j : ℚ) + 1)) ^ r1) =
        F.eval ((b + c : ℕ) : ℚ) - F.eval (b : ℚ) - F.eval (c : ℚ) := by
      rw [hFeval (b + c), hFeval b, hFeval c]
    rw [hFdiff_eq]
    -- Show (p^(r1 - 1)) * (F(b+c) - F(b) - F(c)) has PVal p (vp b + vp c + vp (b+c))
    set V := vp p b + vp p c + vp p (b + c)
    have hFdiff_pv : PVal p V
        ((p : ℚ) ^ (r1 - 1) * (F.eval ((b + c : ℕ) : ℚ) - F.eval (b : ℚ) - F.eval (c : ℚ))) := by
      have hexpF : ∀ x : ℚ, F.eval x = ∑ t ∈ range (2 * r1 + 2), F.coeff t * x ^ t := by
        intro x
        rw [Polynomial.eval_eq_sum_range' (n := 2 * r1 + 2)]
        by_contra hge
        have hlt : 2 * r1 + 1 < F.natDegree := by omega
        have hne : F ≠ 0 := by intro h0; rw [h0, natDegree_zero] at hlt; omega
        exact (Polynomial.leadingCoeff_ne_zero.mpr hne) (by rw [Polynomial.leadingCoeff]; exact hFdeg _ hlt)
      rw [hexpF, hexpF, hexpF, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine PVal.sum hp fun t _ => ?_
      have hre : (p : ℚ) ^ (r1 - 1) *
          (F.coeff t * ((b + c : ℕ) : ℚ) ^ t - F.coeff t * (b : ℚ) ^ t - F.coeff t * (c : ℚ) ^ t) =
          ((p : ℚ) ^ (r1 - 1) * F.coeff t) *
            ((((b : ℤ) + (c : ℤ)) ^ t - (b : ℤ) ^ t - (c : ℤ) ^ t : ℤ) : ℚ) := by
        push_cast; ring
      rw [hre]
      by_cases hev : Even t
      · rw [hFeven t hev, mul_zero, zero_mul]; exact PVal.zero hp
      · have hodd : Odd t := Nat.not_even_iff_odd.mp hev
        by_cases ht1 : t = 1
        · subst ht1
          have : (((b : ℤ) + (c : ℤ)) ^ 1 - (b : ℤ) ^ 1 - (c : ℤ) ^ 1 : ℤ) = 0 := by ring
          rw [this, Int.cast_zero, mul_zero]; exact PVal.zero hp
        · have ht3 : 3 ≤ t := by rcases hodd with ⟨k, rfl⟩; omega
          have hdvd1 : (b : ℤ) * (c : ℤ) * ((b : ℤ) + (c : ℤ)) ∣
              ((b : ℤ) + (c : ℤ)) ^ t - (b : ℤ) ^ t - (c : ℤ) ^ t :=
            odd_pow_sub_dvd (b : ℤ) (c : ℤ) t hodd ht3
          have hdvd_p : (p : ℤ) ^ V ∣ (b : ℤ) * (c : ℤ) * ((b : ℤ) + (c : ℤ)) := by
            have hb' : (p : ℤ) ^ vp p b ∣ (b : ℤ) := by exact_mod_cast vp_dvd hp (by omega)
            have hc' : (p : ℤ) ^ vp p c ∣ (c : ℤ) := by exact_mod_cast vp_dvd hp (by omega)
            have hbc' : (p : ℤ) ^ vp p (b + c) ∣ ((b + c : ℕ) : ℤ) := by
              exact_mod_cast vp_dvd hp (by omega)
            rw [Nat.cast_add] at hbc'
            have h1 := mul_dvd_mul (mul_dvd_mul hb' hc') hbc'
            simpa [V, pow_add] using h1
          exact (hFden p hp hp5 t).zero_mul hp (PVal.of_dvd_int hp (dvd_trans hdvd_p hdvd1))
    -- Now separate r = 0 (r1 = 1) vs r >= 1 (r1 >= 2)
    have hE_eq : E = 3 + V := by simp only [E, V]; ring
    rw [hE_eq]
    by_cases hr0 : r = 0
    · subst hr0
      have hpair := sum_pair_inv_mod_p p hp hp5
      have hre : ((-1 : ℚ) ^ 0 / ((0 + 1 : ℕ) : ℚ)) * (p : ℚ) ^ (2 * (0 + 1)) *
          (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ (0 + 1))) *
          (F.eval ((b + c : ℕ) : ℚ) - F.eval (b : ℚ) - F.eval (c : ℚ)) =
          ((p : ℚ) ^ 2 * (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))))) *
          ((p : ℚ) ^ (1 - 1) * (F.eval ((b + c : ℕ) : ℚ) - F.eval (b : ℚ) - F.eval (c : ℚ))) := by
        simp [pow_one]
      rw [hre]
      have hleft : PVal p 3
          ((p : ℚ) ^ 2 * (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / ((i : ℚ) * ((p : ℚ) - (i : ℚ))))) :=
        (PVal.of_pow_p hp).mul hp hpair
      exact hleft.mul hp hFdiff_pv
    · have hr2 : 2 ≤ r1 := by omega
      have hp_ne : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hexp : 2 * r1 = 3 + (r1 - 2) + (r1 - 1) := by omega
      have hre : ((-1 : ℚ) ^ r / ((r1 : ℕ) : ℚ)) * (p : ℚ) ^ (2 * r1) *
          (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ r1)) *
          (F.eval ((b + c : ℕ) : ℚ) - F.eval (b : ℚ) - F.eval (c : ℚ)) =
          ((p : ℚ) ^ 3 * (((-1 : ℚ) ^ r * (p : ℚ) ^ (r1 - 2)) / ((r1 : ℕ) : ℚ)) *
            (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ r1))) *
          ((p : ℚ) ^ (r1 - 1) * (F.eval ((b + c : ℕ) : ℚ) - F.eval (b : ℚ) - F.eval (c : ℚ))) := by
        rw [hexp, pow_add, pow_add]; ring
      rw [hre]
      have hvp_r1 : vp p r1 ≤ r1 - 2 := by
        have h1 : p ^ vp p r1 ≤ r1 := pow_vp_le hp (by omega)
        have h2 : r1 < 5 ^ (r1 - 1) := lt_five_pow_sub_one r1 hr2
        have h3 : 5 ^ (r1 - 1) ≤ p ^ (r1 - 1) := Nat.pow_le_pow_left hp5 (r1 - 1)
        have hlt : vp p r1 < r1 - 1 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (by omega)
        omega
      have hfrac : PVal p 0 (((-1 : ℚ) ^ r * (p : ℚ) ^ (r1 - 2)) / ((r1 : ℕ) : ℚ)) := by
        have hnum : PVal p (0 + (r1 - 2)) ((-1 : ℚ) ^ r * (p : ℚ) ^ (r1 - 2)) := by
          rw [zero_add]
          have hs : PVal p 0 ((-1 : ℚ) ^ r) := by simpa using (PVal.int hp (-1)).pow hp r
          exact hs.zero_mul hp (PVal.of_pow_p hp)
        exact hnum.div_nat_vp hp (by omega) hvp_r1
      have hpair_r1 : PVal p 0
          (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ r1)) := by
        refine PVal.sum hp fun i hi => ?_
        rw [mem_Ico] at hi
        have hnd : ¬ p ∣ (i * (p - i)) ^ r1 := by
          intro h
          have h1 := hp.dvd_of_dvd_pow h
          rcases hp.dvd_mul.mp h1 with h2 | h3
          · have := Nat.le_of_dvd hi.1 h2; omega
          · have := Nat.le_of_dvd (by omega) h3; omega
        have heq : (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ r1) =
            (1 : ℚ) / ((((i * (p - i)) ^ r1 : ℕ) : ℚ)) := by
          push_cast; rw [Nat.cast_sub (by omega)]
        rw [heq]
        exact (PVal.nat hp 1).div_nat hp hnd
      have hleft : PVal p 3
          ((p : ℚ) ^ 3 * (((-1 : ℚ) ^ r * (p : ℚ) ^ (r1 - 2)) / ((r1 : ℕ) : ℚ)) *
            (∑ i ∈ Ico 1 (m + 1), (1 : ℚ) / (((i : ℚ) * ((p : ℚ) - (i : ℚ))) ^ r1))) :=
        ((PVal.of_pow_p hp).mul_zero hp hfrac).mul_zero hp hpair_r1
      exact hleft.mul hp hFdiff_pv
  have hfin := hlogR2.add hp hsumL_pv
  simpa using hfin


-- ============================================================================
-- Block C: Elementary Non-Divisible Supercongruence (Lemma 3)
-- ============================================================================

/-- L3.1: Exact p-adic factorization of C(M' * p + L, L) by induction on L. -/
private lemma choose_p_shift_general (p M' L : ℕ) (hp : p.Prime) :
    (Nat.choose (M' * p + L) L : ℚ) =
      (Nat.choose (M' + L / p) (L / p) : ℚ) *
      ∏ i ∈ (Ico 1 (L + 1)).filter (fun i => ¬ p ∣ i),
        (1 + (M' * p : ℚ) / (i : ℚ)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hstep_lhs : (Nat.choose (M' * p + (L + 1)) (L + 1) : ℚ) =
        (Nat.choose (M' * p + L) L : ℚ) * (1 + (M' * p : ℚ) / ((L + 1 : ℕ) : ℚ)) := by
      have hnat : (L + 1) * Nat.choose (M' * p + L + 1) (L + 1) =
          (M' * p + L + 1) * Nat.choose (M' * p + L) L := by
        have h := Nat.add_one_mul_choose_eq (M' * p + L) L
        linarith
      have hq : ((L + 1 : ℕ) : ℚ) * (Nat.choose (M' * p + (L + 1)) (L + 1) : ℚ) =
          ((M' * p + L + 1 : ℕ) : ℚ) * (Nat.choose (M' * p + L) L : ℚ) := by
        rw [show M' * p + (L + 1) = M' * p + L + 1 by omega]
        exact_mod_cast hnat
      have hL1 : ((L + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp [hL1]
      push_cast at hq ⊢
      linarith
    have hunion : Ico 1 (L + 1 + 1) = insert (L + 1) (Ico 1 (L + 1)) := by
      ext x; simp only [mem_Ico, mem_insert]; omega
    have hnotmem : L + 1 ∉ Ico 1 (L + 1) := by simp
    rw [hstep_lhs, ih, hunion, Finset.filter_insert]
    by_cases hdiv : p ∣ L + 1
    · simp only [hdiv, not_true_eq_false, ↓reduceIte]
      obtain ⟨q1, hq1⟩ := hdiv
      have hq1_pos : 1 ≤ q1 := by
        by_contra h0
        have : q1 = 0 := by omega
        subst this; omega
      obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q1 ≠ 0)
      have hdiv1 : (L + 1) / p = q' + 1 := by
        rw [hq1, Nat.mul_div_cancel_left (q' + 1) hp.pos]
      have hdiv0 : L / p = q' := by
        have hL : L = p * q' + (p - 1) := by
          have hp1 := hp.pos
          have hq1' : L + 1 = p * q' + p := by simpa [Nat.mul_succ] using hq1
          omega
        rw [hL, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by have := hp.pos; omega), add_zero]
      have hstep_q : (Nat.choose (M' + (q' + 1)) (q' + 1) : ℚ) =
          (Nat.choose (M' + q') q' : ℚ) * (1 + (M' * p : ℚ) / ((L + 1 : ℕ) : ℚ)) := by
        have hnat : (q' + 1) * Nat.choose (M' + (q' + 1)) (q' + 1) =
            (M' + (q' + 1)) * Nat.choose (M' + q') q' := by
          have h := Nat.add_one_mul_choose_eq (M' + q') q'
          rw [show M' + q' + 1 = M' + (q' + 1) by omega] at h
          linarith
        have hq : ((q' + 1 : ℕ) : ℚ) * (Nat.choose (M' + (q' + 1)) (q' + 1) : ℚ) =
            ((M' + (q' + 1) : ℕ) : ℚ) * (Nat.choose (M' + q') q' : ℚ) := by
          exact_mod_cast hnat
        have hL1 : ((L + 1 : ℕ) : ℚ) = (p : ℚ) * ((q' + 1 : ℕ) : ℚ) := by exact_mod_cast hq1
        have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hq10 : ((q' + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        rw [hL1]
        field_simp [hp0, hq10]
        push_cast at hq ⊢
        linarith
      rw [hdiv1, hdiv0, hstep_q]
      ring
    · simp only [hdiv, not_false_eq_true, ↓reduceIte]
      have hnotmem_f : L + 1 ∉ (Ico 1 (L + 1)).filter (fun i => ¬ p ∣ i) := by
        intro h; exact hnotmem (Finset.mem_filter.mp h).1
      rw [Finset.prod_insert hnotmem_f]
      have hdiv_eq : (L + 1) / p = L / p := by
        have hmod : L % p + 1 < p := by
          have hlt := Nat.mod_lt L hp.pos
          by_contra hge
          have heq : L % p + 1 = p := by omega
          apply hdiv
          have hdm := Nat.div_add_mod L p
          exact ⟨L / p + 1, by rw [mul_add, mul_one]; omega⟩
        have hL : L + 1 = p * (L / p) + (L % p + 1) := by
          have hdm := Nat.div_add_mod L p
          omega
        conv_lhs => rw [hL]
        rw [Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hmod, add_zero]
      rw [hdiv_eq]
      ring

/-- L3.1(b): Congruence C(M'*p + (a*p + b), a*p + b) == C(M' + a, a) mod p^m when p^m | M'*p. -/
private lemma choose_shift_mod_pow (p M' m a b : ℕ) (hp : p.Prime)
    (hM : p ^ m ∣ M' * p) (hb : b < p) :
    (Nat.choose (M' * p + (a * p + b)) (a * p + b) : ℤ) ≡
      (Nat.choose (M' + a) a : ℤ) [ZMOD (p : ℤ) ^ m] := by
  have hfac := choose_p_shift_general p M' (a * p + b) hp
  have hdiv : (a * p + b) / p = a := by
    rw [mul_comm a p, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hb, add_zero]
  rw [hdiv] at hfac
  have hprod : PVal p m ((∏ i ∈ (Ico 1 (a * p + b + 1)).filter (fun i => ¬ p ∣ i),
      (1 + (M' * p : ℚ) / (i : ℚ))) - 1) := by
    refine PVal.prod_one_add hp fun i hi => ?_
    have hnd : ¬ p ∣ i := (Finset.mem_filter.mp hi).2
    have hMp : PVal p m ((M' * p : ℚ)) := by
      simpa [Nat.cast_mul] using PVal.of_dvd_nat hp hM
    exact hMp.div_nat hp hnd
  have hdiff : PVal p m
      (((Nat.choose (M' * p + (a * p + b)) (a * p + b) : ℤ) : ℚ) -
       ((Nat.choose (M' + a) a : ℤ) : ℚ)) := by
    have heq : ((Nat.choose (M' * p + (a * p + b)) (a * p + b) : ℤ) : ℚ) -
        ((Nat.choose (M' + a) a : ℤ) : ℚ) =
        (Nat.choose (M' + a) a : ℚ) *
          ((∏ i ∈ (Ico 1 (a * p + b + 1)).filter (fun i => ¬ p ∣ i),
            (1 + (M' * p : ℚ) / (i : ℚ))) - 1) := by
      push_cast; rw [hfac]; ring
    rw [heq]
    exact (PVal.nat hp _).zero_mul hp hprod
  exact PVal.modEq_of_sub hp hdiff


/-- Helper: partition sum over range (M * p) into double sum over a < M, b < p. -/
private lemma sum_range_mul_eq {α : Type*} [AddCommMonoid α] (M p : ℕ) (f : ℕ → α) :
    ∑ q ∈ range (M * p), f q = ∑ a ∈ range M, ∑ b ∈ range p, f (a * p + b) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show (M + 1) * p = M * p + p by ring, Finset.sum_range_add, Finset.sum_range_succ, ih]

/-- Helper: for odd p, p divides sum_{b < p} b in Z. -/
private lemma p_dvd_sum_range_id (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ∣ ∑ b ∈ range p, (b : ℤ) := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
  have h2sum : 2 * ∑ b ∈ range p, (b : ℤ) = (p : ℤ) * ((p : ℤ) - 1) := by
    clear hm hp hp5
    induction p with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast; ring
  refine ⟨(m : ℤ), ?_⟩
  have hm_z : (p : ℤ) - 1 = 2 * (m : ℤ) := by omega
  rw [hm_z] at h2sum
  linarith


/-- Helper: partition filter (not p | j) on range (M * p) into q < M, 1 <= s < p. -/
private lemma sum_filter_not_dvd_range_mul {α : Type*} [AddCommMonoid α] (M p : ℕ)
    (hp : p.Prime) (f : ℕ → α) :
    ∑ j ∈ (range (M * p)).filter (fun j => ¬ p ∣ j), f j =
      ∑ q ∈ range M, ∑ s ∈ Ico 1 p, f (q * p + s) := by
  rw [Finset.sum_filter, sum_range_mul_eq M p]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hp1 : 1 ≤ p := hp.one_le
  have hsplit : range p = insert 0 (Ico 1 p) := by
    ext x; simp only [mem_range, mem_insert, mem_Ico]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have h0 : p ∣ q * p + 0 := by simp
  simp only [h0, not_true_eq_false, ↓reduceIte, zero_add]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [mem_Ico] at hs
  have hnd : ¬ p ∣ q * p + s := by
    intro h
    have hps := (Nat.dvd_add_right (dvd_mul_left p q)).mp h
    have := Nat.le_of_dvd hs.1 hps
    omega
  simp [hnd]

/-- Helper: partition filter (p | j) on range (M * p) into r < M with j = p * r. -/
private lemma sum_filter_dvd_range_mul {α : Type*} [AddCommMonoid α] (M p : ℕ)
    (hp : p.Prime) (f : ℕ → α) :
    ∑ j ∈ (range (M * p)).filter (fun j => p ∣ j), f j =
      ∑ r ∈ range M, f (p * r) := by
  rw [Finset.sum_filter, sum_range_mul_eq M p]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hp1 : 1 ≤ p := hp.one_le
  have hsplit : range p = insert 0 (Ico 1 p) := by
    ext x; simp only [mem_range, mem_insert, mem_Ico]; omega
  rw [hsplit, Finset.sum_insert (by simp)]
  have h0 : p ∣ r * p + 0 := by simp
  have hrest : ∑ s ∈ Ico 1 p, (if p ∣ r * p + s then f (r * p + s) else 0) = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [mem_Ico] at hs
    have hnd : ¬ p ∣ r * p + s := by
      intro h
      have hps := (Nat.dvd_add_right (dvd_mul_left p r)).mp h
      have := Nat.le_of_dvd hs.1 hps
      omega
    simp [hnd]
  rw [hrest, add_zero]
  simp [mul_comm]


-- ============================================================================
-- Block A: Exact Combinatorial Identities (Q-rep and Chu-Vandermonde Duality)
-- ============================================================================

private def cJ (n j : ℕ) : ℤ :=
  (Nat.choose n j : ℤ) * (Nat.choose (n + j) j : ℤ)

private noncomputable def Lpoly (n : ℕ) : ℤ[X] :=
  ∑ j ∈ range (n + 1), C (cJ n j) * X ^ j

private lemma a_cast_eq (n : ℕ) :
    (OMA.S_oeis_a364114.a n : ℤ) =
      ∑ j ∈ range (n + 1), (Nat.choose n j : ℤ) * ((Lpoly n) ^ 3).coeff j := by
  unfold OMA.S_oeis_a364114.a
  dsimp only
  set Lnat : ℕ[X] := ∑ j ∈ range (n + 1), Polynomial.monomial j (n.choose j * (n + j).choose j)
  have hmap : Lnat.map (Nat.castRingHom ℤ) = Lpoly n := by
    simp only [Lnat, Lpoly, cJ, Polynomial.map_sum, Polynomial.map_monomial,
      Polynomial.C_mul_X_pow_eq_monomial]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.cast_mul, ← hmap]
  have hc : ((Lnat ^ 3).coeff j : ℤ) = ((Lnat ^ 3).map (Nat.castRingHom ℤ)).coeff j := by
    rw [Polynomial.coeff_map]; rfl
  rw [hc, Polynomial.map_pow]

private lemma coeff_X_pow_mul_one_add_X_pow (k m j : ℕ) :
    ((X : ℤ[X]) ^ k * (1 + X) ^ m).coeff j =
      if k ≤ j then (Nat.choose m (j - k) : ℤ) else 0 := by
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs with h
  · rw [add_comm (1 : ℤ[X]) X, Polynomial.coeff_X_add_one_pow]
  · rfl

/-- A1: Lpoly n = sum_{k=0}^n C(n,k)^2 * X^k * (1 + X)^(n - k) in Z[X]. -/
private lemma Lpoly_eq_sq_sum (n : ℕ) :
    Lpoly n = ∑ k ∈ range (n + 1), C ((Nat.choose n k : ℤ) ^ 2) * X ^ k * (1 + X) ^ (n - k) := by
  ext j
  simp only [Lpoly, Polynomial.finsetSum_coeff]
  have hL : (∑ i ∈ range (n + 1), (C (cJ n i) * X ^ i).coeff j) =
      if j ≤ n then cJ n j else 0 := by
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (range (n + 1)) j]
    simp [Finset.mem_range]
  rw [hL]
  have hR : (∑ k ∈ range (n + 1), (C ((Nat.choose n k : ℤ) ^ 2) * X ^ k * (1 + X) ^ (n - k)).coeff j) =
      ∑ k ∈ range (n + 1), if k ≤ j then (Nat.choose n k : ℤ) ^ 2 * (Nat.choose (n - k) (j - k) : ℤ) else 0 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Polynomial.coeff_C_mul, coeff_X_pow_mul_one_add_X_pow]
    split_ifs <;> ring
  rw [hR]
  by_cases hjn : j ≤ n
  · simp only [hjn, ↓reduceIte, cJ]
    have hsplit : (∑ k ∈ range (n + 1),
        if k ≤ j then (Nat.choose n k : ℤ) ^ 2 * (Nat.choose (n - k) (j - k) : ℤ) else 0) =
        ∑ k ∈ range (j + 1), (Nat.choose n k : ℤ) ^ 2 * (Nat.choose (n - k) (j - k) : ℤ) := by
      rw [← Finset.sum_filter]
      have hf : (range (n + 1)).filter (fun k => k ≤ j) = range (j + 1) := by
        ext k; simp only [mem_filter, mem_range]; omega
      rw [hf]
    rw [hsplit]
    have hnat : Nat.choose n j * Nat.choose (n + j) j =
        ∑ k ∈ range (j + 1), Nat.choose n k ^ 2 * Nat.choose (n - k) (j - k) := by
      have hv : Nat.choose (n + j) j = ∑ k ∈ range (j + 1), Nat.choose n k * Nat.choose j (j - k) := by
        rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => Nat.choose n a * Nat.choose j b)]
      rw [hv, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      have hkj : k ≤ j := by omega
      have hsym : Nat.choose j (j - k) = Nat.choose j k := Nat.choose_symm hkj
      have htri : Nat.choose n k * Nat.choose (n - k) (j - k) = Nat.choose n j * Nat.choose j k := by
        have h := Nat.choose_mul (n := n) hkj
        exact h.symm
      rw [hsym]
      calc Nat.choose n j * (Nat.choose n k * Nat.choose j k)
          = Nat.choose n k * (Nat.choose n j * Nat.choose j k) := by ring
        _ = Nat.choose n k * (Nat.choose n k * Nat.choose (n - k) (j - k)) := by rw [← htri]
        _ = Nat.choose n k ^ 2 * Nat.choose (n - k) (j - k) := by ring
    exact_mod_cast hnat
  · simp only [hjn, ↓reduceIte]
    symm
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [mem_range] at hk
    split_ifs with hkj
    · have hgt : n - k < j - k := by omega
      rw [Nat.choose_eq_zero_of_lt hgt]; simp
    · rfl

/-- A2: Q-representation of a(n). -/
private lemma a_eq_Q_rep (n : ℕ) :
    (OMA.S_oeis_a364114.a n : ℤ) =
      ∑ k₁ ∈ range (n + 1), ∑ k₂ ∈ range (n + 1), ∑ k₃ ∈ range (n + 1),
        if k₁ + k₂ + k₃ ≤ n then
          (Nat.choose (4 * n - (k₁ + k₂ + k₃)) (n - (k₁ + k₂ + k₃)) : ℤ) *
            (Nat.choose n k₁ : ℤ) ^ 2 * (Nat.choose n k₂ : ℤ) ^ 2 * (Nat.choose n k₃ : ℤ) ^ 2
        else 0 := by
  rw [a_cast_eq, Lpoly_eq_sq_sum]
  have hcube : (∑ k ∈ range (n + 1), C ((Nat.choose n k : ℤ) ^ 2) * X ^ k * (1 + X) ^ (n - k)) ^ 3 =
      ∑ k₁ ∈ range (n + 1), ∑ k₂ ∈ range (n + 1), ∑ k₃ ∈ range (n + 1),
        C ((Nat.choose n k₁ : ℤ) ^ 2 * (Nat.choose n k₂ : ℤ) ^ 2 * (Nat.choose n k₃ : ℤ) ^ 2) *
          (X ^ (k₁ + k₂ + k₃) * (1 + X) ^ (3 * n - (k₁ + k₂ + k₃))) := by
    rw [pow_three]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k₁ hk₁ => Finset.sum_congr rfl fun k₂ hk₂ =>
      Finset.sum_congr rfl fun k₃ hk₃ => ?_
    rw [mem_range] at hk₁ hk₂ hk₃
    have hexp : n - k₁ + (n - k₂) + (n - k₃) = 3 * n - (k₁ + k₂ + k₃) := by omega
    simp only [map_mul]
    rw [← hexp]
    ring
  rw [hcube]
  simp_rw [Polynomial.finsetSum_coeff, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k₂ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k₃ _ => ?_
  set s := k₁ + k₂ + k₃
  set w : ℤ := (Nat.choose n k₁ : ℤ) ^ 2 * (Nat.choose n k₂ : ℤ) ^ 2 * (Nat.choose n k₃ : ℤ) ^ 2
  have hterm : ∑ j ∈ range (n + 1), (Nat.choose n j : ℤ) *
        (C w * (X ^ s * (1 + X) ^ (3 * n - s))).coeff j =
      (∑ j ∈ range (n + 1), if s ≤ j then
        (Nat.choose n j : ℤ) * (Nat.choose (3 * n - s) (j - s) : ℤ) else 0) * w := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.coeff_C_mul, coeff_X_pow_mul_one_add_X_pow]
    split_ifs <;> ring
  rw [hterm]
  by_cases hsn : s ≤ n
  · simp only [hsn, ↓reduceIte]
    have hcv : ∑ j ∈ range (n + 1), (if s ≤ j then
          (Nat.choose n j : ℤ) * (Nat.choose (3 * n - s) (j - s) : ℤ) else 0) =
        (Nat.choose (4 * n - s) (n - s) : ℤ) := by
      rw [← Finset.sum_filter]
      have hnat : ∑ j ∈ (range (n + 1)).filter (fun j => s ≤ j),
            Nat.choose n j * Nat.choose (3 * n - s) (j - s) =
          Nat.choose (4 * n - s) (n - s) := by
        have hbij : ∑ j ∈ (range (n + 1)).filter (fun j => s ≤ j),
              Nat.choose n j * Nat.choose (3 * n - s) (j - s) =
            ∑ u ∈ range (n - s + 1), Nat.choose n (n - s - u) * Nat.choose (3 * n - s) u := by
          refine Finset.sum_bij (fun j _ => j - s) ?_ ?_ ?_ ?_
          · intro j hj; rw [mem_filter, mem_range] at hj; rw [mem_range]; omega
          · intro j₁ hj₁ j₂ hj₂ h; rw [mem_filter] at hj₁ hj₂; omega
          · intro u hu; rw [mem_range] at hu
            exact ⟨u + s, by rw [mem_filter, mem_range]; omega, by omega⟩
          · intro j hj
            rw [mem_filter, mem_range] at hj
            have hsym : Nat.choose n j = Nat.choose n (n - j) := (Nat.choose_symm (by omega)).symm
            rw [hsym, show n - j = n - s - (j - s) by omega]
        rw [hbij]
        have hv : Nat.choose (4 * n - s) (n - s) =
            ∑ u ∈ range (n - s + 1), Nat.choose n u * Nat.choose (3 * n - s) (n - s - u) := by
          rw [show 4 * n - s = n + (3 * n - s) by omega, Nat.add_choose_eq,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => Nat.choose n a * Nat.choose (3 * n - s) b)]
        rw [hv, ← Finset.sum_range_reflect (fun u => Nat.choose n u * Nat.choose (3 * n - s) (n - s - u)) (n - s + 1)]
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [mem_range] at hu
        have h1 : n - s + 1 - 1 - u = n - s - u := by omega
        have h2 : n - s - (n - s - u) = u := by omega
        rw [h1, h2]
      exact_mod_cast hnat
    rw [hcv]
    ring
  · simp only [hsn, ↓reduceIte]
    have hzero : ∑ j ∈ range (n + 1), (if s ≤ j then
          (Nat.choose n j : ℤ) * (Nat.choose (3 * n - s) (j - s) : ℤ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [mem_range] at hj
      have : ¬ s ≤ j := by omega
      simp [this]
    rw [hzero, zero_mul]

/-- A3: Reflection symmetry Lpoly n (-1 - X) = (-1)^n * Lpoly n. -/
private lemma Lpoly_reflect (n : ℕ) :
    (Lpoly n).comp (-1 - X) = (-1 : ℤ[X]) ^ n * Lpoly n := by
  rw [Lpoly_eq_sq_sum, Polynomial.sum_comp, Finset.mul_sum]
  have hrew : ∑ k ∈ range (n + 1),
        (C ((Nat.choose n k : ℤ) ^ 2) * X ^ k * (1 + X) ^ (n - k)).comp (-1 - X) =
      ∑ k ∈ range (n + 1),
        (-1 : ℤ[X]) ^ n * (C ((Nat.choose n (n - k) : ℤ) ^ 2) * X ^ (n - k) * (1 + X) ^ k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    have hkn : k ≤ n := by omega
    simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
      Polynomial.add_comp, Polynomial.one_comp]
    have h1 : (1 + (-1 - X) : ℤ[X]) = -(X : ℤ[X]) := by ring
    have h2 : (-1 - X : ℤ[X]) = -(1 + X : ℤ[X]) := by ring
    rw [h1, h2, neg_pow (X : ℤ[X]), neg_pow (1 + X : ℤ[X]), Nat.choose_symm hkn]
    have hsign : (-1 : ℤ[X]) ^ k * (-1 : ℤ[X]) ^ (n - k) = (-1 : ℤ[X]) ^ n := by
      rw [← pow_add, Nat.add_sub_of_le hkn]
    set c : ℤ[X] := C ((Nat.choose n k : ℤ) ^ 2)
    set a : ℤ[X] := (-1 : ℤ[X]) ^ k
    set b : ℤ[X] := (-1 : ℤ[X]) ^ (n - k)
    set p1 : ℤ[X] := (1 + X) ^ k
    set p2 : ℤ[X] := X ^ (n - k)
    have hr : c * (a * p1) * (b * p2) = (a * b) * (c * p2 * p1) := by
      simp only [mul_assoc, mul_left_comm, mul_comm]
    rw [hr, hsign]
  rw [hrew]
  have href := Finset.sum_range_reflect (fun k =>
    (-1 : ℤ[X]) ^ n * (C ((Nat.choose n k : ℤ) ^ 2) * X ^ k * (1 + X) ^ (n - k))) (n + 1)
  rw [← href]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [mem_range] at hk
  have h1 : n + 1 - 1 - k = n - k := by omega
  have h2 : n - (n - k) = k := by omega
  rw [h1, h2]

/-- Helper for A4: Vandermonde identity on (-1 - X)^m. -/
private lemma sum_choose_coeff_neg_one_sub_X_pow (n m : ℕ) :
    ∑ j ∈ range (n + 1), (Nat.choose n j : ℤ) * ((-1 - X : ℤ[X]) ^ m).coeff j =
      (-1 : ℤ) ^ m * (Nat.choose (n + m) m : ℤ) := by
  have heq : (-1 - X : ℤ[X]) ^ m = C ((-1 : ℤ) ^ m) * (X + 1) ^ m := by
    rw [show (-1 - X : ℤ[X]) = -(X + 1 : ℤ[X]) by ring, neg_pow (X + 1 : ℤ[X])]
    simp [map_pow]
  rw [heq]
  have hnat : ∑ j ∈ range (n + 1), Nat.choose n j * Nat.choose m j = Nat.choose (n + m) m := by
    have hv : Nat.choose (n + m) m = ∑ k ∈ range (n + 1), Nat.choose n k * Nat.choose m (n - k) := by
      rw [← Nat.choose_symm_add, Nat.add_choose_eq,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => Nat.choose n a * Nat.choose m b)]
    rw [hv, ← Finset.sum_range_reflect (fun k => Nat.choose n k * Nat.choose m (n - k)) (n + 1)]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    have h1 : n + 1 - 1 - j = n - j := by omega
    have h2 : n - (n - j) = j := by omega
    rw [h1, h2, Nat.choose_symm (by omega : j ≤ n)]
  calc ∑ j ∈ range (n + 1), (Nat.choose n j : ℤ) * (C ((-1 : ℤ) ^ m) * (X + 1) ^ m).coeff j
      = (-1 : ℤ) ^ m * ∑ j ∈ range (n + 1), (Nat.choose n j : ℤ) * (Nat.choose m j : ℤ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_one_pow]; ring
    _ = (-1 : ℤ) ^ m * (Nat.choose (n + m) m : ℤ) := by
        congr 1; exact_mod_cast hnat

/-- A4: Dual representation (-1)^(3*n) * a(n) = sum (-1)^s C(n+s, s) prod cJ(n, j_i). -/
private lemma a_eq_dual_rep (n : ℕ) :
    (-1 : ℤ) ^ (3 * n) * (OMA.S_oeis_a364114.a n : ℤ) =
      ∑ j₁ ∈ range (n + 1), ∑ j₂ ∈ range (n + 1), ∑ j₃ ∈ range (n + 1),
        (-1 : ℤ) ^ (j₁ + j₂ + j₃) * (Nat.choose (n + (j₁ + j₂ + j₃)) (j₁ + j₂ + j₃) : ℤ) *
          cJ n j₁ * cJ n j₂ * cJ n j₃ := by
  have hcomp : ((Lpoly n) ^ 3).comp (-1 - X) = C ((-1 : ℤ) ^ (3 * n)) * (Lpoly n) ^ 3 := by
    rw [Polynomial.pow_comp, Lpoly_reflect, mul_pow, ← pow_mul, mul_comm n 3]
    simp [map_pow]
  have hlhs : (-1 : ℤ) ^ (3 * n) * (OMA.S_oeis_a364114.a n : ℤ) =
      ∑ j ∈ range (n + 1), (Nat.choose n j : ℤ) * (((Lpoly n) ^ 3).comp (-1 - X)).coeff j := by
    rw [a_cast_eq, hcomp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.coeff_C_mul]; ring
  rw [hlhs]
  have hcube : (Lpoly n) ^ 3 =
      ∑ j₁ ∈ range (n + 1), ∑ j₂ ∈ range (n + 1), ∑ j₃ ∈ range (n + 1),
        C (cJ n j₁ * cJ n j₂ * cJ n j₃) * X ^ (j₁ + j₂ + j₃) := by
    simp only [Lpoly, pow_three]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ =>
      Finset.sum_congr rfl fun j₃ _ => ?_
    simp only [map_mul, pow_add]; ring
  rw [hcube]
  simp_rw [Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.finsetSum_coeff, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j₂ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j₃ _ => ?_
  have hfac : ∑ j ∈ range (n + 1), (Nat.choose n j : ℤ) *
        (C (cJ n j₁ * cJ n j₂ * cJ n j₃) * (-1 - X) ^ (j₁ + j₂ + j₃)).coeff j =
      (∑ j ∈ range (n + 1), (Nat.choose n j : ℤ) * ((-1 - X : ℤ[X]) ^ (j₁ + j₂ + j₃)).coeff j) *
        (cJ n j₁ * cJ n j₂ * cJ n j₃) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.coeff_C_mul]; ring
  rw [hfac, sum_choose_coeff_neg_one_sub_X_pow]
  ring

-- ============================================================================
-- Block B Extensions: Additional p-Local Binomial & Geometric Series Lemmas
-- ============================================================================

private lemma vp_choose_ge (p N k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hkN : k ≤ N) (hN : N ≠ 0) :
    p ^ (vp p N - vp p k) ∣ Nat.choose N k := by
  have hrel : k * Nat.choose N k = N * Nat.choose (N - 1) (k - 1) := by
    have h := Nat.add_one_mul_choose_eq (N - 1) (k - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ N), Nat.sub_add_cancel hk1] at h
    linarith
  have hdvd : p ^ vp p N ∣ k * Nat.choose N k := by
    rw [hrel]; exact dvd_mul_of_dvd_left (vp_dvd hp hN) _
  obtain ⟨u, hu, hku⟩ := vp_split hp (by omega : k ≠ 0)
  by_cases hle : vp p N ≤ vp p k
  · rw [Nat.sub_eq_zero_of_le hle, pow_zero]; exact one_dvd _
  · have hsub : vp p k + (vp p N - vp p k) = vp p N := by omega
    have hdvd' : p ^ vp p k * p ^ (vp p N - vp p k) ∣ p ^ vp p k * (u * Nat.choose N k) := by
      have h1 : p ^ vp p N ∣ p ^ vp p k * (u * Nat.choose N k) := by
        rwa [← mul_assoc, ← hku]
      rwa [← pow_add, hsub]
    have h1 : p ^ (vp p N - vp p k) ∣ u * Nat.choose N k :=
      (Nat.mul_dvd_mul_iff_left (Nat.pow_pos hp.pos)).mp hdvd'
    have hcop : Nat.Coprime (p ^ (vp p N - vp p k)) u :=
      (hp.coprime_iff_not_dvd.mpr hu).pow_left _
    exact hcop.dvd_of_dvd_mul_left h1

private lemma vp_choose_pred_add_ge (p N k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hN : N ≠ 0) :
    p ^ (vp p N - vp p k) ∣ Nat.choose (N - 1 + k) k := by
  have hrel : k * Nat.choose (N - 1 + k) k = N * Nat.choose (N - 1 + k) (k - 1) := by
    have hb : k - 1 + 1 = k := by omega
    have h2 := Nat.choose_succ_right_eq (N - 1 + k) (k - 1)
    rw [hb, show N - 1 + k - (k - 1) = N by omega] at h2
    linarith
  have hdvd : p ^ vp p N ∣ k * Nat.choose (N - 1 + k) k := by
    rw [hrel]; exact dvd_mul_of_dvd_left (vp_dvd hp hN) _
  obtain ⟨u, hu, hku⟩ := vp_split hp (by omega : k ≠ 0)
  by_cases hle : vp p N ≤ vp p k
  · rw [Nat.sub_eq_zero_of_le hle, pow_zero]; exact one_dvd _
  · have hsub : vp p k + (vp p N - vp p k) = vp p N := by omega
    have hdvd' : p ^ vp p k * p ^ (vp p N - vp p k) ∣
        p ^ vp p k * (u * Nat.choose (N - 1 + k) k) := by
      have h1 : p ^ vp p N ∣ p ^ vp p k * (u * Nat.choose (N - 1 + k) k) := by
        rwa [← mul_assoc, ← hku]
      rwa [← pow_add, hsub]
    have h1 : p ^ (vp p N - vp p k) ∣ u * Nat.choose (N - 1 + k) k :=
      (Nat.mul_dvd_mul_iff_left (Nat.pow_pos hp.pos)).mp hdvd'
    have hcop : Nat.Coprime (p ^ (vp p N - vp p k)) u :=
      (hp.coprime_iff_not_dvd.mpr hu).pow_left _
    exact hcop.dvd_of_dvd_mul_left h1

/-- Exact p-adic factorization of C(M' * p - 1, L) for odd prime p and L < M' * p. -/
private lemma choose_pred_p_shift_general (p M' L : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (hL : L < M' * p) :
    (Nat.choose (M' * p - 1) L : ℚ) =
      (-1 : ℚ) ^ (L % p) * (Nat.choose (M' - 1) (L / p) : ℚ) *
      ∏ i ∈ (Ico 1 (L + 1)).filter (fun i => ¬ p ∣ i),
        (1 - (M' * p : ℚ) / (i : ℚ)) := by
  have hp_even : Even (p - 1) := by
    obtain ⟨t, ht⟩ := hp.odd_of_ne_two hpodd
    exact ⟨t, by omega⟩
  induction L with
  | zero => simp
  | succ L ih =>
    have hLlt : L < M' * p := by omega
    have hih := ih hLlt
    have hstep_lhs : (Nat.choose (M' * p - 1) (L + 1) : ℚ) =
        (Nat.choose (M' * p - 1) L : ℚ) * (- (1 - (M' * p : ℚ) / ((L + 1 : ℕ) : ℚ))) := by
      have hnat : (L + 1) * Nat.choose (M' * p - 1) (L + 1) =
          (M' * p - (L + 1)) * Nat.choose (M' * p - 1) L := by
        have h := Nat.choose_succ_right_eq (M' * p - 1) L
        rw [show M' * p - 1 - L = M' * p - (L + 1) by omega] at h
        linarith
      have hq : ((L + 1 : ℕ) : ℚ) * (Nat.choose (M' * p - 1) (L + 1) : ℚ) =
          (((M' * p : ℕ) : ℚ) - ((L + 1 : ℕ) : ℚ)) * (Nat.choose (M' * p - 1) L : ℚ) := by
        have h1 : ((M' * p - (L + 1) : ℕ) : ℚ) = ((M' * p : ℕ) : ℚ) - ((L + 1 : ℕ) : ℚ) := by
          rw [Nat.cast_sub (by omega)]
        rw [← h1]; exact_mod_cast hnat
      have hL1 : ((L + 1 : ℕ) : ℚ) ≠ 0 := by positivity
      field_simp [hL1]
      push_cast at hq ⊢
      linarith
    have hunion : Ico 1 (L + 1 + 1) = insert (L + 1) (Ico 1 (L + 1)) := by
      ext x; simp only [mem_Ico, mem_insert]; omega
    have hnotmem : L + 1 ∉ Ico 1 (L + 1) := by simp
    rw [hstep_lhs, hih, hunion, Finset.filter_insert]
    by_cases hdiv : p ∣ L + 1
    · simp only [hdiv, not_true_eq_false, ↓reduceIte]
      obtain ⟨q1, hq1⟩ := hdiv
      have hq1_pos : 1 ≤ q1 := by
        rcases Nat.eq_zero_or_pos q1 with rfl | hpos
        · simp at hq1
        · exact hpos
      obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q1 ≠ 0)
      have hdiv1 : (L + 1) / p = q' + 1 := by
        rw [hq1, Nat.mul_div_cancel_left (q' + 1) hp.pos]
      have hmod1 : (L + 1) % p = 0 := Nat.mod_eq_zero_of_dvd ⟨q' + 1, hq1⟩
      have hL_eq : L = p * q' + (p - 1) := by
        have hq1' : L + 1 = p * q' + p := by simpa [Nat.mul_succ] using hq1
        have := hp.pos; omega
      have hdiv0 : L / p = q' := by
        rw [hL_eq, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by have := hp.pos; omega), add_zero]
      have hmod0 : L % p = p - 1 := by
        rw [hL_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by have := hp.pos; omega)]
      have hq'_lt : q' + 1 < M' := by nlinarith [hp.pos]
      have hstep_q : (Nat.choose (M' - 1) (q' + 1) : ℚ) =
          (Nat.choose (M' - 1) q' : ℚ) * (- (1 - (M' * p : ℚ) / ((L + 1 : ℕ) : ℚ))) := by
        have hnat : (q' + 1) * Nat.choose (M' - 1) (q' + 1) =
            (M' - (q' + 1)) * Nat.choose (M' - 1) q' := by
          have h := Nat.choose_succ_right_eq (M' - 1) q'
          rw [show M' - 1 - q' = M' - (q' + 1) by omega] at h
          linarith
        have hq : ((q' + 1 : ℕ) : ℚ) * (Nat.choose (M' - 1) (q' + 1) : ℚ) =
            ((M' : ℚ) - ((q' + 1 : ℕ) : ℚ)) * (Nat.choose (M' - 1) q' : ℚ) := by
          have h1 : ((M' - (q' + 1) : ℕ) : ℚ) = (M' : ℚ) - ((q' + 1 : ℕ) : ℚ) := by
            rw [Nat.cast_sub (by omega)]
          rw [← h1]; exact_mod_cast hnat
        have hL1 : ((L + 1 : ℕ) : ℚ) = (p : ℚ) * ((q' + 1 : ℕ) : ℚ) := by exact_mod_cast hq1
        have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hq10 : ((q' + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        rw [hL1]
        field_simp [hp0, hq10]
        push_cast at hq ⊢
        linarith
      rw [hdiv1, hdiv0, hmod1, hmod0, hstep_q, pow_zero, hp_even.neg_one_pow]
      ring
    · simp only [hdiv, not_false_eq_true, ↓reduceIte]
      have hnotmem_f : L + 1 ∉ (Ico 1 (L + 1)).filter (fun i => ¬ p ∣ i) := by
        intro h; exact hnotmem (Finset.mem_filter.mp h).1
      rw [Finset.prod_insert hnotmem_f]
      have hmod_lt : L % p + 1 < p := by
        have hlt := Nat.mod_lt L hp.pos
        by_contra hge
        have heq : L % p + 1 = p := by omega
        apply hdiv
        have hdm := Nat.div_add_mod L p
        exact ⟨L / p + 1, by rw [mul_add, mul_one]; omega⟩
      have hL_eq : L + 1 = p * (L / p) + (L % p + 1) := by
        have hdm := Nat.div_add_mod L p; omega
      have hdiv_eq : (L + 1) / p = L / p := by
        conv_lhs => rw [hL_eq]
        rw [Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hmod_lt, add_zero]
      have hmod_eq : (L + 1) % p = L % p + 1 := by
        conv_lhs => rw [hL_eq]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hmod_lt]
      rw [hdiv_eq, hmod_eq, pow_succ]
      ring

private lemma choose_pred_mod_pow (p M' m a b : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (hM : p ^ m ∣ M' * p) (ha : a < M') (hb : b < p) :
    (Nat.choose (M' * p - 1) (a * p + b) : ℤ) ≡
      (-1 : ℤ) ^ b * (Nat.choose (M' - 1) a : ℤ) [ZMOD (p : ℤ) ^ m] := by
  have hlt : a * p + b < M' * p := by nlinarith [hp.pos]
  have hfac := choose_pred_p_shift_general p M' (a * p + b) hp hpodd hlt
  have hdiv : (a * p + b) / p = a := by
    rw [mul_comm a p, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hb, add_zero]
  have hmod : (a * p + b) % p = b := by
    rw [mul_comm a p, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  rw [hdiv, hmod] at hfac
  have hprod : PVal p m ((∏ i ∈ (Ico 1 (a * p + b + 1)).filter (fun i => ¬ p ∣ i),
      (1 + (-(M' * p : ℚ) / (i : ℚ)))) - 1) := by
    refine PVal.prod_one_add hp fun i hi => ?_
    have hnd : ¬ p ∣ i := (Finset.mem_filter.mp hi).2
    have hMp0 : PVal p m ((M' * p : ℚ)) := by
      simpa [Nat.cast_mul] using PVal.of_dvd_nat hp hM
    have hMp : PVal p m (-(M' * p : ℚ)) := hMp0.neg
    exact hMp.div_nat hp hnd
  have hprod' : PVal p m ((∏ i ∈ (Ico 1 (a * p + b + 1)).filter (fun i => ¬ p ∣ i),
      (1 - (M' * p : ℚ) / (i : ℚ))) - 1) := by
    convert hprod using 3 with i _
    ring
  have hdiff : PVal p m
      (((Nat.choose (M' * p - 1) (a * p + b) : ℤ) : ℚ) -
       (((-1 : ℤ) ^ b * (Nat.choose (M' - 1) a : ℤ) : ℤ) : ℚ)) := by
    have heq : ((Nat.choose (M' * p - 1) (a * p + b) : ℤ) : ℚ) -
        (((-1 : ℤ) ^ b * (Nat.choose (M' - 1) a : ℤ) : ℤ) : ℚ) =
        ((-1 : ℚ) ^ b * (Nat.choose (M' - 1) a : ℚ)) *
          ((∏ i ∈ (Ico 1 (a * p + b + 1)).filter (fun i => ¬ p ∣ i),
            (1 - (M' * p : ℚ) / (i : ℚ))) - 1) := by
      push_cast; rw [hfac]; ring
    rw [heq]
    have hs : PVal p 0 ((-1 : ℚ) ^ b) := by simpa using (PVal.int hp (-1)).pow hp b
    have hcoeff : PVal p 0 ((-1 : ℚ) ^ b * (Nat.choose (M' - 1) a : ℚ)) :=
      hs.mul_zero hp (PVal.nat hp _)
    exact hcoeff.zero_mul hp hprod'
  exact PVal.modEq_of_sub hp hdiff

private lemma choose_ndiv_exact (p M q s : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (hq : q < M) (hs1 : 1 ≤ s) (hsp : s < p) :
    (Nat.choose (M * p) (q * p + s) : ℚ) =
      (-1 : ℚ) ^ (s - 1) * ((M * p : ℚ) / ((q * p + s : ℕ) : ℚ)) *
        (Nat.choose (M - 1) q : ℚ) *
        ∏ i ∈ (Ico 1 (q * p + s)).filter (fun i => ¬ p ∣ i),
          (1 - (M * p : ℚ) / (i : ℚ)) := by
  set j := q * p + s
  have hj1 : 1 ≤ j := by omega
  have hjlt : j < M * p := by simp only [j]; nlinarith [hp.pos]
  have hrel : (j : ℚ) * (Nat.choose (M * p) j : ℚ) =
      (M * p : ℚ) * (Nat.choose (M * p - 1) (j - 1) : ℚ) := by
    have hnat : j * Nat.choose (M * p) j = M * p * Nat.choose (M * p - 1) (j - 1) := by
      have h := Nat.add_one_mul_choose_eq (M * p - 1) (j - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ M * p), Nat.sub_add_cancel hj1] at h
      linarith
    exact_mod_cast hnat
  have hfac := choose_pred_p_shift_general p M (j - 1) hp hpodd (by omega)
  have hjm1 : j - 1 = q * p + (s - 1) := by omega
  have hdiv : (j - 1) / p = q := by
    rw [hjm1, mul_comm q p, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt (by omega), add_zero]
  have hmod : (j - 1) % p = s - 1 := by
    rw [hjm1, mul_comm q p, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hj1eq : j - 1 + 1 = j := by omega
  rw [hdiv, hmod, hj1eq] at hfac
  have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  apply mul_left_cancel₀ hj0
  rw [hrel, hfac]
  field_simp [hj0]

private lemma choose_pred_add_ndiv_exact (p M q s : ℕ) (hp : p.Prime)
    (hMpos : 1 ≤ M) (hs1 : 1 ≤ s) (hsp : s < p) :
    (Nat.choose (M * p - 1 + (q * p + s)) (q * p + s) : ℚ) =
      ((M * p : ℚ) / ((q * p + s : ℕ) : ℚ)) * (Nat.choose (M + q) q : ℚ) *
        ∏ i ∈ (Ico 1 (q * p + s)).filter (fun i => ¬ p ∣ i),
          (1 + (M * p : ℚ) / (i : ℚ)) := by
  set N := M * p
  set j := q * p + s
  have hNpos : 1 ≤ N := Nat.mul_pos hMpos hp.pos
  have hjpos : 1 ≤ j := by omega
  have hndj : ¬ p ∣ j := by
    intro h
    have hs : p ∣ s := (Nat.dvd_add_right (dvd_mul_left p q)).mp h
    have := Nat.le_of_dvd hs1 hs; omega
  have hrel : ((N + j : ℕ) : ℚ) * (Nat.choose (N - 1 + j) j : ℚ) =
      (N : ℚ) * (Nat.choose (N + j) j : ℚ) := by
    have hnat : (N + j) * Nat.choose (N - 1 + j) j = N * Nat.choose (N + j) j := by
      have h := Nat.add_one_mul_choose_eq (N - 1 + j) (N - 1)
      have h1 : N - 1 + j + 1 = N + j := by omega
      have h2 : N - 1 + 1 = N := by omega
      have hs1' : Nat.choose (N - 1 + j) (N - 1) = Nat.choose (N - 1 + j) j := by
        have hs := Nat.choose_symm (by omega : j ≤ N - 1 + j)
        rwa [show N - 1 + j - j = N - 1 by omega] at hs
      have hs2' : Nat.choose (N + j) N = Nat.choose (N + j) j := by
        have hs := Nat.choose_symm (by omega : j ≤ N + j)
        rwa [show N + j - j = N by omega] at hs
      rw [h1, h2, hs1', hs2'] at h; linarith
    exact_mod_cast hnat
  have hshift := choose_p_shift_general p M j hp
  have hdiv : j / p = q := by
    simp only [j, mul_comm q p, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hsp, add_zero]
  rw [hdiv] at hshift
  have hunion : Ico 1 (j + 1) = insert j (Ico 1 j) := by
    ext x; simp only [mem_Ico, mem_insert]; omega
  have hnotmem : j ∉ (Ico 1 j).filter (fun i => ¬ p ∣ i) := by
    intro h; have := (mem_Ico.mp (Finset.mem_filter.mp h).1).2; omega
  have hshift' : (Nat.choose (N + j) j : ℚ) =
      (Nat.choose (M + q) q : ℚ) * (1 + (N : ℚ) / (j : ℚ)) *
        ∏ i ∈ (Ico 1 j).filter (fun i => ¬ p ∣ i), (1 + (N : ℚ) / (i : ℚ)) := by
    rw [hshift, hunion, Finset.filter_insert]
    simp only [hndj, not_false_eq_true, ↓reduceIte, Finset.prod_insert hnotmem]
    simp only [N, Nat.cast_mul]; ring
  have hNj : ((N + j : ℕ) : ℚ) ≠ 0 := by positivity
  have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  apply mul_left_cancel₀ hNj
  rw [hrel, hshift']
  simp only [N, j, Nat.cast_add, Nat.cast_mul]
  field_simp [hj0]
  ring

/-- Corollary B3a: C(M*p - 1 + p*t, p*t) - C(M - 1 + t, t) in p^(3 + 2*vp p M) Z_(p). -/
private lemma kazandzidis_pred_add (p M t : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : 1 ≤ M) (ht : 1 ≤ t) :
    PVal p (3 + 2 * vp p M)
      ((Nat.choose (M * p - 1 + p * t) (p * t) : ℚ) - (Nat.choose (M - 1 + t) t : ℚ)) := by
  have hrelN : ((M + t : ℕ) : ℚ) * (Nat.choose (M * p - 1 + p * t) (p * t) : ℚ) =
      (M : ℚ) * (Nat.choose ((t + M) * p) (t * p) : ℚ) := by
    have hnat : (M * p + p * t) * Nat.choose (M * p - 1 + p * t) (p * t) =
        (M * p) * Nat.choose ((t + M) * p) (t * p) := by
      have h := Nat.add_one_mul_choose_eq (M * p - 1 + p * t) (M * p - 1)
      have hNpos : 1 ≤ M * p := Nat.mul_pos hM hp.pos
      have h1 : M * p - 1 + p * t + 1 = (t + M) * p := by ring_nf; omega
      have h2 : M * p - 1 + 1 = M * p := by omega
      have hs1 : Nat.choose (M * p - 1 + p * t) (M * p - 1) =
          Nat.choose (M * p - 1 + p * t) (p * t) := by
        have hs := Nat.choose_symm (by omega : p * t ≤ M * p - 1 + p * t)
        rwa [show M * p - 1 + p * t - p * t = M * p - 1 by omega] at hs
      have hs2 : Nat.choose ((t + M) * p) (M * p) = Nat.choose ((t + M) * p) (t * p) := by
        have hs := Nat.choose_symm (by nlinarith : t * p ≤ (t + M) * p)
        rwa [show (t + M) * p - t * p = M * p by
          rw [add_mul]; omega] at hs
      rw [h1, h2, hs1, hs2] at h
      have h3 : M * p + p * t = (t + M) * p := by ring
      rw [h3]; linarith
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    apply mul_left_cancel₀ hp0
    have hq : ((M * p + p * t : ℕ) : ℚ) * (Nat.choose (M * p - 1 + p * t) (p * t) : ℚ) =
        ((M * p : ℕ) : ℚ) * (Nat.choose ((t + M) * p) (t * p) : ℚ) := by exact_mod_cast hnat
    push_cast at hq ⊢; linarith
  have hrelM : ((M + t : ℕ) : ℚ) * (Nat.choose (M - 1 + t) t : ℚ) =
      (M : ℚ) * (Nat.choose (t + M) t : ℚ) := by
    have hnat : (M + t) * Nat.choose (M - 1 + t) t = M * Nat.choose (t + M) t := by
      have h := Nat.add_one_mul_choose_eq (M - 1 + t) (M - 1)
      have h1 : M - 1 + t + 1 = t + M := by omega
      have h2 : M - 1 + 1 = M := by omega
      have hs1 : Nat.choose (M - 1 + t) (M - 1) = Nat.choose (M - 1 + t) t := by
        have hs := Nat.choose_symm (by omega : t ≤ M - 1 + t)
        rwa [show M - 1 + t - t = M - 1 by omega] at hs
      have hs2 : Nat.choose (t + M) M = Nat.choose (t + M) t := by
        have hs := Nat.choose_symm (by omega : t ≤ t + M)
        rwa [show t + M - t = M by omega] at hs
      rw [h1, h2, hs1, hs2] at h; linarith
    exact_mod_cast hnat
  have hkaz := kazandzidis_ratio p t M hp hp5 ht hM
  have hBpos : (Nat.choose (t + M) t : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hMt0 : ((M + t : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdiff : (Nat.choose (M * p - 1 + p * t) (p * t) : ℚ) - (Nat.choose (M - 1 + t) t : ℚ) =
      (Nat.choose (M - 1 + t) t : ℚ) *
        ((Nat.choose ((t + M) * p) (t * p) : ℚ) / (Nat.choose (t + M) t : ℚ) - 1) := by
    apply mul_left_cancel₀ hMt0
    rw [mul_sub, hrelN, hrelM]
    have hmul : ((M + t : ℕ) : ℚ) * ((Nat.choose (M - 1 + t) t : ℚ) *
        ((Nat.choose ((t + M) * p) (t * p) : ℚ) / (Nat.choose (t + M) t : ℚ) - 1)) =
        ((M + t : ℕ) : ℚ) * (Nat.choose (M - 1 + t) t : ℚ) *
        ((Nat.choose ((t + M) * p) (t * p) : ℚ) / (Nat.choose (t + M) t : ℚ) - 1) := by ring
    rw [hmul, hrelM]
    field_simp [hBpos]
  rw [hdiff]
  have hch_pv : PVal p (vp p M - vp p t) (Nat.choose (M - 1 + t) t : ℚ) :=
    PVal.of_dvd_nat hp (vp_choose_pred_add_ge p M t hp ht (by omega))
  by_cases hlt : vp p t < vp p M
  · have hadd := vp_add_of_lt hp (by omega : t ≠ 0) (by omega : M ≠ 0) hlt
    have hmul := hch_pv.mul hp hkaz
    refine hmul.mono ?_
    rw [hadd]; omega
  · have hmul := (PVal.nat hp (Nat.choose (M - 1 + t) t)).mul hp hkaz
    refine hmul.mono ?_
    have htm_ge : vp p M ≤ vp p (t + M) := by
      apply vp_le_of_dvd hp (by omega)
      exact dvd_add (dvd_trans (Nat.pow_dvd_pow p (by omega)) (vp_dvd hp (by omega : t ≠ 0)))
        (vp_dvd hp (by omega : M ≠ 0))
    omega

/-- Helper: 1-variable finite geometric series 1 / (a * p + s) mod p^K. -/
private lemma inv_lin_geom_series (p K s : ℕ) (a : ℤ) (hp : p.Prime)
    (hs1 : 1 ≤ s) (hsp : s < p) :
    PVal p K ((((a : ℚ) * (p : ℚ) + (s : ℚ)))⁻¹ -
      ∑ i ∈ range K, (-1 : ℚ) ^ i * (a : ℚ) ^ i * (p : ℚ) ^ i / (s : ℚ) ^ (i + 1)) := by
  set u : ℚ := (a : ℚ) * (p : ℚ) / (s : ℚ)
  have hgeom : ∀ m : ℕ, (1 + u) * ∑ i ∈ range m, (-u) ^ i = 1 - (-u) ^ m := by
    intro m; induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
  have hs0 : (s : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnds : ¬ p ∣ s := fun h => by have := Nat.le_of_dvd hs1 h; omega
  have hnd_aps : ¬ (p : ℤ) ∣ (a * (p : ℤ) + (s : ℤ)) := by
    intro h
    have hps : (p : ℤ) ∣ (s : ℤ) := (Int.dvd_add_right (dvd_mul_left (p : ℤ) a)).mp h
    exact hnds (Int.natCast_dvd_natCast.mp hps)
  have haps0 : ((a : ℚ) * (p : ℚ) + (s : ℚ)) ≠ 0 := by
    intro h
    have hz : a * (p : ℤ) + (s : ℤ) = 0 := by exact_mod_cast h
    rw [hz] at hnd_aps; exact hnd_aps (dvd_zero _)
  have hsum_eq : ∑ i ∈ range K, (-1 : ℚ) ^ i * (a : ℚ) ^ i * (p : ℚ) ^ i / (s : ℚ) ^ (i + 1) =
      (s : ℚ)⁻¹ * ∑ i ∈ range K, (-u) ^ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [neg_pow u i]
    simp only [u, div_pow, mul_pow, pow_succ]
    field_simp [hs0]
  have hdiff : ((a : ℚ) * (p : ℚ) + (s : ℚ))⁻¹ -
      ∑ i ∈ range K, (-1 : ℚ) ^ i * (a : ℚ) ^ i * (p : ℚ) ^ i / (s : ℚ) ^ (i + 1) =
      (-u) ^ K / (((a * (p : ℤ) + (s : ℤ) : ℤ) : ℚ)) := by
    rw [hsum_eq]
    have h1u : (s : ℚ) * (1 + u) = (a : ℚ) * (p : ℚ) + (s : ℚ) := by
      simp only [u]; field_simp [hs0]; ring
    have haps_cast : ((a * (p : ℤ) + (s : ℤ) : ℤ) : ℚ) = (a : ℚ) * (p : ℚ) + (s : ℚ) := by
      push_cast; rfl
    rw [haps_cast, eq_div_iff haps0, sub_mul, inv_mul_cancel₀ haps0]
    have hg := hgeom K
    calc 1 - (s : ℚ)⁻¹ * (∑ i ∈ range K, (-u) ^ i) * ((a : ℚ) * (p : ℚ) + (s : ℚ))
        = 1 - (s : ℚ)⁻¹ * (∑ i ∈ range K, (-u) ^ i) * ((s : ℚ) * (1 + u)) := by rw [← h1u]
      _ = 1 - (1 + u) * ∑ i ∈ range K, (-u) ^ i := by field_simp [hs0]
      _ = (-u) ^ K := by rw [hg]; ring
  rw [hdiff]
  have hu_pv : PVal p 1 (-u) := by
    have hnum : PVal p 1 (-(a : ℚ) * (p : ℚ)) := by
      rw [mul_comm]; simpa using (PVal.of_pow_p (e := 1) hp).mul_zero hp (PVal.int hp (-a))
    have heq : -u = (-(a : ℚ) * (p : ℚ)) / (s : ℚ) := by simp only [u]; ring
    rw [heq]; exact hnum.div_nat hp hnds
  have huk : PVal p K ((-u) ^ K) := by simpa using hu_pv.pow hp K
  exact huk.div_int hp hnd_aps

/-- B4: Truncated bivariate geometric series for 1 / ((a*p + s)*(b*p + s)) mod p^K. -/
private lemma inv_bivar_geom_series (p K s : ℕ) (a b : ℤ) (hp : p.Prime)
    (hs1 : 1 ≤ s) (hsp : s < p) :
    PVal p K ((((a : ℚ) * (p : ℚ) + (s : ℚ)) * ((b : ℚ) * (p : ℚ) + (s : ℚ)))⁻¹ -
      ∑ d ∈ range K, (-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
        ∑ i ∈ range (d + 1), (a : ℚ) ^ i * (b : ℚ) ^ (d - i)) := by
  set A : ℚ := ((a : ℚ) * (p : ℚ) + (s : ℚ))⁻¹
  set B : ℚ := ((b : ℚ) * (p : ℚ) + (s : ℚ))⁻¹
  set SA : ℚ := ∑ i ∈ range K, (-1 : ℚ) ^ i * (a : ℚ) ^ i * (p : ℚ) ^ i / (s : ℚ) ^ (i + 1)
  set SB : ℚ := ∑ j ∈ range K, (-1 : ℚ) ^ j * (b : ℚ) ^ j * (p : ℚ) ^ j / (s : ℚ) ^ (j + 1)
  have hA := inv_lin_geom_series p K s a hp hs1 hsp
  have hB := inv_lin_geom_series p K s b hp hs1 hsp
  have hnds : ¬ p ∣ s := fun h => by have := Nat.le_of_dvd hs1 h; omega
  have hA0 : PVal p 0 A := by
    have hnd : ¬ (p : ℤ) ∣ (a * (p : ℤ) + (s : ℤ)) := fun h =>
      hnds (Int.natCast_dvd_natCast.mp ((Int.dvd_add_right (dvd_mul_left (p : ℤ) a)).mp h))
    have heq : A = (1 : ℚ) / (((a * (p : ℤ) + (s : ℤ) : ℤ) : ℚ)) := by
      simp only [A]; push_cast; rw [one_div]
    rw [heq]; exact (PVal.nat hp 1).div_int hp hnd
  have hSB0 : PVal p 0 SB := by
    refine PVal.sum hp fun j _ => ?_
    have hnum : PVal p 0 ((-1 : ℚ) ^ j * (b : ℚ) ^ j * (p : ℚ) ^ j) := by
      have h1 : PVal p 0 ((-1 : ℚ) ^ j) := by simpa using (PVal.int hp (-1)).pow hp j
      have h2 : PVal p 0 ((b : ℚ) ^ j) := by simpa using (PVal.int hp b).pow hp j
      have h3 : PVal p 0 ((p : ℚ) ^ j) := (PVal.of_pow_p hp).mono (Nat.zero_le j)
      exact (h1.mul_zero hp h2).mul_zero hp h3
    have hnd : ¬ p ∣ s ^ (j + 1) := fun h => hnds (hp.dvd_of_dvd_pow h)
    simpa [Nat.cast_pow] using hnum.div_nat hp hnd
  have hAB_SASB : PVal p K (A * B - SA * SB) := by
    have heq : A * B - SA * SB = A * (B - SB) + (A - SA) * SB := by ring
    rw [heq]
    exact (hA0.zero_mul hp hB).add hp (hA.mul_zero hp hSB0)
  -- Split SA * SB into d = i + j < K (matching the target sum) and d = i + j >= K (in p^K Z_(p))
  have hprod_split : SA * SB - ∑ d ∈ range K, (-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
      ∑ i ∈ range (d + 1), (a : ℚ) ^ i * (b : ℚ) ^ (d - i) =
      ∑ i ∈ range K, ∑ j ∈ range K,
        if K ≤ i + j then
          ((-1 : ℚ) ^ i * (a : ℚ) ^ i * (p : ℚ) ^ i / (s : ℚ) ^ (i + 1)) *
          ((-1 : ℚ) ^ j * (b : ℚ) ^ j * (p : ℚ) ^ j / (s : ℚ) ^ (j + 1))
        else 0 := by
    have hmul : SA * SB = ∑ i ∈ range K, ∑ j ∈ range K,
        ((-1 : ℚ) ^ i * (a : ℚ) ^ i * (p : ℚ) ^ i / (s : ℚ) ^ (i + 1)) *
        ((-1 : ℚ) ^ j * (b : ℚ) ^ j * (p : ℚ) ^ j / (s : ℚ) ^ (j + 1)) := by
      simp only [SA, SB, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.mul_sum ..
    have hlow : ∑ d ∈ range K, (-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
        ∑ i ∈ range (d + 1), (a : ℚ) ^ i * (b : ℚ) ^ (d - i) =
        ∑ i ∈ range K, ∑ j ∈ range K,
          if i + j < K then
            ((-1 : ℚ) ^ i * (a : ℚ) ^ i * (p : ℚ) ^ i / (s : ℚ) ^ (i + 1)) *
            ((-1 : ℚ) ^ j * (b : ℚ) ^ j * (p : ℚ) ^ j / (s : ℚ) ^ (j + 1))
          else 0 := by
      have h1 : ∀ d ∈ range K, (-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
          ∑ i ∈ range (d + 1), (a : ℚ) ^ i * (b : ℚ) ^ (d - i) =
          ∑ i ∈ range (d + 1),
            ((-1 : ℚ) ^ i * (a : ℚ) ^ i * (p : ℚ) ^ i / (s : ℚ) ^ (i + 1)) *
            ((-1 : ℚ) ^ (d - i) * (b : ℚ) ^ (d - i) * (p : ℚ) ^ (d - i) / (s : ℚ) ^ (d - i + 1)) := by
        intro d _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [mem_range] at hi
        have hid : i + (d - i) = d := by omega
        have hpow_neg : (-1 : ℚ) ^ i * (-1 : ℚ) ^ (d - i) = (-1 : ℚ) ^ d := by rw [← pow_add, hid]
        have hpow_p : (p : ℚ) ^ i * (p : ℚ) ^ (d - i) = (p : ℚ) ^ d := by rw [← pow_add, hid]
        have hpow_s : (s : ℚ) ^ (i + 1) * (s : ℚ) ^ (d - i + 1) = (s : ℚ) ^ (d + 2) := by
          rw [← pow_add]; congr 1; omega
        rw [div_mul_div_comm, div_mul_eq_mul_div, hpow_s]
        congr 1
        calc (-1 : ℚ) ^ d * (p : ℚ) ^ d * ((a : ℚ) ^ i * (b : ℚ) ^ (d - i))
            = ((-1 : ℚ) ^ i * (-1 : ℚ) ^ (d - i)) * ((p : ℚ) ^ i * (p : ℚ) ^ (d - i)) *
              ((a : ℚ) ^ i * (b : ℚ) ^ (d - i)) := by rw [hpow_neg, hpow_p]
          _ = ((-1 : ℚ) ^ i * (a : ℚ) ^ i * (p : ℚ) ^ i) *
              ((-1 : ℚ) ^ (d - i) * (b : ℚ) ^ (d - i) * (p : ℚ) ^ (d - i)) := by ring
      rw [Finset.sum_congr rfl h1]
      set F : ℕ → ℕ → ℚ := fun i j =>
        ((-1 : ℚ) ^ i * (a : ℚ) ^ i * (p : ℚ) ^ i / (s : ℚ) ^ (i + 1)) *
        ((-1 : ℚ) ^ j * (b : ℚ) ^ j * (p : ℚ) ^ j / (s : ℚ) ^ (j + 1))
      have hsig : ∑ d ∈ range K, ∑ i ∈ range (d + 1), F i (d - i) =
          ∑ y ∈ (range K).sigma (fun d => range (d + 1)), F y.2 (y.1 - y.2) :=
        Finset.sum_sigma' (range K) (fun d => range (d + 1)) (fun d i => F i (d - i))
      have hprod : ∑ i ∈ range K, ∑ j ∈ range K, (if i + j < K then F i j else 0) =
          ∑ x ∈ (range K ×ˢ range K).filter (fun x => x.1 + x.2 < K), F x.1 x.2 := by
        rw [← Finset.sum_product', ← Finset.sum_filter]
      change ∑ d ∈ range K, ∑ i ∈ range (d + 1), F i (d - i) =
        ∑ i ∈ range K, ∑ j ∈ range K, (if i + j < K then F i j else 0)
      rw [hsig, hprod]
      symm
      refine Finset.sum_bij (fun x _ => (⟨x.1 + x.2, x.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
      · intro x hx; rw [mem_filter, mem_product, mem_range, mem_range] at hx
        rw [mem_sigma, mem_range, mem_range]; dsimp; omega
      · intro x₁ hx₁ x₂ hx₂ heq
        simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
        ext <;> omega
      · rintro ⟨d, i⟩ hy; rw [mem_sigma, mem_range, mem_range] at hy; dsimp at hy
        refine ⟨(i, d - i), ?_, ?_⟩
        · rw [mem_filter, mem_product, mem_range, mem_range]; dsimp; omega
        · exact Sigma.ext (by dsimp; omega) (heq_of_eq rfl)
      · intro x _
        simp only [Nat.add_sub_cancel_left]
    rw [hmul, hlow, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i + j < K
    · simp [hij, show ¬ K ≤ i + j by omega]
    · simp [hij, show K ≤ i + j by omega]
  have htail : PVal p K (SA * SB - ∑ d ∈ range K, (-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
      ∑ i ∈ range (d + 1), (a : ℚ) ^ i * (b : ℚ) ^ (d - i)) := by
    rw [hprod_split]
    refine PVal.sum hp fun i _ => PVal.sum hp fun j _ => ?_
    split_ifs with hij
    · have h1 : PVal p i ((-1 : ℚ) ^ i * (a : ℚ) ^ i * (p : ℚ) ^ i / (s : ℚ) ^ (i + 1)) := by
        have hs1i : PVal p 0 ((-1 : ℚ) ^ i) := by simpa using (PVal.int hp (-1)).pow hp i
        have ha1i : PVal p 0 ((a : ℚ) ^ i) := by simpa using (PVal.int hp a).pow hp i
        have hc : PVal p 0 ((-1 : ℚ) ^ i * (a : ℚ) ^ i) := hs1i.mul_zero hp ha1i
        have hnum := hc.zero_mul hp (PVal.of_pow_p (e := i) hp)
        have hnd : ¬ p ∣ s ^ (i + 1) := fun h => hnds (hp.dvd_of_dvd_pow h)
        simpa [Nat.cast_pow, mul_assoc] using hnum.div_nat hp hnd
      have h2 : PVal p j ((-1 : ℚ) ^ j * (b : ℚ) ^ j * (p : ℚ) ^ j / (s : ℚ) ^ (j + 1)) := by
        have hs1j : PVal p 0 ((-1 : ℚ) ^ j) := by simpa using (PVal.int hp (-1)).pow hp j
        have hb1j : PVal p 0 ((b : ℚ) ^ j) := by simpa using (PVal.int hp b).pow hp j
        have hc : PVal p 0 ((-1 : ℚ) ^ j * (b : ℚ) ^ j) := hs1j.mul_zero hp hb1j
        have hnum := hc.zero_mul hp (PVal.of_pow_p (e := j) hp)
        have hnd : ¬ p ∣ s ^ (j + 1) := fun h => hnds (hp.dvd_of_dvd_pow h)
        simpa [Nat.cast_pow, mul_assoc] using hnum.div_nat hp hnd
      exact (h1.mul hp h2).mono hij
    · exact PVal.zero hp
  have hfin := hAB_SASB.add hp htail
  have heq_inv : (((a : ℚ) * (p : ℚ) + (s : ℚ)) * ((b : ℚ) * (p : ℚ) + (s : ℚ)))⁻¹ = A * B := by
    simp only [A, B, mul_inv]
  rw [heq_inv]
  have hrew : A * B - ∑ d ∈ range K, (-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
      ∑ i ∈ range (d + 1), (a : ℚ) ^ i * (b : ℚ) ^ (d - i) =
      (A * B - SA * SB) + (SA * SB - ∑ d ∈ range K, (-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
        ∑ i ∈ range (d + 1), (a : ℚ) ^ i * (b : ℚ) ^ (d - i)) := by ring
  rw [hrew]
  exact hfin

-- ============================================================================
-- Block C: Proof of (P1): a(n * p^r) == a(n * p^(r - 1)) [MOD p^(3*r)], p >= 5
-- ============================================================================

private lemma choose_sq_div_supercong (p M r m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 1 ≤ r) (hM : p ^ (r - 1) ∣ M) (hMpos : 1 ≤ M) (hm : m ≤ M) :
    PVal p (3 * r) ((Nat.choose (M * p) (p * m) : ℚ) ^ 2 - (Nat.choose M m : ℚ) ^ 2) := by
  by_cases hm0 : m = 0
  · subst hm0; simpa using PVal.zero hp
  by_cases hmM : m = M
  · rw [hmM, mul_comm p M, Nat.choose_self, Nat.choose_self]; simpa using PVal.zero hp
  have hm1 : 1 ≤ m := by omega
  have hMm1 : 1 ≤ M - m := by omega
  have hvpM : r - 1 ≤ vp p M := vp_le_of_dvd hp (by omega) hM
  have hkaz := kazandzidis_ratio p m (M - m) hp hp5 hm1 hMm1
  rw [Nat.add_sub_of_le hm] at hkaz
  have hB0 : (Nat.choose M m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hm).ne'
  set u : ℚ := (Nat.choose (M * p) (p * m) : ℚ)
  set v : ℚ := (Nat.choose M m : ℚ)
  have hdiff : u - v = v * ((Nat.choose (M * p) (m * p) : ℚ) / (Nat.choose M m : ℚ) - 1) := by
    have hpm : p * m = m * p := mul_comm p m
    simp only [u, v, hpm]; rw [mul_sub, mul_one, mul_div_cancel₀ _ hB0]
  have hsq : u ^ 2 - v ^ 2 = (u - v) * (2 * v + (u - v)) := by ring
  rw [hsq]
  have hv_dvd := vp_choose_ge p M m hp hm1 hm (by omega)
  have hv_pv : PVal p (vp p M - vp p m) v := PVal.of_dvd_nat hp hv_dvd
  by_cases hlt : vp p m < vp p M
  · have hvp_sub : vp p (M - m) = vp p m := by
      have hsum : m + (M - m) = M := Nat.add_sub_of_le hm
      have hle1 : vp p m ≤ vp p (M - m) := by
        apply vp_le_of_dvd hp (by omega)
        have h1 : p ^ vp p m ∣ M := dvd_trans (Nat.pow_dvd_pow p (Nat.le_of_lt hlt)) (vp_dvd hp (by omega))
        have h2 : p ^ vp p m ∣ m := vp_dvd hp (by omega)
        have h3 := Nat.dvd_sub h1 h2
        exact h3
      by_contra hne
      have hgt : vp p m < vp p (M - m) := by omega
      have hvp_eq := vp_add_of_lt hp (by omega : m ≠ 0) (by omega : M - m ≠ 0) hgt
      rw [hsum] at hvp_eq; omega
    have huv : PVal p (3 + 2 * vp p M + vp p m) (u - v) := by
      rw [hdiff]
      have hmul := hv_pv.mul hp hkaz
      refine hmul.mono ?_
      rw [hvp_sub]; omega
    have h2v : PVal p (vp p M - vp p m) (2 * v + (u - v)) :=
      ((PVal.nat hp 2).zero_mul hp hv_pv).add hp (huv.mono (by omega))
    exact (huv.mul hp h2v).mono (by omega)
  · have hvp_sub : vp p M ≤ vp p (M - m) := by
      apply vp_le_of_dvd hp (by omega)
      have h1 : p ^ vp p M ∣ M := vp_dvd hp (by omega)
      have h2 : p ^ vp p M ∣ m := dvd_trans (Nat.pow_dvd_pow p (by omega)) (vp_dvd hp (by omega))
      exact Nat.dvd_sub h1 h2
    have huv : PVal p (3 * r) (u - v) := by
      rw [hdiff]
      exact ((PVal.nat hp _).zero_mul hp hkaz).mono (by omega)
    have h0 : PVal p 0 (2 * v + (u - v)) :=
      ((PVal.nat hp 2).zero_mul hp (PVal.nat hp _)).add hp (huv.mono (Nat.zero_le _))
    exact huv.mul_zero hp h0

private lemma vp_mul_three {p n : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : n ≠ 0) :
    vp p (3 * n) = vp p n := by
  have h3n : 3 * n ≠ 0 := by omega
  have hcop : Nat.Coprime p 3 := hp.coprime_iff_not_dvd.mpr (by intro h; have := Nat.le_of_dvd (by decide) h; omega)
  apply le_antisymm
  · exact vp_le_of_dvd hp hn ((hcop.pow_left _).dvd_of_dvd_mul_left (vp_dvd hp h3n))
  · exact vp_le_of_dvd hp h3n (dvd_mul_of_dvd_right (vp_dvd hp hn) 3)

/-- C1: Divisible-index terms of Q-rep match term-by-term modulo p^(3*r). -/
private lemma part1_div_term (p M r m₁ m₂ m₃ : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 1 ≤ r) (hM : p ^ (r - 1) ∣ M) (hMpos : 1 ≤ M) (ht : m₁ + m₂ + m₃ ≤ M) :
    PVal p (3 * r)
      ((Nat.choose (4 * (M * p) - (p * m₁ + p * m₂ + p * m₃)) (M * p - (p * m₁ + p * m₂ + p * m₃)) : ℚ) *
        (Nat.choose (M * p) (p * m₁) : ℚ) ^ 2 * (Nat.choose (M * p) (p * m₂) : ℚ) ^ 2 *
        (Nat.choose (M * p) (p * m₃) : ℚ) ^ 2 -
       (Nat.choose (4 * M - (m₁ + m₂ + m₃)) (M - (m₁ + m₂ + m₃)) : ℚ) *
        (Nat.choose M m₁ : ℚ) ^ 2 * (Nat.choose M m₂ : ℚ) ^ 2 * (Nat.choose M m₃ : ℚ) ^ 2) := by
  set t := m₁ + m₂ + m₃
  set A0 : ℚ := (Nat.choose (4 * (M * p) - (p * m₁ + p * m₂ + p * m₃)) (M * p - (p * m₁ + p * m₂ + p * m₃)) : ℚ)
  set B0 : ℚ := (Nat.choose (4 * M - t) (M - t) : ℚ)
  set A1 : ℚ := (Nat.choose (M * p) (p * m₁) : ℚ) ^ 2
  set A2 : ℚ := (Nat.choose (M * p) (p * m₂) : ℚ) ^ 2
  set A3 : ℚ := (Nat.choose (M * p) (p * m₃) : ℚ) ^ 2
  set B1 : ℚ := (Nat.choose M m₁ : ℚ) ^ 2
  set B2 : ℚ := (Nat.choose M m₂ : ℚ) ^ 2
  set B3 : ℚ := (Nat.choose M m₃ : ℚ) ^ 2
  have h1 := choose_sq_div_supercong p M r m₁ hp hp5 hr hM hMpos (by omega)
  have h2 := choose_sq_div_supercong p M r m₂ hp hp5 hr hM hMpos (by omega)
  have h3 := choose_sq_div_supercong p M r m₃ hp hp5 hr hM hMpos (by omega)
  have hA123 : PVal p (3 * r) (A1 * A2 * A3 - B1 * B2 * B3) := by
    have heq : A1 * A2 * A3 - B1 * B2 * B3 =
        (A1 - B1) * A2 * A3 + B1 * (A2 - B2) * A3 + B1 * B2 * (A3 - B3) := by ring
    rw [heq]
    have hA20 : PVal p 0 A2 := by simpa [A2] using (PVal.nat hp _).pow hp 2
    have hA30 : PVal p 0 A3 := by simpa [A3] using (PVal.nat hp _).pow hp 2
    have hB10 : PVal p 0 B1 := by simpa [B1] using (PVal.nat hp _).pow hp 2
    have hB20 : PVal p 0 B2 := by simpa [B2] using (PVal.nat hp _).pow hp 2
    exact (((h1.mul_zero hp hA20).mul_zero hp hA30).add hp
      ((hB10.zero_mul hp h2).mul_zero hp hA30)).add hp ((hB10.mul_zero hp hB20).zero_mul hp h3)
  have hA0B : PVal p (3 * r) ((A0 - B0) * (B1 * B2 * B3)) := by
    by_cases htM : t = M
    · have hA0_eq : A0 = 1 := by
        simp only [A0]
        have hpm : p * m₁ + p * m₂ + p * m₃ = M * p := by rw [← htM]; simp only [t]; ring
        rw [hpm, Nat.sub_self, Nat.choose_zero_right]; norm_num
      have hB0_eq : B0 = 1 := by
        simp only [B0]; rw [show M - t = 0 by omega, Nat.choose_zero_right]; norm_num
      rw [hA0_eq, hB0_eq, sub_self, zero_mul]; exact PVal.zero hp
    · set b := M - t
      have hb1 : 1 ≤ b := by omega
      have h3M1 : 1 ≤ 3 * M := by omega
      have hkaz := kazandzidis_ratio p b (3 * M) hp hp5 hb1 h3M1
      have hA0_eq : A0 = (Nat.choose ((b + 3 * M) * p) (b * p) : ℚ) := by
        simp only [A0]
        have hpm : p * m₁ + p * m₂ + p * m₃ = p * t := by simp only [t]; ring
        have h1 : 4 * (M * p) - (p * m₁ + p * m₂ + p * m₃) = (b + 3 * M) * p := by
          rw [hpm]; simp only [b]
          zify [show p * t ≤ 4 * (M * p) by nlinarith, show t ≤ M by omega]; ring
        have h2 : M * p - (p * m₁ + p * m₂ + p * m₃) = b * p := by
          rw [hpm]; simp only [b]
          zify [show p * t ≤ M * p by nlinarith, show t ≤ M by omega]; ring
        rw [h1, h2]
      have hB0_eq : B0 = (Nat.choose (b + 3 * M) b : ℚ) := by
        simp only [B0]; congr 2; omega
      have hB0_ne : (Nat.choose (b + 3 * M) b : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
      have hdiff0 : A0 - B0 = (Nat.choose (b + 3 * M) b : ℚ) *
          ((Nat.choose ((b + 3 * M) * p) (b * p) : ℚ) / (Nat.choose (b + 3 * M) b : ℚ) - 1) := by
        rw [hA0_eq, hB0_eq]; field_simp [hB0_ne]
      have hvpM : r - 1 ≤ vp p M := vp_le_of_dvd hp (by omega) hM
      have hvp3M : vp p (3 * M) = vp p M := vp_mul_three hp hp5 (by omega)
      have hA0_diff : PVal p (3 + vp p b + vp p M + vp p (b + 3 * M)) (A0 - B0) := by
        rw [hdiff0]
        have h := (PVal.nat hp (Nat.choose (b + 3 * M) b)).zero_mul hp hkaz
        rwa [hvp3M] at h
      by_cases hlt : vp p b < vp p M
      · have hvp_add : vp p (b + 3 * M) = vp p b :=
          vp_add_of_lt hp (by omega) (by omega) (by rw [hvp3M]; exact hlt)
        have hA0' : PVal p (3 + vp p M + 2 * vp p b) (A0 - B0) := by
          refine hA0_diff.mono ?_; rw [hvp_add]; omega
        -- Some m_i has m_i >= 1 and vp p m_i <= vp p b
        have hex : (1 ≤ m₁ ∧ vp p m₁ ≤ vp p b) ∨ (1 ≤ m₂ ∧ vp p m₂ ≤ vp p b) ∨ (1 ≤ m₃ ∧ vp p m₃ ≤ vp p b) := by
          by_contra hnot
          push Not at hnot
          have hd : ∀ x, (x = 0 ∨ vp p b < vp p x) → p ^ (vp p b + 1) ∣ x := by
            intro x hx
            rcases hx with rfl | hgt
            · exact dvd_zero _
            · exact dvd_trans (Nat.pow_dvd_pow p hgt) (vp_dvd hp (by intro h0; subst h0; simp [vp] at hgt))
          have hd1 : p ^ (vp p b + 1) ∣ m₁ := hd m₁ (by by_cases h0 : m₁ = 0; left; exact h0; right; exact hnot.1 (by omega))
          have hd2 : p ^ (vp p b + 1) ∣ m₂ := hd m₂ (by by_cases h0 : m₂ = 0; left; exact h0; right; exact hnot.2.1 (by omega))
          have hd3 : p ^ (vp p b + 1) ∣ m₃ := hd m₃ (by by_cases h0 : m₃ = 0; left; exact h0; right; exact hnot.2.2 (by omega))
          have hdt : p ^ (vp p b + 1) ∣ t := dvd_add (dvd_add hd1 hd2) hd3
          have hdM : p ^ (vp p b + 1) ∣ M := dvd_trans (Nat.pow_dvd_pow p hlt) (vp_dvd hp (by omega))
          have hdb : p ^ (vp p b + 1) ∣ b := Nat.dvd_sub hdM hdt
          exact vp_succ_not_dvd hp (by omega) hdb
        have hB123 : PVal p (2 * (vp p M - vp p b)) (B1 * B2 * B3) := by
          have hB10 : PVal p 0 B1 := by simpa [B1] using (PVal.nat hp _).pow hp 2
          have hB20 : PVal p 0 B2 := by simpa [B2] using (PVal.nat hp _).pow hp 2
          have hB30 : PVal p 0 B3 := by simpa [B3] using (PVal.nat hp _).pow hp 2
          rcases hex with ⟨hm1, hvp1⟩ | ⟨hm2, hvp2⟩ | ⟨hm3, hvp3⟩
          · have hsq1 : PVal p (2 * (vp p M - vp p b)) B1 := by
              have hc := (PVal.of_dvd_nat hp (vp_choose_ge p M m₁ hp hm1 (by omega) (by omega))).pow hp 2
              exact hc.mono (by omega)
            exact (hsq1.mul_zero hp hB20).mul_zero hp hB30
          · have hsq2 : PVal p (2 * (vp p M - vp p b)) B2 := by
              have hc := (PVal.of_dvd_nat hp (vp_choose_ge p M m₂ hp hm2 (by omega) (by omega))).pow hp 2
              exact hc.mono (by omega)
            exact (hB10.zero_mul hp hsq2).mul_zero hp hB30
          · have hsq3 : PVal p (2 * (vp p M - vp p b)) B3 := by
              have hc := (PVal.of_dvd_nat hp (vp_choose_ge p M m₃ hp hm3 (by omega) (by omega))).pow hp 2
              exact hc.mono (by omega)
            exact (hB10.mul_zero hp hB20).zero_mul hp hsq3
        exact (hA0'.mul hp hB123).mono (by omega)
      · have hvp_add : vp p M ≤ vp p (b + 3 * M) := by
          apply vp_le_of_dvd hp (by omega)
          exact dvd_add (dvd_trans (Nat.pow_dvd_pow p (by omega)) (vp_dvd hp (by omega)))
            (dvd_mul_of_dvd_right (vp_dvd hp (by omega)) 3)
        have hB1230 : PVal p 0 (B1 * B2 * B3) :=
          ((by simpa [B1] using (PVal.nat hp _).pow hp 2 : PVal p 0 B1).mul_zero hp
            (by simpa [B2] using (PVal.nat hp _).pow hp 2 : PVal p 0 B2)).mul_zero hp
            (by simpa [B3] using (PVal.nat hp _).pow hp 2 : PVal p 0 B3)
        exact ((hA0_diff.mono (by omega)).mul_zero hp hB1230)
  have hcomb : A0 * A1 * A2 * A3 - B0 * B1 * B2 * B3 =
      A0 * (A1 * A2 * A3 - B1 * B2 * B3) + (A0 - B0) * (B1 * B2 * B3) := by ring
  rw [hcomb]
  exact ((PVal.nat hp _).zero_mul hp hA123).add hp hA0B

/-- C2: Inductive moment-sum lemma for (P1). -/
private lemma part1_moment_sum_dvd (p m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ M L : ℕ, 1 ≤ M → 1 ≤ L → p ^ m ∣ M → p ^ m ∣ L →
      ((p : ℤ) ^ m ∣ ∑ q ∈ range L, (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℤ) *
        (Nat.choose (M - 1) q : ℤ) ^ 2) ∧
      (∀ d : ℕ, 1 ≤ d →
        (p : ℤ) ^ (m + 1) ∣ (p : ℤ) ^ d * ∑ q ∈ range L,
          (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℤ) * (Nat.choose (M - 1) q : ℤ) ^ 2 * (q : ℤ) ^ d) := by
  induction m with
  | zero =>
    intro M L _ _ _ _
    constructor
    · simp
    · intro d hd
      rw [zero_add, pow_one]
      exact dvd_mul_of_dvd_left (dvd_pow_self (p : ℤ) (by omega)) _
  | succ m ih =>
    intro M L hMpos hLpos hMd hLd
    have hp_dvd_M : p ∣ M := dvd_trans (dvd_pow_self p (by omega)) hMd
    have hp_dvd_L : p ∣ L := dvd_trans (dvd_pow_self p (by omega)) hLd
    obtain ⟨M', hM'eq⟩ := hp_dvd_M
    obtain ⟨L', hL'eq⟩ := hp_dvd_L
    have hM_eq : M = M' * p := by linarith
    have hL_eq : L = L' * p := by linarith
    have hM'pos : 1 ≤ M' := by nlinarith [hp.pos]
    have hL'pos : 1 ≤ L' := by nlinarith [hp.pos]
    have hM'd : p ^ m ∣ M' := by
      have h1 : p * p ^ m ∣ p * M' := by rw [← pow_succ', ← hM'eq]; exact hMd
      exact (Nat.mul_dvd_mul_iff_left hp.pos).mp h1
    have hL'd : p ^ m ∣ L' := by
      have h1 : p * p ^ m ∣ p * L' := by rw [← pow_succ', ← hL'eq]; exact hLd
      exact (Nat.mul_dvd_mul_iff_left hp.pos).mp h1
    have ⟨ih0, ihd⟩ := ih M' L' hM'pos hL'pos hM'd hL'd
    have hpodd : p ≠ 2 := by omega
    -- Weight congruence mod p^(m+1) for q = a*p + b
    have hwt : ∀ a < L', ∀ b < p,
        (Nat.choose (3 * M + L - 1 - (a * p + b)) (L - 1 - (a * p + b)) : ℤ) *
          (Nat.choose (M - 1) (a * p + b) : ℤ) ^ 2 ≡
        (Nat.choose (3 * M' + L' - 1 - a) (L' - 1 - a) : ℤ) *
          (Nat.choose (M' - 1) a : ℤ) ^ 2 [ZMOD (p : ℤ) ^ (m + 1)] := by
      intro a ha b hb
      have h1 : (Nat.choose (3 * M + L - 1 - (a * p + b)) (L - 1 - (a * p + b)) : ℤ) ≡
          (Nat.choose (3 * M' + L' - 1 - a) (L' - 1 - a) : ℤ) [ZMOD (p : ℤ) ^ (m + 1)] := by
        have h3M : p ^ (m + 1) ∣ (3 * M') * p := by
          have : (3 * M') * p = 3 * M := by rw [hM_eq]; ring
          rw [this]; exact dvd_mul_of_dvd_right hMd 3
        have hsh := choose_shift_mod_pow p (3 * M') (m + 1) (L' - 1 - a) (p - 1 - b) hp h3M (by omega)
        have heq1 : L - 1 - (a * p + b) = (L' - 1 - a) * p + (p - 1 - b) := by
          have hle1 : a * p + b + 1 ≤ L' * p := by
            have : (a + 1) * p ≤ L' * p := Nat.mul_le_mul_right p (by omega)
            linarith
          rw [hL_eq]; zify [show a * p + b ≤ L' * p - 1 by omega, show 1 ≤ L' * p by omega,
            show a ≤ L' - 1 by omega, show 1 ≤ L' by omega, show b ≤ p - 1 by omega, show 1 ≤ p by omega]
          ring
        have heq2 : 3 * M + L - 1 - (a * p + b) = (3 * M') * p + ((L' - 1 - a) * p + (p - 1 - b)) := by
          have hle1 : a * p + b + 1 ≤ L' * p := by
            have : (a + 1) * p ≤ L' * p := Nat.mul_le_mul_right p (by omega)
            linarith
          rw [hM_eq, hL_eq]; zify [show a * p + b ≤ 3 * (M' * p) + L' * p - 1 by omega,
            show 1 ≤ 3 * (M' * p) + L' * p by omega, show a ≤ L' - 1 by omega,
            show 1 ≤ L' by omega, show b ≤ p - 1 by omega, show 1 ≤ p by omega]; ring
        have heq3 : 3 * M' + L' - 1 - a = 3 * M' + (L' - 1 - a) := by omega
        rw [heq2, heq1, heq3]; exact hsh
      have h2 : (Nat.choose (M - 1) (a * p + b) : ℤ) ^ 2 ≡
          (Nat.choose (M' - 1) a : ℤ) ^ 2 [ZMOD (p : ℤ) ^ (m + 1)] := by
        by_cases haM' : a < M'
        · have hpr := choose_pred_mod_pow p M' (m + 1) a b hp hpodd (by rw [← hM_eq]; exact hMd) haM' hb
          rw [← hM_eq] at hpr
          have hsq := hpr.pow 2
          have hs1 : ((-1 : ℤ) ^ b * (Nat.choose (M' - 1) a : ℤ)) ^ 2 = (Nat.choose (M' - 1) a : ℤ) ^ 2 := by
            rw [mul_pow, ← pow_mul, mul_comm b 2, pow_mul]; norm_num
          rwa [hs1] at hsq
        · have h0a : Nat.choose (M' - 1) a = 0 := Nat.choose_eq_zero_of_lt (by omega)
          have hleM : M' * p ≤ a * p := Nat.mul_le_mul_right p (by omega)
          have h0q : Nat.choose (M - 1) (a * p + b) = 0 := Nat.choose_eq_zero_of_lt (by rw [hM_eq]; omega)
          rw [h0a, h0q]
      exact h1.mul h2
    set g : ℕ → ℤ := fun a =>
      (Nat.choose (3 * M' + L' - 1 - a) (L' - 1 - a) : ℤ) * (Nat.choose (M' - 1) a : ℤ) ^ 2
    constructor
    · -- Part (1)
      have hcong : ∑ q ∈ range L, (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℤ) *
            (Nat.choose (M - 1) q : ℤ) ^ 2 ≡
          (p : ℤ) * ∑ a ∈ range L', g a [ZMOD (p : ℤ) ^ (m + 1)] := by
        rw [hL_eq, sum_range_mul_eq L' p]
        calc ∑ a ∈ range L', ∑ b ∈ range p,
              (Nat.choose (3 * M + L' * p - 1 - (a * p + b)) (L' * p - 1 - (a * p + b)) : ℤ) *
                (Nat.choose (M - 1) (a * p + b) : ℤ) ^ 2
            ≡ ∑ a ∈ range L', ∑ _b ∈ range p, g a [ZMOD (p : ℤ) ^ (m + 1)] := by
              refine Int.ModEq.sum fun a ha => Int.ModEq.sum fun b hb => ?_
              rw [mem_range] at ha hb
              simpa only [← hL_eq, g] using hwt a ha b hb
          _ = (p : ℤ) * ∑ a ∈ range L', g a := by
              simp [Finset.sum_const, Finset.mul_sum]
      have hdvd_rhs : (p : ℤ) ^ (m + 1) ∣ (p : ℤ) * ∑ a ∈ range L', g a := by
        rw [pow_succ']; exact mul_dvd_mul_left (p : ℤ) ih0
      have hdiff : (p : ℤ) ^ (m + 1) ∣
          ((p : ℤ) * ∑ a ∈ range L', g a) -
          ∑ q ∈ range L, (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℤ) * (Nat.choose (M - 1) q : ℤ) ^ 2 :=
        Int.modEq_iff_dvd.mp hcong
      exact dvd_sub hdvd_rhs hdiff |> fun h => by simpa using h
    · -- Part (2)
      intro d hd
      have hcong_m : ∑ q ∈ range L, (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℤ) *
            (Nat.choose (M - 1) q : ℤ) ^ 2 * (q : ℤ) ^ d ≡
          ∑ a ∈ range L', ∑ b ∈ range p, g a * ((a * p + b : ℕ) : ℤ) ^ d [ZMOD (p : ℤ) ^ (m + 1)] := by
        rw [hL_eq, sum_range_mul_eq L' p]
        refine Int.ModEq.sum fun a ha => Int.ModEq.sum fun b hb => ?_
        rw [mem_range] at ha hb
        have h1 : (Nat.choose (3 * M + L' * p - 1 - (a * p + b)) (L' * p - 1 - (a * p + b)) : ℤ) *
            (Nat.choose (M - 1) (a * p + b) : ℤ) ^ 2 ≡ g a [ZMOD (p : ℤ) ^ (m + 1)] := by
          simpa only [← hL_eq, g] using hwt a ha b hb
        exact h1.mul_right _
      have hcong_mul : (p : ℤ) ^ d * ∑ q ∈ range L, (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℤ) *
            (Nat.choose (M - 1) q : ℤ) ^ 2 * (q : ℤ) ^ d ≡
          (p : ℤ) ^ d * ∑ a ∈ range L', ∑ b ∈ range p, g a * ((a * p + b : ℕ) : ℤ) ^ d
            [ZMOD (p : ℤ) ^ (m + 2)] := by
        have h1 : (p : ℤ) ^ (m + 1) ∣
            (∑ a ∈ range L', ∑ b ∈ range p, g a * ((a * p + b : ℕ) : ℤ) ^ d) -
            (∑ q ∈ range L, (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℤ) *
              (Nat.choose (M - 1) q : ℤ) ^ 2 * (q : ℤ) ^ d) := Int.modEq_iff_dvd.mp hcong_m
        have h2 : (p : ℤ) ^ (m + 1 + d) ∣ (p : ℤ) ^ d *
            ((∑ a ∈ range L', ∑ b ∈ range p, g a * ((a * p + b : ℕ) : ℤ) ^ d) -
             (∑ q ∈ range L, (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℤ) *
              (Nat.choose (M - 1) q : ℤ) ^ 2 * (q : ℤ) ^ d)) := by
          rw [pow_add, mul_comm ((p : ℤ) ^ (m + 1))]
          exact mul_dvd_mul_left _ h1
        have h3 : (p : ℤ) ^ (m + 2) ∣ (p : ℤ) ^ (m + 1 + d) := pow_dvd_pow (p : ℤ) (by omega)
        exact Int.modEq_iff_dvd.mpr (by simpa [mul_sub] using dvd_trans h3 h2)
      have hbin : (p : ℤ) ^ d * ∑ a ∈ range L', ∑ b ∈ range p, g a * ((a * p + b : ℕ) : ℤ) ^ d =
          ∑ j ∈ range (d + 1), (Nat.choose d j : ℤ) * (p : ℤ) ^ d *
            (∑ b ∈ range p, (b : ℤ) ^ (d - j)) *
            ((p : ℤ) ^ j * ∑ a ∈ range L', g a * (a : ℤ) ^ j) := by
        have hexp : ∀ a b : ℕ, ((a * p + b : ℕ) : ℤ) ^ d =
            ∑ j ∈ range (d + 1), (Nat.choose d j : ℤ) * (b : ℤ) ^ (d - j) * ((p : ℤ) ^ j * (a : ℤ) ^ j) := by
          intro a b
          have h := add_pow ((a : ℤ) * (p : ℤ)) (b : ℤ) d
          push_cast; rw [h]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_pow]; ring
        calc (p : ℤ) ^ d * ∑ a ∈ range L', ∑ b ∈ range p, g a * ((a * p + b : ℕ) : ℤ) ^ d
            = ∑ a ∈ range L', ∑ b ∈ range p, ∑ j ∈ range (d + 1),
              (p : ℤ) ^ d * (g a * ((Nat.choose d j : ℤ) * (b : ℤ) ^ (d - j) * ((p : ℤ) ^ j * (a : ℤ) ^ j))) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [hexp, Finset.mul_sum, Finset.mul_sum]
          _ = ∑ a ∈ range L', ∑ j ∈ range (d + 1), ∑ b ∈ range p,
              (p : ℤ) ^ d * (g a * ((Nat.choose d j : ℤ) * (b : ℤ) ^ (d - j) * ((p : ℤ) ^ j * (a : ℤ) ^ j))) :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ j ∈ range (d + 1), ∑ a ∈ range L', ∑ b ∈ range p,
              (p : ℤ) ^ d * (g a * ((Nat.choose d j : ℤ) * (b : ℤ) ^ (d - j) * ((p : ℤ) ^ j * (a : ℤ) ^ j))) :=
              Finset.sum_comm
          _ = ∑ j ∈ range (d + 1), (Nat.choose d j : ℤ) * (p : ℤ) ^ d *
              (∑ b ∈ range p, (b : ℤ) ^ (d - j)) *
              ((p : ℤ) ^ j * ∑ a ∈ range L', g a * (a : ℤ) ^ j) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_comm]
              symm
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun a _ => ?_
              ring
      have hdvd_rhs : (p : ℤ) ^ (m + 2) ∣
          (p : ℤ) ^ d * ∑ a ∈ range L', ∑ b ∈ range p, g a * ((a * p + b : ℕ) : ℤ) ^ d := by
        rw [hbin]
        refine Finset.dvd_sum fun j _ => ?_
        by_cases hj : 1 ≤ j
        · have h1 := ihd j hj
          have h2 : (p : ℤ) ^ 1 ∣ (p : ℤ) ^ d := pow_dvd_pow (p : ℤ) hd
          have h3 : (p : ℤ) ^ 1 * (p : ℤ) ^ (m + 1) ∣
              ((Nat.choose d j : ℤ) * (p : ℤ) ^ d * ∑ b ∈ range p, (b : ℤ) ^ (d - j)) *
              ((p : ℤ) ^ j * ∑ a ∈ range L', g a * (a : ℤ) ^ j) := by
            refine mul_dvd_mul ?_ h1
            exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h2 _) _
          rwa [← pow_add, show 1 + (m + 1) = m + 2 by omega] at h3
        · have hj0 : j = 0 := by omega
          subst hj0
          simp only [Nat.sub_zero, pow_zero, mul_one, one_mul, Nat.choose_zero_right, Nat.cast_one]
          by_cases hd2 : 2 ≤ d
          · have h2 : (p : ℤ) ^ 2 ∣ (p : ℤ) ^ d := pow_dvd_pow (p : ℤ) hd2
            have h3 : (p : ℤ) ^ 2 * (p : ℤ) ^ m ∣
                ((p : ℤ) ^ d * ∑ b ∈ range p, (b : ℤ) ^ d) * ∑ a ∈ range L', g a :=
              mul_dvd_mul (dvd_mul_of_dvd_left h2 _) ih0
            rwa [← pow_add, show 2 + m = m + 2 by omega] at h3
          · have hd1 : d = 1 := by omega
            subst hd1
            simp only [pow_one]
            have hsum_b := p_dvd_sum_range_id p hp hp5
            have h3 : (p : ℤ) * (p : ℤ) * (p : ℤ) ^ m ∣
                ((p : ℤ) * ∑ b ∈ range p, (b : ℤ)) * ∑ a ∈ range L', g a :=
              mul_dvd_mul (mul_dvd_mul_left (p : ℤ) hsum_b) ih0
            have hexp : (p : ℤ) * (p : ℤ) * (p : ℤ) ^ m = (p : ℤ) ^ (m + 2) := by
              rw [show m + 2 = 1 + 1 + m by omega, pow_add, pow_add, pow_one]
            rwa [hexp] at h3
      have hdiff := Int.modEq_iff_dvd.mp hcong_mul
      exact dvd_sub hdvd_rhs hdiff |> fun h => by simpa using h

/-- C3: 1-non-divisible bucket vanishes per fixed (m2, m3) modulo p^(3*r). -/
private lemma part1_ndiv1_pair (p M r m₂ m₃ : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 1 ≤ r) (hM : p ^ (r - 1) ∣ M) (hMpos : 1 ≤ M) (hm23 : m₂ + m₃ < M) :
    PVal p (3 * r)
      ((Nat.choose (M * p) (p * m₂) : ℚ) ^ 2 * (Nat.choose (M * p) (p * m₃) : ℚ) ^ 2 *
        ∑ k ∈ (range (M * p - p * (m₂ + m₃) + 1)).filter (fun k => ¬ p ∣ k),
          (Nat.choose (4 * (M * p) - (p * (m₂ + m₃) + k)) (M * p - (p * (m₂ + m₃) + k)) : ℚ) *
            (Nat.choose (M * p) k : ℚ) ^ 2) := by
  set N := M * p
  set L := M - m₂ - m₃
  have hLpos : 1 ≤ L := by omega
  have hN_dvd : p ^ r ∣ N := by
    have : p ^ (r - 1) * p ∣ M * p := Nat.mul_dvd_mul_right hM p
    rwa [← pow_succ, Nat.sub_add_cancel hr] at this
  have hNpos : 1 ≤ N := Nat.mul_pos hMpos hp.pos
  have hvpN : r ≤ vp p N := vp_le_of_dvd hp (by omega) hN_dvd
  have hvpM : r - 1 ≤ vp p M := vp_le_of_dvd hp (by omega) hM
  set m := min (r - 1) (vp p L)
  have hm_le : m ≤ r - 1 := min_le_left _ _
  have hm_M : p ^ m ∣ M := dvd_trans (Nat.pow_dvd_pow p hm_le) hM
  have hm_L : p ^ m ∣ L := dvd_trans (Nat.pow_dvd_pow p (min_le_right _ _)) (vp_dvd hp (by omega))
  -- Outer factor valuation >= r - 1 - m
  have houter : PVal p (r - 1 - m) ((Nat.choose N (p * m₂) : ℚ) ^ 2 * (Nat.choose N (p * m₃) : ℚ) ^ 2) := by
    by_cases hmr : m = r - 1
    · rw [hmr, Nat.sub_self]
      exact (by simpa using (PVal.nat hp _).pow hp 2 : PVal p 0 _).mul_zero hp
        (by simpa using (PVal.nat hp _).pow hp 2)
    · have hvpL_lt : vp p L < r - 1 := by omega
      have hm_eq : m = vp p L := min_eq_right (Nat.le_of_lt hvpL_lt)
      have hex : (1 ≤ m₂ ∧ vp p m₂ ≤ m) ∨ (1 ≤ m₃ ∧ vp p m₃ ≤ m) := by
        by_contra hnot; push Not at hnot
        have hd : ∀ x, (x = 0 ∨ m < vp p x) → p ^ (m + 1) ∣ x := by
          intro x hx; rcases hx with rfl | hgt
          · exact dvd_zero _
          · exact dvd_trans (Nat.pow_dvd_pow p hgt) (vp_dvd hp (by intro h0; subst h0; simp [vp] at hgt))
        have hd2 := hd m₂ (by by_cases h0 : m₂ = 0; left; exact h0; right; exact hnot.1 (by omega))
        have hd3 := hd m₃ (by by_cases h0 : m₃ = 0; left; exact h0; right; exact hnot.2 (by omega))
        have hdM : p ^ (m + 1) ∣ M := dvd_trans (Nat.pow_dvd_pow p (by omega)) hM
        have hdL : p ^ (m + 1) ∣ L := by
          rw [show L = M - (m₂ + m₃) by omega]
          exact Nat.dvd_sub hdM (dvd_add hd2 hd3)
        rw [hm_eq] at hdL
        exact vp_succ_not_dvd hp (by omega) hdL
      have hvp_pm : ∀ x, 1 ≤ x → vp p (p * x) = vp p x + 1 := by
        intro x hx
        have hpx : p * x ≠ 0 := (Nat.mul_pos hp.pos hx).ne'
        have h1 : p ^ (vp p x + 1) ∣ p * x := by rw [pow_succ']; exact Nat.mul_dvd_mul_left p (vp_dvd hp (by omega))
        have h2 : ¬ p ^ (vp p x + 2) ∣ p * x := by
          intro h; rw [show vp p x + 2 = (vp p x + 1) + 1 by omega, pow_succ'] at h
          exact vp_succ_not_dvd hp (by omega) ((Nat.mul_dvd_mul_iff_left hp.pos).mp h)
        have hle := vp_le_of_dvd hp hpx h1
        by_contra hne
        have hgt : vp p x + 2 ≤ vp p (p * x) := by omega
        exact h2 (dvd_trans (Nat.pow_dvd_pow p hgt) (vp_dvd hp hpx))
      rcases hex with ⟨h1, hv1⟩ | ⟨h1, hv1⟩
      · have hpm2_le : p * m₂ ≤ N := by
          simpa [N, mul_comm] using Nat.mul_le_mul_left p (by omega : m₂ ≤ M)
        have hc := (PVal.of_dvd_nat hp (vp_choose_ge p N (p * m₂) hp (Nat.mul_pos hp.pos h1) hpm2_le (by omega))).pow hp 2
        have h30 : PVal p 0 ((Nat.choose N (p * m₃) : ℚ) ^ 2) := by
          simpa using (PVal.nat hp (Nat.choose N (p * m₃))).pow hp 2
        have h2 := hc.mul_zero hp h30
        refine h2.mono ?_; rw [hvp_pm m₂ h1]; omega
      · have hpm3_le : p * m₃ ≤ N := by
          simpa [N, mul_comm] using Nat.mul_le_mul_left p (by omega : m₃ ≤ M)
        have hc := (PVal.of_dvd_nat hp (vp_choose_ge p N (p * m₃) hp (Nat.mul_pos hp.pos h1) hpm3_le (by omega))).pow hp 2
        have h20 : PVal p 0 ((Nat.choose N (p * m₂) : ℚ) ^ 2) := by
          simpa using (PVal.nat hp (Nat.choose N (p * m₂))).pow hp 2
        have h2 := h20.zero_mul hp hc
        refine h2.mono ?_; rw [hvp_pm m₃ h1]; omega
  -- Now show inner sum lies in p^(2*r + m + 1) Z_(p)
  have hinner : PVal p (2 * r + m + 1)
      (∑ k ∈ (range (M * p - p * (m₂ + m₃) + 1)).filter (fun k => ¬ p ∣ k),
        (Nat.choose (4 * N - (p * (m₂ + m₃) + k)) (N - (p * (m₂ + m₃) + k)) : ℚ) *
          (Nat.choose N k : ℚ) ^ 2) := by
    have hfilt : (range (M * p - p * (m₂ + m₃) + 1)).filter (fun k => ¬ p ∣ k) =
        (range (L * p)).filter (fun k => ¬ p ∣ k) := by
      have hLp : M * p - p * (m₂ + m₃) = L * p := by
        simp only [L]
        rw [Nat.sub_mul, Nat.sub_mul, Nat.mul_add, mul_comm p m₂, mul_comm p m₃]
        omega
      rw [hLp]
      ext k; simp only [mem_filter, mem_range]
      constructor
      · intro ⟨hk, hnd⟩
        refine ⟨?_, hnd⟩
        by_contra hge
        have heq : k = L * p := by omega
        exact hnd (heq ▸ dvd_mul_left p L)
      · intro ⟨hk, hnd⟩; exact ⟨by omega, hnd⟩
    rw [hfilt, sum_filter_not_dvd_range_mul L p hp]
    -- Approximate each term by N^2 * C(3*M + L - 1 - q, L - 1 - q) * C(M - 1, q)^2 / (q*p + s)^2 mod p^(3*r)
    set target : ℕ → ℕ → ℚ := fun q s =>
      (N : ℚ) ^ 2 * (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ) *
        (Nat.choose (M - 1) q : ℚ) ^ 2 * (((q * p + s : ℕ) : ℚ) ^ 2)⁻¹
    have hstep1 : PVal p (2 * r + m + 1)
        ((∑ q ∈ range L, ∑ s ∈ Ico 1 p,
          (Nat.choose (4 * N - (p * (m₂ + m₃) + (q * p + s))) (N - (p * (m₂ + m₃) + (q * p + s))) : ℚ) *
            (Nat.choose N (q * p + s) : ℚ) ^ 2) -
         (∑ q ∈ range L, ∑ s ∈ Ico 1 p, target q s)) := by
      rw [← Finset.sum_sub_distrib]
      refine PVal.sum hp fun q hq => ?_
      rw [← Finset.sum_sub_distrib]
      refine PVal.sum hp fun s hs => ?_
      rw [mem_range] at hq; rw [mem_Ico] at hs
      have hqM : q < M := by omega
      have hpodd : p ≠ 2 := by omega
      have hfac := choose_ndiv_exact p M q s hp hpodd hqM hs.1 hs.2
      set j := q * p + s
      set P : ℚ := ∏ i ∈ (Ico 1 j).filter (fun i => ¬ p ∣ i), (1 - (N : ℚ) / (i : ℚ))
      have hP_sub : PVal p r (P - 1) := by
        have h1 : PVal p r ((∏ i ∈ (Ico 1 j).filter (fun i => ¬ p ∣ i),
            (1 + (-(N : ℚ) / (i : ℚ)))) - 1) := by
          refine PVal.prod_one_add hp fun i hi => ?_
          exact (PVal.of_dvd_nat hp hN_dvd).neg.div_nat hp (Finset.mem_filter.mp hi).2
        convert h1 using 3 with i _; ring
      have hP2_sub : PVal p r (P ^ 2 - 1) := by
        have heq : P ^ 2 - 1 = (P - 1) * ((P - 1) + 2) := by ring
        rw [heq]
        exact hP_sub.mul_zero hp ((hP_sub.mono (Nat.zero_le _)).add hp (PVal.nat hp 2))
      have hndj : ¬ p ∣ j := fun h => by
        have hps := (Nat.dvd_add_right (dvd_mul_left p q)).mp h
        have := Nat.le_of_dvd hs.1 hps; omega
      have hsq_approx : PVal p (3 * r)
          ((Nat.choose N j : ℚ) ^ 2 - (N : ℚ) ^ 2 * (Nat.choose (M - 1) q : ℚ) ^ 2 * ((j : ℚ) ^ 2)⁻¹) := by
        have hsq_eq : (Nat.choose N j : ℚ) ^ 2 =
            ((N : ℚ) ^ 2 * (Nat.choose (M - 1) q : ℚ) ^ 2 * ((j : ℚ) ^ 2)⁻¹) * P ^ 2 := by
          have hfac' : (Nat.choose N j : ℚ) =
              (-1 : ℚ) ^ (s - 1) * ((N : ℚ) / (j : ℚ)) * (Nat.choose (M - 1) q : ℚ) * P := by
            simpa only [N, j, P, Nat.cast_mul] using hfac
          have hneg : ((-1 : ℚ) ^ (s - 1)) ^ 2 = 1 := by
            rw [← pow_mul, mul_comm (s - 1) 2, pow_mul]; norm_num
          rw [hfac', mul_pow, mul_pow, mul_pow, hneg, div_pow, div_eq_mul_inv]; ring
        have hdiff : (Nat.choose N j : ℚ) ^ 2 - (N : ℚ) ^ 2 * (Nat.choose (M - 1) q : ℚ) ^ 2 * ((j : ℚ) ^ 2)⁻¹ =
            ((N : ℚ) ^ 2 * (Nat.choose (M - 1) q : ℚ) ^ 2 * ((j : ℚ) ^ 2)⁻¹) * (P ^ 2 - 1) := by
          rw [hsq_eq]; ring
        rw [hdiff]
        have hbase : PVal p (2 * r) ((N : ℚ) ^ 2 * (Nat.choose (M - 1) q : ℚ) ^ 2 * ((j : ℚ) ^ 2)⁻¹) := by
          have hN2 : PVal p (2 * r) ((N : ℚ) ^ 2) := by simpa [mul_comm] using (PVal.of_dvd_nat hp hN_dvd).pow hp 2
          have hch : PVal p 0 ((Nat.choose (M - 1) q : ℚ) ^ 2) := by simpa using (PVal.nat hp _).pow hp 2
          have hj2 : PVal p 0 (((j : ℚ) ^ 2)⁻¹) := by
            simpa [Nat.cast_pow] using PVal.inv_nat (fun h => hndj (hp.dvd_of_dvd_pow h))
          exact (hN2.mul_zero hp hch).mul_zero hp hj2
        exact (hbase.mul hp hP2_sub).mono (by omega)
      have hsh : PVal p r
          ((Nat.choose (4 * N - (p * (m₂ + m₃) + j)) (N - (p * (m₂ + m₃) + j)) : ℚ) -
           (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ)) := by
        have h3N : p ^ r ∣ (3 * M) * p := by
          have : (3 * M) * p = 3 * N := by simp only [N]; ring
          rw [this]; exact dvd_mul_of_dvd_right hN_dvd 3
        have hcm := choose_shift_mod_pow p (3 * M) r (L - 1 - q) (p - s) hp h3N (by omega)
        have hleN : p * (m₂ + m₃) + (q * p + s) ≤ M * p := by
          have h1 : (m₂ + m₃ + q + 1) * p ≤ M * p := Nat.mul_le_mul_right p (by omega)
          have h2 : p * (m₂ + m₃) + (q * p + s) < (m₂ + m₃ + q + 1) * p := by nlinarith
          omega
        have heq1 : N - (p * (m₂ + m₃) + j) = (L - 1 - q) * p + (p - s) := by
          simp only [N, L, j]
          zify [hleN, show q ≤ M - m₂ - m₃ - 1 by omega, show m₂ + m₃ ≤ M by omega,
            show m₂ ≤ M by omega, show m₃ ≤ M - m₂ by omega, show 1 ≤ M - m₂ - m₃ by omega,
            show s ≤ p by omega]; ring
        have heq2 : 4 * N - (p * (m₂ + m₃) + j) = (3 * M) * p + ((L - 1 - q) * p + (p - s)) := by
          simp only [N, L, j]
          zify [show p * (m₂ + m₃) + (q * p + s) ≤ 4 * (M * p) by omega,
            show q ≤ M - m₂ - m₃ - 1 by omega, show m₂ + m₃ ≤ M by omega,
            show m₂ ≤ M by omega, show m₃ ≤ M - m₂ by omega, show 1 ≤ M - m₂ - m₃ by omega,
            show s ≤ p by omega]; ring
        have heq3 : 3 * M + L - 1 - q = 3 * M + (L - 1 - q) := by omega
        rw [heq2, heq1, heq3]
        have hdvd := Int.modEq_iff_dvd.mp hcm
        have h1 := (PVal.of_dvd_int hp hdvd).neg
        convert h1 using 1; push_cast; ring
      have hbase_pv : PVal p (2 * r) ((N : ℚ) ^ 2 * (Nat.choose (M - 1) q : ℚ) ^ 2 * ((j : ℚ) ^ 2)⁻¹) := by
        have hN2 : PVal p (2 * r) ((N : ℚ) ^ 2) := by simpa [mul_comm] using (PVal.of_dvd_nat hp hN_dvd).pow hp 2
        have hch : PVal p 0 ((Nat.choose (M - 1) q : ℚ) ^ 2) := by simpa using (PVal.nat hp _).pow hp 2
        have hj2 : PVal p 0 (((j : ℚ) ^ 2)⁻¹) := by
          simpa [Nat.cast_pow] using PVal.inv_nat (fun h => hndj (hp.dvd_of_dvd_pow h))
        exact (hN2.mul_zero hp hch).mul_zero hp hj2
      set X1 : ℚ := (Nat.choose (4 * N - (p * (m₂ + m₃) + j)) (N - (p * (m₂ + m₃) + j)) : ℚ)
      set X2 : ℚ := (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ)
      set Y1 : ℚ := (Nat.choose N j : ℚ) ^ 2
      set Y2 : ℚ := (N : ℚ) ^ 2 * (Nat.choose (M - 1) q : ℚ) ^ 2 * ((j : ℚ) ^ 2)⁻¹
      have hsplit : X1 * Y1 - target q s = X1 * (Y1 - Y2) + (X1 - X2) * Y2 := by
        simp only [target, X2, Y2, j]; ring
      rw [hsplit]
      have ht1 : PVal p (3 * r) (X1 * (Y1 - Y2)) := (PVal.nat hp _).zero_mul hp hsq_approx
      have ht2 : PVal p (3 * r) ((X1 - X2) * Y2) := (hsh.mul hp hbase_pv).mono (by omega)
      exact (ht1.add hp ht2).mono (by omega)
    -- Step 2: Expand 1/(q*p + s)^2 up to m+1 terms via inv_bivar_geom_series and apply part1_moment_sum_dvd
    have hstep2 : PVal p (2 * r + m + 1) (∑ q ∈ range L, ∑ s ∈ Ico 1 p, target q s) := by
      set ser : ℕ → ℕ → ℚ := fun q s =>
        ∑ d ∈ range (m + 1), (-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
          ∑ _i ∈ range (d + 1), (q : ℚ) ^ d
      have happrox : PVal p (2 * r + m + 1)
          ((∑ q ∈ range L, ∑ s ∈ Ico 1 p, target q s) -
           (∑ q ∈ range L, ∑ s ∈ Ico 1 p,
             (N : ℚ) ^ 2 * (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ) *
               (Nat.choose (M - 1) q : ℚ) ^ 2 * ser q s)) := by
        rw [← Finset.sum_sub_distrib]
        refine PVal.sum hp fun q _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine PVal.sum hp fun s hs => ?_
        rw [mem_Ico] at hs
        have hgeom := inv_bivar_geom_series p (m + 1) s (q : ℤ) (q : ℤ) hp hs.1 hs.2
        have hgeom' : PVal p (m + 1) ((((q * p + s : ℕ) : ℚ) ^ 2)⁻¹ - ser q s) := by
          convert hgeom using 2
          · push_cast; ring
          · refine Finset.sum_congr rfl fun d _ => ?_
            congr 1
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [mem_range] at hi
            push_cast; rw [← pow_add, Nat.add_sub_of_le (by omega)]
        have hN2 : PVal p (2 * r) ((N : ℚ) ^ 2 * (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ) *
            (Nat.choose (M - 1) q : ℚ) ^ 2) := by
          have h1 : PVal p (2 * r) ((N : ℚ) ^ 2) := by simpa [mul_comm] using (PVal.of_dvd_nat hp hN_dvd).pow hp 2
          have h2 : PVal p 0 ((Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ)) := PVal.nat hp _
          have h3 : PVal p 0 ((Nat.choose (M - 1) q : ℚ) ^ 2) := by simpa using (PVal.nat hp _).pow hp 2
          exact (h1.mul_zero hp h2).mul_zero hp h3
        have hsub : target q s - (N : ℚ) ^ 2 * (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ) *
            (Nat.choose (M - 1) q : ℚ) ^ 2 * ser q s =
            ((N : ℚ) ^ 2 * (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ) *
              (Nat.choose (M - 1) q : ℚ) ^ 2) * ((((q * p + s : ℕ) : ℚ) ^ 2)⁻¹ - ser q s) := by
          simp only [target]; ring
        rw [hsub]
        exact (hN2.mul hp hgeom').mono (by omega)
      have hser_zero : PVal p (2 * r + m + 1)
          (∑ q ∈ range L, ∑ s ∈ Ico 1 p,
            (N : ℚ) ^ 2 * (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ) *
              (Nat.choose (M - 1) q : ℚ) ^ 2 * ser q s) := by
        -- Swap sums to outer d in range (m + 1)
        have hswap : ∑ q ∈ range L, ∑ s ∈ Ico 1 p,
              (N : ℚ) ^ 2 * (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ) *
                (Nat.choose (M - 1) q : ℚ) ^ 2 * ser q s =
            ∑ d ∈ range (m + 1),
              (N : ℚ) ^ 2 * ((-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ)) *
              (∑ s ∈ Ico 1 p, ((s : ℚ) ^ (d + 2))⁻¹) *
              ((p : ℚ) ^ d * ∑ q ∈ range L,
                (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ) *
                (Nat.choose (M - 1) q : ℚ) ^ 2 * (q : ℚ) ^ d) := by
          simp only [ser, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          calc ∑ q ∈ range L, ∑ s ∈ Ico 1 p,
                (N : ℚ) ^ 2 * (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ) *
                  (Nat.choose (M - 1) q : ℚ) ^ 2 *
                  ∑ d ∈ range (m + 1), (-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
                    (((d + 1 : ℕ) : ℚ) * (q : ℚ) ^ d)
              = ∑ q ∈ range L, ∑ d ∈ range (m + 1), ∑ s ∈ Ico 1 p,
                (N : ℚ) ^ 2 * (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ) *
                  (Nat.choose (M - 1) q : ℚ) ^ 2 *
                  ((-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) * (((d + 1 : ℕ) : ℚ) * (q : ℚ) ^ d)) := by
                refine Finset.sum_congr rfl fun q _ => ?_
                simp_rw [Finset.mul_sum]
                exact Finset.sum_comm
            _ = ∑ d ∈ range (m + 1), ∑ q ∈ range L, ∑ s ∈ Ico 1 p,
                (N : ℚ) ^ 2 * (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ) *
                  (Nat.choose (M - 1) q : ℚ) ^ 2 *
                  ((-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) * (((d + 1 : ℕ) : ℚ) * (q : ℚ) ^ d)) :=
                Finset.sum_comm
            _ = ∑ d ∈ range (m + 1),
                (N : ℚ) ^ 2 * ((-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ)) *
                (∑ s ∈ Ico 1 p, ((s : ℚ) ^ (d + 2))⁻¹) *
                ((p : ℚ) ^ d * ∑ q ∈ range L,
                  (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ) *
                  (Nat.choose (M - 1) q : ℚ) ^ 2 * (q : ℚ) ^ d) := by
                refine Finset.sum_congr rfl fun d _ => ?_
                symm
                rw [Finset.mul_sum, Finset.sum_mul]
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun s _ => ?_
                rw [Finset.mul_sum, Finset.mul_sum]
                refine Finset.sum_congr rfl fun q _ => ?_
                rw [div_eq_mul_inv]; ring
        rw [hswap]
        have ⟨hm0, hmd⟩ := part1_moment_sum_dvd p m hp hp5 M L hMpos hLpos hm_M hm_L
        refine PVal.sum hp fun d _ => ?_
        have hN2 : PVal p (2 * r) ((N : ℚ) ^ 2) := by simpa [mul_comm] using (PVal.of_dvd_nat hp hN_dvd).pow hp 2
        have hc0 : PVal p 0 ((-1 : ℚ) ^ d * ((d + 1 : ℕ) : ℚ)) :=
          (by simpa using (PVal.int hp (-1)).pow hp d : PVal p 0 _).mul_zero hp (PVal.nat hp _)
        by_cases hd0 : d = 0
        · subst hd0
          have hs2 := sum_inv_sq_mod_p p hp hp5
          have hq0 : PVal p m ((p : ℚ) ^ 0 * ∑ q ∈ range L,
              (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ) * (Nat.choose (M - 1) q : ℚ) ^ 2 * (q : ℚ) ^ 0) := by
            simpa using PVal.of_dvd_int hp hm0
          exact (((hN2.mul_zero hp hc0).mul hp hs2).mul hp hq0).mono (by omega)
        · have hs_pv : PVal p 0 (∑ s ∈ Ico 1 p, ((s : ℚ) ^ (d + 2))⁻¹) := by
            refine PVal.sum hp fun s hs => ?_
            rw [mem_Ico] at hs
            have hnds : ¬ p ∣ s ^ (d + 2) := fun h => by
              have h1 := hp.dvd_of_dvd_pow h; have := Nat.le_of_dvd hs.1 h1; omega
            simpa [Nat.cast_pow] using PVal.inv_nat hnds
          have hqd : PVal p (m + 1) ((p : ℚ) ^ d * ∑ q ∈ range L,
              (Nat.choose (3 * M + L - 1 - q) (L - 1 - q) : ℚ) * (Nat.choose (M - 1) q : ℚ) ^ 2 * (q : ℚ) ^ d) := by
            simpa using PVal.of_dvd_int hp (hmd d (by omega))
          exact (((hN2.mul_zero hp hc0).mul_zero hp hs_pv).mul hp hqd).mono (by omega)
      have hfin := happrox.add hp hser_zero
      simpa using hfin
    have hfin := hstep1.add hp hstep2
    simpa using hfin
  exact (houter.mul hp hinner).mono (by omega)

/-- C4 (Theorem P1): a(n * p^r) == a(n * p^(r - 1)) [MOD p^(3*r)] for prime p >= 5, n > 0, r > 0. -/
private lemma part1_main (p n r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    Nat.ModEq (p ^ (3 * r)) (OMA.S_oeis_a364114.a (n * p ^ r)) (OMA.S_oeis_a364114.a (n * p ^ (r - 1))) := by
  set M := n * p ^ (r - 1)
  have hMpos : 1 ≤ M := Nat.mul_pos hn (Nat.pow_pos hp.pos)
  have hM_dvd : p ^ (r - 1) ∣ M := ⟨n, by simp [M, mul_comm]⟩
  have hN_eq : n * p ^ r = M * p := by
    simp only [M, mul_assoc, ← pow_succ]; rw [Nat.sub_add_cancel hr]
  rw [hN_eq]
  set N := M * p
  have hN_dvd : p ^ r ∣ N := by
    have : p ^ (r - 1) * p ∣ M * p := Nat.mul_dvd_mul_right hM_dvd p
    rwa [← pow_succ, Nat.sub_add_cancel hr] at this
  set fN : ℕ → ℕ → ℕ → ℚ := fun k₁ k₂ k₃ =>
    if k₁ + k₂ + k₃ ≤ N then
      (Nat.choose (4 * N - (k₁ + k₂ + k₃)) (N - (k₁ + k₂ + k₃)) : ℚ) *
        (Nat.choose N k₁ : ℚ) ^ 2 * (Nat.choose N k₂ : ℚ) ^ 2 * (Nat.choose N k₃ : ℚ) ^ 2
    else 0
  set fM : ℕ → ℕ → ℕ → ℚ := fun m₁ m₂ m₃ =>
    if m₁ + m₂ + m₃ ≤ M then
      (Nat.choose (4 * M - (m₁ + m₂ + m₃)) (M - (m₁ + m₂ + m₃)) : ℚ) *
        (Nat.choose M m₁ : ℚ) ^ 2 * (Nat.choose M m₂ : ℚ) ^ 2 * (Nat.choose M m₃ : ℚ) ^ 2
    else 0
  -- Cast Q-rep to Q
  have hQN : (OMA.S_oeis_a364114.a N : ℚ) =
      ∑ k₁ ∈ range (N + 1), ∑ k₂ ∈ range (N + 1), ∑ k₃ ∈ range (N + 1), fN k₁ k₂ k₃ := by
    have h := congrArg (Int.cast : ℤ → ℚ) (a_eq_Q_rep N)
    simp only [Int.cast_natCast, Int.cast_sum] at h
    rw [h]
    refine Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ =>
      Finset.sum_congr rfl fun k₃ _ => ?_
    simp only [fN]; split_ifs <;> push_cast <;> rfl
  have hQM : (OMA.S_oeis_a364114.a M : ℚ) =
      ∑ m₁ ∈ range (M + 1), ∑ m₂ ∈ range (M + 1), ∑ m₃ ∈ range (M + 1), fM m₁ m₂ m₃ := by
    have h := congrArg (Int.cast : ℤ → ℚ) (a_eq_Q_rep M)
    simp only [Int.cast_natCast, Int.cast_sum] at h
    rw [h]
    refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ =>
      Finset.sum_congr rfl fun m₃ _ => ?_
    simp only [fM]; split_ifs <;> push_cast <;> rfl
  -- Split each range (N + 1) into p | k and ¬ p | k
  have hsplit_range : ∀ g : ℕ → ℚ,
      ∑ k ∈ range (N + 1), g k =
        (∑ m ∈ range (M + 1), g (p * m)) + ∑ k ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), g k := by
    intro g
    rw [← Finset.sum_filter_add_sum_filter_not (range (N + 1)) (fun k => p ∣ k)]
    congr 1
    have h1 : (range (N + 1)).filter (fun k => p ∣ k) = insert N ((range N).filter (fun k => p ∣ k)) := by
      rw [Finset.range_add_one, Finset.filter_insert]
      have hd : p ∣ N := dvd_mul_left p M
      simp [hd]
    rw [h1, Finset.sum_insert (by simp), sum_filter_dvd_range_mul M p hp, Finset.sum_range_succ, mul_comm p M]
    ring
  -- Helper: any triple with at least two non-divisible indices has PVal p (3*r)
  have hndiv2_pv : ∀ k₁ k₂ k₃, ¬ p ∣ k₁ → ¬ p ∣ k₂ → PVal p (3 * r) (fN k₁ k₂ k₃) := by
    intro k₁ k₂ k₃ hnd1 hnd2
    simp only [fN]
    split_ifs with hle
    · have hk1 : 1 ≤ k₁ := Nat.pos_of_ne_zero fun h0 => hnd1 (h0 ▸ dvd_zero p)
      have hk2 : 1 ≤ k₂ := Nat.pos_of_ne_zero fun h0 => hnd2 (h0 ▸ dvd_zero p)
      have hvp1 : vp p k₁ = 0 := by
        by_contra hne
        exact hnd1 (dvd_trans (dvd_pow_self p hne) (vp_dvd hp (by omega)))
      have hvp2 : vp p k₂ = 0 := by
        by_contra hne
        exact hnd2 (dvd_trans (dvd_pow_self p hne) (vp_dvd hp (by omega)))
      have hNne : N ≠ 0 := (Nat.mul_pos hMpos hp.pos).ne'
      have hc1 : PVal p (2 * r) ((Nat.choose N k₁ : ℚ) ^ 2) := by
        have h := (PVal.of_dvd_nat hp (vp_choose_ge p N k₁ hp hk1 (by omega) hNne)).pow hp 2
        rw [hvp1, Nat.sub_zero] at h
        exact h.mono (by have := vp_le_of_dvd hp hNne hN_dvd; omega)
      have hc2 : PVal p (2 * r) ((Nat.choose N k₂ : ℚ) ^ 2) := by
        have h := (PVal.of_dvd_nat hp (vp_choose_ge p N k₂ hp hk2 (by omega) hNne)).pow hp 2
        rw [hvp2, Nat.sub_zero] at h
        exact h.mono (by have := vp_le_of_dvd hp hNne hN_dvd; omega)
      have hch0 : PVal p 0 (Nat.choose (4 * N - (k₁ + k₂ + k₃)) (N - (k₁ + k₂ + k₃)) : ℚ) := PVal.nat hp _
      have hc3 : PVal p 0 ((Nat.choose N k₃ : ℚ) ^ 2) := by simpa using (PVal.nat hp _).pow hp 2
      have hmul := ((hch0.zero_mul hp hc1).mul hp hc2).mul_zero hp hc3
      exact hmul.mono (by omega)
    · exact PVal.zero hp
  -- Symmetry of fN in its 3 arguments
  have hsym12 : ∀ a b c, fN a b c = fN b a c := by
    intro a b c; simp only [fN, show a + b + c = b + a + c by omega]; split_ifs <;> ring
  have hsym13 : ∀ a b c, fN a b c = fN c b a := by
    intro a b c; simp only [fN, show a + b + c = c + b + a by omega]; split_ifs <;> ring
  -- Single non-divisible bucket in first slot vanishes mod p^(3*r)
  have hndiv1_slot1 : PVal p (3 * r)
      (∑ k₁ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k),
        ∑ m₂ ∈ range (M + 1), ∑ m₃ ∈ range (M + 1), fN k₁ (p * m₂) (p * m₃)) := by
    rw [Finset.sum_comm]
    refine PVal.sum hp fun m₂ hm₂ => ?_
    rw [Finset.sum_comm]
    refine PVal.sum hp fun m₃ hm₃ => ?_
    by_cases hlt : m₂ + m₃ < M
    · have hp_pair := part1_ndiv1_pair p M r m₂ m₃ hp hp5 hr hM_dvd hMpos hlt
      have hpm23_le : p * (m₂ + m₃) ≤ N := by
        simpa [N, mul_comm] using Nat.mul_le_mul_left p (by omega : m₂ + m₃ ≤ M)
      have heq : ∑ k₁ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN k₁ (p * m₂) (p * m₃) =
          (Nat.choose N (p * m₂) : ℚ) ^ 2 * (Nat.choose N (p * m₃) : ℚ) ^ 2 *
          ∑ k ∈ (range (N - p * (m₂ + m₃) + 1)).filter (fun k => ¬ p ∣ k),
            (Nat.choose (4 * N - (p * (m₂ + m₃) + k)) (N - (p * (m₂ + m₃) + k)) : ℚ) *
              (Nat.choose N k : ℚ) ^ 2 := by
        rw [Finset.mul_sum]
        have hsub : (range (N - p * (m₂ + m₃) + 1)).filter (fun k => ¬ p ∣ k) ⊆
            (range (N + 1)).filter (fun k => ¬ p ∣ k) := by
          intro k hk; rw [mem_filter, mem_range] at hk ⊢; exact ⟨by omega, hk.2⟩
        rw [← Finset.sum_subset hsub]
        · refine Finset.sum_congr rfl fun k hk => ?_
          rw [mem_filter, mem_range] at hk
          have hle : k + p * m₂ + p * m₃ ≤ N := by
            have : p * m₂ + p * m₃ = p * (m₂ + m₃) := by ring
            omega
          simp only [fN, show k + p * m₂ + p * m₃ = p * (m₂ + m₃) + k by ring]
          rw [if_pos (by omega)]
          ring
        · intro k hk hnot
          rw [mem_filter, mem_range] at hk hnot
          have hgt : ¬ k + p * m₂ + p * m₃ ≤ N := by
            intro hle
            have : p * m₂ + p * m₃ = p * (m₂ + m₃) := by ring
            apply hnot; exact ⟨by omega, hk.2⟩
          simp [fN, hgt]
      rw [heq]; exact hp_pair
    · have hzero : ∑ k₁ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN k₁ (p * m₂) (p * m₃) = 0 := by
        refine Finset.sum_eq_zero fun k₁ hk₁ => ?_
        rw [mem_filter] at hk₁
        have hk1_pos : 1 ≤ k₁ := Nat.pos_of_ne_zero fun h0 => hk₁.2 (h0 ▸ dvd_zero p)
        have hgt : ¬ k₁ + p * m₂ + p * m₃ ≤ N := by simp only [N]; nlinarith [hp.pos]
        simp [fN, hgt]
      rw [hzero]; exact PVal.zero hp
  -- Divisible bucket matches a(M) mod p^(3*r)
  have hdiv_diff : PVal p (3 * r)
      ((∑ m₁ ∈ range (M + 1), ∑ m₂ ∈ range (M + 1), ∑ m₃ ∈ range (M + 1), fN (p * m₁) (p * m₂) (p * m₃)) -
       (∑ m₁ ∈ range (M + 1), ∑ m₂ ∈ range (M + 1), ∑ m₃ ∈ range (M + 1), fM m₁ m₂ m₃)) := by
    rw [← Finset.sum_sub_distrib]
    refine PVal.sum hp fun m₁ _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine PVal.sum hp fun m₂ _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine PVal.sum hp fun m₃ _ => ?_
    by_cases ht : m₁ + m₂ + m₃ ≤ M
    · have hpt : p * m₁ + p * m₂ + p * m₃ ≤ N := by simp only [N]; nlinarith [hp.pos]
      simp only [fN, fM, ht, hpt, ↓reduceIte]
      exact part1_div_term p M r m₁ m₂ m₃ hp hp5 hr hM_dvd hMpos ht
    · have hpt : ¬ p * m₁ + p * m₂ + p * m₃ ≤ N := by simp only [N]; nlinarith [hp.pos]
      simp only [fN, fM, ht, hpt, ↓reduceIte, sub_self]
      exact PVal.zero hp
  -- Combine all 8 octants of the 3-fold split
  have hdecomp_N : (OMA.S_oeis_a364114.a N : ℚ) =
      (∑ m₁ ∈ range (M + 1), ∑ m₂ ∈ range (M + 1), ∑ m₃ ∈ range (M + 1), fN (p * m₁) (p * m₂) (p * m₃)) +
      (∑ k₁ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ m₂ ∈ range (M + 1), ∑ m₃ ∈ range (M + 1), fN k₁ (p * m₂) (p * m₃)) +
      (∑ m₁ ∈ range (M + 1), ∑ k₂ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ m₃ ∈ range (M + 1), fN (p * m₁) k₂ (p * m₃)) +
      (∑ m₁ ∈ range (M + 1), ∑ m₂ ∈ range (M + 1), ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN (p * m₁) (p * m₂) k₃) +
      (∑ k₁ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ k₂ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ m₃ ∈ range (M + 1), fN k₁ k₂ (p * m₃)) +
      (∑ k₁ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ m₂ ∈ range (M + 1), ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN k₁ (p * m₂) k₃) +
      (∑ m₁ ∈ range (M + 1), ∑ k₂ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN (p * m₁) k₂ k₃) +
      (∑ k₁ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ k₂ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN k₁ k₂ k₃) := by
    rw [hQN, hsplit_range]
    simp_rw [hsplit_range, Finset.sum_add_distrib]
    ring
  have hdecomp : (OMA.S_oeis_a364114.a N : ℚ) - (OMA.S_oeis_a364114.a M : ℚ) =
      ((∑ m₁ ∈ range (M + 1), ∑ m₂ ∈ range (M + 1), ∑ m₃ ∈ range (M + 1), fN (p * m₁) (p * m₂) (p * m₃)) -
       (∑ m₁ ∈ range (M + 1), ∑ m₂ ∈ range (M + 1), ∑ m₃ ∈ range (M + 1), fM m₁ m₂ m₃)) +
      (∑ k₁ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ m₂ ∈ range (M + 1), ∑ m₃ ∈ range (M + 1), fN k₁ (p * m₂) (p * m₃)) +
      (∑ m₁ ∈ range (M + 1), ∑ k₂ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ m₃ ∈ range (M + 1), fN (p * m₁) k₂ (p * m₃)) +
      (∑ m₁ ∈ range (M + 1), ∑ m₂ ∈ range (M + 1), ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN (p * m₁) (p * m₂) k₃) +
      (∑ k₁ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ k₂ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ m₃ ∈ range (M + 1), fN k₁ k₂ (p * m₃)) +
      (∑ k₁ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ m₂ ∈ range (M + 1), ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN k₁ (p * m₂) k₃) +
      (∑ m₁ ∈ range (M + 1), ∑ k₂ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN (p * m₁) k₂ k₃) +
      (∑ k₁ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ k₂ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN k₁ k₂ k₃) := by
    rw [hdecomp_N, hQM]; ring
  have hpv_total : PVal p (3 * r) ((OMA.S_oeis_a364114.a N : ℚ) - (OMA.S_oeis_a364114.a M : ℚ)) := by
    rw [hdecomp]
    have hndiv1_slot2 : PVal p (3 * r)
        (∑ m₁ ∈ range (M + 1), ∑ k₂ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ m₃ ∈ range (M + 1), fN (p * m₁) k₂ (p * m₃)) := by
      rw [Finset.sum_comm]
      convert hndiv1_slot1 using 2 with k₂ _
      refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₃ _ => hsym12 (p * m₁) k₂ (p * m₃)
    have hndiv1_slot3 : PVal p (3 * r)
        (∑ m₁ ∈ range (M + 1), ∑ m₂ ∈ range (M + 1), ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN (p * m₁) (p * m₂) k₃) := by
      have hswap : ∑ m₁ ∈ range (M + 1), ∑ m₂ ∈ range (M + 1), ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN (p * m₁) (p * m₂) k₃ =
          ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ m₂ ∈ range (M + 1), ∑ m₁ ∈ range (M + 1), fN k₃ (p * m₂) (p * m₁) := by
        calc ∑ m₁ ∈ range (M + 1), ∑ m₂ ∈ range (M + 1), ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN (p * m₁) (p * m₂) k₃
            = ∑ m₁ ∈ range (M + 1), ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ m₂ ∈ range (M + 1), fN (p * m₁) (p * m₂) k₃ :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ m₁ ∈ range (M + 1), ∑ m₂ ∈ range (M + 1), fN (p * m₁) (p * m₂) k₃ :=
              Finset.sum_comm
          _ = ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ m₂ ∈ range (M + 1), ∑ m₁ ∈ range (M + 1), fN (p * m₁) (p * m₂) k₃ :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = _ := Finset.sum_congr rfl fun k₃ _ => Finset.sum_congr rfl fun m₂ _ =>
              Finset.sum_congr rfl fun m₁ _ => hsym13 (p * m₁) (p * m₂) k₃
      rw [hswap]; exact hndiv1_slot1
    have h2_12 : PVal p (3 * r)
        (∑ k₁ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ k₂ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ m₃ ∈ range (M + 1), fN k₁ k₂ (p * m₃)) :=
      PVal.sum hp fun k₁ hk₁ => PVal.sum hp fun k₂ hk₂ => PVal.sum hp fun m₃ _ =>
        hndiv2_pv k₁ k₂ (p * m₃) (Finset.mem_filter.mp hk₁).2 (Finset.mem_filter.mp hk₂).2
    have h2_13 : PVal p (3 * r)
        (∑ k₁ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ m₂ ∈ range (M + 1), ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN k₁ (p * m₂) k₃) :=
      PVal.sum hp fun k₁ hk₁ => PVal.sum hp fun m₂ _ => PVal.sum hp fun k₃ hk₃ => by
        rw [hsym12, hsym13]
        exact hndiv2_pv k₃ k₁ (p * m₂) (Finset.mem_filter.mp hk₃).2 (Finset.mem_filter.mp hk₁).2
    have h2_23 : PVal p (3 * r)
        (∑ m₁ ∈ range (M + 1), ∑ k₂ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN (p * m₁) k₂ k₃) :=
      PVal.sum hp fun m₁ _ => PVal.sum hp fun k₂ hk₂ => PVal.sum hp fun k₃ hk₃ => by
        rw [hsym13]
        exact hndiv2_pv k₃ k₂ (p * m₁) (Finset.mem_filter.mp hk₃).2 (Finset.mem_filter.mp hk₂).2
    have h3_123 : PVal p (3 * r)
        (∑ k₁ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ k₂ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), ∑ k₃ ∈ (range (N + 1)).filter (fun k => ¬ p ∣ k), fN k₁ k₂ k₃) :=
      PVal.sum hp fun k₁ hk₁ => PVal.sum hp fun k₂ hk₂ => PVal.sum hp fun k₃ _ =>
        hndiv2_pv k₁ k₂ k₃ (Finset.mem_filter.mp hk₁).2 (Finset.mem_filter.mp hk₂).2
    exact ((((((hdiv_diff.add hp hndiv1_slot1).add hp hndiv1_slot2).add hp hndiv1_slot3).add hp h2_12).add hp h2_13).add hp h2_23).add hp h3_123
  have hz : (OMA.S_oeis_a364114.a N : ℤ) ≡ (OMA.S_oeis_a364114.a M : ℤ) [ZMOD (p : ℤ) ^ (3 * r)] :=
    PVal.modEq_of_sub hp (by simpa using hpv_total)
  exact Int.natCast_modEq_iff.mp (by simpa [Nat.cast_pow] using hz)

-- ============================================================================
-- Block D: Proof of (P2): a(n * p^r - 1) == a(n * p^(r - 1) - 1) [MOD p^(3*r)]
-- ============================================================================

private lemma vp_mul_p {p x : ℕ} (hp : p.Prime) (hx : 1 ≤ x) : vp p (p * x) = vp p x + 1 := by
  have hpx : p * x ≠ 0 := (Nat.mul_pos hp.pos hx).ne'
  have h1 : p ^ (vp p x + 1) ∣ p * x := by rw [pow_succ']; exact Nat.mul_dvd_mul_left p (vp_dvd hp (by omega))
  have h2 : ¬ p ^ (vp p x + 2) ∣ p * x := by
    intro h; rw [show vp p x + 2 = (vp p x + 1) + 1 by omega, pow_succ'] at h
    exact vp_succ_not_dvd hp (by omega) ((Nat.mul_dvd_mul_iff_left hp.pos).mp h)
  have hle := vp_le_of_dvd hp hpx h1
  by_contra hne
  have hgt : vp p x + 2 ≤ vp p (p * x) := by omega
  exact h2 (dvd_trans (Nat.pow_dvd_pow p hgt) (vp_dvd hp hpx))

private lemma cJ_pred_div_ratio (p M m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hMpos : 1 ≤ M) (hm1 : 1 ≤ m) (hmM : m < M) :
    PVal p (3 + vp p m + vp p M + min (vp p (M - m)) (vp p (m + M)))
      ((cJ (M * p - 1) (p * m) : ℚ) / (cJ (M - 1) m : ℚ) - 1) := by
  have hNpos : 1 ≤ M * p := Nat.mul_pos hMpos hp.pos
  -- Express cJ(K - 1, k) via C(K, k) * C(K + k, k) * (K - k) / (K + k)
  have hrel_gen : ∀ K k : ℕ, 1 ≤ K → 1 ≤ k → k < K →
      ((K + k : ℕ) : ℚ) * (cJ (K - 1) k : ℚ) =
        ((K - k : ℕ) : ℚ) * (Nat.choose K k : ℚ) * (Nat.choose (k + K) k : ℚ) := by
    intro K k hK hk1 hkK
    have h1 : K * Nat.choose (K - 1) k = (K - k) * Nat.choose K k := by
      have h := Nat.choose_succ_right_eq K (K - k - 1)
      -- Use K * C(K-1, k) = (K - k) * C(K, k) via symmetry C(K-1, k) = C(K-1, K-1-k)
      have ha := Nat.add_one_mul_choose_eq (K - 1) (K - 1 - k)
      have hK1 : K - 1 + 1 = K := by omega
      have hKk1 : K - 1 - k + 1 = K - k := by omega
      have hs1 : Nat.choose (K - 1) (K - 1 - k) = Nat.choose (K - 1) k := Nat.choose_symm (by omega)
      have hs2 : Nat.choose K (K - k) = Nat.choose K k := Nat.choose_symm (by omega)
      rw [hK1, hKk1, hs1, hs2] at ha; linarith
    have h2 : (K + k) * Nat.choose (K - 1 + k) k = K * Nat.choose (k + K) k := by
      have ha := Nat.add_one_mul_choose_eq (K - 1 + k) (K - 1)
      have h1' : K - 1 + k + 1 = k + K := by omega
      have h2' : K - 1 + 1 = K := by omega
      have hs1 : Nat.choose (K - 1 + k) (K - 1) = Nat.choose (K - 1 + k) k := by
        have hs := Nat.choose_symm (by omega : k ≤ K - 1 + k)
        rwa [show K - 1 + k - k = K - 1 by omega] at hs
      have hs2 : Nat.choose (k + K) K = Nat.choose (k + K) k := by
        have hs := Nat.choose_symm (by omega : k ≤ k + K)
        rwa [show k + K - k = K by omega] at hs
      rw [h1', h2', hs1, hs2] at ha; linarith
    have hK0 : (K : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    apply mul_left_cancel₀ hK0
    have h1q : (K : ℚ) * (Nat.choose (K - 1) k : ℚ) = ((K - k : ℕ) : ℚ) * (Nat.choose K k : ℚ) := by exact_mod_cast h1
    have h2q : ((K + k : ℕ) : ℚ) * (Nat.choose (K - 1 + k) k : ℚ) = (K : ℚ) * (Nat.choose (k + K) k : ℚ) := by exact_mod_cast h2
    simp only [cJ, Int.cast_mul, Int.cast_natCast]
    calc (K : ℚ) * (((K + k : ℕ) : ℚ) * ((Nat.choose (K - 1) k : ℚ) * (Nat.choose (K - 1 + k) k : ℚ)))
        = ((K : ℚ) * (Nat.choose (K - 1) k : ℚ)) * (((K + k : ℕ) : ℚ) * (Nat.choose (K - 1 + k) k : ℚ)) := by ring
      _ = (((K - k : ℕ) : ℚ) * (Nat.choose K k : ℚ)) * ((K : ℚ) * (Nat.choose (k + K) k : ℚ)) := by rw [h1q, h2q]
      _ = (K : ℚ) * (((K - k : ℕ) : ℚ) * (Nat.choose K k : ℚ) * (Nat.choose (k + K) k : ℚ)) := by ring
  have hNrel := hrel_gen (M * p) (p * m) hNpos (Nat.mul_pos hp.pos hm1) (by simpa [mul_comm] using Nat.mul_lt_mul_of_pos_left hmM hp.pos)
  have hMrel := hrel_gen M m hMpos hm1 hmM
  have h1 := kazandzidis_ratio p m (M - m) hp hp5 hm1 (by omega)
  rw [Nat.add_sub_of_le (by omega : m ≤ M)] at h1
  have h2 := kazandzidis_ratio p m M hp hp5 hm1 hMpos
  have hcM_ne : (cJ (M - 1) m : ℚ) ≠ 0 := by
    simp only [cJ, Int.cast_mul, Int.cast_natCast]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne')
      (Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne')
  have hch1_ne : (Nat.choose M m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hch2_ne : (Nat.choose (m + M) m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hMm_ne : ((M - m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hMp_ne : ((M + m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hrat : (cJ (M * p - 1) (p * m) : ℚ) / (cJ (M - 1) m : ℚ) =
      ((Nat.choose (M * p) (m * p) : ℚ) / (Nat.choose M m : ℚ)) *
      ((Nat.choose ((m + M) * p) (m * p) : ℚ) / (Nat.choose (m + M) m : ℚ)) := by
    have hpm : p * m = m * p := mul_comm p m
    have hadd_eq : p * m + M * p = (m + M) * p := by ring
    have hsub_eq : ((M * p - p * m : ℕ) : ℚ) = ((M - m : ℕ) : ℚ) * (p : ℚ) := by
      have : M * p - p * m = (M - m) * p := by rw [Nat.sub_mul, mul_comm p m]
      rw [this, Nat.cast_mul]
    have hsum_eq : ((M * p + p * m : ℕ) : ℚ) = ((M + m : ℕ) : ℚ) * (p : ℚ) := by
      push_cast; ring
    rw [hsum_eq, hsub_eq, hadd_eq, hpm] at hNrel
    have hNrel' : ((M + m : ℕ) : ℚ) * (cJ (M * p - 1) (m * p) : ℚ) =
        ((M - m : ℕ) : ℚ) * (Nat.choose (M * p) (m * p) : ℚ) * (Nat.choose ((m + M) * p) (m * p) : ℚ) := by
      apply mul_left_cancel₀ hp_ne
      linarith
    rw [hpm]
    have hLHS : (cJ (M * p - 1) (m * p) : ℚ) =
        ((M - m : ℕ) : ℚ) / ((M + m : ℕ) : ℚ) * (Nat.choose (M * p) (m * p) : ℚ) * (Nat.choose ((m + M) * p) (m * p) : ℚ) := by
      apply mul_left_cancel₀ hMp_ne; rw [hNrel']; field_simp [hMp_ne]
    have hRHS : (cJ (M - 1) m : ℚ) =
        ((M - m : ℕ) : ℚ) / ((M + m : ℕ) : ℚ) * (Nat.choose M m : ℚ) * (Nat.choose (m + M) m : ℚ) := by
      apply mul_left_cancel₀ hMp_ne; rw [hMrel]; field_simp [hMp_ne]
    rw [hLHS, hRHS]
    field_simp [hMp_ne, hMm_ne, hch1_ne, hch2_ne]
  rw [hrat]
  set d1 : ℚ := (Nat.choose (M * p) (m * p) : ℚ) / (Nat.choose M m : ℚ) - 1
  set d2 : ℚ := (Nat.choose ((m + M) * p) (m * p) : ℚ) / (Nat.choose (m + M) m : ℚ) - 1
  have heq : ((Nat.choose (M * p) (m * p) : ℚ) / (Nat.choose M m : ℚ)) *
      ((Nat.choose ((m + M) * p) (m * p) : ℚ) / (Nat.choose (m + M) m : ℚ)) - 1 =
      d1 + d2 + d1 * d2 := by simp only [d1, d2]; ring
  rw [heq]
  set E := 3 + vp p m + vp p M + min (vp p (M - m)) (vp p (m + M))
  have hd1 : PVal p E d1 := h1.mono (by have := min_le_left (vp p (M - m)) (vp p (m + M)); omega)
  have hd2 : PVal p E d2 := h2.mono (by have := min_le_right (vp p (M - m)) (vp p (m + M)); omega)
  exact (hd1.add hp hd2).add hp ((hd1.mul hp hd2).mono (by omega))

/-- D1: Divisible-index terms b0 of dual rep g_3(N - 1) match term-by-term modulo p^(3*r). -/
private lemma part2_b0_term (p M r m₁ m₂ m₃ : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 1 ≤ r) (hM : p ^ (r - 1) ∣ M) (hMpos : 1 ≤ M)
    (hm1 : m₁ < M) (hm2 : m₂ < M) (hm3 : m₃ < M) :
    PVal p (3 * r)
      ((-1 : ℚ) ^ (p * m₁ + p * m₂ + p * m₃) *
        (Nat.choose (M * p - 1 + (p * m₁ + p * m₂ + p * m₃)) (p * m₁ + p * m₂ + p * m₃) : ℚ) *
        (cJ (M * p - 1) (p * m₁) : ℚ) * (cJ (M * p - 1) (p * m₂) : ℚ) * (cJ (M * p - 1) (p * m₃) : ℚ) -
       (-1 : ℚ) ^ (m₁ + m₂ + m₃) *
        (Nat.choose (M - 1 + (m₁ + m₂ + m₃)) (m₁ + m₂ + m₃) : ℚ) *
        (cJ (M - 1) m₁ : ℚ) * (cJ (M - 1) m₂ : ℚ) * (cJ (M - 1) m₃ : ℚ)) := by
  set t := m₁ + m₂ + m₃
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hsign : (-1 : ℚ) ^ (p * m₁ + p * m₂ + p * m₃) = (-1 : ℚ) ^ t := by
    rw [show p * m₁ + p * m₂ + p * m₃ = p * t by simp only [t]; ring, pow_mul, hpodd.neg_one_pow]
  rw [hsign]
  set A0 : ℚ := (Nat.choose (M * p - 1 + p * t) (p * t) : ℚ)
  set B0 : ℚ := (Nat.choose (M - 1 + t) t : ℚ)
  set A1 : ℚ := (cJ (M * p - 1) (p * m₁) : ℚ)
  set A2 : ℚ := (cJ (M * p - 1) (p * m₂) : ℚ)
  set A3 : ℚ := (cJ (M * p - 1) (p * m₃) : ℚ)
  set B1 : ℚ := (cJ (M - 1) m₁ : ℚ)
  set B2 : ℚ := (cJ (M - 1) m₂ : ℚ)
  set B3 : ℚ := (cJ (M - 1) m₃ : ℚ)
  have hB0_ne : B0 ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hB_ne : ∀ m < M, (cJ (M - 1) m : ℚ) ≠ 0 := fun m hm => by
    simp only [cJ, Int.cast_mul, Int.cast_natCast]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne')
      (Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne')
  set d0 : ℚ := A0 / B0 - 1
  set d1 : ℚ := A1 / B1 - 1
  set d2 : ℚ := A2 / B2 - 1
  set d3 : ℚ := A3 / B3 - 1
  have hvpM : r - 1 ≤ vp p M := vp_le_of_dvd hp (by omega) hM
  -- Helper: B_i valuation when m_i >= 1
  have hBi_pv : ∀ m < M, 1 ≤ m → PVal p (vp p M - vp p m) (cJ (M - 1) m : ℚ) := by
    intro m _ hm1'
    simp only [cJ, Int.cast_mul, Int.cast_natCast]
    exact (PVal.nat hp _).zero_mul hp (PVal.of_dvd_nat hp (vp_choose_pred_add_ge p M m hp hm1' (by omega)))
  have hB0_pv : 1 ≤ t → PVal p (vp p M - vp p t) B0 := fun ht1 =>
    PVal.of_dvd_nat hp (vp_choose_pred_add_ge p M t hp ht1 (by omega))
  -- Helper ratio identity: A0 / B0 = C((t+M)*p, t*p) / C(t+M, t)
  have hrat0_eq : A0 / B0 = (Nat.choose ((t + M) * p) (t * p) : ℚ) / (Nat.choose (t + M) t : ℚ) := by
    have hNpos : 1 ≤ M * p := Nat.mul_pos hMpos hp.pos
    have hrelN : ((M + t : ℕ) : ℚ) * A0 = (M : ℚ) * (Nat.choose ((t + M) * p) (t * p) : ℚ) := by
      have hnat : (M * p + p * t) * Nat.choose (M * p - 1 + p * t) (p * t) =
          (M * p) * Nat.choose ((t + M) * p) (t * p) := by
        have h := Nat.add_one_mul_choose_eq (M * p - 1 + p * t) (M * p - 1)
        have h1 : M * p - 1 + p * t + 1 = (t + M) * p := by ring_nf; omega
        have h2 : M * p - 1 + 1 = M * p := by omega
        have hs1 : Nat.choose (M * p - 1 + p * t) (M * p - 1) = Nat.choose (M * p - 1 + p * t) (p * t) := by
          have hs := Nat.choose_symm (by omega : p * t ≤ M * p - 1 + p * t)
          rwa [show M * p - 1 + p * t - p * t = M * p - 1 by omega] at hs
        have hs2 : Nat.choose ((t + M) * p) (M * p) = Nat.choose ((t + M) * p) (t * p) := by
          have hs := Nat.choose_symm (by nlinarith : t * p ≤ (t + M) * p)
          rwa [show (t + M) * p - t * p = M * p by rw [add_mul]; omega] at hs
        rw [h1, h2, hs1, hs2] at h; rw [show M * p + p * t = (t + M) * p by ring]; linarith
      have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      apply mul_left_cancel₀ hp0
      have hq : ((M * p + p * t : ℕ) : ℚ) * A0 = ((M * p : ℕ) : ℚ) * (Nat.choose ((t + M) * p) (t * p) : ℚ) := by
        simp only [A0]; exact_mod_cast hnat
      push_cast at hq ⊢; linarith
    have hrelM : ((M + t : ℕ) : ℚ) * B0 = (M : ℚ) * (Nat.choose (t + M) t : ℚ) := by
      have hnat : (M + t) * Nat.choose (M - 1 + t) t = M * Nat.choose (t + M) t := by
        have h := Nat.add_one_mul_choose_eq (M - 1 + t) (M - 1)
        have hs1 : Nat.choose (M - 1 + t) (M - 1) = Nat.choose (M - 1 + t) t := by
          have hs := Nat.choose_symm (by omega : t ≤ M - 1 + t)
          rwa [show M - 1 + t - t = M - 1 by omega] at hs
        have hs2 : Nat.choose (t + M) M = Nat.choose (t + M) t := by
          have hs := Nat.choose_symm (by omega : t ≤ t + M)
          rwa [show t + M - t = M by omega] at hs
        rw [show M - 1 + t + 1 = t + M by omega, show M - 1 + 1 = M by omega, hs1, hs2] at h; linarith
      simp only [B0]; exact_mod_cast hnat
    have hMt0 : ((M + t : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hch0 : (Nat.choose (t + M) t : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
    rw [div_eq_div_iff hB0_ne hch0]
    apply mul_left_cancel₀ hMt0
    calc ((M + t : ℕ) : ℚ) * (A0 * (Nat.choose (t + M) t : ℚ))
        = (((M + t : ℕ) : ℚ) * A0) * (Nat.choose (t + M) t : ℚ) := by ring
      _ = ((M : ℚ) * (Nat.choose ((t + M) * p) (t * p) : ℚ)) * (Nat.choose (t + M) t : ℚ) := by rw [hrelN]
      _ = (Nat.choose ((t + M) * p) (t * p) : ℚ) * ((M : ℚ) * (Nat.choose (t + M) t : ℚ)) := by ring
      _ = (Nat.choose ((t + M) * p) (t * p) : ℚ) * (((M + t : ℕ) : ℚ) * B0) := by rw [← hrelM]
      _ = ((M + t : ℕ) : ℚ) * ((Nat.choose ((t + M) * p) (t * p) : ℚ) * B0) := by ring
  -- d0 in p^3 Z_(p) and B0*B1*B2*B3*d0 in p^(3*r) Z_(p)
  have hd0_pv : PVal p 0 d0 := by
    by_cases ht0 : t = 0
    · simp [d0, A0, B0, ht0]; exact PVal.zero hp
    · have hkaz := kazandzidis_ratio p t M hp hp5 (by omega) hMpos
      simpa only [d0, hrat0_eq] using hkaz.mono (Nat.zero_le _)
  have hdi_pv : ∀ m < M, PVal p 0 ((cJ (M * p - 1) (p * m) : ℚ) / (cJ (M - 1) m : ℚ) - 1) := by
    intro m hm
    by_cases hm0 : m = 0
    · subst hm0; simp [cJ]; exact PVal.zero hp
    · exact (cJ_pred_div_ratio p M m hp hp5 hMpos (by omega) hm).mono (Nat.zero_le _)
  have hB0_prod_d0 : PVal p (3 * r) (B0 * B1 * B2 * B3 * d0) := by
    by_cases ht0 : t = 0
    · have : d0 = 0 := by simp [d0, A0, B0, ht0]
      rw [this, mul_zero]; exact PVal.zero hp
    · have hB0d0 : B0 * d0 = A0 - B0 := by simp only [d0]; rw [mul_sub, mul_one, mul_div_cancel₀ _ hB0_ne]
      have hre : B0 * B1 * B2 * B3 * d0 = (B0 * d0) * (B1 * B2 * B3) := by ring
      rw [hre]
      by_cases hlt : vp p t < vp p M
      · -- Some m_i has 1 <= m_i and vp p m_i <= vp p t
        have hex : (1 ≤ m₁ ∧ vp p m₁ ≤ vp p t) ∨ (1 ≤ m₂ ∧ vp p m₂ ≤ vp p t) ∨ (1 ≤ m₃ ∧ vp p m₃ ≤ vp p t) := by
          by_contra hnot; push Not at hnot
          have hd : ∀ x, (x = 0 ∨ vp p t < vp p x) → p ^ (vp p t + 1) ∣ x := by
            intro x hx; rcases hx with rfl | hgt
            · exact dvd_zero _
            · exact dvd_trans (Nat.pow_dvd_pow p hgt) (vp_dvd hp (by intro h0; subst h0; simp [vp] at hgt))
          have hd1 := hd m₁ (by by_cases h0 : m₁ = 0; left; exact h0; right; exact hnot.1 (by omega))
          have hd2 := hd m₂ (by by_cases h0 : m₂ = 0; left; exact h0; right; exact hnot.2.1 (by omega))
          have hd3 := hd m₃ (by by_cases h0 : m₃ = 0; left; exact h0; right; exact hnot.2.2 (by omega))
          exact vp_succ_not_dvd hp (by omega) (dvd_add (dvd_add hd1 hd2) hd3)
        -- Use stronger bound on B0 * d0: 3 + 2*vp p M + vp p t
        have hA0B0 : PVal p (3 + 2 * vp p M + vp p t) (B0 * d0) := by
          have hkaz0 := kazandzidis_ratio p t M hp hp5 (by omega) hMpos
          have hd0_eq : d0 = (Nat.choose ((t + M) * p) (t * p) : ℚ) / (Nat.choose (t + M) t : ℚ) - 1 := by
            simp only [d0, hrat0_eq]
          rw [hd0_eq]
          have hadd := vp_add_of_lt hp (by omega : t ≠ 0) (by omega : M ≠ 0) hlt
          have hmul := (hB0_pv (by omega)).mul hp hkaz0
          refine hmul.mono ?_; rw [hadd]; omega
        have hB123 : PVal p (vp p M - vp p t) (B1 * B2 * B3) := by
          rcases hex with ⟨h1, hv1⟩ | ⟨h2, hv2⟩ | ⟨h3, hv3⟩
          · exact (((hBi_pv m₁ hm1 h1).mono (by omega)).mul_zero hp (PVal.int hp _)).mul_zero hp (PVal.int hp _)
          · exact ((PVal.int hp _).zero_mul hp ((hBi_pv m₂ hm2 h2).mono (by omega))).mul_zero hp (PVal.int hp _)
          · exact ((PVal.int hp _).mul_zero hp (PVal.int hp _)).zero_mul hp ((hBi_pv m₃ hm3 h3).mono (by omega))
        exact (hA0B0.mul hp hB123).mono (by omega)
      · -- vp p t >= vp p M => B0 * d0 already in p^(3*r) Z_(p)
        have hkaz0 := kazandzidis_ratio p t M hp hp5 (by omega) hMpos
        have hB0d0_pv : PVal p (3 * r) (B0 * d0) := by
          have htm : vp p M ≤ vp p (t + M) := by
            apply vp_le_of_dvd hp (by omega)
            exact dvd_add (dvd_trans (Nat.pow_dvd_pow p (by omega)) (vp_dvd hp (by omega))) (vp_dvd hp (by omega))
          have hd0_eq : d0 = (Nat.choose ((t + M) * p) (t * p) : ℚ) / (Nat.choose (t + M) t : ℚ) - 1 := by
            simp only [d0, hrat0_eq]
          rw [hd0_eq]
          exact ((PVal.nat hp _).zero_mul hp hkaz0).mono (by omega)
        have hB1230 : PVal p 0 (B1 * B2 * B3) := ((PVal.int hp _).mul_zero hp (PVal.int hp _)).mul_zero hp (PVal.int hp _)
        exact hB0d0_pv.mul_zero hp hB1230
  -- Helper: symmetric claim B0*B1*B2*B3 * (cJ(Mp-1, px)/cJ(M-1, x) - 1) in p^(3*r) Z_(p)
  have hslot_pv : ∀ x y z : ℕ, x < M → y < M → z < M → x + y + z = t →
      PVal p (3 * r)
        (B0 * (cJ (M - 1) x : ℚ) * (cJ (M - 1) y : ℚ) * (cJ (M - 1) z : ℚ) *
          ((cJ (M * p - 1) (p * x) : ℚ) / (cJ (M - 1) x : ℚ) - 1)) := by
    intro x y z hx hy hz hxyz
    by_cases hx0 : x = 0
    · subst hx0; simp [cJ]; exact PVal.zero hp
    · have hdx := cJ_pred_div_ratio p M x hp hp5 hMpos (by omega) hx
      by_cases hlt : vp p x < vp p M
      · have hvp_add := vp_add_of_lt hp (by omega : x ≠ 0) (by omega : M ≠ 0) hlt
        have hvp_sub : vp p (M - x) = vp p x := by
          have hle1 : vp p x ≤ vp p (M - x) := by
            apply vp_le_of_dvd hp (by omega)
            exact Nat.dvd_sub (dvd_trans (Nat.pow_dvd_pow p (Nat.le_of_lt hlt)) (vp_dvd hp (by omega)))
              (vp_dvd hp (by omega))
          by_contra hne
          have hgt : vp p x < vp p (M - x) := by omega
          have heq := vp_add_of_lt hp (by omega : x ≠ 0) (by omega : M - x ≠ 0) hgt
          rw [Nat.add_sub_of_le (by omega : x ≤ M)] at heq; omega
        have hdx' : PVal p (3 + vp p M + 2 * vp p x) ((cJ (M * p - 1) (p * x) : ℚ) / (cJ (M - 1) x : ℚ) - 1) := by
          refine hdx.mono ?_; rw [hvp_sub, hvp_add, min_self]; omega
        have hBx : PVal p (vp p M - vp p x) (cJ (M - 1) x : ℚ) := hBi_pv x hx (by omega)
        -- Either y >= 1 with vp y <= vp x, or z >= 1 with vp z <= vp x, or vp t = vp x
        have hrest : PVal p (vp p M - vp p x) (B0 * (cJ (M - 1) y : ℚ) * (cJ (M - 1) z : ℚ)) := by
          by_cases hy1 : 1 ≤ y ∧ vp p y ≤ vp p x
          · exact ((PVal.nat hp _).zero_mul hp ((hBi_pv y hy hy1.1).mono (by omega))).mul_zero hp (PVal.int hp _)
          · by_cases hz1 : 1 ≤ z ∧ vp p z ≤ vp p x
            · exact ((PVal.nat hp _).mul_zero hp (PVal.int hp _)).zero_mul hp ((hBi_pv z hz hz1.1).mono (by omega))
            · have hd : ∀ w, ¬ (1 ≤ w ∧ vp p w ≤ vp p x) → p ^ (vp p x + 1) ∣ w := by
                intro w hw
                by_cases hw0 : w = 0
                · subst hw0; exact dvd_zero _
                · have hgt : vp p x < vp p w := by omega
                  exact dvd_trans (Nat.pow_dvd_pow p hgt) (vp_dvd hp hw0)
              have hdy := hd y hy1
              have hdz := hd z hz1
              have ht_pos : 1 ≤ t := by omega
              have hvp_t : vp p t = vp p x := by
                have hdyz : p ^ (vp p x + 1) ∣ y + z := dvd_add hdy hdz
                by_cases hyz0 : y + z = 0
                · have : t = x := by omega
                  rw [this]
                · have hlt_yz : vp p x < vp p (y + z) := by
                    have hle := vp_le_of_dvd hp hyz0 hdyz; omega
                  rw [← hxyz, add_assoc]
                  exact vp_add_of_lt hp (by omega) hyz0 hlt_yz
              have hB0' : PVal p (vp p M - vp p x) B0 := by rw [← hvp_t]; exact hB0_pv ht_pos
              exact (hB0'.mul_zero hp (PVal.int hp _)).mul_zero hp (PVal.int hp _)
        have hre : B0 * (cJ (M - 1) x : ℚ) * (cJ (M - 1) y : ℚ) * (cJ (M - 1) z : ℚ) *
            ((cJ (M * p - 1) (p * x) : ℚ) / (cJ (M - 1) x : ℚ) - 1) =
            (B0 * (cJ (M - 1) y : ℚ) * (cJ (M - 1) z : ℚ)) * (cJ (M - 1) x : ℚ) *
            ((cJ (M * p - 1) (p * x) : ℚ) / (cJ (M - 1) x : ℚ) - 1) := by ring
        rw [hre]
        exact ((hrest.mul hp hBx).mul hp hdx').mono (by omega)
      · have hvp_add : vp p M ≤ vp p (x + M) := by
          apply vp_le_of_dvd hp (by omega)
          exact dvd_add (dvd_trans (Nat.pow_dvd_pow p (by omega)) (vp_dvd hp (by omega))) (vp_dvd hp (by omega))
        have hvp_sub : vp p M ≤ vp p (M - x) := by
          apply vp_le_of_dvd hp (by omega)
          exact Nat.dvd_sub (vp_dvd hp (by omega)) (dvd_trans (Nat.pow_dvd_pow p (by omega)) (vp_dvd hp (by omega)))
        have hdx' : PVal p (3 * r) ((cJ (M * p - 1) (p * x) : ℚ) / (cJ (M - 1) x : ℚ) - 1) := by
          refine hdx.mono ?_; have := le_min hvp_sub hvp_add; omega
        have hB0123 : PVal p 0 (B0 * (cJ (M - 1) x : ℚ) * (cJ (M - 1) y : ℚ) * (cJ (M - 1) z : ℚ)) :=
          (((PVal.nat hp _).mul_zero hp (PVal.int hp _)).mul_zero hp (PVal.int hp _)).mul_zero hp (PVal.int hp _)
        exact hB0123.zero_mul hp hdx'
  have hB0_prod_d1 : PVal p (3 * r) (B0 * B1 * B2 * B3 * d1) := hslot_pv m₁ m₂ m₃ hm1 hm2 hm3 rfl
  have hB0_prod_d2 : PVal p (3 * r) (B0 * B1 * B2 * B3 * d2) := by
    have h := hslot_pv m₂ m₁ m₃ hm2 hm1 hm3 (by simp only [t]; omega)
    convert h using 1; simp only [B1, B2, B3, d2]; ring
  have hB0_prod_d3 : PVal p (3 * r) (B0 * B1 * B2 * B3 * d3) := by
    have h := hslot_pv m₃ m₁ m₂ hm3 hm1 hm2 (by simp only [t]; omega)
    convert h using 1; simp only [B1, B2, B3, d3]; ring
  have hA0_eq : A0 = B0 * (1 + d0) := by
    simp only [d0, add_sub_cancel]; exact (mul_div_cancel₀ A0 hB0_ne).symm
  have hA1_eq : A1 = B1 * (1 + d1) := by
    simp only [d1, add_sub_cancel]; exact (mul_div_cancel₀ A1 (hB_ne m₁ hm1)).symm
  have hA2_eq : A2 = B2 * (1 + d2) := by
    simp only [d2, add_sub_cancel]; exact (mul_div_cancel₀ A2 (hB_ne m₂ hm2)).symm
  have hA3_eq : A3 = B3 * (1 + d3) := by
    simp only [d3, add_sub_cancel]; exact (mul_div_cancel₀ A3 (hB_ne m₃ hm3)).symm
  have hpt : p * m₁ + p * m₂ + p * m₃ = p * t := by simp only [t]; ring
  have hfactor : (-1 : ℚ) ^ t *
        (Nat.choose (M * p - 1 + (p * m₁ + p * m₂ + p * m₃)) (p * m₁ + p * m₂ + p * m₃) : ℚ) *
        A1 * A2 * A3 - (-1 : ℚ) ^ t * B0 * B1 * B2 * B3 =
      (-1 : ℚ) ^ t *
        ((B0 * B1 * B2 * B3 * d0) * ((1 + d1) * (1 + d2) * (1 + d3)) +
         (B0 * B1 * B2 * B3 * d1) * ((1 + d2) * (1 + d3)) +
         (B0 * B1 * B2 * B3 * d2) * (1 + d3) +
         (B0 * B1 * B2 * B3 * d3)) := by
    rw [hpt]
    change (-1 : ℚ) ^ t * A0 * A1 * A2 * A3 - (-1 : ℚ) ^ t * B0 * B1 * B2 * B3 = _
    rw [hA0_eq, hA1_eq, hA2_eq, hA3_eq]; ring
  rw [hfactor]
  have h1d1 : PVal p 0 (1 + d1) := (PVal.nat hp 1).add hp (hdi_pv m₁ hm1)
  have h1d2 : PVal p 0 (1 + d2) := (PVal.nat hp 1).add hp (hdi_pv m₂ hm2)
  have h1d3 : PVal p 0 (1 + d3) := (PVal.nat hp 1).add hp (hdi_pv m₃ hm3)
  have hsign0 : PVal p 0 ((-1 : ℚ) ^ t) := by simpa using (PVal.int hp (-1)).pow hp t
  have hsum := ((hB0_prod_d0.mul_zero hp ((h1d1.mul_zero hp h1d2).mul_zero hp h1d3)).add hp
    (hB0_prod_d1.mul_zero hp (h1d2.mul_zero hp h1d3))).add hp
    ((hB0_prod_d2.mul_zero hp h1d3).add hp hB0_prod_d3)
  convert hsign0.zero_mul hp hsum using 1; ring

/-- D2: Single-sum inductive moment lemma for b1 of (P2). -/
private lemma part2_b1_moment_dvd (p m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ M T : ℕ, 1 ≤ M → p ^ m ∣ M → p ^ m ∣ T →
      ((p : ℤ) ^ m ∣ ∑ q ∈ range M, (-1 : ℤ) ^ q *
        (Nat.choose (M + T + q) (T + q) : ℤ) * (Nat.choose (M - 1) q : ℤ) * (Nat.choose (M + q) q : ℤ)) ∧
      (∀ d : ℕ, 1 ≤ d →
        (p : ℤ) ^ (m + 1) ∣ (p : ℤ) ^ d * ∑ q ∈ range M, (-1 : ℤ) ^ q *
          (Nat.choose (M + T + q) (T + q) : ℤ) * (Nat.choose (M - 1) q : ℤ) * (Nat.choose (M + q) q : ℤ) * (q : ℤ) ^ d) := by
  induction m with
  | zero =>
    intro M T _ _ _
    constructor
    · simp
    · intro d hd; rw [zero_add, pow_one]; exact dvd_mul_of_dvd_left (dvd_pow_self (p : ℤ) (by omega)) _
  | succ m ih =>
    intro M T hMpos hMd hTd
    obtain ⟨M', hM'eq⟩ := dvd_trans (dvd_pow_self p (by omega)) hMd
    obtain ⟨T', hT'eq⟩ := dvd_trans (dvd_pow_self p (by omega)) hTd
    have hM_eq : M = M' * p := by linarith
    have hT_eq : T = T' * p := by linarith
    have hM'pos : 1 ≤ M' := by nlinarith [hp.pos]
    have hM'd : p ^ m ∣ M' := (Nat.mul_dvd_mul_iff_left hp.pos).mp (by rw [← pow_succ', ← hM'eq]; exact hMd)
    have hT'd : p ^ m ∣ T' := (Nat.mul_dvd_mul_iff_left hp.pos).mp (by rw [← pow_succ', ← hT'eq]; exact hTd)
    have ⟨ih0, ihd⟩ := ih M' T' hM'pos hM'd hT'd
    have hpodd : p ≠ 2 := by omega
    have hp_odd : Odd p := hp.odd_of_ne_two hpodd
    set g : ℕ → ℤ := fun a =>
      (-1 : ℤ) ^ a * (Nat.choose (M' + T' + a) (T' + a) : ℤ) *
        (Nat.choose (M' - 1) a : ℤ) * (Nat.choose (M' + a) a : ℤ)
    have hwt : ∀ a < M', ∀ b < p,
        (-1 : ℤ) ^ (a * p + b) * (Nat.choose (M + T + (a * p + b)) (T + (a * p + b)) : ℤ) *
          (Nat.choose (M - 1) (a * p + b) : ℤ) * (Nat.choose (M + (a * p + b)) (a * p + b) : ℤ) ≡
        g a [ZMOD (p : ℤ) ^ (m + 1)] := by
      intro a ha b hb
      have h1 : (Nat.choose (M + T + (a * p + b)) (T + (a * p + b)) : ℤ) ≡
          (Nat.choose (M' + (T' + a)) (T' + a) : ℤ) [ZMOD (p : ℤ) ^ (m + 1)] := by
        have hsh := choose_shift_mod_pow p M' (m + 1) (T' + a) b hp (by rw [← hM_eq]; exact hMd) hb
        have heq1 : T + (a * p + b) = (T' + a) * p + b := by rw [hT_eq]; ring
        have heq2 : M + T + (a * p + b) = M' * p + ((T' + a) * p + b) := by rw [hM_eq, hT_eq]; ring
        rw [heq2, heq1]; exact hsh
      have h2 : (Nat.choose (M - 1) (a * p + b) : ℤ) ≡
          (-1 : ℤ) ^ b * (Nat.choose (M' - 1) a : ℤ) [ZMOD (p : ℤ) ^ (m + 1)] := by
        simpa only [← hM_eq] using choose_pred_mod_pow p M' (m + 1) a b hp hpodd (by rw [← hM_eq]; exact hMd) ha hb
      have h3 : (Nat.choose (M + (a * p + b)) (a * p + b) : ℤ) ≡
          (Nat.choose (M' + a) a : ℤ) [ZMOD (p : ℤ) ^ (m + 1)] := by
        simpa only [← hM_eq] using choose_shift_mod_pow p M' (m + 1) a b hp (by rw [← hM_eq]; exact hMd) hb
      have hsign : (-1 : ℤ) ^ (a * p + b) = (-1 : ℤ) ^ a * (-1 : ℤ) ^ b := by
        rw [pow_add, mul_comm a p, pow_mul, hp_odd.neg_one_pow]
      have hprod := (((Int.ModEq.refl ((-1 : ℤ) ^ (a * p + b))).mul h1).mul h2).mul h3
      have hrhs : (-1 : ℤ) ^ (a * p + b) * (Nat.choose (M' + (T' + a)) (T' + a) : ℤ) *
          ((-1 : ℤ) ^ b * (Nat.choose (M' - 1) a : ℤ)) * (Nat.choose (M' + a) a : ℤ) = g a := by
        rw [hsign]; simp only [g, show M' + (T' + a) = M' + T' + a by omega]
        have hbb : (-1 : ℤ) ^ b * (-1 : ℤ) ^ b = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
        calc (-1 : ℤ) ^ a * (-1 : ℤ) ^ b * (Nat.choose (M' + T' + a) (T' + a) : ℤ) *
              ((-1 : ℤ) ^ b * (Nat.choose (M' - 1) a : ℤ)) * (Nat.choose (M' + a) a : ℤ)
            = ((-1 : ℤ) ^ b * (-1 : ℤ) ^ b) * ((-1 : ℤ) ^ a * (Nat.choose (M' + T' + a) (T' + a) : ℤ) *
              (Nat.choose (M' - 1) a : ℤ) * (Nat.choose (M' + a) a : ℤ)) := by ring
          _ = _ := by rw [hbb, one_mul]
      rwa [hrhs] at hprod
    constructor
    · have hcong : ∑ q ∈ range M, (-1 : ℤ) ^ q *
            (Nat.choose (M + T + q) (T + q) : ℤ) * (Nat.choose (M - 1) q : ℤ) * (Nat.choose (M + q) q : ℤ) ≡
          (p : ℤ) * ∑ a ∈ range M', g a [ZMOD (p : ℤ) ^ (m + 1)] := by
        rw [hM_eq, sum_range_mul_eq M' p]
        calc ∑ a ∈ range M', ∑ b ∈ range p, (-1 : ℤ) ^ (a * p + b) *
              (Nat.choose (M' * p + T + (a * p + b)) (T + (a * p + b)) : ℤ) *
              (Nat.choose (M' * p - 1) (a * p + b) : ℤ) * (Nat.choose (M' * p + (a * p + b)) (a * p + b) : ℤ)
            ≡ ∑ a ∈ range M', ∑ _b ∈ range p, g a [ZMOD (p : ℤ) ^ (m + 1)] := by
              refine Int.ModEq.sum fun a ha => Int.ModEq.sum fun b hb => ?_
              rw [mem_range] at ha hb
              simpa only [← hM_eq] using hwt a ha b hb
          _ = (p : ℤ) * ∑ a ∈ range M', g a := by simp [Finset.sum_const, Finset.mul_sum]
      have hdvd_rhs : (p : ℤ) ^ (m + 1) ∣ (p : ℤ) * ∑ a ∈ range M', g a := by
        rw [pow_succ']; exact mul_dvd_mul_left (p : ℤ) ih0
      exact dvd_sub hdvd_rhs (Int.modEq_iff_dvd.mp hcong) |> fun h => by simpa using h
    · intro d hd
      have hcong_m : ∑ q ∈ range M, (-1 : ℤ) ^ q *
            (Nat.choose (M + T + q) (T + q) : ℤ) * (Nat.choose (M - 1) q : ℤ) * (Nat.choose (M + q) q : ℤ) * (q : ℤ) ^ d ≡
          ∑ a ∈ range M', ∑ b ∈ range p, g a * ((a * p + b : ℕ) : ℤ) ^ d [ZMOD (p : ℤ) ^ (m + 1)] := by
        rw [hM_eq, sum_range_mul_eq M' p]
        refine Int.ModEq.sum fun a ha => Int.ModEq.sum fun b hb => ?_
        rw [mem_range] at ha hb
        have h1 : (-1 : ℤ) ^ (a * p + b) * (Nat.choose (M' * p + T + (a * p + b)) (T + (a * p + b)) : ℤ) *
            (Nat.choose (M' * p - 1) (a * p + b) : ℤ) * (Nat.choose (M' * p + (a * p + b)) (a * p + b) : ℤ) ≡
            g a [ZMOD (p : ℤ) ^ (m + 1)] := by simpa only [← hM_eq] using hwt a ha b hb
        exact h1.mul_right _
      have hcong_mul : (p : ℤ) ^ d * ∑ q ∈ range M, (-1 : ℤ) ^ q *
            (Nat.choose (M + T + q) (T + q) : ℤ) * (Nat.choose (M - 1) q : ℤ) * (Nat.choose (M + q) q : ℤ) * (q : ℤ) ^ d ≡
          (p : ℤ) ^ d * ∑ a ∈ range M', ∑ b ∈ range p, g a * ((a * p + b : ℕ) : ℤ) ^ d [ZMOD (p : ℤ) ^ (m + 2)] := by
        have h1 := Int.modEq_iff_dvd.mp hcong_m
        have h2 := mul_dvd_mul_left ((p : ℤ) ^ d) h1
        rw [mul_comm ((p : ℤ) ^ d) ((p : ℤ) ^ (m + 1)), ← pow_add] at h2
        exact Int.modEq_iff_dvd.mpr (by simpa [mul_sub] using dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) h2)
      have hbin : (p : ℤ) ^ d * ∑ a ∈ range M', ∑ b ∈ range p, g a * ((a * p + b : ℕ) : ℤ) ^ d =
          ∑ j ∈ range (d + 1), (Nat.choose d j : ℤ) * (p : ℤ) ^ d *
            (∑ b ∈ range p, (b : ℤ) ^ (d - j)) *
            ((p : ℤ) ^ j * ∑ a ∈ range M', g a * (a : ℤ) ^ j) := by
        have hexp : ∀ a b : ℕ, ((a * p + b : ℕ) : ℤ) ^ d =
            ∑ j ∈ range (d + 1), (Nat.choose d j : ℤ) * (b : ℤ) ^ (d - j) * ((p : ℤ) ^ j * (a : ℤ) ^ j) := by
          intro a b; push_cast; rw [add_pow]
          refine Finset.sum_congr rfl fun j _ => ?_; rw [mul_pow]; ring
        calc (p : ℤ) ^ d * ∑ a ∈ range M', ∑ b ∈ range p, g a * ((a * p + b : ℕ) : ℤ) ^ d
            = ∑ a ∈ range M', ∑ b ∈ range p, ∑ j ∈ range (d + 1),
              (p : ℤ) ^ d * (g a * ((Nat.choose d j : ℤ) * (b : ℤ) ^ (d - j) * ((p : ℤ) ^ j * (a : ℤ) ^ j))) := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_
              rw [hexp, Finset.mul_sum, Finset.mul_sum]
          _ = ∑ a ∈ range M', ∑ j ∈ range (d + 1), ∑ b ∈ range p,
              (p : ℤ) ^ d * (g a * ((Nat.choose d j : ℤ) * (b : ℤ) ^ (d - j) * ((p : ℤ) ^ j * (a : ℤ) ^ j))) :=
              Finset.sum_congr rfl fun _ _ => Finset.sum_comm
          _ = ∑ j ∈ range (d + 1), ∑ a ∈ range M', ∑ b ∈ range p,
              (p : ℤ) ^ d * (g a * ((Nat.choose d j : ℤ) * (b : ℤ) ^ (d - j) * ((p : ℤ) ^ j * (a : ℤ) ^ j))) :=
              Finset.sum_comm
          _ = _ := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_comm]; symm
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun a _ => ?_; ring
      have hdvd_rhs : (p : ℤ) ^ (m + 2) ∣
          (p : ℤ) ^ d * ∑ a ∈ range M', ∑ b ∈ range p, g a * ((a * p + b : ℕ) : ℤ) ^ d := by
        rw [hbin]
        refine Finset.dvd_sum fun j _ => ?_
        by_cases hj : 1 ≤ j
        · have h3 : (p : ℤ) ^ 1 * (p : ℤ) ^ (m + 1) ∣
              ((Nat.choose d j : ℤ) * (p : ℤ) ^ d * ∑ b ∈ range p, (b : ℤ) ^ (d - j)) *
              ((p : ℤ) ^ j * ∑ a ∈ range M', g a * (a : ℤ) ^ j) :=
            mul_dvd_mul (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow (p : ℤ) hd) _) _) (ihd j hj)
          rwa [← pow_add, show 1 + (m + 1) = m + 2 by omega] at h3
        · have hj0 : j = 0 := by omega
          subst hj0; simp only [Nat.sub_zero, pow_zero, mul_one, one_mul, Nat.choose_zero_right, Nat.cast_one]
          by_cases hd2 : 2 ≤ d
          · have h3 : (p : ℤ) ^ 2 * (p : ℤ) ^ m ∣ ((p : ℤ) ^ d * ∑ b ∈ range p, (b : ℤ) ^ d) * ∑ a ∈ range M', g a :=
              mul_dvd_mul (dvd_mul_of_dvd_left (pow_dvd_pow (p : ℤ) hd2) _) ih0
            rwa [← pow_add, show 2 + m = m + 2 by omega] at h3
          · have hd1 : d = 1 := by omega
            subst hd1; simp only [pow_one]
            have h3 : (p : ℤ) * (p : ℤ) * (p : ℤ) ^ m ∣
                ((p : ℤ) * ∑ b ∈ range p, (b : ℤ)) * ∑ a ∈ range M', g a :=
              mul_dvd_mul (mul_dvd_mul_left (p : ℤ) (p_dvd_sum_range_id p hp hp5)) ih0
            rwa [show (p : ℤ) * (p : ℤ) * (p : ℤ) ^ m = (p : ℤ) ^ (m + 2) by
              rw [show m + 2 = 1 + 1 + m by omega, pow_add, pow_add, pow_one]] at h3
      exact dvd_sub hdvd_rhs (Int.modEq_iff_dvd.mp hcong_mul) |> fun h => by simpa using h

/-- D3: b1 bucket vanishes per fixed (m2, m3) modulo p^(3*r). -/
private lemma part2_b1_pair (p M r m₂ m₃ : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 1 ≤ r) (hM : p ^ (r - 1) ∣ M) (hMpos : 1 ≤ M) (_hm2 : m₂ < M) (_hm3 : m₃ < M) :
    PVal p (3 * r)
      ((cJ (M * p - 1) (p * m₂) : ℚ) * (cJ (M * p - 1) (p * m₃) : ℚ) *
        ∑ j ∈ (range (M * p)).filter (fun j => ¬ p ∣ j),
          (-1 : ℚ) ^ j * (Nat.choose (M * p - 1 + (j + p * m₂ + p * m₃)) (j + p * m₂ + p * m₃) : ℚ) *
            (cJ (M * p - 1) j : ℚ)) := by
  set N := M * p
  set T := m₂ + m₃
  have hNpos : 1 ≤ N := Nat.mul_pos hMpos hp.pos
  have hN_dvd : p ^ r ∣ N := by
    have : p ^ (r - 1) * p ∣ M * p := Nat.mul_dvd_mul_right hM p
    rwa [← pow_succ, Nat.sub_add_cancel hr] at this
  have hvpN : r ≤ vp p N := vp_le_of_dvd hp (by omega) hN_dvd
  set m := if T = 0 then r - 1 else min (r - 1) (vp p T)
  have hm_le : m ≤ r - 1 := by
    simp only [m]; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hm_M : p ^ m ∣ M := dvd_trans (Nat.pow_dvd_pow p hm_le) hM
  have hm_T : p ^ m ∣ T := by
    simp only [m]; split_ifs with hT0
    · rw [hT0]; exact dvd_zero _
    · exact dvd_trans (Nat.pow_dvd_pow p (min_le_right _ _)) (vp_dvd hp hT0)
  -- Outer factor valuation >= r - 1 - m
  have houter : PVal p (r - 1 - m) ((cJ (N - 1) (p * m₂) : ℚ) * (cJ (N - 1) (p * m₃) : ℚ)) := by
    by_cases hmr : m = r - 1
    · rw [hmr, Nat.sub_self]; exact (PVal.int hp _).mul_zero hp (PVal.int hp _)
    · have hTne : T ≠ 0 := by intro h0; simp [m, h0] at hmr
      have hm_eq : m = vp p T := by
        simp only [m, hTne, ↓reduceIte] at hmr ⊢
        exact min_eq_right (by omega)
      have hex : (1 ≤ m₂ ∧ vp p m₂ ≤ m) ∨ (1 ≤ m₃ ∧ vp p m₃ ≤ m) := by
        by_contra hnot; push Not at hnot
        have hd : ∀ x, (x = 0 ∨ m < vp p x) → p ^ (m + 1) ∣ x := by
          intro x hx; rcases hx with rfl | hgt
          · exact dvd_zero _
          · exact dvd_trans (Nat.pow_dvd_pow p hgt) (vp_dvd hp (by intro h0; subst h0; simp [vp] at hgt))
        have hd2 := hd m₂ (by by_cases h0 : m₂ = 0; left; exact h0; right; exact hnot.1 (by omega))
        have hd3 := hd m₃ (by by_cases h0 : m₃ = 0; left; exact h0; right; exact hnot.2 (by omega))
        have hdT : p ^ (m + 1) ∣ T := dvd_add hd2 hd3
        rw [hm_eq] at hdT; exact vp_succ_not_dvd hp hTne hdT
      rcases hex with ⟨h1, hv1⟩ | ⟨h1, hv1⟩
      · have hc : PVal p (vp p N - vp p (p * m₂)) (cJ (N - 1) (p * m₂) : ℚ) := by
          simp only [cJ, Int.cast_mul, Int.cast_natCast]
          exact (PVal.nat hp _).zero_mul hp (PVal.of_dvd_nat hp (vp_choose_pred_add_ge p N (p * m₂) hp (Nat.mul_pos hp.pos h1) (by omega)))
        refine (hc.mul_zero hp (PVal.int hp _)).mono ?_; rw [vp_mul_p hp h1]; omega
      · have hc : PVal p (vp p N - vp p (p * m₃)) (cJ (N - 1) (p * m₃) : ℚ) := by
          simp only [cJ, Int.cast_mul, Int.cast_natCast]
          exact (PVal.nat hp _).zero_mul hp (PVal.of_dvd_nat hp (vp_choose_pred_add_ge p N (p * m₃) hp (Nat.mul_pos hp.pos h1) (by omega)))
        refine ((PVal.int hp _).zero_mul hp hc).mono ?_; rw [vp_mul_p hp h1]; omega
  -- Inner sum lies in p^(2*r + m + 1) Z_(p)
  have hinner : PVal p (2 * r + m + 1)
      (∑ j ∈ (range N).filter (fun j => ¬ p ∣ j),
        (-1 : ℚ) ^ j * (Nat.choose (N - 1 + (j + p * m₂ + p * m₃)) (j + p * m₂ + p * m₃) : ℚ) *
          (cJ (N - 1) j : ℚ)) := by
    rw [sum_filter_not_dvd_range_mul M p hp]
    set target : ℕ → ℕ → ℚ := fun q s =>
      (N : ℚ) ^ 2 * (-1 : ℚ) ^ q * (Nat.choose (M + T + q) (T + q) : ℚ) *
        (Nat.choose (M - 1) q : ℚ) * (Nat.choose (M + q) q : ℚ) *
        ((((T + q : ℕ) : ℚ) * (p : ℚ) + (s : ℚ)) * ((q : ℚ) * (p : ℚ) + (s : ℚ)))⁻¹
    have hpodd : p ≠ 2 := by omega
    have hp_odd : Odd p := hp.odd_of_ne_two hpodd
    have hstep1 : PVal p (2 * r + m + 1)
        ((∑ q ∈ range M, ∑ s ∈ Ico 1 p,
          (-1 : ℚ) ^ (q * p + s) *
            (Nat.choose (N - 1 + (q * p + s + p * m₂ + p * m₃)) (q * p + s + p * m₂ + p * m₃) : ℚ) *
            (cJ (N - 1) (q * p + s) : ℚ)) -
         (∑ q ∈ range M, ∑ s ∈ Ico 1 p, target q s)) := by
      rw [← Finset.sum_sub_distrib]
      refine PVal.sum hp fun q hq => ?_
      rw [← Finset.sum_sub_distrib]
      refine PVal.sum hp fun s hs => ?_
      rw [mem_range] at hq; rw [mem_Ico] at hs
      have hidx : q * p + s + p * m₂ + p * m₃ = (T + q) * p + s := by simp only [T]; ring
      rw [hidx]
      have hf1 := choose_pred_add_ndiv_exact p M (T + q) s hp hMpos hs.1 hs.2
      have hf2 := choose_pred_p_shift_general p M (q * p + s) hp hpodd (by nlinarith [hp.pos])
      have hf3 := choose_pred_add_ndiv_exact p M q s hp hMpos hs.1 hs.2
      have hdiv_j : (q * p + s) / p = q := by
        rw [mul_comm q p, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hs.2, add_zero]
      have hmod_j : (q * p + s) % p = s := by
        rw [mul_comm q p, Nat.mul_add_mod, Nat.mod_eq_of_lt hs.2]
      rw [hdiv_j, hmod_j] at hf2
      set P1 : ℚ := ∏ i ∈ (Ico 1 ((T + q) * p + s)).filter (fun i => ¬ p ∣ i), (1 + (N : ℚ) / (i : ℚ))
      set P2 : ℚ := ∏ i ∈ (Ico 1 (q * p + s + 1)).filter (fun i => ¬ p ∣ i), (1 - (N : ℚ) / (i : ℚ))
      set P3 : ℚ := ∏ i ∈ (Ico 1 (q * p + s)).filter (fun i => ¬ p ∣ i), (1 + (N : ℚ) / (i : ℚ))
      have hP1 : PVal p r (P1 - 1) := PVal.prod_one_add hp fun i hi =>
        (PVal.of_dvd_nat hp hN_dvd).div_nat hp (Finset.mem_filter.mp hi).2
      have hP2 : PVal p r (P2 - 1) := by
        have h := PVal.prod_one_add hp (s := (Ico 1 (q * p + s + 1)).filter (fun i => ¬ p ∣ i))
          (f := fun i => -(N : ℚ) / (i : ℚ)) fun i hi =>
          (PVal.of_dvd_nat hp hN_dvd).neg.div_nat hp (Finset.mem_filter.mp hi).2
        convert h using 3 with i _; ring
      have hP3 : PVal p r (P3 - 1) := PVal.prod_one_add hp fun i hi =>
        (PVal.of_dvd_nat hp hN_dvd).div_nat hp (Finset.mem_filter.mp hi).2
      have hP123 : PVal p r (P1 * P2 * P3 - 1) := by
        have heq : P1 * P2 * P3 - 1 = (P1 - 1) * P2 * P3 + (P2 - 1) * P3 + (P3 - 1) := by ring
        rw [heq]
        have hP20 : PVal p 0 P2 := by
          have : P2 = (P2 - 1) + 1 := by ring
          rw [this]; exact (hP2.mono (Nat.zero_le _)).add hp (PVal.nat hp 1)
        have hP30 : PVal p 0 P3 := by
          have : P3 = (P3 - 1) + 1 := by ring
          rw [this]; exact (hP3.mono (Nat.zero_le _)).add hp (PVal.nat hp 1)
        exact (((hP1.mul_zero hp hP20).mul_zero hp hP30).add hp (hP2.mul_zero hp hP30)).add hp hP3
      have hterm_eq : (-1 : ℚ) ^ (q * p + s) * (Nat.choose (N - 1 + ((T + q) * p + s)) ((T + q) * p + s) : ℚ) *
            (cJ (N - 1) (q * p + s) : ℚ) = target q s * (P1 * P2 * P3) := by
        simp only [cJ, Int.cast_mul, Int.cast_natCast, target]
        have hf1' : (Nat.choose (N - 1 + ((T + q) * p + s)) ((T + q) * p + s) : ℚ) =
            ((N : ℚ) / (((T + q) * p + s : ℕ) : ℚ)) * (Nat.choose (M + (T + q)) (T + q) : ℚ) * P1 := by
          simpa only [N, P1, Nat.cast_mul] using hf1
        have hf2' : (Nat.choose (N - 1) (q * p + s) : ℚ) =
            (-1 : ℚ) ^ s * (Nat.choose (M - 1) q : ℚ) * P2 := by
          simpa only [N, P2, Nat.cast_mul] using hf2
        have hf3' : (Nat.choose (N - 1 + (q * p + s)) (q * p + s) : ℚ) =
            ((N : ℚ) / ((q * p + s : ℕ) : ℚ)) * (Nat.choose (M + q) q : ℚ) * P3 := by
          simpa only [N, P3, Nat.cast_mul] using hf3
        rw [hf1', hf2', hf3', show M + (T + q) = M + T + q by omega]
        have hs_eq : (-1 : ℚ) ^ (q * p + s) * (-1 : ℚ) ^ s = (-1 : ℚ) ^ q := by
          rw [pow_add, mul_comm q p, pow_mul, hp_odd.neg_one_pow, mul_assoc, ← pow_add, ← two_mul, pow_mul]
          norm_num
        have hd_eq : (((T + q) * p + s : ℕ) : ℚ)⁻¹ * ((q * p + s : ℕ) : ℚ)⁻¹ =
            ((((T + q : ℕ) : ℚ) * (p : ℚ) + (s : ℚ)) * ((q : ℚ) * (p : ℚ) + (s : ℚ)))⁻¹ := by
          rw [← mul_inv]; push_cast; rfl
        rw [div_eq_mul_inv, div_eq_mul_inv]
        calc (-1 : ℚ) ^ (q * p + s) * ((N : ℚ) * (((T + q) * p + s : ℕ) : ℚ)⁻¹ * (Nat.choose (M + T + q) (T + q) : ℚ) * P1) *
              ((-1 : ℚ) ^ s * (Nat.choose (M - 1) q : ℚ) * P2 * ((N : ℚ) * ((q * p + s : ℕ) : ℚ)⁻¹ * (Nat.choose (M + q) q : ℚ) * P3))
            = (N : ℚ) ^ 2 * ((-1 : ℚ) ^ (q * p + s) * (-1 : ℚ) ^ s) * (Nat.choose (M + T + q) (T + q) : ℚ) *
              (Nat.choose (M - 1) q : ℚ) * (Nat.choose (M + q) q : ℚ) *
              ((((T + q) * p + s : ℕ) : ℚ)⁻¹ * ((q * p + s : ℕ) : ℚ)⁻¹) * (P1 * P2 * P3) := by ring
          _ = _ := by rw [hs_eq, hd_eq]
      rw [hterm_eq, show target q s * (P1 * P2 * P3) - target q s = target q s * (P1 * P2 * P3 - 1) by ring]
      have ht_pv : PVal p (2 * r) (target q s) := by
        simp only [target]
        have hN2 : PVal p (2 * r) ((N : ℚ) ^ 2) := by simpa [mul_comm] using (PVal.of_dvd_nat hp hN_dvd).pow hp 2
        have hnd1 : ¬ p ∣ (T + q) * p + s := fun h => by
          have := Nat.le_of_dvd hs.1 ((Nat.dvd_add_right (dvd_mul_left p (T + q))).mp h); omega
        have hnd2 : ¬ p ∣ q * p + s := fun h => by
          have := Nat.le_of_dvd hs.1 ((Nat.dvd_add_right (dvd_mul_left p q)).mp h); omega
        have hinv : PVal p 0 ((((T + q : ℕ) : ℚ) * (p : ℚ) + (s : ℚ)) * ((q : ℚ) * (p : ℚ) + (s : ℚ)))⁻¹ := by
          have hnd : ¬ p ∣ ((T + q) * p + s) * (q * p + s) := fun h => by
            rcases hp.dvd_mul.mp h with h1 | h2; exact hnd1 h1; exact hnd2 h2
          simpa [Nat.cast_mul, Nat.cast_add] using PVal.inv_nat hnd
        have hq0 : PVal p 0 ((-1 : ℚ) ^ q) := by simpa using (PVal.int hp (-1)).pow hp q
        exact ((((hN2.mul_zero hp hq0).mul_zero hp (PVal.nat hp _)).mul_zero hp (PVal.nat hp _)).mul_zero hp (PVal.nat hp _)).mul_zero hp hinv
      exact (ht_pv.mul hp hP123).mono (by omega)
    -- Step 2: Expand 1/(((T+q)p+s)(qp+s)) via inv_bivar_geom_series up to m+1 terms
    have hstep2 : PVal p (2 * r + m + 1) (∑ q ∈ range M, ∑ s ∈ Ico 1 p, target q s) := by
      set ser : ℕ → ℕ → ℚ := fun q s =>
        ∑ d ∈ range (m + 1), (-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
          ∑ i ∈ range (d + 1), ((T + q : ℕ) : ℚ) ^ i * (q : ℚ) ^ (d - i)
      have happrox : PVal p (2 * r + m + 1)
          ((∑ q ∈ range M, ∑ s ∈ Ico 1 p, target q s) -
           (∑ q ∈ range M, ∑ s ∈ Ico 1 p,
             (N : ℚ) ^ 2 * (-1 : ℚ) ^ q * (Nat.choose (M + T + q) (T + q) : ℚ) *
               (Nat.choose (M - 1) q : ℚ) * (Nat.choose (M + q) q : ℚ) * ser q s)) := by
        rw [← Finset.sum_sub_distrib]; refine PVal.sum hp fun q _ => ?_
        rw [← Finset.sum_sub_distrib]; refine PVal.sum hp fun s hs => ?_
        rw [mem_Ico] at hs
        have hgeom := inv_bivar_geom_series p (m + 1) s ((T + q : ℕ) : ℤ) (q : ℤ) hp hs.1 hs.2
        have hgeom' : PVal p (m + 1)
            (((((T + q : ℕ) : ℚ) * (p : ℚ) + (s : ℚ)) * ((q : ℚ) * (p : ℚ) + (s : ℚ)))⁻¹ - ser q s) := by
          simpa only [ser, Int.cast_natCast] using hgeom
        have hbase : PVal p (2 * r)
            ((N : ℚ) ^ 2 * (-1 : ℚ) ^ q * (Nat.choose (M + T + q) (T + q) : ℚ) *
              (Nat.choose (M - 1) q : ℚ) * (Nat.choose (M + q) q : ℚ)) := by
          have hN2 : PVal p (2 * r) ((N : ℚ) ^ 2) := by simpa [mul_comm] using (PVal.of_dvd_nat hp hN_dvd).pow hp 2
          have hq0 : PVal p 0 ((-1 : ℚ) ^ q) := by simpa using (PVal.int hp (-1)).pow hp q
          exact (((hN2.mul_zero hp hq0).mul_zero hp (PVal.nat hp _)).mul_zero hp (PVal.nat hp _)).mul_zero hp (PVal.nat hp _)
        have hsub : target q s - (N : ℚ) ^ 2 * (-1 : ℚ) ^ q * (Nat.choose (M + T + q) (T + q) : ℚ) *
            (Nat.choose (M - 1) q : ℚ) * (Nat.choose (M + q) q : ℚ) * ser q s =
            ((N : ℚ) ^ 2 * (-1 : ℚ) ^ q * (Nat.choose (M + T + q) (T + q) : ℚ) *
              (Nat.choose (M - 1) q : ℚ) * (Nat.choose (M + q) q : ℚ)) *
            (((((T + q : ℕ) : ℚ) * (p : ℚ) + (s : ℚ)) * ((q : ℚ) * (p : ℚ) + (s : ℚ)))⁻¹ - ser q s) := by
          simp only [target]; ring
        rw [hsub]; exact (hbase.mul hp hgeom').mono (by omega)
      have hser_zero : PVal p (2 * r + m + 1)
          (∑ q ∈ range M, ∑ s ∈ Ico 1 p,
            (N : ℚ) ^ 2 * (-1 : ℚ) ^ q * (Nat.choose (M + T + q) (T + q) : ℚ) *
              (Nat.choose (M - 1) q : ℚ) * (Nat.choose (M + q) q : ℚ) * ser q s) := by
        set w : ℕ → ℚ := fun q =>
          (-1 : ℚ) ^ q * (Nat.choose (M + T + q) (T + q) : ℚ) *
            (Nat.choose (M - 1) q : ℚ) * (Nat.choose (M + q) q : ℚ)
        have hswap : ∑ q ∈ range M, ∑ s ∈ Ico 1 p,
              (N : ℚ) ^ 2 * (-1 : ℚ) ^ q * (Nat.choose (M + T + q) (T + q) : ℚ) *
                (Nat.choose (M - 1) q : ℚ) * (Nat.choose (M + q) q : ℚ) * ser q s =
            ∑ d ∈ range (m + 1), (N : ℚ) ^ 2 * (-1 : ℚ) ^ d *
              (∑ s ∈ Ico 1 p, ((s : ℚ) ^ (d + 2))⁻¹) *
              ((p : ℚ) ^ d * ∑ i ∈ range (d + 1), ∑ q ∈ range M,
                w q * (((T + q : ℕ) : ℚ) ^ i * (q : ℚ) ^ (d - i))) := by
          calc ∑ q ∈ range M, ∑ s ∈ Ico 1 p, (N : ℚ) ^ 2 * (-1 : ℚ) ^ q * (Nat.choose (M + T + q) (T + q) : ℚ) *
                (Nat.choose (M - 1) q : ℚ) * (Nat.choose (M + q) q : ℚ) * ser q s
              = ∑ q ∈ range M, ∑ d ∈ range (m + 1), ∑ s ∈ Ico 1 p,
                (N : ℚ) ^ 2 * w q * ((-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
                  ∑ i ∈ range (d + 1), ((T + q : ℕ) : ℚ) ^ i * (q : ℚ) ^ (d - i)) := by
                refine Finset.sum_congr rfl fun q _ => ?_
                have hq_exp : ∑ s ∈ Ico 1 p, (N : ℚ) ^ 2 * (-1 : ℚ) ^ q * (Nat.choose (M + T + q) (T + q) : ℚ) *
                    (Nat.choose (M - 1) q : ℚ) * (Nat.choose (M + q) q : ℚ) * ser q s =
                    ∑ s ∈ Ico 1 p, ∑ d ∈ range (m + 1),
                    (N : ℚ) ^ 2 * w q * ((-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
                      ∑ i ∈ range (d + 1), ((T + q : ℕ) : ℚ) ^ i * (q : ℚ) ^ (d - i)) := by
                  refine Finset.sum_congr rfl fun s _ => ?_
                  simp only [ser, w, Finset.mul_sum]
                  refine Finset.sum_congr rfl fun d _ => by ring
                rw [hq_exp, Finset.sum_comm]
            _ = ∑ d ∈ range (m + 1), ∑ q ∈ range M, ∑ s ∈ Ico 1 p,
                (N : ℚ) ^ 2 * w q * ((-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
                  ∑ i ∈ range (d + 1), ((T + q : ℕ) : ℚ) ^ i * (q : ℚ) ^ (d - i)) := Finset.sum_comm
            _ = _ := by
                refine Finset.sum_congr rfl fun d _ => ?_
                symm
                rw [Finset.mul_sum (s := Ico 1 p), Finset.sum_mul, Finset.sum_comm (s := range M) (t := Ico 1 p)]
                -- Rewrite inner sum over i, q to q, i
                have hinner_eq : ∀ s ∈ Ico 1 p,
                    (N : ℚ) ^ 2 * (-1 : ℚ) ^ d * ((s : ℚ) ^ (d + 2))⁻¹ *
                      ((p : ℚ) ^ d * ∑ i ∈ range (d + 1), ∑ q ∈ range M, w q * (((T + q : ℕ) : ℚ) ^ i * (q : ℚ) ^ (d - i))) =
                    ∑ q ∈ range M, (N : ℚ) ^ 2 * w q * ((-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
                      ∑ i ∈ range (d + 1), ((T + q : ℕ) : ℚ) ^ i * (q : ℚ) ^ (d - i)) := by
                  intro s _
                  rw [Finset.sum_comm (s := range (d + 1)) (t := range M), Finset.mul_sum, Finset.mul_sum]
                  refine Finset.sum_congr rfl fun q _ => ?_
                  rw [← Finset.mul_sum, div_eq_mul_inv]; ring
                exact Finset.sum_congr rfl hinner_eq
        rw [hswap]
        have ⟨hm0, hmd⟩ := part2_b1_moment_dvd p m hp hp5 M T hMpos hm_M hm_T
        refine PVal.sum hp fun d _ => ?_
        have hN2 : PVal p (2 * r) ((N : ℚ) ^ 2) := by simpa [mul_comm] using (PVal.of_dvd_nat hp hN_dvd).pow hp 2
        have hd0_sign : PVal p 0 ((-1 : ℚ) ^ d) := by simpa using (PVal.int hp (-1)).pow hp d
        by_cases hd0 : d = 0
        · subst hd0
          have hs2 := sum_inv_sq_mod_p p hp hp5
          have hq0 : PVal p m ((p : ℚ) ^ 0 * ∑ i ∈ range 1, ∑ q ∈ range M,
              w q * (((T + q : ℕ) : ℚ) ^ i * (q : ℚ) ^ (0 - i))) := by
            have h1 := PVal.of_dvd_int hp hm0
            convert h1 using 1; simp [w]
          exact (((hN2.mul_zero hp hd0_sign).mul hp hs2).mul hp hq0).mono (by omega)
        · have hs_pv : PVal p 0 (∑ s ∈ Ico 1 p, ((s : ℚ) ^ (d + 2))⁻¹) := by
            refine PVal.sum hp fun s hs => ?_
            rw [mem_Ico] at hs
            have hnds : ¬ p ∣ s ^ (d + 2) := fun h => by
              have := Nat.le_of_dvd hs.1 (hp.dvd_of_dvd_pow h); omega
            simpa [Nat.cast_pow] using PVal.inv_nat hnds
          -- Expand (T + q)^i * q^(d - i) using binomial theorem
          have hinner_d : PVal p (m + 1)
              ((p : ℚ) ^ d * ∑ i ∈ range (d + 1), ∑ q ∈ range M,
                w q * (((T + q : ℕ) : ℚ) ^ i * (q : ℚ) ^ (d - i))) := by
            rw [Finset.mul_sum]
            refine PVal.sum hp fun i hi => ?_
            rw [mem_range] at hi
            have hexp : ∑ q ∈ range M, w q * (((T + q : ℕ) : ℚ) ^ i * (q : ℚ) ^ (d - i)) =
                ∑ u ∈ range (i + 1), (Nat.choose i u : ℚ) * (T : ℚ) ^ (i - u) *
                  ∑ q ∈ range M, w q * (q : ℚ) ^ (u + (d - i)) := by
              calc ∑ q ∈ range M, w q * (((T + q : ℕ) : ℚ) ^ i * (q : ℚ) ^ (d - i))
                  = ∑ q ∈ range M, ∑ u ∈ range (i + 1),
                    (Nat.choose i u : ℚ) * (T : ℚ) ^ (i - u) * (w q * (q : ℚ) ^ (u + (d - i))) := by
                    refine Finset.sum_congr rfl fun q _ => ?_
                    rw [Nat.cast_add, add_comm (T : ℚ) (q : ℚ), add_pow, Finset.sum_mul, Finset.mul_sum]
                    refine Finset.sum_congr rfl fun u _ => ?_
                    rw [pow_add]; ring
                _ = ∑ u ∈ range (i + 1), ∑ q ∈ range M,
                    (Nat.choose i u : ℚ) * (T : ℚ) ^ (i - u) * (w q * (q : ℚ) ^ (u + (d - i))) := Finset.sum_comm
                _ = _ := Finset.sum_congr rfl fun u _ => (Finset.mul_sum ..).symm
            rw [hexp, Finset.mul_sum]
            refine PVal.sum hp fun u hu => ?_
            rw [mem_range] at hu
            set e := u + (d - i)
            have he_le : e ≤ d := by omega
            by_cases he0 : e = 0
            · have hq0 : PVal p m (∑ q ∈ range M, w q * (q : ℚ) ^ e) := by
                have h1 := PVal.of_dvd_int hp hm0
                convert h1 using 1; simp [w, he0]
              have hp_d : PVal p 1 ((p : ℚ) ^ d) := (PVal.of_pow_p hp).mono (by omega)
              have hc : PVal p 0 ((Nat.choose i u : ℚ) * (T : ℚ) ^ (i - u)) :=
                (PVal.nat hp _).mul_zero hp (by simpa using (PVal.nat hp T).pow hp (i - u))
              have hre : (p : ℚ) ^ d * ((Nat.choose i u : ℚ) * (T : ℚ) ^ (i - u) * ∑ q ∈ range M, w q * (q : ℚ) ^ e) =
                  (p : ℚ) ^ d * ((Nat.choose i u : ℚ) * (T : ℚ) ^ (i - u)) * ∑ q ∈ range M, w q * (q : ℚ) ^ e := by ring
              rw [hre]; exact ((hp_d.mul_zero hp hc).mul hp hq0).mono (by omega)
            · have hqe : PVal p (m + 1) ((p : ℚ) ^ e * ∑ q ∈ range M, w q * (q : ℚ) ^ e) := by
                have h1 := PVal.of_dvd_int hp (hmd e (by omega))
                convert h1 using 1; simp [w]
              have hre : (p : ℚ) ^ d * ((Nat.choose i u : ℚ) * (T : ℚ) ^ (i - u) * ∑ q ∈ range M, w q * (q : ℚ) ^ e) =
                  ((p : ℚ) ^ (d - e) * ((Nat.choose i u : ℚ) * (T : ℚ) ^ (i - u))) *
                    ((p : ℚ) ^ e * ∑ q ∈ range M, w q * (q : ℚ) ^ e) := by
                have : (p : ℚ) ^ (d - e) * (p : ℚ) ^ e = (p : ℚ) ^ d := by rw [← pow_add, Nat.sub_add_cancel he_le]
                calc (p : ℚ) ^ d * ((Nat.choose i u : ℚ) * (T : ℚ) ^ (i - u) * ∑ q ∈ range M, w q * (q : ℚ) ^ e)
                    = ((p : ℚ) ^ (d - e) * (p : ℚ) ^ e) * ((Nat.choose i u : ℚ) * (T : ℚ) ^ (i - u) * ∑ q ∈ range M, w q * (q : ℚ) ^ e) := by rw [this]
                  _ = _ := by ring
              rw [hre]
              have hc : PVal p 0 ((p : ℚ) ^ (d - e) * ((Nat.choose i u : ℚ) * (T : ℚ) ^ (i - u))) :=
                ((PVal.of_pow_p hp).mono (Nat.zero_le _)).mul_zero hp
                  ((PVal.nat hp _).mul_zero hp (by simpa using (PVal.nat hp T).pow hp (i - u)))
              exact hc.zero_mul hp hqe
          exact (((hN2.mul_zero hp hd0_sign).mul_zero hp hs_pv).mul hp hinner_d).mono (by omega)
      have hfin := happrox.add hp hser_zero
      simpa using hfin
    have hfin := hstep1.add hp hstep2
    simpa using hfin
  exact (houter.mul hp hinner).mono (by omega)

/-- Helper weight for D4 double-sum inductive lemma. -/
private def w2 (M m₃ q₁ q₂ : ℕ) : ℤ :=
  (-1 : ℤ) ^ (q₁ + q₂) *
    (Nat.choose (M - 1 + (q₁ + q₂ + m₃ + 1)) (q₁ + q₂ + m₃ + 1) : ℤ) *
    (Nat.choose (M - 1) q₁ : ℤ) * (Nat.choose (M + q₁) q₁ : ℤ) *
    (Nat.choose (M - 1) q₂ : ℤ) * (Nat.choose (M + q₂) q₂ : ℤ)

private def W2 (p M m₃ a b : ℕ) : ℤ :=
  (p : ℤ) ^ (a + b) * ∑ q₁ ∈ range M, ∑ q₂ ∈ range M,
    w2 M m₃ q₁ q₂ * (q₁ : ℤ) ^ a * ((q₂ + 1 : ℕ) : ℤ) ^ b

/-- D4: Double-sum inductive moment lemma for b2 of (P2). -/
private lemma part2_b2_moment_dvd (p m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ M m₃ : ℕ, 1 ≤ M → p ^ m ∣ M → p ^ m ∣ m₃ →
      ((p : ℤ) ^ m ∣ W2 p M m₃ 0 0) ∧
      (∀ a b : ℕ, 1 ≤ a + b → (p : ℤ) ^ (m + 1) ∣ W2 p M m₃ a b) := by
  induction m with
  | zero =>
    intro M m₃ _ _ _
    constructor
    · simp
    · intro a b hab
      simp only [W2, zero_add, pow_one]
      exact dvd_mul_of_dvd_left (dvd_pow_self (p : ℤ) (by omega)) _
  | succ m ih =>
    intro M m₃ hMpos hMd hm3d
    obtain ⟨M', hM'eq⟩ := dvd_trans (dvd_pow_self p (by omega)) hMd
    obtain ⟨m₃', hm3'eq⟩ := dvd_trans (dvd_pow_self p (by omega)) hm3d
    have hM_eq : M = M' * p := by linarith
    have hm3_eq : m₃ = m₃' * p := by linarith
    have hM'pos : 1 ≤ M' := by nlinarith [hp.pos]
    have hM'd : p ^ m ∣ M' := (Nat.mul_dvd_mul_iff_left hp.pos).mp (by rw [← pow_succ', ← hM'eq]; exact hMd)
    have hm3'd : p ^ m ∣ m₃' := (Nat.mul_dvd_mul_iff_left hp.pos).mp (by rw [← pow_succ', ← hm3'eq]; exact hm3d)
    have ⟨ih0, ihd⟩ := ih M' m₃' hM'pos hM'd hm3'd
    have hpodd : p ≠ 2 := by omega
    have hp_odd : Odd p := hp.odd_of_ne_two hpodd
    -- Key congruence for w2 M m3 (u1*p + v1) (u2*p + v2) mod p^(m+1)
    have hw2_ndiv : ∀ u₁ < M', ∀ u₂ < M', ∀ v₁ < p, ∀ v₂ < p, v₁ + v₂ ≠ p - 1 →
        (p : ℤ) ^ (m + 1) ∣ w2 M m₃ (u₁ * p + v₁) (u₂ * p + v₂) := by
      intro u₁ _ u₂ _ v₁ hv1 v₂ hv2 hne
      set s := (u₁ * p + v₁) + (u₂ * p + v₂) + m₃ + 1
      have hnds : ¬ p ∣ s := by
        intro h
        have hs_eq : s = (u₁ + u₂ + m₃') * p + (v₁ + v₂ + 1) := by simp only [s, hm3_eq]; ring
        rw [hs_eq] at h
        have hv : p ∣ v₁ + v₂ + 1 := (Nat.dvd_add_right (dvd_mul_left p _)).mp h
        obtain ⟨k, hk⟩ := hv
        have hk1 : k = 1 := by
          by_contra h1
          have : k = 0 ∨ 2 ≤ k := by omega
          rcases this with rfl | h2
          · simp at hk
          · nlinarith
        subst hk1; omega
      have hvp_s : vp p s = 0 := by
        by_contra h0; exact hnds (dvd_trans (dvd_pow_self p h0) (vp_dvd hp (by omega)))
      have hch_dvd : p ^ (m + 1) ∣ Nat.choose (M - 1 + s) s := by
        have h1 := vp_choose_pred_add_ge p M s hp (by omega) (by omega)
        rw [hvp_s, Nat.sub_zero] at h1
        exact dvd_trans (Nat.pow_dvd_pow p (vp_le_of_dvd hp (by omega) hMd)) h1
      have hch_z : (p : ℤ) ^ (m + 1) ∣ (Nat.choose (M - 1 + s) s : ℤ) := by exact_mod_cast hch_dvd
      simp only [w2]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right hch_z _) _) _) _) _
    have hw2_diag : ∀ u₁ < M', ∀ u₂ < M', ∀ v₁ < p,
        w2 M m₃ (u₁ * p + v₁) (u₂ * p + (p - 1 - v₁)) ≡ w2 M' m₃' u₁ u₂ [ZMOD (p : ℤ) ^ (m + 1)] := by
      intro u₁ hu1 u₂ hu2 v₁ hv1
      set v₂ := p - 1 - v₁
      have hv2 : v₂ < p := by omega
      have hs_eq : (u₁ * p + v₁) + (u₂ * p + v₂) + m₃ + 1 = p * (u₁ + u₂ + m₃' + 1) := by
        simp only [v₂, hm3_eq]
        zify [show v₁ ≤ p - 1 by omega, show 1 ≤ p by omega]; ring
      have hch0 : (Nat.choose (M - 1 + ((u₁ * p + v₁) + (u₂ * p + v₂) + m₃ + 1))
            ((u₁ * p + v₁) + (u₂ * p + v₂) + m₃ + 1) : ℤ) ≡
          (Nat.choose (M' - 1 + (u₁ + u₂ + m₃' + 1)) (u₁ + u₂ + m₃' + 1) : ℤ) [ZMOD (p : ℤ) ^ (m + 1)] := by
        rw [hs_eq, hM_eq]
        have hkaz := kazandzidis_pred_add p M' (u₁ + u₂ + m₃' + 1) hp hp5 hM'pos (by omega)
        have hvpM' : m ≤ vp p M' := vp_le_of_dvd hp (by omega) hM'd
        exact PVal.modEq_of_sub hp (by simpa using hkaz.mono (by omega : m + 1 ≤ 3 + 2 * vp p M'))
      have hfactor : ∀ u < M', ∀ v < p,
          (-1 : ℤ) ^ (u * p + v) * (Nat.choose (M - 1) (u * p + v) : ℤ) * (Nat.choose (M + (u * p + v)) (u * p + v) : ℤ) ≡
          (-1 : ℤ) ^ u * (Nat.choose (M' - 1) u : ℤ) * (Nat.choose (M' + u) u : ℤ) [ZMOD (p : ℤ) ^ (m + 1)] := by
        intro u hu v hv
        have ha := choose_pred_mod_pow p M' (m + 1) u v hp hpodd (by rw [← hM_eq]; exact hMd) hu hv
        have hb := choose_shift_mod_pow p M' (m + 1) u v hp (by rw [← hM_eq]; exact hMd) hv
        rw [← hM_eq] at ha hb
        have hm := ((Int.ModEq.refl ((-1 : ℤ) ^ (u * p + v))).mul ha).mul hb
        have hsign : (-1 : ℤ) ^ (u * p + v) * (-1 : ℤ) ^ v = (-1 : ℤ) ^ u := by
          rw [pow_add, mul_comm u p, pow_mul, hp_odd.neg_one_pow, mul_assoc, ← pow_add, ← two_mul, pow_mul]
          norm_num
        have hrhs : (-1 : ℤ) ^ (u * p + v) * ((-1 : ℤ) ^ v * (Nat.choose (M' - 1) u : ℤ)) * (Nat.choose (M' + u) u : ℤ) =
            (-1 : ℤ) ^ u * (Nat.choose (M' - 1) u : ℤ) * (Nat.choose (M' + u) u : ℤ) := by
          calc _ = ((-1 : ℤ) ^ (u * p + v) * (-1 : ℤ) ^ v) * (Nat.choose (M' - 1) u : ℤ) * (Nat.choose (M' + u) u : ℤ) := by ring
            _ = _ := by rw [hsign]
        rwa [hrhs] at hm
      have hf1 := hfactor u₁ hu1 v₁ hv1
      have hf2 := hfactor u₂ hu2 v₂ hv2
      have hprod := (hch0.mul hf1).mul hf2
      have hlhs : (Nat.choose (M - 1 + ((u₁ * p + v₁) + (u₂ * p + v₂) + m₃ + 1))
            ((u₁ * p + v₁) + (u₂ * p + v₂) + m₃ + 1) : ℤ) *
            ((-1 : ℤ) ^ (u₁ * p + v₁) * (Nat.choose (M - 1) (u₁ * p + v₁) : ℤ) * (Nat.choose (M + (u₁ * p + v₁)) (u₁ * p + v₁) : ℤ)) *
            ((-1 : ℤ) ^ (u₂ * p + v₂) * (Nat.choose (M - 1) (u₂ * p + v₂) : ℤ) * (Nat.choose (M + (u₂ * p + v₂)) (u₂ * p + v₂) : ℤ)) =
          w2 M m₃ (u₁ * p + v₁) (u₂ * p + v₂) := by
        simp only [w2, pow_add]; ring
      have hrhs : (Nat.choose (M' - 1 + (u₁ + u₂ + m₃' + 1)) (u₁ + u₂ + m₃' + 1) : ℤ) *
            ((-1 : ℤ) ^ u₁ * (Nat.choose (M' - 1) u₁ : ℤ) * (Nat.choose (M' + u₁) u₁ : ℤ)) *
            ((-1 : ℤ) ^ u₂ * (Nat.choose (M' - 1) u₂ : ℤ) * (Nat.choose (M' + u₂) u₂ : ℤ)) =
          w2 M' m₃' u₁ u₂ := by
        simp only [w2, pow_add]; ring
      rwa [hlhs, hrhs] at hprod
    -- Helper: collapse sum over v₂ < p to single term v₂ = p - 1 - v₁ mod p^(m+1)
    have hinner_v2 : ∀ u₁ < M', ∀ u₂ < M', ∀ v₁ < p, ∀ F : ℕ → ℤ,
        ∑ v₂ ∈ range p, w2 M m₃ (u₁ * p + v₁) (u₂ * p + v₂) * F v₂ ≡
          w2 M' m₃' u₁ u₂ * F (p - 1 - v₁) [ZMOD (p : ℤ) ^ (m + 1)] := by
      intro u₁ hu1 u₂ hu2 v₁ hv1 F
      have hmem : p - 1 - v₁ ∈ range p := by rw [mem_range]; omega
      rw [← Finset.add_sum_erase _ _ hmem]
      have hrest : ∑ v₂ ∈ (range p).erase (p - 1 - v₁), w2 M m₃ (u₁ * p + v₁) (u₂ * p + v₂) * F v₂ ≡
          0 [ZMOD (p : ℤ) ^ (m + 1)] := by
        rw [Int.modEq_zero_iff_dvd]
        refine Finset.dvd_sum fun v₂ hv2 => ?_
        rw [mem_erase, mem_range] at hv2
        exact dvd_mul_of_dvd_left (hw2_ndiv u₁ hu1 u₂ hu2 v₁ hv1 v₂ hv2.2 (by omega)) _
      have hmain := (hw2_diag u₁ hu1 u₂ hu2 v₁ hv1).mul_right (F (p - 1 - v₁))
      simpa only [add_zero] using hmain.add hrest
    constructor
    · -- Part (1): a = b = 0
      have hcong : W2 p M m₃ 0 0 ≡ (p : ℤ) * W2 p M' m₃' 0 0 [ZMOD (p : ℤ) ^ (m + 1)] := by
        simp only [W2, add_zero, pow_zero, one_mul, mul_one]
        rw [hM_eq, sum_range_mul_eq M' p]
        calc ∑ u₁ ∈ range M', ∑ v₁ ∈ range p, ∑ q₂ ∈ range (M' * p), w2 (M' * p) m₃ (u₁ * p + v₁) q₂
            = ∑ u₁ ∈ range M', ∑ v₁ ∈ range p, ∑ u₂ ∈ range M', ∑ v₂ ∈ range p,
              w2 (M' * p) m₃ (u₁ * p + v₁) (u₂ * p + v₂) := by
              refine Finset.sum_congr rfl fun u₁ _ => Finset.sum_congr rfl fun v₁ _ => sum_range_mul_eq M' p _
          _ ≡ ∑ u₁ ∈ range M', ∑ _v₁ ∈ range p, ∑ u₂ ∈ range M', w2 M' m₃' u₁ u₂ [ZMOD (p : ℤ) ^ (m + 1)] := by
              refine Int.ModEq.sum fun u₁ hu1 => Int.ModEq.sum fun v₁ hv1 => Int.ModEq.sum fun u₂ hu2 => ?_
              rw [mem_range] at hu1 hv1 hu2
              simpa only [← hM_eq, mul_one] using hinner_v2 u₁ hu1 u₂ hu2 v₁ hv1 (fun _ => 1)
          _ = (p : ℤ) * ∑ u₁ ∈ range M', ∑ u₂ ∈ range M', w2 M' m₃' u₁ u₂ := by
              simp [Finset.sum_const, Finset.mul_sum]
      have hdvd_rhs : (p : ℤ) ^ (m + 1) ∣ (p : ℤ) * W2 p M' m₃' 0 0 := by
        rw [pow_succ']; exact mul_dvd_mul_left (p : ℤ) ih0
      exact dvd_sub hdvd_rhs (Int.modEq_iff_dvd.mp hcong) |> fun h => by simpa using h
    · -- Part (2): a + b >= 1
      intro a b hab
      set d := a + b
      have hcong_m : ∑ q₁ ∈ range M, ∑ q₂ ∈ range M, w2 M m₃ q₁ q₂ * (q₁ : ℤ) ^ a * ((q₂ + 1 : ℕ) : ℤ) ^ b ≡
          ∑ u₁ ∈ range M', ∑ u₂ ∈ range M', ∑ v₁ ∈ range p,
            w2 M' m₃' u₁ u₂ * ((u₁ * p + v₁ : ℕ) : ℤ) ^ a * (((u₂ + 1) * p - v₁ : ℤ)) ^ b [ZMOD (p : ℤ) ^ (m + 1)] := by
        rw [hM_eq, sum_range_mul_eq M' p]
        calc ∑ u₁ ∈ range M', ∑ v₁ ∈ range p, ∑ q₂ ∈ range (M' * p),
              w2 (M' * p) m₃ (u₁ * p + v₁) q₂ * ((u₁ * p + v₁ : ℕ) : ℤ) ^ a * ((q₂ + 1 : ℕ) : ℤ) ^ b
            = ∑ u₁ ∈ range M', ∑ u₂ ∈ range M', ∑ v₁ ∈ range p, ∑ v₂ ∈ range p,
              w2 (M' * p) m₃ (u₁ * p + v₁) (u₂ * p + v₂) * (((u₁ * p + v₁ : ℕ) : ℤ) ^ a * ((u₂ * p + v₂ + 1 : ℕ) : ℤ) ^ b) := by
              refine Finset.sum_congr rfl fun u₁ _ => ?_
              have h1 : ∀ v₁ ∈ range p, ∑ q₂ ∈ range (M' * p),
                  w2 (M' * p) m₃ (u₁ * p + v₁) q₂ * ((u₁ * p + v₁ : ℕ) : ℤ) ^ a * ((q₂ + 1 : ℕ) : ℤ) ^ b =
                  ∑ u₂ ∈ range M', ∑ v₂ ∈ range p,
                  w2 (M' * p) m₃ (u₁ * p + v₁) (u₂ * p + v₂) * (((u₁ * p + v₁ : ℕ) : ℤ) ^ a * ((u₂ * p + v₂ + 1 : ℕ) : ℤ) ^ b) := by
                intro v₁ _; rw [sum_range_mul_eq M' p]
                refine Finset.sum_congr rfl fun u₂ _ => Finset.sum_congr rfl fun v₂ _ => by ring
              rw [Finset.sum_congr rfl h1, Finset.sum_comm]
          _ ≡ ∑ u₁ ∈ range M', ∑ u₂ ∈ range M', ∑ v₁ ∈ range p,
              w2 M' m₃' u₁ u₂ * ((u₁ * p + v₁ : ℕ) : ℤ) ^ a * (((u₂ + 1) * p - v₁ : ℤ)) ^ b [ZMOD (p : ℤ) ^ (m + 1)] := by
              refine Int.ModEq.sum fun u₁ hu1 => Int.ModEq.sum fun u₂ hu2 => Int.ModEq.sum fun v₁ hv1 => ?_
              rw [mem_range] at hu1 hu2 hv1
              have h := hinner_v2 u₁ hu1 u₂ hu2 v₁ hv1 (fun v₂ => ((u₁ * p + v₁ : ℕ) : ℤ) ^ a * ((u₂ * p + v₂ + 1 : ℕ) : ℤ) ^ b)
              have hq2 : ((u₂ * p + (p - 1 - v₁) + 1 : ℕ) : ℤ) = ((u₂ + 1 : ℕ) : ℤ) * (p : ℤ) - (v₁ : ℤ) := by
                zify [show v₁ ≤ p - 1 by omega, show 1 ≤ p by omega]; ring
              rw [hq2] at h
              simpa only [← hM_eq, mul_assoc, Nat.cast_add, Nat.cast_one] using h
      have hcong_mul : W2 p M m₃ a b ≡
          (p : ℤ) ^ d * ∑ u₁ ∈ range M', ∑ u₂ ∈ range M', ∑ v₁ ∈ range p,
            w2 M' m₃' u₁ u₂ * ((u₁ * p + v₁ : ℕ) : ℤ) ^ a * (((u₂ + 1) * p - v₁ : ℤ)) ^ b [ZMOD (p : ℤ) ^ (m + 2)] := by
        simp only [W2]
        have h1 := Int.modEq_iff_dvd.mp hcong_m
        have h2 := mul_dvd_mul_left ((p : ℤ) ^ d) h1
        rw [mul_comm ((p : ℤ) ^ d) ((p : ℤ) ^ (m + 1)), ← pow_add] at h2
        exact Int.modEq_iff_dvd.mpr (by simpa [mul_sub, d] using dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) h2)
      -- Expand (u1*p + v1)^a * ((u2+1)*p - v1)^b
      have hbin : (p : ℤ) ^ d * ∑ u₁ ∈ range M', ∑ u₂ ∈ range M', ∑ v₁ ∈ range p,
            w2 M' m₃' u₁ u₂ * ((u₁ * p + v₁ : ℕ) : ℤ) ^ a * (((u₂ + 1) * p - v₁ : ℤ)) ^ b =
          ∑ i ∈ range (a + 1), ∑ j ∈ range (b + 1),
            (Nat.choose a i : ℤ) * (Nat.choose b j : ℤ) * (-1 : ℤ) ^ (b - j) * (p : ℤ) ^ d *
            (∑ v₁ ∈ range p, (v₁ : ℤ) ^ (a - i + (b - j))) * W2 p M' m₃' i j := by
        have hexp : ∀ u₁ u₂ v₁ : ℕ,
            ((u₁ * p + v₁ : ℕ) : ℤ) ^ a * (((u₂ + 1) * p - v₁ : ℤ)) ^ b =
            ∑ i ∈ range (a + 1), ∑ j ∈ range (b + 1),
              (Nat.choose a i : ℤ) * (Nat.choose b j : ℤ) * (-1 : ℤ) ^ (b - j) *
              (v₁ : ℤ) ^ (a - i + (b - j)) *
              ((p : ℤ) ^ (i + j) * (u₁ : ℤ) ^ i * ((u₂ + 1 : ℕ) : ℤ) ^ j) := by
          intro u₁ u₂ v₁
          have ha_e : ((u₁ * p + v₁ : ℕ) : ℤ) ^ a =
              ∑ i ∈ range (a + 1), ((u₁ : ℤ) * (p : ℤ)) ^ i * (v₁ : ℤ) ^ (a - i) * (Nat.choose a i : ℤ) := by
            push_cast; exact add_pow _ _ _
          have hb_e : (((u₂ + 1) * p - v₁ : ℤ)) ^ b =
              ∑ j ∈ range (b + 1), (((u₂ + 1 : ℕ) : ℤ) * (p : ℤ)) ^ j * (-(v₁ : ℤ)) ^ (b - j) * (Nat.choose b j : ℤ) := by
            have : (((u₂ + 1) * p - v₁ : ℤ)) = ((u₂ + 1 : ℕ) : ℤ) * (p : ℤ) + (-(v₁ : ℤ)) := by push_cast; ring
            rw [this]; exact add_pow _ _ _
          rw [ha_e, hb_e, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_pow, mul_pow, neg_pow (v₁ : ℤ), pow_add, pow_add]; ring
        calc (p : ℤ) ^ d * ∑ u₁ ∈ range M', ∑ u₂ ∈ range M', ∑ v₁ ∈ range p,
              w2 M' m₃' u₁ u₂ * ((u₁ * p + v₁ : ℕ) : ℤ) ^ a * (((u₂ + 1) * p - v₁ : ℤ)) ^ b
            = ∑ u₁ ∈ range M', ∑ u₂ ∈ range M', ∑ v₁ ∈ range p, ∑ i ∈ range (a + 1), ∑ j ∈ range (b + 1),
              (p : ℤ) ^ d * (w2 M' m₃' u₁ u₂ *
                ((Nat.choose a i : ℤ) * (Nat.choose b j : ℤ) * (-1 : ℤ) ^ (b - j) *
                (v₁ : ℤ) ^ (a - i + (b - j)) *
                ((p : ℤ) ^ (i + j) * (u₁ : ℤ) ^ i * ((u₂ + 1 : ℕ) : ℤ) ^ j))) := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u₁ _ => ?_
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun u₂ _ => ?_
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun v₁ _ => ?_
              rw [mul_assoc, hexp, Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum, Finset.mul_sum]
          _ = ∑ i ∈ range (a + 1), ∑ j ∈ range (b + 1), ∑ v₁ ∈ range p, ∑ u₁ ∈ range M', ∑ u₂ ∈ range M',
              (p : ℤ) ^ d * (w2 M' m₃' u₁ u₂ *
                ((Nat.choose a i : ℤ) * (Nat.choose b j : ℤ) * (-1 : ℤ) ^ (b - j) *
                (v₁ : ℤ) ^ (a - i + (b - j)) *
                ((p : ℤ) ^ (i + j) * (u₁ : ℤ) ^ i * ((u₂ + 1 : ℕ) : ℤ) ^ j))) := by
              -- Swap u1, u2, v1 past i, j
              trans ∑ u₁ ∈ range M', ∑ u₂ ∈ range M', ∑ i ∈ range (a + 1), ∑ j ∈ range (b + 1), ∑ v₁ ∈ range p,
                (p : ℤ) ^ d * (w2 M' m₃' u₁ u₂ *
                  ((Nat.choose a i : ℤ) * (Nat.choose b j : ℤ) * (-1 : ℤ) ^ (b - j) *
                  (v₁ : ℤ) ^ (a - i + (b - j)) *
                  ((p : ℤ) ^ (i + j) * (u₁ : ℤ) ^ i * ((u₂ + 1 : ℕ) : ℤ) ^ j)))
              · refine Finset.sum_congr rfl fun u₁ _ => Finset.sum_congr rfl fun u₂ _ => ?_
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
              trans ∑ u₁ ∈ range M', ∑ i ∈ range (a + 1), ∑ j ∈ range (b + 1), ∑ v₁ ∈ range p, ∑ u₂ ∈ range M',
                (p : ℤ) ^ d * (w2 M' m₃' u₁ u₂ *
                  ((Nat.choose a i : ℤ) * (Nat.choose b j : ℤ) * (-1 : ℤ) ^ (b - j) *
                  (v₁ : ℤ) ^ (a - i + (b - j)) *
                  ((p : ℤ) ^ (i + j) * (u₁ : ℤ) ^ i * ((u₂ + 1 : ℕ) : ℤ) ^ j)))
              · refine Finset.sum_congr rfl fun u₁ _ => ?_
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun j _ => Finset.sum_comm
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Finset.sum_comm]
          _ = _ := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
              symm
              simp only [W2]
              rw [Finset.mul_sum, Finset.sum_mul]
              refine Finset.sum_congr rfl fun v₁ _ => ?_
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun u₁ _ => ?_
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun u₂ _ => ?_; ring
      have hdvd_rhs : (p : ℤ) ^ (m + 2) ∣
          (p : ℤ) ^ d * ∑ u₁ ∈ range M', ∑ u₂ ∈ range M', ∑ v₁ ∈ range p,
            w2 M' m₃' u₁ u₂ * ((u₁ * p + v₁ : ℕ) : ℤ) ^ a * (((u₂ + 1) * p - v₁ : ℤ)) ^ b := by
        rw [hbin]
        refine Finset.dvd_sum fun i _ => Finset.dvd_sum fun j _ => ?_
        by_cases hij : 1 ≤ i + j
        · have h3 : (p : ℤ) ^ 1 * (p : ℤ) ^ (m + 1) ∣
              ((Nat.choose a i : ℤ) * (Nat.choose b j : ℤ) * (-1 : ℤ) ^ (b - j) * (p : ℤ) ^ d *
                ∑ v₁ ∈ range p, (v₁ : ℤ) ^ (a - i + (b - j))) * W2 p M' m₃' i j :=
            mul_dvd_mul (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow (p : ℤ) (by omega : 1 ≤ d)) _) _) (ihd i j hij)
          rwa [← pow_add, show 1 + (m + 1) = m + 2 by omega] at h3
        · have hi0 : i = 0 := by omega
          have hj0 : j = 0 := by omega
          subst hi0; subst hj0
          simp only [Nat.sub_zero]
          by_cases hd2 : 2 ≤ d
          · have h3 : (p : ℤ) ^ 2 * (p : ℤ) ^ m ∣
                ((Nat.choose a 0 : ℤ) * (Nat.choose b 0 : ℤ) * (-1 : ℤ) ^ b * (p : ℤ) ^ d *
                  ∑ v₁ ∈ range p, (v₁ : ℤ) ^ (a + b)) * W2 p M' m₃' 0 0 :=
              mul_dvd_mul (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow (p : ℤ) hd2) _) _) ih0
            rwa [← pow_add, show 2 + m = m + 2 by omega] at h3
          · have hd1 : a + b = 1 := by omega
            have hd_eq : d = 1 := hd1
            rw [hd1, hd_eq, pow_one]
            have hsum_v := p_dvd_sum_range_id p hp hp5
            have h3 : (p : ℤ) * (p : ℤ) * (p : ℤ) ^ m ∣
                ((Nat.choose a 0 : ℤ) * (Nat.choose b 0 : ℤ) * (-1 : ℤ) ^ b * (p : ℤ) *
                  ∑ v₁ ∈ range p, (v₁ : ℤ) ^ 1) * W2 p M' m₃' 0 0 := by
              refine mul_dvd_mul ?_ ih0
              have : (p : ℤ) * (p : ℤ) ∣ (p : ℤ) * ∑ v₁ ∈ range p, (v₁ : ℤ) ^ 1 := by
                simpa only [pow_one] using mul_dvd_mul_left (p : ℤ) hsum_v
              calc (p : ℤ) * (p : ℤ) ∣ (p : ℤ) * ∑ v₁ ∈ range p, (v₁ : ℤ) ^ 1 := this
                _ ∣ ((Nat.choose a 0 : ℤ) * (Nat.choose b 0 : ℤ) * (-1 : ℤ) ^ b) *
                    ((p : ℤ) * ∑ v₁ ∈ range p, (v₁ : ℤ) ^ 1) := dvd_mul_left _ _
                _ = _ := by ring
            rwa [show (p : ℤ) * (p : ℤ) * (p : ℤ) ^ m = (p : ℤ) ^ (m + 2) by
              rw [show m + 2 = 1 + 1 + m by omega, pow_add, pow_add, pow_one]] at h3
      exact dvd_sub hdvd_rhs (Int.modEq_iff_dvd.mp hcong_mul) |> fun h => by simpa using h

/-- D5: b2 bucket with p | (j1 + j2) vanishes per fixed m3 modulo p^(3*r). -/
private lemma part2_b2_m3 (p M r m₃ : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hr : 1 ≤ r) (hM : p ^ (r - 1) ∣ M) (hMpos : 1 ≤ M) (_hm3 : m₃ < M) :
    PVal p (3 * r)
      ((cJ (M * p - 1) (p * m₃) : ℚ) *
        ∑ j₁ ∈ (range (M * p)).filter (fun j => ¬ p ∣ j),
          ∑ j₂ ∈ ((range (M * p)).filter (fun j => ¬ p ∣ j)).filter (fun j₂ => p ∣ j₁ + j₂),
            (-1 : ℚ) ^ (j₁ + j₂ + p * m₃) *
              (Nat.choose (M * p - 1 + (j₁ + j₂ + p * m₃)) (j₁ + j₂ + p * m₃) : ℚ) *
              (cJ (M * p - 1) j₁ : ℚ) * (cJ (M * p - 1) j₂ : ℚ)) := by
  set N := M * p
  have hNpos : 1 ≤ N := Nat.mul_pos hMpos hp.pos
  have hN_dvd : p ^ r ∣ N := by
    have : p ^ (r - 1) * p ∣ M * p := Nat.mul_dvd_mul_right hM p
    rwa [← pow_succ, Nat.sub_add_cancel hr] at this
  have hvpN : r ≤ vp p N := vp_le_of_dvd hp (by omega) hN_dvd
  set m := if m₃ = 0 then r - 1 else min (r - 1) (vp p m₃)
  have hm_le : m ≤ r - 1 := by
    simp only [m]; split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  have hm_M : p ^ m ∣ M := dvd_trans (Nat.pow_dvd_pow p hm_le) hM
  have hm_m3 : p ^ m ∣ m₃ := by
    simp only [m]; split_ifs with h0
    · rw [h0]; exact dvd_zero _
    · exact dvd_trans (Nat.pow_dvd_pow p (min_le_right _ _)) (vp_dvd hp h0)
  have houter : PVal p (r - 1 - m) (cJ (N - 1) (p * m₃) : ℚ) := by
    by_cases hmr : m = r - 1
    · rw [hmr, Nat.sub_self]; exact PVal.int hp _
    · have hm3_ne : m₃ ≠ 0 := by intro h0; simp [m, h0] at hmr
      have hm_eq : m = vp p m₃ := by simp only [m, hm3_ne, ↓reduceIte] at hmr ⊢; exact min_eq_right (by omega)
      simp only [cJ, Int.cast_mul, Int.cast_natCast]
      have hc := (PVal.nat hp (Nat.choose (N - 1) (p * m₃))).zero_mul hp
        (PVal.of_dvd_nat hp (vp_choose_pred_add_ge p N (p * m₃) hp (Nat.mul_pos hp.pos (by omega)) (by omega)))
      refine hc.mono ?_; rw [vp_mul_p hp (by omega), ← hm_eq]; omega
  -- Reindex double sum over (j1, j2) with p !| j1, p !| j2, p | j1 + j2 as (q1, q2, s)
  have hreidx : ∀ F : ℕ → ℕ → ℚ,
      ∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j),
        ∑ j₂ ∈ ((range N).filter (fun j => ¬ p ∣ j)).filter (fun j₂ => p ∣ j₁ + j₂), F j₁ j₂ =
      ∑ q₁ ∈ range M, ∑ q₂ ∈ range M, ∑ s ∈ Ico 1 p, F (q₁ * p + s) (q₂ * p + (p - s)) := by
    intro F
    rw [sum_filter_not_dvd_range_mul M p hp]
    trans ∑ q₁ ∈ range M, ∑ s ∈ Ico 1 p, ∑ q₂ ∈ range M, F (q₁ * p + s) (q₂ * p + (p - s))
    · refine Finset.sum_congr rfl fun q₁ _ => Finset.sum_congr rfl fun s hs => ?_
      rw [mem_Ico] at hs
      rw [Finset.sum_filter, sum_filter_not_dvd_range_mul M p hp]
      refine Finset.sum_congr rfl fun q₂ _ => ?_
      have hmem : p - s ∈ Ico 1 p := by rw [mem_Ico]; omega
      rw [← Finset.add_sum_erase _ _ hmem]
      have hdiv_hit : p ∣ q₁ * p + s + (q₂ * p + (p - s)) := by
        have : q₁ * p + s + (q₂ * p + (p - s)) = (q₁ + q₂ + 1) * p := by
          zify [show s ≤ p by omega]; ring
        rw [this]; exact dvd_mul_left p _
      have hrest : ∑ s₂ ∈ (Ico 1 p).erase (p - s),
          (if p ∣ q₁ * p + s + (q₂ * p + s₂) then F (q₁ * p + s) (q₂ * p + s₂) else 0) = 0 := by
        refine Finset.sum_eq_zero fun s₂ hs₂ => ?_
        rw [mem_erase, mem_Ico] at hs₂
        have hnd : ¬ p ∣ q₁ * p + s + (q₂ * p + s₂) := by
          intro h
          have heq : q₁ * p + s + (q₂ * p + s₂) = (q₁ + q₂) * p + (s + s₂) := by ring
          rw [heq] at h
          have hs12 : p ∣ s + s₂ := (Nat.dvd_add_right (dvd_mul_left p _)).mp h
          obtain ⟨k, hk⟩ := hs12
          have hk1 : k = 1 := by
            by_contra h1; rcases (show k = 0 ∨ 2 ≤ k by omega) with rfl | h2
            · simp at hk; omega
            · nlinarith
          subst hk1; omega
        simp [hnd]
      simp [hdiv_hit, hrest]
    · refine Finset.sum_congr rfl fun q₁ _ => Finset.sum_comm
  -- Show inner sum lies in p^(2*r + m + 1) Z_(p)
  have hinner : PVal p (2 * r + m + 1)
      (∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j),
        ∑ j₂ ∈ ((range N).filter (fun j => ¬ p ∣ j)).filter (fun j₂ => p ∣ j₁ + j₂),
          (-1 : ℚ) ^ (j₁ + j₂ + p * m₃) *
            (Nat.choose (N - 1 + (j₁ + j₂ + p * m₃)) (j₁ + j₂ + p * m₃) : ℚ) *
            (cJ (N - 1) j₁ : ℚ) * (cJ (N - 1) j₂ : ℚ)) := by
    rw [hreidx]
    have hpodd : p ≠ 2 := by omega
    have hp_odd : Odd p := hp.odd_of_ne_two hpodd
    set target : ℕ → ℕ → ℕ → ℚ := fun q₁ q₂ s =>
      (-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (w2 M m₃ q₁ q₂ : ℚ) *
        (((q₁ : ℚ) * (p : ℚ) + (s : ℚ)) * (-((q₂ + 1 : ℕ) : ℚ) * (p : ℚ) + (s : ℚ)))⁻¹
    have hstep1 : PVal p (2 * r + m + 1)
        ((∑ q₁ ∈ range M, ∑ q₂ ∈ range M, ∑ s ∈ Ico 1 p,
          (-1 : ℚ) ^ (q₁ * p + s + (q₂ * p + (p - s)) + p * m₃) *
            (Nat.choose (N - 1 + (q₁ * p + s + (q₂ * p + (p - s)) + p * m₃))
              (q₁ * p + s + (q₂ * p + (p - s)) + p * m₃) : ℚ) *
            (cJ (N - 1) (q₁ * p + s) : ℚ) * (cJ (N - 1) (q₂ * p + (p - s)) : ℚ)) -
         (∑ q₁ ∈ range M, ∑ q₂ ∈ range M, ∑ s ∈ Ico 1 p, target q₁ q₂ s)) := by
      rw [← Finset.sum_sub_distrib]; refine PVal.sum hp fun q₁ hq1 => ?_
      rw [← Finset.sum_sub_distrib]; refine PVal.sum hp fun q₂ hq2 => ?_
      rw [← Finset.sum_sub_distrib]; refine PVal.sum hp fun s hs => ?_
      rw [mem_range] at hq1 hq2; rw [mem_Ico] at hs
      set t' := q₁ + q₂ + m₃ + 1
      have hidx : q₁ * p + s + (q₂ * p + (p - s)) + p * m₃ = p * t' := by
        simp only [t']; zify [show s ≤ p by omega]; ring
      rw [hidx]
      have hch_kaz : PVal p r ((Nat.choose (N - 1 + p * t') (p * t') : ℚ) - (Nat.choose (M - 1 + t') t' : ℚ)) := by
        have h := kazandzidis_pred_add p M t' hp hp5 hMpos (by omega)
        have hvpM : r - 1 ≤ vp p M := vp_le_of_dvd hp (by omega) hM
        exact h.mono (by omega)
      -- Factor cJ(N - 1, q₁*p + s) and cJ(N - 1, q₂*p + (p - s))
      have hc_fac : ∀ q < M, ∀ u : ℕ, 1 ≤ u → u < p →
          PVal p (2 * r)
            ((cJ (N - 1) (q * p + u) : ℚ) -
             (-1 : ℚ) ^ u * ((N : ℚ) / ((q * p + u : ℕ) : ℚ)) *
               (Nat.choose (M - 1) q : ℚ) * (Nat.choose (M + q) q : ℚ)) := by
        intro q hq u hu1 hup
        have hf1 := choose_pred_p_shift_general p M (q * p + u) hp hpodd (by nlinarith [hp.pos])
        have hf2 := choose_pred_add_ndiv_exact p M q u hp hMpos hu1 hup
        have hdiv : (q * p + u) / p = q := by
          rw [mul_comm q p, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hup, add_zero]
        have hmod : (q * p + u) % p = u := by
          rw [mul_comm q p, Nat.mul_add_mod, Nat.mod_eq_of_lt hup]
        rw [hdiv, hmod] at hf1
        set Pa : ℚ := ∏ i ∈ (Ico 1 (q * p + u + 1)).filter (fun i => ¬ p ∣ i), (1 - (N : ℚ) / (i : ℚ))
        set Pb : ℚ := ∏ i ∈ (Ico 1 (q * p + u)).filter (fun i => ¬ p ∣ i), (1 + (N : ℚ) / (i : ℚ))
        have hPa : PVal p r (Pa - 1) := by
          have h := PVal.prod_one_add hp (s := (Ico 1 (q * p + u + 1)).filter (fun i => ¬ p ∣ i))
            (f := fun i => -(N : ℚ) / (i : ℚ)) fun i hi =>
            (PVal.of_dvd_nat hp hN_dvd).neg.div_nat hp (Finset.mem_filter.mp hi).2
          convert h using 3 with i _; ring
        have hPb : PVal p r (Pb - 1) := PVal.prod_one_add hp fun i hi =>
          (PVal.of_dvd_nat hp hN_dvd).div_nat hp (Finset.mem_filter.mp hi).2
        have hPab : PVal p r (Pa * Pb - 1) := by
          have heq : Pa * Pb - 1 = (Pa - 1) * Pb + (Pb - 1) := by ring
          rw [heq]
          have hPb0 : PVal p 0 Pb := by
            have : Pb = (Pb - 1) + 1 := by ring
            rw [this]; exact (hPb.mono (Nat.zero_le _)).add hp (PVal.nat hp 1)
          exact (hPa.mul_zero hp hPb0).add hp hPb
        have hnd : ¬ p ∣ q * p + u := fun h => by
          have := Nat.le_of_dvd hu1 ((Nat.dvd_add_right (dvd_mul_left p q)).mp h); omega
        have hbase : PVal p r ((-1 : ℚ) ^ u * ((N : ℚ) / ((q * p + u : ℕ) : ℚ)) *
            (Nat.choose (M - 1) q : ℚ) * (Nat.choose (M + q) q : ℚ)) := by
          have h1 : PVal p r ((N : ℚ) / ((q * p + u : ℕ) : ℚ)) := (PVal.of_dvd_nat hp hN_dvd).div_nat hp hnd
          have hu0 : PVal p 0 ((-1 : ℚ) ^ u) := by simpa using (PVal.int hp (-1)).pow hp u
          exact ((hu0.zero_mul hp h1).mul_zero hp (PVal.nat hp _)).mul_zero hp (PVal.nat hp _)
        have heq_c : (cJ (N - 1) (q * p + u) : ℚ) -
            (-1 : ℚ) ^ u * ((N : ℚ) / ((q * p + u : ℕ) : ℚ)) * (Nat.choose (M - 1) q : ℚ) * (Nat.choose (M + q) q : ℚ) =
            ((-1 : ℚ) ^ u * ((N : ℚ) / ((q * p + u : ℕ) : ℚ)) * (Nat.choose (M - 1) q : ℚ) * (Nat.choose (M + q) q : ℚ)) *
            (Pa * Pb - 1) := by
          simp only [cJ, Int.cast_mul, Int.cast_natCast]
          have hf1' : (Nat.choose (N - 1) (q * p + u) : ℚ) = (-1 : ℚ) ^ u * (Nat.choose (M - 1) q : ℚ) * Pa := by
            simpa only [N, Pa, Nat.cast_mul] using hf1
          have hf2' : (Nat.choose (N - 1 + (q * p + u)) (q * p + u) : ℚ) =
              ((N : ℚ) / ((q * p + u : ℕ) : ℚ)) * (Nat.choose (M + q) q : ℚ) * Pb := by
            simpa only [N, Pb, Nat.cast_mul] using hf2
          rw [hf1', hf2']; ring
        rw [heq_c]; exact (hbase.mul hp hPab).mono (by omega)
      set C1 : ℚ := (cJ (N - 1) (q₁ * p + s) : ℚ)
      set C2 : ℚ := (cJ (N - 1) (q₂ * p + (p - s)) : ℚ)
      set L1 : ℚ := (-1 : ℚ) ^ s * ((N : ℚ) / ((q₁ * p + s : ℕ) : ℚ)) * (Nat.choose (M - 1) q₁ : ℚ) * (Nat.choose (M + q₁) q₁ : ℚ)
      set L2 : ℚ := (-1 : ℚ) ^ (p - s) * ((N : ℚ) / ((q₂ * p + (p - s) : ℕ) : ℚ)) * (Nat.choose (M - 1) q₂ : ℚ) * (Nat.choose (M + q₂) q₂ : ℚ)
      have hC1L1 := hc_fac q₁ hq1 s hs.1 hs.2
      have hC2L2 := hc_fac q₂ hq2 (p - s) (by omega) (by omega)
      have hC1_r : PVal p r C1 := by
        simp only [C1, cJ, Int.cast_mul, Int.cast_natCast]
        have hnd : ¬ p ∣ q₁ * p + s := fun h => by have := Nat.le_of_dvd hs.1 ((Nat.dvd_add_right (dvd_mul_left p q₁)).mp h); omega
        have hvp0 : vp p (q₁ * p + s) = 0 := by by_contra h0; exact hnd (dvd_trans (dvd_pow_self p h0) (vp_dvd hp (by omega)))
        have hd := vp_choose_pred_add_ge p N (q₁ * p + s) hp (by omega) (by omega)
        rw [hvp0, Nat.sub_zero] at hd
        exact ((PVal.nat hp _).zero_mul hp (PVal.of_dvd_nat hp hd)).mono (by omega)
      have hL2_r : PVal p r L2 := by
        have hnd : ¬ p ∣ q₂ * p + (p - s) := fun h => by
          have := Nat.le_of_dvd (by omega : 1 ≤ p - s) ((Nat.dvd_add_right (dvd_mul_left p q₂)).mp h); omega
        have h1 : PVal p r ((N : ℚ) / ((q₂ * p + (p - s) : ℕ) : ℚ)) := (PVal.of_dvd_nat hp hN_dvd).div_nat hp hnd
        have hu0 : PVal p 0 ((-1 : ℚ) ^ (p - s)) := by simpa using (PVal.int hp (-1)).pow hp (p - s)
        exact ((hu0.zero_mul hp h1).mul_zero hp (PVal.nat hp _)).mul_zero hp (PVal.nat hp _)
      have hL1_r : PVal p r L1 := by
        have hnd : ¬ p ∣ q₁ * p + s := fun h => by
          have := Nat.le_of_dvd hs.1 ((Nat.dvd_add_right (dvd_mul_left p q₁)).mp h); omega
        have h1 : PVal p r ((N : ℚ) / ((q₁ * p + s : ℕ) : ℚ)) := (PVal.of_dvd_nat hp hN_dvd).div_nat hp hnd
        have hu0 : PVal p 0 ((-1 : ℚ) ^ s) := by simpa using (PVal.int hp (-1)).pow hp s
        exact ((hu0.zero_mul hp h1).mul_zero hp (PVal.nat hp _)).mul_zero hp (PVal.nat hp _)
      -- Check (-1)^(p*t') * C(M-1+t', t') * L1 * L2 = target q₁ q₂ s!
      have ht_match : (-1 : ℚ) ^ (p * t') * (Nat.choose (M - 1 + t') t' : ℚ) * L1 * L2 = target q₁ q₂ s := by
        have hs1 : (-1 : ℚ) ^ (p * t') = (-1 : ℚ) ^ (m₃ + 1) * (-1 : ℚ) ^ (q₁ + q₂) := by
          rw [pow_mul, hp_odd.neg_one_pow, show t' = (m₃ + 1) + (q₁ + q₂) by simp only [t']; omega, pow_add]
        have hs2 : (-1 : ℚ) ^ s * (-1 : ℚ) ^ (p - s) = -1 := by
          rw [← pow_add, Nat.add_sub_of_le (by omega : s ≤ p), hp_odd.neg_one_pow]
        have hd2 : ((q₂ * p + (p - s) : ℕ) : ℚ) = -(-((q₂ + 1 : ℕ) : ℚ) * (p : ℚ) + (s : ℚ)) := by
          rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : s ≤ p)]; push_cast; ring
        simp only [target, w2, L1, L2, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]
        rw [hs1, div_eq_mul_inv, div_eq_mul_inv, hd2, inv_neg]
        have hd_mul : ((q₁ * p + s : ℕ) : ℚ)⁻¹ * (-((q₂ + 1 : ℕ) : ℚ) * (p : ℚ) + (s : ℚ))⁻¹ =
            (((q₁ : ℚ) * (p : ℚ) + (s : ℚ)) * (-((q₂ + 1 : ℕ) : ℚ) * (p : ℚ) + (s : ℚ)))⁻¹ := by
          rw [← mul_inv]; push_cast; rfl
        calc (-1 : ℚ) ^ (m₃ + 1) * (-1 : ℚ) ^ (q₁ + q₂) * (Nat.choose (M - 1 + t') t' : ℚ) *
              ((-1 : ℚ) ^ s * ((N : ℚ) * ((q₁ * p + s : ℕ) : ℚ)⁻¹) * (Nat.choose (M - 1) q₁ : ℚ) * (Nat.choose (M + q₁) q₁ : ℚ)) *
              ((-1 : ℚ) ^ (p - s) * ((N : ℚ) * -(-((q₂ + 1 : ℕ) : ℚ) * (p : ℚ) + (s : ℚ))⁻¹) * (Nat.choose (M - 1) q₂ : ℚ) * (Nat.choose (M + q₂) q₂ : ℚ))
            = -((-1 : ℚ) ^ s * (-1 : ℚ) ^ (p - s)) *
              ((-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 *
                ((-1 : ℚ) ^ (q₁ + q₂) * (Nat.choose (M - 1 + t') t' : ℚ) *
                  (Nat.choose (M - 1) q₁ : ℚ) * (Nat.choose (M + q₁) q₁ : ℚ) *
                  (Nat.choose (M - 1) q₂ : ℚ) * (Nat.choose (M + q₂) q₂ : ℚ)) *
                (((q₁ * p + s : ℕ) : ℚ)⁻¹ * (-((q₂ + 1 : ℕ) : ℚ) * (p : ℚ) + (s : ℚ))⁻¹)) := by ring
          _ = _ := by rw [hs2, hd_mul]; simp only [t']; ring
      rw [← ht_match]
      set X1 : ℚ := (Nat.choose (N - 1 + p * t') (p * t') : ℚ)
      set X2 : ℚ := (Nat.choose (M - 1 + t') t' : ℚ)
      have hsplit : (-1 : ℚ) ^ (p * t') * X1 * C1 * C2 - (-1 : ℚ) ^ (p * t') * X2 * L1 * L2 =
          (-1 : ℚ) ^ (p * t') *
            (X1 * (C1 * (C2 - L2) + (C1 - L1) * L2) + (X1 - X2) * (L1 * L2)) := by ring
      rw [hsplit]
      have hsign0 : PVal p 0 ((-1 : ℚ) ^ (p * t')) := by simpa using (PVal.int hp (-1)).pow hp (p * t')
      have hterm1 : PVal p (3 * r) (X1 * (C1 * (C2 - L2) + (C1 - L1) * L2)) :=
        (PVal.nat hp _).zero_mul hp (((hC1_r.mul hp hC2L2).mono (by omega)).add hp ((hC1L1.mul hp hL2_r).mono (by omega)))
      have hterm2 : PVal p (3 * r) ((X1 - X2) * (L1 * L2)) :=
        (hch_kaz.mul hp (hL1_r.mul hp hL2_r)).mono (by omega)
      exact (hsign0.zero_mul hp (hterm1.add hp hterm2)).mono (by omega)
    -- Step 2: Expand bivariate geometric series up to m+1 terms and apply part2_b2_moment_dvd
    have hstep2 : PVal p (2 * r + m + 1) (∑ q₁ ∈ range M, ∑ q₂ ∈ range M, ∑ s ∈ Ico 1 p, target q₁ q₂ s) := by
      set ser : ℕ → ℕ → ℕ → ℚ := fun q₁ q₂ s =>
        ∑ d ∈ range (m + 1), (-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
          ∑ a ∈ range (d + 1), (q₁ : ℚ) ^ a * (-((q₂ + 1 : ℕ) : ℚ)) ^ (d - a)
      have happrox : PVal p (2 * r + m + 1)
          ((∑ q₁ ∈ range M, ∑ q₂ ∈ range M, ∑ s ∈ Ico 1 p, target q₁ q₂ s) -
           (∑ q₁ ∈ range M, ∑ q₂ ∈ range M, ∑ s ∈ Ico 1 p,
             (-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (w2 M m₃ q₁ q₂ : ℚ) * ser q₁ q₂ s)) := by
        rw [← Finset.sum_sub_distrib]; refine PVal.sum hp fun q₁ _ => ?_
        rw [← Finset.sum_sub_distrib]; refine PVal.sum hp fun q₂ _ => ?_
        rw [← Finset.sum_sub_distrib]; refine PVal.sum hp fun s hs => ?_
        rw [mem_Ico] at hs
        have hgeom := inv_bivar_geom_series p (m + 1) s (q₁ : ℤ) (-((q₂ + 1 : ℕ) : ℤ)) hp hs.1 hs.2
        have hgeom' : PVal p (m + 1)
            ((((q₁ : ℚ) * (p : ℚ) + (s : ℚ)) * (-((q₂ + 1 : ℕ) : ℚ) * (p : ℚ) + (s : ℚ)))⁻¹ - ser q₁ q₂ s) := by
          simpa only [ser, Int.cast_neg, Int.cast_natCast] using hgeom
        have hbase : PVal p (2 * r) ((-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (w2 M m₃ q₁ q₂ : ℚ)) := by
          have hN2 : PVal p (2 * r) ((N : ℚ) ^ 2) := by simpa [mul_comm] using (PVal.of_dvd_nat hp hN_dvd).pow hp 2
          have hs0 : PVal p 0 ((-1 : ℚ) ^ (m₃ + 1)) := by simpa using (PVal.int hp (-1)).pow hp (m₃ + 1)
          exact (hs0.zero_mul hp hN2).mul_zero hp (PVal.int hp _)
        have hsub : target q₁ q₂ s - (-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (w2 M m₃ q₁ q₂ : ℚ) * ser q₁ q₂ s =
            ((-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (w2 M m₃ q₁ q₂ : ℚ)) *
            ((((q₁ : ℚ) * (p : ℚ) + (s : ℚ)) * (-((q₂ + 1 : ℕ) : ℚ) * (p : ℚ) + (s : ℚ)))⁻¹ - ser q₁ q₂ s) := by
          simp only [target]; ring
        rw [hsub]; exact (hbase.mul hp hgeom').mono (by omega)
      have hser_zero : PVal p (2 * r + m + 1)
          (∑ q₁ ∈ range M, ∑ q₂ ∈ range M, ∑ s ∈ Ico 1 p,
            (-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (w2 M m₃ q₁ q₂ : ℚ) * ser q₁ q₂ s) := by
        have hswap : ∑ q₁ ∈ range M, ∑ q₂ ∈ range M, ∑ s ∈ Ico 1 p,
              (-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (w2 M m₃ q₁ q₂ : ℚ) * ser q₁ q₂ s =
            ∑ d ∈ range (m + 1), (-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (-1 : ℚ) ^ d *
              (∑ s ∈ Ico 1 p, ((s : ℚ) ^ (d + 2))⁻¹) *
              ∑ a ∈ range (d + 1), (-1 : ℚ) ^ (d - a) * (W2 p M m₃ a (d - a) : ℚ) := by
          -- Move outer d and s out cleanly
          calc ∑ q₁ ∈ range M, ∑ q₂ ∈ range M, ∑ s ∈ Ico 1 p,
                (-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (w2 M m₃ q₁ q₂ : ℚ) * ser q₁ q₂ s
              = ∑ q₁ ∈ range M, ∑ q₂ ∈ range M, ∑ d ∈ range (m + 1), ∑ s ∈ Ico 1 p,
                (-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (w2 M m₃ q₁ q₂ : ℚ) *
                ((-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
                  ∑ a ∈ range (d + 1), (q₁ : ℚ) ^ a * (-((q₂ + 1 : ℕ) : ℚ)) ^ (d - a)) := by
                refine Finset.sum_congr rfl fun q₁ _ => Finset.sum_congr rfl fun q₂ _ => ?_
                symm; rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun s _ => ?_
                simp only [ser, Finset.mul_sum]
            _ = ∑ d ∈ range (m + 1), ∑ q₁ ∈ range M, ∑ q₂ ∈ range M, ∑ s ∈ Ico 1 p,
                (-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (w2 M m₃ q₁ q₂ : ℚ) *
                ((-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
                  ∑ a ∈ range (d + 1), (q₁ : ℚ) ^ a * (-((q₂ + 1 : ℕ) : ℚ)) ^ (d - a)) := by
                trans ∑ q₁ ∈ range M, ∑ d ∈ range (m + 1), ∑ q₂ ∈ range M, ∑ s ∈ Ico 1 p,
                  (-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (w2 M m₃ q₁ q₂ : ℚ) *
                  ((-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
                    ∑ a ∈ range (d + 1), (q₁ : ℚ) ^ a * (-((q₂ + 1 : ℕ) : ℚ)) ^ (d - a))
                · exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
                · exact Finset.sum_comm
            _ = _ := by
                refine Finset.sum_congr rfl fun d _ => ?_
                -- Pull s out of q₁, q₂
                have hs_out : ∑ q₁ ∈ range M, ∑ q₂ ∈ range M, ∑ s ∈ Ico 1 p,
                    (-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (w2 M m₃ q₁ q₂ : ℚ) *
                    ((-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
                      ∑ a ∈ range (d + 1), (q₁ : ℚ) ^ a * (-((q₂ + 1 : ℕ) : ℚ)) ^ (d - a)) =
                    ∑ s ∈ Ico 1 p, ∑ q₁ ∈ range M, ∑ q₂ ∈ range M,
                    (-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (w2 M m₃ q₁ q₂ : ℚ) *
                    ((-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
                      ∑ a ∈ range (d + 1), (q₁ : ℚ) ^ a * (-((q₂ + 1 : ℕ) : ℚ)) ^ (d - a)) := by
                  rw [Finset.sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm]
                rw [hs_out]; symm
                rw [Finset.mul_sum (s := Ico 1 p), Finset.sum_mul]
                refine Finset.sum_congr rfl fun s _ => ?_
                -- Pull a inside q₁, q₂
                have ha_in : (-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (-1 : ℚ) ^ d * ((s : ℚ) ^ (d + 2))⁻¹ *
                    ∑ a ∈ range (d + 1), (-1 : ℚ) ^ (d - a) * (W2 p M m₃ a (d - a) : ℚ) =
                    ∑ a ∈ range (d + 1), ∑ q₁ ∈ range M, ∑ q₂ ∈ range M,
                    (-1 : ℚ) ^ (m₃ + 1) * (N : ℚ) ^ 2 * (w2 M m₃ q₁ q₂ : ℚ) *
                    ((-1 : ℚ) ^ d * (p : ℚ) ^ d / (s : ℚ) ^ (d + 2) *
                      ((q₁ : ℚ) ^ a * (-((q₂ + 1 : ℕ) : ℚ)) ^ (d - a))) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun a ha => ?_
                  rw [mem_range] at ha
                  simp only [W2, show a + (d - a) = d by omega, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_sum]
                  simp_rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun q₁ _ => Finset.sum_congr rfl fun q₂ _ => ?_
                  rw [neg_pow (((q₂ + 1 : ℕ) : ℚ)) (d - a), div_eq_mul_inv]; ring
                rw [ha_in]
                rw [Finset.sum_comm (s := range (d + 1)) (t := range M)]
                refine Finset.sum_congr rfl fun q₁ _ => ?_
                rw [Finset.sum_comm (s := range (d + 1)) (t := range M)]
                refine Finset.sum_congr rfl fun q₂ _ => ?_
                simp_rw [← Finset.mul_sum]
        rw [hswap]
        have ⟨hm0, hmd⟩ := part2_b2_moment_dvd p m hp hp5 M m₃ hMpos hm_M hm_m3
        refine PVal.sum hp fun d _ => ?_
        have hN2 : PVal p (2 * r) ((N : ℚ) ^ 2) := by simpa [mul_comm] using (PVal.of_dvd_nat hp hN_dvd).pow hp 2
        have hc0 : PVal p 0 ((-1 : ℚ) ^ (m₃ + 1)) := by simpa using (PVal.int hp (-1)).pow hp (m₃ + 1)
        have hd0_s : PVal p 0 ((-1 : ℚ) ^ d) := by simpa using (PVal.int hp (-1)).pow hp d
        by_cases hd0 : d = 0
        · subst hd0
          have hs2 := sum_inv_sq_mod_p p hp hp5
          have hW0 : PVal p m (∑ a ∈ range 1, (-1 : ℚ) ^ (0 - a) * (W2 p M m₃ a (0 - a) : ℚ)) := by
            simpa using PVal.of_dvd_int hp hm0
          exact ((((hc0.zero_mul hp hN2).mul_zero hp hd0_s).mul hp hs2).mul hp hW0).mono (by omega)
        · have hs_pv : PVal p 0 (∑ s ∈ Ico 1 p, ((s : ℚ) ^ (d + 2))⁻¹) := by
            refine PVal.sum hp fun s hs => ?_
            rw [mem_Ico] at hs
            have hnds : ¬ p ∣ s ^ (d + 2) := fun h => by
              have := Nat.le_of_dvd hs.1 (hp.dvd_of_dvd_pow h); omega
            simpa [Nat.cast_pow] using PVal.inv_nat hnds
          have hWd : PVal p (m + 1) (∑ a ∈ range (d + 1), (-1 : ℚ) ^ (d - a) * (W2 p M m₃ a (d - a) : ℚ)) := by
            refine PVal.sum hp fun a ha => ?_
            rw [mem_range] at ha
            have hsa : PVal p 0 ((-1 : ℚ) ^ (d - a)) := by simpa using (PVal.int hp (-1)).pow hp (d - a)
            exact hsa.zero_mul hp (PVal.of_dvd_int hp (hmd a (d - a) (by omega)))
          exact ((((hc0.zero_mul hp hN2).mul_zero hp hd0_s).mul_zero hp hs_pv).mul hp hWd).mono (by omega)
      have hfin := happrox.add hp hser_zero
      simpa using hfin
    have hfin := hstep1.add hp hstep2
    simpa using hfin
  exact (houter.mul hp hinner).mono (by omega)

/-- D6 (Theorem P2): a(n * p^r - 1) == a(n * p^(r - 1) - 1) [MOD p^(3*r)] for prime p >= 5, n > 0, r > 0. -/
private lemma part2_main (p n r : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hr : 0 < r) :
    Nat.ModEq (p ^ (3 * r)) (OMA.S_oeis_a364114.a (n * p ^ r - 1)) (OMA.S_oeis_a364114.a (n * p ^ (r - 1) - 1)) := by
  set M := n * p ^ (r - 1)
  have hMpos : 1 ≤ M := Nat.mul_pos hn (Nat.pow_pos hp.pos)
  have hM_dvd : p ^ (r - 1) ∣ M := ⟨n, by simp [M, mul_comm]⟩
  have hN_eq : n * p ^ r = M * p := by
    simp only [M, mul_assoc, ← pow_succ]; rw [Nat.sub_add_cancel hr]
  rw [hN_eq]
  set N := M * p
  have hNpos : 1 ≤ N := Nat.mul_pos hMpos hp.pos
  have hN_dvd : p ^ r ∣ N := by
    have : p ^ (r - 1) * p ∣ M * p := Nat.mul_dvd_mul_right hM_dvd p
    rwa [← pow_succ, Nat.sub_add_cancel hr] at this
  have hvpN : r ≤ vp p N := vp_le_of_dvd hp (by omega) hN_dvd
  have hsign_eq : (-1 : ℤ) ^ (3 * (N - 1)) = (-1 : ℤ) ^ (3 * (M - 1)) := by
    have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
    obtain ⟨t, ht⟩ := hp_odd
    have hpar : Even (3 * (N - 1) - 3 * (M - 1)) := by
      have hNM : M ≤ N := Nat.le_mul_of_pos_right M hp.pos
      have hdiff : 3 * (N - 1) - 3 * (M - 1) = 3 * (2 * t * M) := by
        have : N - M = 2 * t * M := by simp only [N, ht]; ring_nf; omega
        omega
      rw [hdiff]; exact ⟨3 * t * M, by ring⟩
    have hle : 3 * (M - 1) ≤ 3 * (N - 1) := by have := Nat.le_mul_of_pos_right M hp.pos; omega
    rw [← Nat.add_sub_of_le hle, pow_add, hpar.neg_one_pow, mul_one]
  -- Cast dual rep to Q
  set gN : ℕ → ℕ → ℕ → ℚ := fun j₁ j₂ j₃ =>
    (-1 : ℚ) ^ (j₁ + j₂ + j₃) * (Nat.choose (N - 1 + (j₁ + j₂ + j₃)) (j₁ + j₂ + j₃) : ℚ) *
      (cJ (N - 1) j₁ : ℚ) * (cJ (N - 1) j₂ : ℚ) * (cJ (N - 1) j₃ : ℚ)
  set gM : ℕ → ℕ → ℕ → ℚ := fun m₁ m₂ m₃ =>
    (-1 : ℚ) ^ (m₁ + m₂ + m₃) * (Nat.choose (M - 1 + (m₁ + m₂ + m₃)) (m₁ + m₂ + m₃) : ℚ) *
      (cJ (M - 1) m₁ : ℚ) * (cJ (M - 1) m₂ : ℚ) * (cJ (M - 1) m₃ : ℚ)
  have hDN : (-1 : ℚ) ^ (3 * (N - 1)) * (OMA.S_oeis_a364114.a (N - 1) : ℚ) =
      ∑ j₁ ∈ range N, ∑ j₂ ∈ range N, ∑ j₃ ∈ range N, gN j₁ j₂ j₃ := by
    have h := congrArg (Int.cast : ℤ → ℚ) (a_eq_dual_rep (N - 1))
    rw [Nat.sub_add_cancel hNpos] at h
    simpa only [gN, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, Int.cast_sum] using h
  have hDM : (-1 : ℚ) ^ (3 * (M - 1)) * (OMA.S_oeis_a364114.a (M - 1) : ℚ) =
      ∑ m₁ ∈ range M, ∑ m₂ ∈ range M, ∑ m₃ ∈ range M, gM m₁ m₂ m₃ := by
    have h := congrArg (Int.cast : ℤ → ℚ) (a_eq_dual_rep (M - 1))
    rw [Nat.sub_add_cancel hMpos] at h
    simpa only [gM, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast, Int.cast_sum] using h
  have hsplit_range : ∀ f : ℕ → ℚ,
      ∑ j ∈ range N, f j = (∑ m ∈ range M, f (p * m)) + ∑ j ∈ (range N).filter (fun j => ¬ p ∣ j), f j := by
    intro f
    rw [← Finset.sum_filter_add_sum_filter_not (range N) (fun j => p ∣ j), sum_filter_dvd_range_mul M p hp]
  have hsym12 : ∀ a b c, gN a b c = gN b a c := fun a b c => by
    simp only [gN, show a + b + c = b + a + c by omega]; ring
  have hsym13 : ∀ a b c, gN a b c = gN c b a := fun a b c => by
    simp only [gN, show a + b + c = c + b + a by omega]; ring
  -- Helper: non-divisible cJ(N - 1, j) has PVal p r
  have hcJ_ndiv : ∀ j, ¬ p ∣ j → PVal p r (cJ (N - 1) j : ℚ) := by
    intro j hnd
    have hj1 : 1 ≤ j := Nat.pos_of_ne_zero fun h0 => hnd (h0 ▸ dvd_zero p)
    have hvp0 : vp p j = 0 := by by_contra h0; exact hnd (dvd_trans (dvd_pow_self p h0) (vp_dvd hp (by omega)))
    have hd := vp_choose_pred_add_ge p N j hp hj1 (by omega)
    rw [hvp0, Nat.sub_zero] at hd
    simp only [cJ, Int.cast_mul, Int.cast_natCast]
    exact ((PVal.nat hp _).zero_mul hp (PVal.of_dvd_nat hp hd)).mono hvpN
  -- Bucket b0 matches gM term-by-term
  have hb0 : PVal p (3 * r)
      ((∑ m₁ ∈ range M, ∑ m₂ ∈ range M, ∑ m₃ ∈ range M, gN (p * m₁) (p * m₂) (p * m₃)) -
       (∑ m₁ ∈ range M, ∑ m₂ ∈ range M, ∑ m₃ ∈ range M, gM m₁ m₂ m₃)) := by
    rw [← Finset.sum_sub_distrib]; refine PVal.sum hp fun m₁ hm1 => ?_
    rw [← Finset.sum_sub_distrib]; refine PVal.sum hp fun m₂ hm2 => ?_
    rw [← Finset.sum_sub_distrib]; refine PVal.sum hp fun m₃ hm3 => ?_
    rw [mem_range] at hm1 hm2 hm3
    exact part2_b0_term p M r m₁ m₂ m₃ hp hp5 hr hM_dvd hMpos hm1 hm2 hm3
  -- Bucket b1 (slot 1 non-divisible)
  have hb1_slot1 : PVal p (3 * r)
      (∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j),
        ∑ m₂ ∈ range M, ∑ m₃ ∈ range M, gN j₁ (p * m₂) (p * m₃)) := by
    rw [Finset.sum_comm]; refine PVal.sum hp fun m₂ hm2 => ?_
    rw [Finset.sum_comm]; refine PVal.sum hp fun m₃ hm3 => ?_
    rw [mem_range] at hm2 hm3
    have hpair := part2_b1_pair p M r m₂ m₃ hp hp5 hr hM_dvd hMpos hm2 hm3
    have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
    have heq : ∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j), gN j₁ (p * m₂) (p * m₃) =
        (-1 : ℚ) ^ (m₂ + m₃) * ((cJ (N - 1) (p * m₂) : ℚ) * (cJ (N - 1) (p * m₃) : ℚ) *
          ∑ j ∈ (range N).filter (fun j => ¬ p ∣ j),
            (-1 : ℚ) ^ j * (Nat.choose (N - 1 + (j + p * m₂ + p * m₃)) (j + p * m₂ + p * m₃) : ℚ) *
              (cJ (N - 1) j : ℚ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j₁ _ => ?_
      simp only [gN]
      have hs : (-1 : ℚ) ^ (j₁ + p * m₂ + p * m₃) = (-1 : ℚ) ^ (m₂ + m₃) * (-1 : ℚ) ^ j₁ := by
        rw [show j₁ + p * m₂ + p * m₃ = p * (m₂ + m₃) + j₁ by ring, pow_add, pow_mul, hp_odd.neg_one_pow]
      rw [hs]; ring
    rw [heq]
    have hs0 : PVal p 0 ((-1 : ℚ) ^ (m₂ + m₃)) := by simpa using (PVal.int hp (-1)).pow hp (m₂ + m₃)
    exact hs0.zero_mul hp hpair
  -- Bucket b2 (slots 1, 2 non-divisible)
  have hb2_12 : PVal p (3 * r)
      (∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j),
        ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j),
          ∑ m₃ ∈ range M, gN j₁ j₂ (p * m₃)) := by
    have hsw : ∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j),
          ∑ m₃ ∈ range M, gN j₁ j₂ (p * m₃) =
        ∑ m₃ ∈ range M, ∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j),
          ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j), gN j₁ j₂ (p * m₃) := by
      trans ∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ m₃ ∈ range M,
        ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j), gN j₁ j₂ (p * m₃)
      · exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      · exact Finset.sum_comm
    rw [hsw]
    refine PVal.sum hp fun m₃ hm3 => ?_
    rw [mem_range] at hm3
    -- Split j2 into p | (j1 + j2) and ¬ p | (j1 + j2)
    have hsplit2 : ∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j),
          gN j₁ j₂ (p * m₃) =
        (∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j),
          ∑ j₂ ∈ ((range N).filter (fun j => ¬ p ∣ j)).filter (fun j₂ => p ∣ j₁ + j₂), gN j₁ j₂ (p * m₃)) +
        (∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j),
          ∑ j₂ ∈ ((range N).filter (fun j => ¬ p ∣ j)).filter (fun j₂ => ¬ p ∣ j₁ + j₂), gN j₁ j₂ (p * m₃)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j₁ _ => (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    rw [hsplit2]
    have hdiv_part : PVal p (3 * r)
        (∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j),
          ∑ j₂ ∈ ((range N).filter (fun j => ¬ p ∣ j)).filter (fun j₂ => p ∣ j₁ + j₂), gN j₁ j₂ (p * m₃)) := by
      have h := part2_b2_m3 p M r m₃ hp hp5 hr hM_dvd hMpos hm3
      convert h using 1
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j₁ _ => ?_
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j₂ _ => ?_
      simp only [gN]; ring
    have hndiv_part : PVal p (3 * r)
        (∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j),
          ∑ j₂ ∈ ((range N).filter (fun j => ¬ p ∣ j)).filter (fun j₂ => ¬ p ∣ j₁ + j₂), gN j₁ j₂ (p * m₃)) := by
      refine PVal.sum hp fun j₁ hj1 => PVal.sum hp fun j₂ hj2 => ?_
      have hnd1 : ¬ p ∣ j₁ := (Finset.mem_filter.mp hj1).2
      have hnd2 : ¬ p ∣ j₂ := (Finset.mem_filter.mp (Finset.mem_filter.mp hj2).1).2
      have hnd12 : ¬ p ∣ j₁ + j₂ := (Finset.mem_filter.mp hj2).2
      have hnds : ¬ p ∣ j₁ + j₂ + p * m₃ := fun h => hnd12 ((Nat.dvd_add_left (dvd_mul_right p m₃)).mp h)
      have hs1 : 1 ≤ j₁ + j₂ + p * m₃ := Nat.pos_of_ne_zero fun h0 => hnds (h0 ▸ dvd_zero p)
      have hvps : vp p (j₁ + j₂ + p * m₃) = 0 := by
        by_contra h0; exact hnds (dvd_trans (dvd_pow_self p h0) (vp_dvd hp (by omega)))
      have hch : PVal p r (Nat.choose (N - 1 + (j₁ + j₂ + p * m₃)) (j₁ + j₂ + p * m₃) : ℚ) := by
        have hd := vp_choose_pred_add_ge p N (j₁ + j₂ + p * m₃) hp hs1 (by omega)
        rw [hvps, Nat.sub_zero] at hd
        exact (PVal.of_dvd_nat hp hd).mono hvpN
      have hc1 := hcJ_ndiv j₁ hnd1
      have hc2 := hcJ_ndiv j₂ hnd2
      have hsign0 : PVal p 0 ((-1 : ℚ) ^ (j₁ + j₂ + p * m₃)) := by simpa using (PVal.int hp (-1)).pow hp _
      simp only [gN]
      exact ((((hsign0.zero_mul hp hch).mul hp hc1).mul hp hc2).mul_zero hp (PVal.int hp _)).mono (by omega)
    exact hdiv_part.add hp hndiv_part
  -- Bucket b3 (all 3 non-divisible)
  have hb3 : PVal p (3 * r)
      (∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j),
        ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j),
          ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j), gN j₁ j₂ j₃) := by
    refine PVal.sum hp fun j₁ hj1 => PVal.sum hp fun j₂ hj2 => PVal.sum hp fun j₃ hj3 => ?_
    have hc1 := hcJ_ndiv j₁ (Finset.mem_filter.mp hj1).2
    have hc2 := hcJ_ndiv j₂ (Finset.mem_filter.mp hj2).2
    have hc3 := hcJ_ndiv j₃ (Finset.mem_filter.mp hj3).2
    have hsign0 : PVal p 0 ((-1 : ℚ) ^ (j₁ + j₂ + j₃)) := by simpa using (PVal.int hp (-1)).pow hp _
    simp only [gN]
    exact ((((hsign0.zero_mul hp (PVal.nat hp _)).zero_mul hp hc1).mul hp hc2).mul hp hc3).mono (by omega)
  -- Combine all 8 octants
  have hdecomp : (-1 : ℚ) ^ (3 * (N - 1)) * ((OMA.S_oeis_a364114.a (N - 1) : ℚ) - (OMA.S_oeis_a364114.a (M - 1) : ℚ)) =
      ((∑ m₁ ∈ range M, ∑ m₂ ∈ range M, ∑ m₃ ∈ range M, gN (p * m₁) (p * m₂) (p * m₃)) -
       (∑ m₁ ∈ range M, ∑ m₂ ∈ range M, ∑ m₃ ∈ range M, gM m₁ m₂ m₃)) +
      (∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ m₂ ∈ range M, ∑ m₃ ∈ range M, gN j₁ (p * m₂) (p * m₃)) +
      (∑ m₁ ∈ range M, ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ m₃ ∈ range M, gN (p * m₁) j₂ (p * m₃)) +
      (∑ m₁ ∈ range M, ∑ m₂ ∈ range M, ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j), gN (p * m₁) (p * m₂) j₃) +
      (∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ m₃ ∈ range M, gN j₁ j₂ (p * m₃)) +
      (∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ m₂ ∈ range M, ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j), gN j₁ (p * m₂) j₃) +
      (∑ m₁ ∈ range M, ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j), gN (p * m₁) j₂ j₃) +
      (∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j), gN j₁ j₂ j₃) := by
    have hs_q : (-1 : ℚ) ^ (3 * (N - 1)) = (-1 : ℚ) ^ (3 * (M - 1)) := by exact_mod_cast hsign_eq
    have hLHS : (-1 : ℚ) ^ (3 * (N - 1)) * ((OMA.S_oeis_a364114.a (N - 1) : ℚ) - (OMA.S_oeis_a364114.a (M - 1) : ℚ)) =
        (∑ j₁ ∈ range N, ∑ j₂ ∈ range N, ∑ j₃ ∈ range N, gN j₁ j₂ j₃) -
        (∑ m₁ ∈ range M, ∑ m₂ ∈ range M, ∑ m₃ ∈ range M, gM m₁ m₂ m₃) := by
      rw [mul_sub, hDN, hs_q, hDM]
    rw [hLHS, hsplit_range]
    simp_rw [hsplit_range, Finset.sum_add_distrib]
    ring
  have hpv_signed : PVal p (3 * r)
      ((-1 : ℚ) ^ (3 * (N - 1)) * ((OMA.S_oeis_a364114.a (N - 1) : ℚ) - (OMA.S_oeis_a364114.a (M - 1) : ℚ))) := by
    rw [hdecomp]
    have hb1_slot2 : PVal p (3 * r)
        (∑ m₁ ∈ range M, ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ m₃ ∈ range M, gN (p * m₁) j₂ (p * m₃)) := by
      rw [Finset.sum_comm]
      convert hb1_slot1 using 2 with j₂ _
      exact Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₃ _ => hsym12 (p * m₁) j₂ (p * m₃)
    have hb1_slot3 : PVal p (3 * r)
        (∑ m₁ ∈ range M, ∑ m₂ ∈ range M, ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j), gN (p * m₁) (p * m₂) j₃) := by
      have hsw : ∑ m₁ ∈ range M, ∑ m₂ ∈ range M, ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j), gN (p * m₁) (p * m₂) j₃ =
          ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ m₂ ∈ range M, ∑ m₁ ∈ range M, gN j₃ (p * m₂) (p * m₁) := by
        trans ∑ m₁ ∈ range M, ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ m₂ ∈ range M, gN (p * m₁) (p * m₂) j₃
        · exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j₃ _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m₂ _ => Finset.sum_congr rfl fun m₁ _ => hsym13 (p * m₁) (p * m₂) j₃
      rw [hsw]; exact hb1_slot1
    have hb2_13 : PVal p (3 * r)
        (∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ m₂ ∈ range M,
          ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j), gN j₁ (p * m₂) j₃) := by
      have hsw : ∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ m₂ ∈ range M,
            ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j), gN j₁ (p * m₂) j₃ =
          ∑ j₁ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j),
            ∑ m₂ ∈ range M, gN j₁ j₃ (p * m₂) := by
        refine Finset.sum_congr rfl fun j₁ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j₃ _ => Finset.sum_congr rfl fun m₂ _ => ?_
        rw [hsym12, hsym13, hsym12]
      rw [hsw]; exact hb2_12
    have hb2_23 : PVal p (3 * r)
        (∑ m₁ ∈ range M, ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j),
          ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j), gN (p * m₁) j₂ j₃) := by
      have hsw : ∑ m₁ ∈ range M, ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j),
            ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j), gN (p * m₁) j₂ j₃ =
          ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j),
            ∑ m₁ ∈ range M, gN j₃ j₂ (p * m₁) := by
        trans ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ m₁ ∈ range M,
          ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j), gN (p * m₁) j₂ j₃
        · exact Finset.sum_comm
        trans ∑ j₂ ∈ (range N).filter (fun j => ¬ p ∣ j), ∑ j₃ ∈ (range N).filter (fun j => ¬ p ∣ j),
          ∑ m₁ ∈ range M, gN (p * m₁) j₂ j₃
        · exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j₃ _ => Finset.sum_congr rfl fun j₂ _ =>
          Finset.sum_congr rfl fun m₁ _ => hsym13 (p * m₁) j₂ j₃
      rw [hsw]; exact hb2_12
    exact ((((((hb0.add hp hb1_slot1).add hp hb1_slot2).add hp hb1_slot3).add hp hb2_12).add hp hb2_13).add hp hb2_23).add hp hb3
  -- Strip sign (-1)^(3*(N - 1))
  have hpv_total : PVal p (3 * r) ((OMA.S_oeis_a364114.a (N - 1) : ℚ) - (OMA.S_oeis_a364114.a (M - 1) : ℚ)) := by
    have hsign_sq : (-1 : ℚ) ^ (3 * (N - 1)) * ((-1 : ℚ) ^ (3 * (N - 1)) *
        ((OMA.S_oeis_a364114.a (N - 1) : ℚ) - (OMA.S_oeis_a364114.a (M - 1) : ℚ))) =
        (OMA.S_oeis_a364114.a (N - 1) : ℚ) - (OMA.S_oeis_a364114.a (M - 1) : ℚ) := by
      rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num
    rw [← hsign_sq]
    exact (by simpa using (PVal.int hp (-1)).pow hp (3 * (N - 1)) : PVal p 0 _).zero_mul hp hpv_signed
  have hz : (OMA.S_oeis_a364114.a (N - 1) : ℤ) ≡ (OMA.S_oeis_a364114.a (M - 1) : ℤ) [ZMOD (p : ℤ) ^ (3 * r)] :=
    PVal.modEq_of_sub hp (by simpa using hpv_total)
  exact Int.natCast_modEq_iff.mp (by simpa [Nat.cast_pow] using hz)

-- ============================================================================
-- Block E: Proof of (P3) and (P4) (mod p^5, p >= 7)
-- ============================================================================

private def harmH (p m : ℕ) : ℚ := ∑ k ∈ Ico 1 p, ((k : ℚ) ^ m)⁻¹
private def harmh (m k : ℕ) : ℚ := ∑ j ∈ Ico 1 (k + 1), ((j : ℚ) ^ m)⁻¹
private def harmE2 (k : ℕ) : ℚ := ((harmh 1 k) ^ 2 - harmh 2 k) / 2
private def S12 (p : ℕ) : ℚ := ∑ k ∈ Ico 1 p, harmh 1 (k - 1) / (k : ℚ) ^ 2
private def S13 (p : ℕ) : ℚ := ∑ k ∈ Ico 1 p, harmh 1 (k - 1) / (k : ℚ) ^ 3
private def S22 (p : ℕ) : ℚ := ∑ k ∈ Ico 1 p, harmh 2 (k - 1) / (k : ℚ) ^ 2
private def S112 (p : ℕ) : ℚ := ∑ k ∈ Ico 1 p, (harmh 1 (k - 1)) ^ 2 / (k : ℚ) ^ 2

private lemma PVal.of_p {p : ℕ} (hp : p.Prime) : PVal p 1 (p : ℚ) := by
  simpa using PVal.of_pow_p (e := 1) hp

private lemma PVal.neg_of_p {p : ℕ} (hp : p.Prime) : PVal p 1 (-(p : ℚ)) :=
  (PVal.of_p hp).neg

private lemma PVal.div_of_mul_nat {p e n : ℕ} (hp : p.Prime) {q : ℚ}
    (hnd : ¬ p ∣ n) (h : PVal p e ((n : ℚ) * q)) : PVal p e q := by
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr fun h0 => hnd (h0 ▸ dvd_zero p)
  have h1 := h.div_nat hp hnd
  rwa [mul_div_cancel_left₀ q hn0] at h1

private lemma PVal.sub_trans {p e : ℕ} (hp : p.Prime) {x y z : ℚ}
    (h1 : PVal p e (x - y)) (h2 : PVal p e (y - z)) : PVal p e (x - z) := by
  simpa only [sub_add_sub_cancel] using h1.add hp h2

private lemma PVal.prod_sub_prod {ι : Type*} {s : Finset ι} {p e : ℕ} (hp : p.Prime)
    {f g : ι → ℚ} (hf : ∀ i ∈ s, PVal p 0 (f i)) (hg : ∀ i ∈ s, PVal p 0 (g i))
    (hd : ∀ i ∈ s, PVal p e (f i - g i)) :
    PVal p e ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PVal.zero hp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa := hf a (mem_insert_self a s)
    have hga := hg a (mem_insert_self a s)
    have hda := hd a (mem_insert_self a s)
    have hF : PVal p 0 (∏ i ∈ s, f i) := PVal.prod_zero hp fun i hi => hf i (mem_insert_of_mem hi)
    have hih := ih (fun i hi => hf i (mem_insert_of_mem hi))
      (fun i hi => hg i (mem_insert_of_mem hi)) (fun i hi => hd i (mem_insert_of_mem hi))
    have heq : f a * (∏ i ∈ s, f i) - g a * (∏ i ∈ s, g i) =
        (f a - g a) * (∏ i ∈ s, f i) + g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) := by ring
    rw [heq]
    exact (hda.mul_zero hp hF).add hp (hga.zero_mul hp hih)

private lemma PVal.prod_one_add_deg1_sq {ι : Type*} {s : Finset ι} {p : ℕ} (hp : p.Prime)
    {f : ι → ℚ} (hf : ∀ i ∈ s, PVal p 2 (f i)) :
    PVal p 4 ((∏ i ∈ s, (1 + f i)) - (1 + ∑ i ∈ s, f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PVal.zero hp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa := hf a (mem_insert_self a s)
    have hih := ih fun i hi => hf i (mem_insert_of_mem hi)
    have hS : PVal p 2 (∑ i ∈ s, f i) := PVal.sum hp fun i hi => hf i (mem_insert_of_mem hi)
    have h1fa : PVal p 0 (1 + f a) := (PVal.nat hp 1).add hp (hfa.mono (Nat.zero_le _))
    have heq : (1 + f a) * (∏ i ∈ s, (1 + f i)) - (1 + (f a + ∑ i ∈ s, f i)) =
        (1 + f a) * ((∏ i ∈ s, (1 + f i)) - (1 + ∑ i ∈ s, f i)) + f a * (∑ i ∈ s, f i) := by ring
    rw [heq]
    exact (h1fa.zero_mul hp hih).add hp (hfa.mul hp hS)

private lemma PVal.prod_one_add_deg2 {ι : Type*} {s : Finset ι} {p : ℕ} (hp : p.Prime)
    (hp2 : ¬ p ∣ 2) {f g : ι → ℚ}
    (hf : ∀ i ∈ s, PVal p 1 (f i)) (hg : ∀ i ∈ s, PVal p 2 (g i)) :
    PVal p 3 ((∏ i ∈ s, (1 + f i + g i)) -
      (1 + (∑ i ∈ s, f i) + (∑ i ∈ s, g i) + (((∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, (f i) ^ 2) / 2))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PVal.zero hp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    have hfa := hf a (mem_insert_self a s)
    have hga := hg a (mem_insert_self a s)
    have hih := ih (fun i hi => hf i (mem_insert_of_mem hi)) (fun i hi => hg i (mem_insert_of_mem hi))
    set S1 := ∑ i ∈ s, f i
    set S2 := ∑ i ∈ s, (f i) ^ 2
    set G1 := ∑ i ∈ s, g i
    set P := ∏ i ∈ s, (1 + f i + g i)
    set Q := 1 + S1 + G1 + (S1 ^ 2 - S2) / 2
    have hS1 : PVal p 1 S1 := PVal.sum hp fun i hi => hf i (mem_insert_of_mem hi)
    have hS2 : PVal p 2 S2 := PVal.sum hp fun i hi => by
      simpa using (hf i (mem_insert_of_mem hi)).pow hp 2
    have hG1 : PVal p 2 G1 := PVal.sum hp fun i hi => hg i (mem_insert_of_mem hi)
    have hE2 : PVal p 2 ((S1 ^ 2 - S2) / 2) := by
      have hsq : PVal p 2 (S1 ^ 2) := by simpa using hS1.pow hp 2
      simpa using (hsq.sub hp hS2).div_nat hp hp2
    have h1faga : PVal p 0 (1 + f a + g a) :=
      ((PVal.nat hp 1).add hp (hfa.mono (Nat.zero_le _))).add hp (hga.mono (Nat.zero_le _))
    have heq : (1 + f a + g a) * P - (1 + (f a + S1) + (g a + G1) + ((f a + S1) ^ 2 - ((f a) ^ 2 + S2)) / 2) =
        (1 + f a + g a) * (P - Q) + f a * (G1 + (S1 ^ 2 - S2) / 2) +
        g a * (S1 + G1 + (S1 ^ 2 - S2) / 2) := by simp only [Q]; ring
    rw [heq]
    have ht1 := h1faga.zero_mul hp hih
    have ht2 := hfa.mul hp (hG1.add hp hE2)
    have ht3 := hga.mul hp ((hS1.add hp (hG1.mono (by omega))).add hp (hE2.mono (by omega)))
    exact (ht1.add hp ht2).add hp ht3

private lemma PVal.prod_one_add_deg4 {ι : Type*} {s : Finset ι} {p : ℕ} (hp : p.Prime)
    (hp7 : 7 ≤ p) {f : ι → ℚ} (hf : ∀ i ∈ s, PVal p 1 (f i)) :
    PVal p 5 ((∏ i ∈ s, (1 + f i)) -
      (1 + (∑ i ∈ s, f i) +
        ((∑ i ∈ s, f i) ^ 2 - ∑ i ∈ s, (f i) ^ 2) / 2 +
        ((∑ i ∈ s, f i) ^ 3 - 3 * (∑ i ∈ s, f i) * (∑ i ∈ s, (f i) ^ 2) + 2 * ∑ i ∈ s, (f i) ^ 3) / 6 +
        ((∑ i ∈ s, f i) ^ 4 - 6 * (∑ i ∈ s, f i) ^ 2 * (∑ i ∈ s, (f i) ^ 2) +
          3 * (∑ i ∈ s, (f i) ^ 2) ^ 2 + 8 * (∑ i ∈ s, f i) * (∑ i ∈ s, (f i) ^ 3) -
          6 * ∑ i ∈ s, (f i) ^ 4) / 24)) := by
  classical
  have hnd24 : ¬ p ∣ 24 := fun h => by
    have := hp.dvd_mul.mp (show p ∣ 3 * 8 by simpa using h)
    rcases this with h3 | h8
    · have := Nat.le_of_dvd (by decide) h3; omega
    · have := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using h8)
      have := Nat.le_of_dvd (by decide) this; omega
  induction s using Finset.induction_on with
  | empty => simpa using PVal.zero hp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
      Finset.sum_insert ha, Finset.sum_insert ha]
    have hfa := hf a (mem_insert_self a s)
    have hih := ih fun i hi => hf i (mem_insert_of_mem hi)
    set t := f a
    set S1 := ∑ i ∈ s, f i
    set S2 := ∑ i ∈ s, (f i) ^ 2
    set S3 := ∑ i ∈ s, (f i) ^ 3
    set S4 := ∑ i ∈ s, (f i) ^ 4
    set P := ∏ i ∈ s, (1 + f i)
    set E4 := (S1 ^ 4 - 6 * S1 ^ 2 * S2 + 3 * S2 ^ 2 + 8 * S1 * S3 - 6 * S4) / 24
    set Q := 1 + S1 + (S1 ^ 2 - S2) / 2 + (S1 ^ 3 - 3 * S1 * S2 + 2 * S3) / 6 + E4
    have hS1 : PVal p 1 S1 := PVal.sum hp fun i hi => hf i (mem_insert_of_mem hi)
    have hS2 : PVal p 2 S2 := PVal.sum hp fun i hi => by
      simpa using (hf i (mem_insert_of_mem hi)).pow hp 2
    have hS3 : PVal p 3 S3 := PVal.sum hp fun i hi => by
      simpa using (hf i (mem_insert_of_mem hi)).pow hp 3
    have hS4 : PVal p 4 S4 := PVal.sum hp fun i hi => by
      simpa using (hf i (mem_insert_of_mem hi)).pow hp 4
    have hE4 : PVal p 4 E4 := by
      have ha1 : PVal p 4 (S1 ^ 4) := by simpa using hS1.pow hp 4
      have ha2 : PVal p 4 (6 * S1 ^ 2 * S2) :=
        ((PVal.nat hp 6).zero_mul hp (by simpa using hS1.pow hp 2)).mul hp hS2
      have ha3 : PVal p 4 (3 * S2 ^ 2) := (PVal.nat hp 3).zero_mul hp (by simpa using hS2.pow hp 2)
      have ha4 : PVal p 4 (8 * S1 * S3) := ((PVal.nat hp 8).zero_mul hp hS1).mul hp hS3
      have ha5 : PVal p 4 (6 * S4) := (PVal.nat hp 6).zero_mul hp hS4
      have hnum := (((ha1.sub hp ha2).add hp ha3).add hp ha4).sub hp ha5
      simpa only [E4, Nat.cast_ofNat] using hnum.div_nat hp hnd24
    have h1t : PVal p 0 (1 + t) := (PVal.nat hp 1).add hp (hfa.mono (Nat.zero_le _))
    have heq : (1 + t) * P -
        (1 + (t + S1) + ((t + S1) ^ 2 - (t ^ 2 + S2)) / 2 +
          ((t + S1) ^ 3 - 3 * (t + S1) * (t ^ 2 + S2) + 2 * (t ^ 3 + S3)) / 6 +
          ((t + S1) ^ 4 - 6 * (t + S1) ^ 2 * (t ^ 2 + S2) + 3 * (t ^ 2 + S2) ^ 2 +
            8 * (t + S1) * (t ^ 3 + S3) - 6 * (t ^ 4 + S4)) / 24) =
        (1 + t) * (P - Q) + t * E4 := by simp only [Q, E4]; ring
    rw [heq]
    exact (h1t.zero_mul hp hih).add hp (hfa.mul hp hE4)

private lemma sum_Ico_reflect (p : ℕ) (f : ℕ → ℚ) :
    ∑ k ∈ Ico 1 p, f (p - k) = ∑ k ∈ Ico 1 p, f k := by
  refine Finset.sum_bij (fun k _ => p - k) ?_ ?_ ?_ ?_
  · intro k hk; rw [mem_Ico] at hk ⊢; omega
  · intro a ha b hb hab; rw [mem_Ico] at ha hb; omega
  · intro b hb; rw [mem_Ico] at hb; exact ⟨p - b, by rw [mem_Ico]; omega, by omega⟩
  · intro _ _; rfl

private lemma not_dvd_of_lt_prime {p k : ℕ} (_hp : p.Prime) (h1 : 1 ≤ k) (h2 : k < p) : ¬ p ∣ k :=
  fun h => by have := Nat.le_of_dvd h1 h; omega

private lemma inv_sub_inv_pval {p : ℕ} (hp : p.Prime) {a b : ℕ}
    (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) (hcong : (a : ℤ) ≡ (b : ℤ) [ZMOD (p : ℤ)]) :
    PVal p 1 (((a : ℚ))⁻¹ - ((b : ℚ))⁻¹) := by
  have ha0 : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr fun h0 => ha (h0 ▸ dvd_zero p)
  have hb0 : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr fun h0 => hb (h0 ▸ dvd_zero p)
  have heq : ((a : ℚ))⁻¹ - ((b : ℚ))⁻¹ = (((b : ℤ) - (a : ℤ) : ℤ) : ℚ) / (((a * b : ℕ) : ℚ)) := by
    push_cast; field_simp [ha0, hb0]
  rw [heq]
  have hdvd : (p : ℤ) ^ 1 ∣ (b : ℤ) - (a : ℤ) := by
    rw [pow_one]; exact Int.modEq_iff_dvd.mp hcong
  have hnd : ¬ p ∣ a * b := fun h => by rcases hp.dvd_mul.mp h with h1 | h2; exact ha h1; exact hb h2
  exact (PVal.of_dvd_int hp hdvd).div_nat hp hnd

private lemma pow_sub_pow_pval {p e : ℕ} (hp : p.Prime) {x y : ℚ}
    (hx : PVal p 0 x) (hy : PVal p 0 y) (hd : PVal p e (x - y)) (m : ℕ) :
    PVal p e (x ^ m - y ^ m) := by
  induction m with
  | zero => simpa using PVal.zero hp
  | succ m ih =>
    have heq : x ^ (m + 1) - y ^ (m + 1) = (x - y) * x ^ m + y * (x ^ m - y ^ m) := by ring
    rw [heq]
    exact (hd.mul_zero hp (by simpa using hx.pow hp m)).add hp (hy.zero_mul hp ih)

/-- Bijection k |-> (2 * k) % p on Ico 1 p for odd prime p. -/
private lemma sum_Ico_mul_two_mod (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (f : ℕ → ℚ) :
    ∑ k ∈ Ico 1 p, f ((2 * k) % p) = ∑ k ∈ Ico 1 p, f k := by
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  have hnd2 : ¬ p ∣ 2 := not_dvd_of_lt_prime hp (by decide) (by omega)
  refine Finset.sum_bij (fun k _ => (2 * k) % p) ?_ ?_ ?_ ?_
  · intro k hk; rw [mem_Ico] at hk ⊢
    have hne : (2 * k) % p ≠ 0 := by
      intro h0
      have hd : p ∣ 2 * k := Nat.dvd_of_mod_eq_zero h0
      rcases hp.dvd_mul.mp hd with h2 | hk'
      · exact hnd2 h2
      · exact not_dvd_of_lt_prime hp hk.1 hk.2 hk'
    exact ⟨Nat.pos_of_ne_zero hne, Nat.mod_lt _ hp.pos⟩
  · intro a ha b hb hab; rw [mem_Ico] at ha hb
    have hmod : (2 * a : ℤ) ≡ (2 * b : ℤ) [ZMOD (p : ℤ)] := by
      have : ((2 * a) % p : ℤ) = ((2 * b) % p : ℤ) := by exact_mod_cast hab
      simpa only [Int.ModEq, Int.natCast_mod] using this
    have hd : (p : ℤ) ∣ 2 * ((b : ℤ) - (a : ℤ)) := by
      have := Int.modEq_iff_dvd.mp hmod; simpa [mul_sub] using this
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpz.dvd_or_dvd hd with h2 | hab'
    · exact False.elim (hnd2 (Int.natCast_dvd_natCast.mp h2))
    · obtain ⟨c, hc⟩ := hab'
      have hc0 : c = 0 := by
        by_contra hne
        have : 1 ≤ c.natAbs := Int.natAbs_pos.mpr hne
        have hlt : ((b : ℤ) - (a : ℤ)).natAbs < p := by omega
        have heq : ((b : ℤ) - (a : ℤ)).natAbs = p * c.natAbs := by
          rw [hc, Int.natAbs_mul, Int.natAbs_natCast]
        nlinarith
      subst hc0; simp at hc; omega
  · intro b hb; rw [mem_Ico] at hb
    by_cases hev : 2 ∣ b
    · refine ⟨b / 2, by rw [mem_Ico]; omega, ?_⟩
      rw [Nat.mul_div_cancel' hev, Nat.mod_eq_of_lt hb.2]
    · obtain ⟨t, ht⟩ := hp_odd
      have h2bp : 2 ∣ b + p := by omega
      refine ⟨(b + p) / 2, by rw [mem_Ico]; omega, ?_⟩
      rw [Nat.mul_div_cancel' h2bp, Nat.add_mod_right, Nat.mod_eq_of_lt hb.2]
  · intro _ _; rfl

/-- E1(1): (2^m - 1) * H_m in p * Z_(p). -/
private lemma harmH_scale_two (p m : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    PVal p 1 (((2 : ℚ) ^ m - 1) * harmH p m) := by
  have hnd2 : ¬ p ∣ 2 := not_dvd_of_lt_prime hp (by decide) (by omega)
  have hrew : harmH p m = ∑ k ∈ Ico 1 p, ((((2 * k) % p : ℕ) : ℚ) ^ m)⁻¹ :=
    (sum_Ico_mul_two_mod p hp (by omega) (fun k => ((k : ℚ) ^ m)⁻¹)).symm
  have hdiff : PVal p 1 (harmH p m - ((2 : ℚ) ^ m)⁻¹ * harmH p m) := by
    nth_rw 1 [hrew]
    rw [harmH, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine PVal.sum hp fun k hk => ?_
    rw [mem_Ico] at hk
    have hndk : ¬ p ∣ k := not_dvd_of_lt_prime hp hk.1 hk.2
    have hnd2k : ¬ p ∣ 2 * k := fun h => by rcases hp.dvd_mul.mp h with h1 | h2; exact hnd2 h1; exact hndk h2
    have hndphi : ¬ p ∣ (2 * k) % p := by
      have hne : (2 * k) % p ≠ 0 := fun h0 => hnd2k (Nat.dvd_of_mod_eq_zero h0)
      exact not_dvd_of_lt_prime hp (Nat.pos_of_ne_zero hne) (Nat.mod_lt _ hp.pos)
    have hcong : (((2 * k) % p : ℕ) : ℤ) ≡ ((2 * k : ℕ) : ℤ) [ZMOD (p : ℤ)] := by
      simpa only [Int.ModEq, Int.natCast_mod] using Int.emod_emod ((2 * k : ℕ) : ℤ) (p : ℤ)
    have hbase := inv_sub_inv_pval hp hndphi hnd2k hcong
    have hpow := pow_sub_pow_pval hp (PVal.inv_nat hndphi) (PVal.inv_nat hnd2k) hbase m
    convert hpow using 1
    rw [inv_pow, inv_pow, ← mul_inv, ← mul_pow]; push_cast; ring
  have hmul := (by simpa using (PVal.nat hp 2).pow hp m : PVal p 0 ((2 : ℚ) ^ m)).zero_mul hp hdiff
  have h2m0 : (2 : ℚ) ^ m ≠ 0 := by positivity
  convert hmul using 1
  field_simp [h2m0]

private lemma harmH_two_mod_p (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 1 (harmH p 2) := by
  have h := harmH_scale_two p 2 hp (by omega)
  have h3 : (2 : ℚ) ^ 2 - 1 = (3 : ℕ) := by norm_num
  rw [h3] at h
  exact PVal.div_of_mul_nat hp (not_dvd_of_lt_prime hp (by decide) (by omega)) h

private lemma harmH_four_mod_p (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 1 (harmH p 4) := by
  have h := harmH_scale_two p 4 hp (by omega)
  have h15 : (2 : ℚ) ^ 4 - 1 = (15 : ℕ) := by norm_num
  rw [h15] at h
  have hnd15 : ¬ p ∣ 15 := fun h' => by
    rcases hp.dvd_mul.mp (show p ∣ 3 * 5 by simpa using h') with h3 | h5
    · exact not_dvd_of_lt_prime hp (by decide) (by omega) h3
    · exact not_dvd_of_lt_prime hp (by decide) (by omega) h5
  exact PVal.div_of_mul_nat hp hnd15 h

/-- E1(2): H_3 in p^2 * Z_(p) for p >= 7. -/
private lemma harmH_three_mod_p2 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 2 (harmH p 3) := by
  have hpair : (2 : ℚ) * harmH p 3 + 3 * (p : ℚ) * harmH p 4 =
      (p : ℚ) ^ 2 * ∑ k ∈ Ico 1 p,
        (6 * (k : ℚ) ^ 2 - 8 * (p : ℚ) * (k : ℚ) + 3 * (p : ℚ) ^ 2) /
          ((k : ℚ) ^ 4 * ((p - k : ℕ) : ℚ) ^ 3) := by
    have h2 : (2 : ℚ) * harmH p 3 = ∑ k ∈ Ico 1 p, (((k : ℚ) ^ 3)⁻¹ + (((p - k : ℕ) : ℚ) ^ 3)⁻¹) := by
      rw [two_mul]; nth_rw 2 [harmH]
      rw [← sum_Ico_reflect p (fun k => ((k : ℚ) ^ 3)⁻¹), harmH, ← Finset.sum_add_distrib]
    rw [h2, harmH, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [mem_Ico] at hk
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpk0 : ((p - k : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpk_sub : ((p - k : ℕ) : ℚ) = (p : ℚ) - (k : ℚ) := by rw [Nat.cast_sub (by omega)]
    rw [hpk_sub] at hpk0 ⊢
    field_simp [hk0, hpk0]; ring
  have hrhs : PVal p 2 ((2 : ℚ) * harmH p 3 + 3 * (p : ℚ) * harmH p 4) := by
    rw [hpair]
    have hsum : PVal p 0 (∑ k ∈ Ico 1 p,
        (6 * (k : ℚ) ^ 2 - 8 * (p : ℚ) * (k : ℚ) + 3 * (p : ℚ) ^ 2) /
          ((k : ℚ) ^ 4 * ((p - k : ℕ) : ℚ) ^ 3)) := by
      refine PVal.sum hp fun k hk => ?_
      rw [mem_Ico] at hk
      have hndk : ¬ p ∣ k := not_dvd_of_lt_prime hp hk.1 hk.2
      have hndpk : ¬ p ∣ p - k := not_dvd_of_lt_prime hp (by omega) (by omega)
      have hnd_den : ¬ p ∣ k ^ 4 * (p - k) ^ 3 := fun h => by
        rcases hp.dvd_mul.mp h with h1 | h2
        · exact hndk (hp.dvd_of_dvd_pow h1)
        · exact hndpk (hp.dvd_of_dvd_pow h2)
      have hnum : PVal p 0 (6 * (k : ℚ) ^ 2 - 8 * (p : ℚ) * (k : ℚ) + 3 * (p : ℚ) ^ 2) :=
        ((((PVal.nat hp 6).mul_zero hp (by simpa using (PVal.nat hp k).pow hp 2)).sub hp
          (((PVal.nat hp 8).mul_zero hp (PVal.nat hp p)).mul_zero hp (PVal.nat hp k))).add hp
          ((PVal.nat hp 3).mul_zero hp (by simpa using (PVal.nat hp p).pow hp 2)))
      simpa only [Nat.cast_mul, Nat.cast_pow] using hnum.div_nat hp hnd_den
    exact (PVal.of_pow_p (e := 2) hp).mul_zero hp hsum
  have hH4 : PVal p 2 (3 * (p : ℚ) * harmH p 4) := by
    have h1 := ((PVal.nat hp 3).zero_mul hp (PVal.of_p hp)).mul hp (harmH_four_mod_p p hp hp7)
    simpa [mul_assoc] using h1
  have h2H3 : PVal p 2 ((2 : ℕ) * harmH p 3) := by
    simpa using hrhs.sub hp hH4
  exact PVal.div_of_mul_nat hp (not_dvd_of_lt_prime hp (by decide) (by omega)) h2H3

/-- E1(3): 2 * H_1 + p * H_2 in p^4 * Z_(p) for p >= 7. -/
private lemma two_harmH1_add_p_harmH2 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 4 (2 * harmH p 1 + (p : ℚ) * harmH p 2) := by
  have hid : 2 * harmH p 1 + (p : ℚ) * harmH p 2 + (p : ℚ) ^ 2 * harmH p 3 + (p : ℚ) ^ 3 * harmH p 4 =
      (p : ℚ) ^ 4 * ∑ k ∈ Ico 1 p, (((k : ℚ) ^ 4 * ((p - k : ℕ) : ℚ)))⁻¹ := by
    have h2 : 2 * harmH p 1 = ∑ k ∈ Ico 1 p, (((k : ℚ) ^ 1)⁻¹ + (((p - k : ℕ) : ℚ) ^ 1)⁻¹) := by
      rw [two_mul]; nth_rw 2 [harmH]
      rw [← sum_Ico_reflect p (fun k => ((k : ℚ) ^ 1)⁻¹), harmH, ← Finset.sum_add_distrib]
    rw [h2, harmH, harmH, harmH, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [mem_Ico] at hk
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpk0 : ((p - k : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpk_sub : ((p - k : ℕ) : ℚ) = (p : ℚ) - (k : ℚ) := by rw [Nat.cast_sub (by omega)]
    rw [hpk_sub] at hpk0 ⊢
    field_simp [hk0, hpk0]; ring
  have hrhs : PVal p 4 (2 * harmH p 1 + (p : ℚ) * harmH p 2 + (p : ℚ) ^ 2 * harmH p 3 + (p : ℚ) ^ 3 * harmH p 4) := by
    rw [hid]
    have hsum : PVal p 0 (∑ k ∈ Ico 1 p, (((k : ℚ) ^ 4 * ((p - k : ℕ) : ℚ)))⁻¹) := by
      refine PVal.sum hp fun k hk => ?_
      rw [mem_Ico] at hk
      have hnd : ¬ p ∣ k ^ 4 * (p - k) := fun h => by
        rcases hp.dvd_mul.mp h with h1 | h2
        · exact not_dvd_of_lt_prime hp hk.1 hk.2 (hp.dvd_of_dvd_pow h1)
        · exact not_dvd_of_lt_prime hp (by omega) (by omega) h2
      simpa only [Nat.cast_mul, Nat.cast_pow] using PVal.inv_nat hnd
    exact (PVal.of_pow_p (e := 4) hp).mul_zero hp hsum
  have h3 : PVal p 4 ((p : ℚ) ^ 2 * harmH p 3) :=
    (PVal.of_pow_p (e := 2) hp).mul hp (harmH_three_mod_p2 p hp hp7)
  have h4 : PVal p 4 ((p : ℚ) ^ 3 * harmH p 4) :=
    (PVal.of_pow_p (e := 3) hp).mul hp (harmH_four_mod_p p hp hp7)
  have hsub := (hrhs.sub hp h4).sub hp h3
  convert hsub using 1; ring

private lemma harmH1_mod_p2 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 2 (harmH p 1) := by
  have h1 := (two_harmH1_add_p_harmH2 p hp hp7).mono (by decide : 2 ≤ 4)
  have h2 : PVal p 2 ((p : ℚ) * harmH p 2) := by
    simpa using (PVal.of_pow_p (e := 1) hp).mul hp (harmH_two_mod_p p hp hp7)
  have h3 : PVal p 2 ((2 : ℕ) * harmH p 1) := by simpa using h1.sub hp h2
  exact PVal.div_of_mul_nat hp (not_dvd_of_lt_prime hp (by decide) (by omega)) h3

private lemma p2_harmH2_mod_p5 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 5 ((p : ℚ) ^ 2 * harmH p 2 + 2 * (p : ℚ) * harmH p 1) := by
  have h := (PVal.of_pow_p (e := 1) hp).mul hp (two_harmH1_add_p_harmH2 p hp hp7)
  convert h using 1; ring

/-- E2: Truncated product expansion prod_{s=1}^{p-1} (1 + a*p/s) - 1 == (a + a^2) * p * H_1 (mod p^5). -/
private lemma prod_one_add_ap_mod_p5 (p : ℕ) (a : ℤ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 5 ((∏ s ∈ Ico 1 p, (1 + (a : ℚ) * (p : ℚ) / (s : ℚ))) - 1 -
      ((a : ℚ) + (a : ℚ) ^ 2) * (p : ℚ) * harmH p 1) := by
  have hf : ∀ s ∈ Ico 1 p, PVal p 1 ((a : ℚ) * (p : ℚ) / (s : ℚ)) := fun s hs => by
    rw [mem_Ico] at hs
    have hnum : PVal p 1 ((a : ℚ) * (p : ℚ)) := by
      simpa using (PVal.int hp a).zero_mul hp (PVal.of_pow_p (e := 1) hp)
    exact hnum.div_nat hp (not_dvd_of_lt_prime hp hs.1 hs.2)
  have hdeg4 := PVal.prod_one_add_deg4 hp hp7 hf
  have hS : ∀ m : ℕ, ∑ s ∈ Ico 1 p, ((a : ℚ) * (p : ℚ) / (s : ℚ)) ^ m =
      (a : ℚ) ^ m * (p : ℚ) ^ m * harmH p m := by
    intro m; simp only [harmH, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [div_pow, mul_pow, div_eq_mul_inv]
  have hS1 : ∑ s ∈ Ico 1 p, (a : ℚ) * (p : ℚ) / (s : ℚ) = (a : ℚ) * (p : ℚ) * harmH p 1 := by
    simpa only [pow_one] using hS 1
  simp only [hS1, hS 2, hS 3, hS 4] at hdeg4
  have hnd2 : ¬ p ∣ 2 := not_dvd_of_lt_prime hp (by decide) (by omega)
  have hnd6 : ¬ p ∣ 6 := fun h => by
    rcases hp.dvd_mul.mp (show p ∣ 2 * 3 by simpa using h) with h2 | h3
    · exact hnd2 h2
    · exact not_dvd_of_lt_prime hp (by decide) (by omega) h3
  have hnd24 : ¬ p ∣ 24 := fun h => by
    rcases hp.dvd_mul.mp (show p ∣ 6 * 4 by simpa using h) with h6 | h4
    · exact hnd6 h6
    · exact hnd2 (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by simpa using h4))
  have hH1 := harmH1_mod_p2 p hp hp7
  have hH2 := harmH_two_mod_p p hp hp7
  have hH3 := harmH_three_mod_p2 p hp hp7
  have hH4 := harmH_four_mod_p p hp hp7
  have h1 : PVal p 3 ((a : ℚ) * (p : ℚ) * harmH p 1) := by
    simpa [mul_assoc] using (PVal.int hp a).zero_mul hp ((PVal.of_pow_p (e := 1) hp).mul hp hH1)
  have h2 : PVal p 3 ((a : ℚ) ^ 2 * (p : ℚ) ^ 2 * harmH p 2) := by
    simpa [mul_assoc] using (by simpa using (PVal.int hp a).pow hp 2 : PVal p 0 ((a : ℚ) ^ 2)).zero_mul hp
      ((PVal.of_pow_p (e := 2) hp).mul hp hH2)
  have h3 : PVal p 5 ((a : ℚ) ^ 3 * (p : ℚ) ^ 3 * harmH p 3) := by
    simpa [mul_assoc] using (by simpa using (PVal.int hp a).pow hp 3 : PVal p 0 ((a : ℚ) ^ 3)).zero_mul hp
      ((PVal.of_pow_p (e := 3) hp).mul hp hH3)
  have h4 : PVal p 5 ((a : ℚ) ^ 4 * (p : ℚ) ^ 4 * harmH p 4) := by
    simpa [mul_assoc] using (by simpa using (PVal.int hp a).pow hp 4 : PVal p 0 ((a : ℚ) ^ 4)).zero_mul hp
      ((PVal.of_pow_p (e := 4) hp).mul hp hH4)
  have hE2_diff : PVal p 5 ((((a : ℚ) * (p : ℚ) * harmH p 1) ^ 2 - (a : ℚ) ^ 2 * (p : ℚ) ^ 2 * harmH p 2) / 2 -
      (a : ℚ) ^ 2 * (p : ℚ) * harmH p 1) := by
    have heq : (((a : ℚ) * (p : ℚ) * harmH p 1) ^ 2 - (a : ℚ) ^ 2 * (p : ℚ) ^ 2 * harmH p 2) / 2 -
        (a : ℚ) ^ 2 * (p : ℚ) * harmH p 1 =
        (((a : ℚ) * (p : ℚ) * harmH p 1) ^ 2 - (a : ℚ) ^ 2 * ((p : ℚ) ^ 2 * harmH p 2 + 2 * (p : ℚ) * harmH p 1)) / 2 := by ring
    rw [heq]
    have ha2 : PVal p 0 ((a : ℚ) ^ 2) := by simpa using (PVal.int hp a).pow hp 2
    have hnum := ((h1.pow hp 2).mono (by decide)).sub hp (ha2.zero_mul hp (p2_harmH2_mod_p5 p hp hp7))
    simpa only [Nat.cast_ofNat] using hnum.div_nat hp hnd2
  have hE3 : PVal p 5 ((((a : ℚ) * (p : ℚ) * harmH p 1) ^ 3 -
      3 * ((a : ℚ) * (p : ℚ) * harmH p 1) * ((a : ℚ) ^ 2 * (p : ℚ) ^ 2 * harmH p 2) +
      2 * ((a : ℚ) ^ 3 * (p : ℚ) ^ 3 * harmH p 3)) / 6) := by
    have hnum := (((h1.pow hp 3).mono (by decide)).sub hp
      (((PVal.nat hp 3).zero_mul hp h1).mul hp h2 |>.mono (by decide))).add hp
      ((PVal.nat hp 2).zero_mul hp h3)
    simpa only [Nat.cast_ofNat] using hnum.div_nat hp hnd6
  have hE4 : PVal p 5 ((((a : ℚ) * (p : ℚ) * harmH p 1) ^ 4 -
      6 * ((a : ℚ) * (p : ℚ) * harmH p 1) ^ 2 * ((a : ℚ) ^ 2 * (p : ℚ) ^ 2 * harmH p 2) +
      3 * ((a : ℚ) ^ 2 * (p : ℚ) ^ 2 * harmH p 2) ^ 2 +
      8 * ((a : ℚ) * (p : ℚ) * harmH p 1) * ((a : ℚ) ^ 3 * (p : ℚ) ^ 3 * harmH p 3) -
      6 * ((a : ℚ) ^ 4 * (p : ℚ) ^ 4 * harmH p 4)) / 24) := by
    have hnum := (((((h1.pow hp 4).mono (by decide)).sub hp
      (((PVal.nat hp 6).zero_mul hp (h1.pow hp 2)).mul hp h2 |>.mono (by decide))).add hp
      ((PVal.nat hp 3).zero_mul hp ((h2.pow hp 2).mono (by decide)))).add hp
      (((PVal.nat hp 8).zero_mul hp h1).mul hp h3 |>.mono (by decide))).sub hp
      ((PVal.nat hp 6).zero_mul hp h4)
    simpa only [Nat.cast_ofNat] using hnum.div_nat hp hnd24
  have hcomb := ((hdeg4.add hp hE2_diff).add hp hE3).add hp hE4
  convert hcomb using 1; ring

private lemma harmh_pval_zero (p m k : ℕ) (hp : p.Prime) (hk : k < p) :
    PVal p 0 (harmh m k) := by
  refine PVal.sum hp fun j hj => ?_
  rw [mem_Ico] at hj
  have hnd : ¬ p ∣ j ^ m := fun h => not_dvd_of_lt_prime hp hj.1 (by omega) (hp.dvd_of_dvd_pow h)
  simpa only [Nat.cast_pow] using PVal.inv_nat hnd

/-- E3(1a): h_1(p - k) == h_1(k - 1) (mod p) for 1 <= k < p. -/
private lemma harmh1_reflect (p k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hk1 : 1 ≤ k) (hkp : k < p) :
    PVal p 1 (harmh 1 (p - k) - harmh 1 (k - 1)) := by
  have hsplit : harmH p 1 = harmh 1 (p - k) + ∑ j ∈ Ico (p - k + 1) p, ((j : ℚ) ^ 1)⁻¹ := by
    simp only [harmH, harmh]
    exact (Finset.sum_Ico_consecutive (fun j => ((j : ℚ) ^ 1)⁻¹) (by omega) (by omega)).symm
  have htail : ∑ j ∈ Ico (p - k + 1) p, ((j : ℚ) ^ 1)⁻¹ =
      ∑ u ∈ Ico 1 k, (((p - u : ℕ) : ℚ))⁻¹ := by
    refine Finset.sum_bij (fun j _ => p - j) ?_ ?_ ?_ ?_
    · intro j hj; rw [mem_Ico] at hj ⊢; omega
    · intro a ha b hb hab; rw [mem_Ico] at ha hb; omega
    · intro u hu; rw [mem_Ico] at hu; exact ⟨p - u, by rw [mem_Ico]; omega, by omega⟩
    · intro j hj; rw [mem_Ico] at hj; simp [show p - (p - j) = j by omega]
  have hsum : PVal p 1 ((∑ u ∈ Ico 1 k, (((p - u : ℕ) : ℚ))⁻¹) + harmh 1 (k - 1)) := by
    simp only [harmh, show k - 1 + 1 = k by omega, pow_one, ← Finset.sum_add_distrib]
    refine PVal.sum hp fun u hu => ?_
    rw [mem_Ico] at hu
    have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpu0 : ((p - u : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have heq : (((p - u : ℕ) : ℚ))⁻¹ + ((u : ℚ))⁻¹ = (p : ℚ) / (((p - u : ℕ) * u : ℕ) : ℚ) := by
      rw [Nat.cast_mul]; rw [Nat.cast_sub (by omega)] at hpu0 ⊢; field_simp [hu0, hpu0]; ring
    rw [heq]
    have hnd : ¬ p ∣ (p - u) * u := fun h => by
      rcases hp.dvd_mul.mp h with h1 | h2
      · exact not_dvd_of_lt_prime hp (by omega) (by omega) h1
      · exact not_dvd_of_lt_prime hp hu.1 (by omega) h2
    exact (PVal.of_p hp).div_nat hp hnd
  have heq : harmh 1 (p - k) - harmh 1 (k - 1) =
      harmH p 1 - ((∑ u ∈ Ico 1 k, (((p - u : ℕ) : ℚ))⁻¹) + harmh 1 (k - 1)) := by
    rw [hsplit, htail]; ring
  rw [heq]
  exact ((harmH1_mod_p2 p hp hp7).mono (by decide)).sub hp hsum

/-- E3(1b): h_2(p - k) == -h_2(k - 1) (mod p) for 1 <= k < p. -/
private lemma harmh2_reflect (p k : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hk1 : 1 ≤ k) (hkp : k < p) :
    PVal p 1 (harmh 2 (p - k) + harmh 2 (k - 1)) := by
  have hsplit : harmH p 2 = harmh 2 (p - k) + ∑ j ∈ Ico (p - k + 1) p, ((j : ℚ) ^ 2)⁻¹ := by
    simp only [harmH, harmh]
    exact (Finset.sum_Ico_consecutive (fun j => ((j : ℚ) ^ 2)⁻¹) (by omega) (by omega)).symm
  have htail : ∑ j ∈ Ico (p - k + 1) p, ((j : ℚ) ^ 2)⁻¹ =
      ∑ u ∈ Ico 1 k, (((p - u : ℕ) : ℚ) ^ 2)⁻¹ := by
    refine Finset.sum_bij (fun j _ => p - j) ?_ ?_ ?_ ?_
    · intro j hj; rw [mem_Ico] at hj ⊢; omega
    · intro a ha b hb hab; rw [mem_Ico] at ha hb; omega
    · intro u hu; rw [mem_Ico] at hu; exact ⟨p - u, by rw [mem_Ico]; omega, by omega⟩
    · intro j hj; rw [mem_Ico] at hj; simp [show p - (p - j) = j by omega]
  have hdiff : PVal p 1 ((∑ u ∈ Ico 1 k, (((p - u : ℕ) : ℚ) ^ 2)⁻¹) - harmh 2 (k - 1)) := by
    simp only [harmh, show k - 1 + 1 = k by omega, ← Finset.sum_sub_distrib]
    refine PVal.sum hp fun u hu => ?_
    rw [mem_Ico] at hu
    have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpu0 : ((p - u : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have heq : (((p - u : ℕ) : ℚ) ^ 2)⁻¹ - ((u : ℚ) ^ 2)⁻¹ =
        (p : ℚ) * (2 * (u : ℚ) - (p : ℚ)) / ((((p - u : ℕ) ^ 2 * u ^ 2 : ℕ) : ℚ)) := by
      push_cast; rw [Nat.cast_sub (by omega)] at hpu0 ⊢; field_simp [hu0, hpu0]; ring
    rw [heq]
    have hnd : ¬ p ∣ (p - u) ^ 2 * u ^ 2 := fun h => by
      rcases hp.dvd_mul.mp h with h1 | h2
      · exact not_dvd_of_lt_prime hp (by omega) (by omega) (hp.dvd_of_dvd_pow h1)
      · exact not_dvd_of_lt_prime hp hu.1 (by omega) (hp.dvd_of_dvd_pow h2)
    have hnum : PVal p 1 ((p : ℚ) * (2 * (u : ℚ) - (p : ℚ))) :=
      (PVal.of_p hp).mul_zero hp
        (((PVal.nat hp 2).mul_zero hp (PVal.nat hp u)).sub hp (PVal.nat hp p))
    exact hnum.div_nat hp hnd
  have heq : harmh 2 (p - k) + harmh 2 (k - 1) =
      harmH p 2 - ((∑ u ∈ Ico 1 k, (((p - u : ℕ) : ℚ) ^ 2)⁻¹) - harmh 2 (k - 1)) := by
    rw [hsplit, htail]; ring
  rw [heq]
  exact (harmH_two_mod_p p hp hp7).sub hp hdiff

private lemma two_mul_sum_lt_eq (n : ℕ) (f : ℕ → ℚ) :
    2 * ∑ k ∈ Ico 1 n, (∑ j ∈ Ico 1 k, f j) * f k =
      (∑ k ∈ Ico 1 n, f k) ^ 2 - ∑ k ∈ Ico 1 n, (f k) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp
    · have h1n : 1 ≤ n := by omega
      rw [Finset.sum_Ico_succ_top h1n, Finset.sum_Ico_succ_top h1n, Finset.sum_Ico_succ_top h1n]
      linarith

/-- E3(2a): S_{2,2} in p * Z_(p). -/
private lemma S22_mod_p (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : PVal p 1 (S22 p) := by
  have h2 : (2 : ℕ) * S22 p = (harmH p 2) ^ 2 - harmH p 4 := by
    have h := two_mul_sum_lt_eq p (fun k => ((k : ℚ) ^ 2)⁻¹)
    have hS : S22 p = ∑ k ∈ Ico 1 p, (∑ j ∈ Ico 1 k, ((j : ℚ) ^ 2)⁻¹) * ((k : ℚ) ^ 2)⁻¹ := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [mem_Ico] at hk; simp only [harmh, show k - 1 + 1 = k by omega, div_eq_mul_inv]
    have h4 : ∑ k ∈ Ico 1 p, (((k : ℚ) ^ 2)⁻¹) ^ 2 = harmH p 4 := by
      refine Finset.sum_congr rfl fun k _ => ?_; rw [inv_pow, ← pow_mul]
    rw [← hS, ← harmH, h4] at h; simpa using h
  have hrhs : PVal p 1 ((harmH p 2) ^ 2 - harmH p 4) :=
    (((harmH_two_mod_p p hp hp7).pow hp 2).mono (by decide)).sub hp (harmH_four_mod_p p hp hp7)
  rw [← h2] at hrhs
  exact PVal.div_of_mul_nat hp (not_dvd_of_lt_prime hp (by decide) (by omega)) hrhs

/-- E3(2b): S_{1,3} in p * Z_(p). -/
private lemma S13_mod_p (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) : PVal p 1 (S13 p) := by
  have href : S13 p = ∑ k ∈ Ico 1 p, harmh 1 (p - k - 1) / ((p - k : ℕ) : ℚ) ^ 3 :=
    (sum_Ico_reflect p (fun k => harmh 1 (k - 1) / (k : ℚ) ^ 3)).symm
  have hsum : PVal p 1 (2 * S13 p + harmH p 4) := by
    have heq : 2 * S13 p + harmH p 4 =
        ∑ k ∈ Ico 1 p, (harmh 1 (p - k - 1) / ((p - k : ℕ) : ℚ) ^ 3 +
          (harmh 1 (k - 1) + ((k : ℚ))⁻¹) / (k : ℚ) ^ 3) := by
      rw [two_mul]; nth_rw 1 [href]
      simp only [S13, harmH, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [mem_Ico] at hk
      have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp [hk0]; ring
    rw [heq]
    refine PVal.sum hp fun k hk => ?_
    rw [mem_Ico] at hk
    have hndk : ¬ p ∣ k := not_dvd_of_lt_prime hp hk.1 hk.2
    have hndpk : ¬ p ∣ p - k := not_dvd_of_lt_prime hp (by omega) (by omega)
    have hnum_diff : PVal p 1 (harmh 1 (p - k - 1) - (harmh 1 (k - 1) + ((k : ℚ))⁻¹)) := by
      have hstep : harmh 1 (p - k) = harmh 1 (p - k - 1) + (((p - k : ℕ) : ℚ))⁻¹ := by
        simp only [harmh, show p - k - 1 + 1 = p - k by omega, pow_one]
        exact Finset.sum_Ico_succ_top (by omega) _
      have hinv : PVal p 1 ((((p - k : ℕ) : ℚ))⁻¹ + ((k : ℚ))⁻¹) := by
        have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hpk0 : ((p - k : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have h1 : (((p - k : ℕ) : ℚ))⁻¹ + ((k : ℚ))⁻¹ = (p : ℚ) / (((p - k) * k : ℕ) : ℚ) := by
          rw [Nat.cast_mul]; rw [Nat.cast_sub (by omega)] at hpk0 ⊢; field_simp [hk0, hpk0]; ring
        rw [h1]
        have hnd : ¬ p ∣ (p - k) * k := fun h => by rcases hp.dvd_mul.mp h with h1 | h2; exact hndpk h1; exact hndk h2
        exact (PVal.of_p hp).div_nat hp hnd
      have hrew : harmh 1 (p - k - 1) - (harmh 1 (k - 1) + ((k : ℚ))⁻¹) =
          (harmh 1 (p - k) - harmh 1 (k - 1)) - ((((p - k : ℕ) : ℚ))⁻¹ + ((k : ℚ))⁻¹) := by linarith
      rw [hrew]; exact (harmh1_reflect p k hp hp7 hk.1 hk.2).sub hp hinv
    have hden_sum : PVal p 1 ((((p - k : ℕ) : ℚ) ^ 3)⁻¹ + ((k : ℚ) ^ 3)⁻¹) := by
      have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hpk0 : ((p - k : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h1 : (((p - k : ℕ) : ℚ) ^ 3)⁻¹ + ((k : ℚ) ^ 3)⁻¹ =
          (p : ℚ) * (3 * (k : ℚ) ^ 2 - 3 * (p : ℚ) * (k : ℚ) + (p : ℚ) ^ 2) / (((p - k) ^ 3 * k ^ 3 : ℕ) : ℚ) := by
        push_cast; rw [Nat.cast_sub (by omega)] at hpk0 ⊢; field_simp [hk0, hpk0]; ring
      rw [h1]
      have hnd : ¬ p ∣ (p - k) ^ 3 * k ^ 3 := fun h => by
        rcases hp.dvd_mul.mp h with h1 | h2
        · exact hndpk (hp.dvd_of_dvd_pow h1)
        · exact hndk (hp.dvd_of_dvd_pow h2)
      have hnum : PVal p 1 ((p : ℚ) * (3 * (k : ℚ) ^ 2 - 3 * (p : ℚ) * (k : ℚ) + (p : ℚ) ^ 2)) :=
        (PVal.of_p hp).mul_zero hp
          ((((PVal.nat hp 3).mul_zero hp (by simpa using (PVal.nat hp k).pow hp 2)).sub hp
            (((PVal.nat hp 3).mul_zero hp (PVal.nat hp p)).mul_zero hp (PVal.nat hp k))).add hp
            (by simpa using (PVal.nat hp p).pow hp 2))
      exact hnum.div_nat hp hnd
    have hsplit : harmh 1 (p - k - 1) / ((p - k : ℕ) : ℚ) ^ 3 + (harmh 1 (k - 1) + ((k : ℚ))⁻¹) / (k : ℚ) ^ 3 =
        (harmh 1 (p - k - 1) - (harmh 1 (k - 1) + ((k : ℚ))⁻¹)) * (((p - k : ℕ) : ℚ) ^ 3)⁻¹ +
        (harmh 1 (k - 1) + ((k : ℚ))⁻¹) * ((((p - k : ℕ) : ℚ) ^ 3)⁻¹ + ((k : ℚ) ^ 3)⁻¹) := by
      simp only [div_eq_mul_inv]; ring
    rw [hsplit]
    have hpk3 : PVal p 0 ((((p - k : ℕ) : ℚ) ^ 3)⁻¹) := by
      simpa only [Nat.cast_pow] using PVal.inv_nat (fun h => hndpk (hp.dvd_of_dvd_pow h))
    have hhk : PVal p 0 (harmh 1 (k - 1) + ((k : ℚ))⁻¹) :=
      (harmh_pval_zero p 1 (k - 1) hp (by omega)).add hp (PVal.inv_nat hndk)
    exact (hnum_diff.mul_zero hp hpk3).add hp (hhk.zero_mul hp hden_sum)
  have h2S : PVal p 1 ((2 : ℕ) * S13 p) := by simpa using hsum.sub hp (harmH_four_mod_p p hp hp7)
  exact PVal.div_of_mul_nat hp (not_dvd_of_lt_prime hp (by decide) (by omega)) h2S

/-- Exact identity: sum_{k=1}^n (-1)^(k-1)/k * C(n, k) = h_1(n). -/
private lemma sum_alt_inv_choose (n : ℕ) :
    ∑ k ∈ Ico 1 (n + 1), (-1 : ℚ) ^ (k - 1) / (k : ℚ) * (Nat.choose n k : ℚ) = harmh 1 n := by
  induction n with
  | zero => simp [harmh]
  | succ n ih =>
    have hstep : harmh 1 (n + 1) = harmh 1 n + ((n + 1 : ℕ) : ℚ)⁻¹ := by
      simp only [harmh, pow_one]; exact Finset.sum_Ico_succ_top (by omega) _
    rw [hstep, ← ih]
    have hpas : ∑ k ∈ Ico 1 (n + 2), (-1 : ℚ) ^ (k - 1) / (k : ℚ) * (Nat.choose (n + 1) k : ℚ) =
        (∑ k ∈ Ico 1 (n + 1), (-1 : ℚ) ^ (k - 1) / (k : ℚ) * (Nat.choose n k : ℚ)) +
        ∑ k ∈ Ico 1 (n + 2), (-1 : ℚ) ^ (k - 1) / (k : ℚ) * (Nat.choose n (k - 1) : ℚ) := by
      have h0 : ∑ k ∈ Ico 1 (n + 1), (-1 : ℚ) ^ (k - 1) / (k : ℚ) * (Nat.choose n k : ℚ) =
          ∑ k ∈ Ico 1 (n + 2), (-1 : ℚ) ^ (k - 1) / (k : ℚ) * (Nat.choose n k : ℚ) := by
        rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1) _, Nat.choose_eq_zero_of_lt (by omega : n < n + 1)]; simp
      rw [h0, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [mem_Ico] at hk
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      rw [Nat.choose_succ_succ n k', Nat.cast_add]; simp only [Nat.succ_sub_one]; ring
    rw [hpas]
    congr 1
    have hinc : ∑ k ∈ Ico 1 (n + 2), (-1 : ℚ) ^ (k - 1) / (k : ℚ) * (Nat.choose n (k - 1) : ℚ) =
        ((n + 1 : ℕ) : ℚ)⁻¹ * ∑ k ∈ Ico 1 (n + 2), (-1 : ℚ) ^ (k - 1) * (Nat.choose (n + 1) k : ℚ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [mem_Ico] at hk
      obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hrel : (k' + 1 : ℕ) * Nat.choose (n + 1) (k' + 1) = (n + 1) * Nat.choose n k' := by
        have := Nat.add_one_mul_choose_eq n k'; linarith
      have hq : ((k' + 1 : ℕ) : ℚ) * (Nat.choose (n + 1) (k' + 1) : ℚ) =
          ((n + 1 : ℕ) : ℚ) * (Nat.choose n k' : ℚ) := by exact_mod_cast hrel
      have hk0 : ((k' + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hn0 : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simp only [Nat.succ_sub_one]
      have hdiv : (Nat.choose n k' : ℚ) / ((k' + 1 : ℕ) : ℚ) =
          (Nat.choose (n + 1) (k' + 1) : ℚ) / ((n + 1 : ℕ) : ℚ) := by
        rw [div_eq_div_iff hk0 hn0]; linarith
      calc (-1 : ℚ) ^ k' / ((k'.succ : ℕ) : ℚ) * (Nat.choose n k' : ℚ)
          = (-1 : ℚ) ^ k' * ((Nat.choose n k' : ℚ) / ((k' + 1 : ℕ) : ℚ)) := by ring
        _ = (-1 : ℚ) ^ k' * ((Nat.choose (n + 1) (k' + 1) : ℚ) / ((n + 1 : ℕ) : ℚ)) := by rw [hdiv]
        _ = _ := by rw [div_eq_mul_inv]; ring
    have halt : ∑ k ∈ Ico 1 (n + 2), (-1 : ℚ) ^ (k - 1) * (Nat.choose (n + 1) k : ℚ) = 1 := by
      have hbin : ∑ k ∈ range (n + 2), (-1 : ℚ) ^ k * (Nat.choose (n + 1) k : ℚ) = 0 := by
        have h := add_pow (-1 : ℚ) (1 : ℚ) (n + 1)
        simp only [neg_add_cancel, zero_pow (by omega : n + 1 ≠ 0), one_pow, mul_one] at h
        exact h.symm
      rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < n + 2)] at hbin
      simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] at hbin
      have hneg : ∑ k ∈ Ico 1 (n + 2), (-1 : ℚ) ^ k * (Nat.choose (n + 1) k : ℚ) =
          -(∑ k ∈ Ico 1 (n + 2), (-1 : ℚ) ^ (k - 1) * (Nat.choose (n + 1) k : ℚ)) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [mem_Ico] at hk
        obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        simp only [Nat.succ_sub_one, pow_succ]; ring
      linarith
    rw [hinc, halt, mul_one]

/-- Exact product formula for C(a * p, p) for a >= 1, prime p. -/
private lemma choose_mul_p_exact (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a) :
    (Nat.choose (a * p) p : ℚ) =
      (a : ℚ) * ∏ s ∈ Ico 1 p, (1 + ((a - 1 : ℕ) : ℚ) * (p : ℚ) / (s : ℚ)) := by
  have hdesc : (Nat.choose (a * p) p : ℚ) * (p.factorial : ℚ) =
      ∏ j ∈ range p, ((a * p - j : ℕ) : ℚ) := by
    have h1 := Nat.descFactorial_eq_factorial_mul_choose (a * p) p
    rw [Nat.descFactorial_eq_prod_range] at h1
    have hq : (∏ i ∈ range p, ((a * p - i : ℕ) : ℚ)) = (p.factorial : ℚ) * (Nat.choose (a * p) p : ℚ) := by
      exact_mod_cast h1
    linarith
  have hfac : (p.factorial : ℚ) = (p : ℚ) * ∏ s ∈ Ico 1 p, (s : ℚ) := by
    have h1 : p.factorial = p * (p - 1).factorial := by
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
      rw [hm, Nat.factorial_succ, Nat.succ_sub_one]
    have h2 : (p - 1).factorial = ∏ s ∈ Ico 1 p, s := by
      clear hdesc h1
      suffices ∀ m, m.factorial = ∏ s ∈ Ico 1 (m + 1), s by
        simpa [Nat.sub_add_cancel hp.pos] using this (p - 1)
      intro m; induction m with
      | zero => simp
      | succ m ih => rw [Finset.prod_Ico_succ_top (by omega), Nat.factorial_succ, ih, mul_comm]
    rw [h1, h2]; push_cast; rfl
  have hnum : ∏ j ∈ range p, ((a * p - j : ℕ) : ℚ) =
      ((a * p : ℕ) : ℚ) * ∏ s ∈ Ico 1 p, (((a - 1) * p + s : ℕ) : ℚ) := by
    rw [Finset.prod_range_eq_mul_Ico _ hp.pos, Nat.sub_zero]
    congr 1
    refine Finset.prod_bij (fun j _ => p - j) ?_ ?_ ?_ ?_
    · intro j hj; rw [mem_Ico] at hj ⊢; omega
    · intro x hx y hy hxy; rw [mem_Ico] at hx hy; omega
    · intro s hs; rw [mem_Ico] at hs; exact ⟨p - s, by rw [mem_Ico]; omega, by omega⟩
    · intro j hj; rw [mem_Ico] at hj
      congr 1; zify [show j ≤ a * p by nlinarith, show j ≤ p by omega, ha]; ring
  have hfac0 : (p.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)
  apply mul_right_cancel₀ hfac0
  rw [hdesc, hnum, hfac]
  calc ((a * p : ℕ) : ℚ) * ∏ s ∈ Ico 1 p, (((a - 1) * p + s : ℕ) : ℚ)
      = (a : ℚ) * ((p : ℚ) * ∏ s ∈ Ico 1 p, ((s : ℚ) * (1 + ((a - 1 : ℕ) : ℚ) * (p : ℚ) / (s : ℚ)))) := by
        rw [Nat.cast_mul]; ring_nf; congr 1
        refine Finset.prod_congr rfl fun s hs => ?_
        rw [mem_Ico] at hs
        have hs0 : (s : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        push_cast; field_simp [hs0]
    _ = _ := by rw [Finset.prod_mul_distrib]; ring

/-- Exact product formula for C(p, k) for 1 <= k < p. -/
private lemma choose_p_exact_prod (p k : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hk1 : 1 ≤ k) (hkp : k < p) :
    (Nat.choose p k : ℚ) =
      (-1 : ℚ) ^ (k - 1) * ((p : ℚ) / (k : ℚ)) * ∏ j ∈ Ico 1 k, (1 - (p : ℚ) / (j : ℚ)) := by
  have h := choose_ndiv_exact p 1 0 k hp hpodd (by decide) hk1 hkp
  have hfilt : (Ico 1 k).filter (fun i => ¬ p ∣ i) = Ico 1 k :=
    Finset.filter_true_of_mem fun i hi => by
      rw [mem_Ico] at hi; exact not_dvd_of_lt_prime hp hi.1 (by omega)
  simpa [hfilt] using h

/-- E3(3): S_{1,1,2} in p * Z_(p) and p^3 * S_{1,2} == -3 * p * H_1 (mod p^5). -/
private lemma S112_and_S12_system (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 1 (S112 p) ∧ PVal p 5 ((p : ℚ) ^ 3 * S12 p + 3 * (p : ℚ) * harmH p 1) := by
  have hnd2 : ¬ p ∣ 2 := not_dvd_of_lt_prime hp (by decide) (by omega)
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  -- Equation 1: 6*p*H_1 + 2*p^3*S_{1,2} - p^4*S_{1,1,2} in p^5 Z_(p)
  have heq1 : PVal p 5 (6 * (p : ℚ) * harmH p 1 + 2 * (p : ℚ) ^ 3 * S12 p - (p : ℚ) ^ 4 * S112 p) := by
    have hsum1 : ∑ k ∈ Ico 1 p, (-1 : ℚ) ^ (k - 1) / (k : ℚ) * (Nat.choose p k : ℚ) = harmH p 1 := by
      have h := sum_alt_inv_choose p
      rw [Finset.sum_Ico_succ_top hp.pos] at h
      have hh : harmh 1 p = harmH p 1 + ((p : ℚ))⁻¹ := by
        simp only [harmh, harmH, pow_one]; exact Finset.sum_Ico_succ_top hp.pos _
      have hev : Even (p - 1) := by obtain ⟨t, ht⟩ := hp_odd; exact ⟨t, by omega⟩
      rw [hh, hev.neg_one_pow, Nat.choose_self, Nat.cast_one, mul_one, one_div] at h
      linarith
    have hterm : PVal p 5 ((p : ℚ) * harmH p 1 -
        ((p : ℚ) ^ 2 * harmH p 2 - (p : ℚ) ^ 3 * S12 p +
          (p : ℚ) ^ 4 * S112 p / 2 - (p : ℚ) ^ 4 * S22 p / 2)) := by
      have hrew : (p : ℚ) * harmH p 1 -
          ((p : ℚ) ^ 2 * harmH p 2 - (p : ℚ) ^ 3 * S12 p +
            (p : ℚ) ^ 4 * S112 p / 2 - (p : ℚ) ^ 4 * S22 p / 2) =
          ∑ k ∈ Ico 1 p, ((p : ℚ) ^ 2 / (k : ℚ) ^ 2) *
            ((∏ j ∈ Ico 1 k, (1 + (-(p : ℚ) / (j : ℚ)) + 0)) -
              (1 + (∑ j ∈ Ico 1 k, (-(p : ℚ) / (j : ℚ))) + (∑ j ∈ Ico 1 k, (0 : ℚ)) +
                (((∑ j ∈ Ico 1 k, (-(p : ℚ) / (j : ℚ))) ^ 2 - ∑ j ∈ Ico 1 k, (-(p : ℚ) / (j : ℚ)) ^ 2) / 2))) := by
        rw [← hsum1, harmH, S12, S112, S22]
        simp only [Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [mem_Ico] at hk
        have hch := choose_p_exact_prod p k hp (by omega) hk.1 hk.2
        have hneg : (-1 : ℚ) ^ (k - 1) * (-1 : ℚ) ^ (k - 1) = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]; norm_num
        have hprod_eq : ∏ j ∈ Ico 1 k, (1 - (p : ℚ) / (j : ℚ)) =
            ∏ j ∈ Ico 1 k, (1 + (-(p : ℚ) / (j : ℚ)) + 0) :=
          Finset.prod_congr rfl fun j _ => by ring
        have hS1_eq : ∑ j ∈ Ico 1 k, (-(p : ℚ) / (j : ℚ)) = -(p : ℚ) * harmh 1 (k - 1) := by
          simp only [harmh, show k - 1 + 1 = k by omega, pow_one, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [div_eq_mul_inv]
        have hS2_eq : ∑ j ∈ Ico 1 k, (-(p : ℚ) / (j : ℚ)) ^ 2 = (p : ℚ) ^ 2 * harmh 2 (k - 1) := by
          simp only [harmh, show k - 1 + 1 = k by omega, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [div_pow, neg_sq, div_eq_mul_inv]
        rw [hch, hprod_eq, hS1_eq, hS2_eq, Finset.sum_const_zero]
        have hlhs : (p : ℚ) * ((-1 : ℚ) ^ (k - 1) / (k : ℚ) *
            ((-1 : ℚ) ^ (k - 1) * ((p : ℚ) / (k : ℚ)) * ∏ j ∈ Ico 1 k, (1 + (-(p : ℚ) / (j : ℚ)) + 0))) =
            ((p : ℚ) ^ 2 / (k : ℚ) ^ 2) * ∏ j ∈ Ico 1 k, (1 + (-(p : ℚ) / (j : ℚ)) + 0) := by
          calc _ = ((-1 : ℚ) ^ (k - 1) * (-1 : ℚ) ^ (k - 1)) *
                (((p : ℚ) ^ 2 / (k : ℚ) ^ 2) * ∏ j ∈ Ico 1 k, (1 + (-(p : ℚ) / (j : ℚ)) + 0)) := by ring
            _ = _ := by rw [hneg, one_mul]
        rw [hlhs]; simp only [div_eq_mul_inv]; ring
      rw [hrew]
      refine PVal.sum hp fun k hk => ?_
      rw [mem_Ico] at hk
      have hbase : PVal p 2 ((p : ℚ) ^ 2 / (k : ℚ) ^ 2) := by
        simpa only [Nat.cast_pow] using (PVal.of_pow_p (e := 2) hp).div_nat hp
          (fun h => not_dvd_of_lt_prime hp hk.1 hk.2 (hp.dvd_of_dvd_pow h))
      have hdeg : PVal p 3 ((∏ j ∈ Ico 1 k, (1 + (-(p : ℚ) / (j : ℚ)) + 0)) -
          (1 + (∑ j ∈ Ico 1 k, (-(p : ℚ) / (j : ℚ))) + (∑ j ∈ Ico 1 k, (0 : ℚ)) +
            (((∑ j ∈ Ico 1 k, (-(p : ℚ) / (j : ℚ))) ^ 2 - ∑ j ∈ Ico 1 k, (-(p : ℚ) / (j : ℚ)) ^ 2) / 2))) :=
        PVal.prod_one_add_deg2 hp hnd2
          (fun j hj => by rw [mem_Ico] at hj; exact (PVal.neg_of_p hp).div_nat hp (not_dvd_of_lt_prime hp hj.1 (by omega)))
          (fun _ _ => PVal.zero hp)
      exact hbase.mul hp hdeg
    have hS22 : PVal p 5 ((p : ℚ) ^ 4 * S22 p / 2) := by
      simpa only [Nat.cast_ofNat] using ((PVal.of_pow_p (e := 4) hp).mul hp (S22_mod_p p hp hp7)).div_nat hp hnd2
    have hcomb := (PVal.nat hp 2).zero_mul hp ((hterm.add hp (p2_harmH2_mod_p5 p hp hp7)).sub hp hS22)
    convert hcomb using 1; ring
  -- Equation 2: 6*p*H_1 + 2*p^3*S_{1,2} - 2*p^4*S_{1,1,2} in p^5 Z_(p)
  have heq2 : PVal p 5 (6 * (p : ℚ) * harmH p 1 + 2 * (p : ℚ) ^ 3 * S12 p - 2 * (p : ℚ) ^ 4 * S112 p) := by
    have hvand : ∑ k ∈ Ico 1 p, (Nat.choose p k : ℚ) ^ 2 = (Nat.choose (2 * p) p : ℚ) - 2 := by
      have h1 : ∑ k ∈ range (p + 1), Nat.choose p k ^ 2 = Nat.choose (2 * p) p := by
        have h := Nat.add_choose_eq p p p
        rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => p.choose i * p.choose j) p, ← two_mul] at h
        rw [h]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [mem_range] at hk; rw [Nat.choose_symm (by omega), sq]
      have hq : ∑ k ∈ range (p + 1), (Nat.choose p k : ℚ) ^ 2 = (Nat.choose (2 * p) p : ℚ) := by
        exact_mod_cast h1
      rw [Finset.sum_range_succ, Finset.sum_range_eq_add_Ico _ hp.pos] at hq
      simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_pow] at hq
      linarith
    have h2p : PVal p 5 ((Nat.choose (2 * p) p : ℚ) - 2 - 4 * (p : ℚ) * harmH p 1) := by
      have hex := choose_mul_p_exact p 2 hp (by decide)
      have hE2 := prod_one_add_ap_mod_p5 p 1 hp hp7
      have hrew : (Nat.choose (2 * p) p : ℚ) - 2 - 4 * (p : ℚ) * harmH p 1 =
          2 * ((∏ s ∈ Ico 1 p, (1 + ((1 : ℤ) : ℚ) * (p : ℚ) / (s : ℚ))) - 1 -
            (((1 : ℤ) : ℚ) + ((1 : ℤ) : ℚ) ^ 2) * (p : ℚ) * harmH p 1) := by
        rw [hex]; norm_num; ring
      rw [hrew]; exact (PVal.nat hp 2).zero_mul hp hE2
    have hterm : PVal p 5 ((∑ k ∈ Ico 1 p, (Nat.choose p k : ℚ) ^ 2) -
        ((p : ℚ) ^ 2 * harmH p 2 - 2 * (p : ℚ) ^ 3 * S12 p +
          2 * (p : ℚ) ^ 4 * S112 p - (p : ℚ) ^ 4 * S22 p)) := by
      have hrew : (∑ k ∈ Ico 1 p, (Nat.choose p k : ℚ) ^ 2) -
          ((p : ℚ) ^ 2 * harmH p 2 - 2 * (p : ℚ) ^ 3 * S12 p +
            2 * (p : ℚ) ^ 4 * S112 p - (p : ℚ) ^ 4 * S22 p) =
          ∑ k ∈ Ico 1 p, ((p : ℚ) ^ 2 / (k : ℚ) ^ 2) *
            ((∏ j ∈ Ico 1 k, (1 + (-2 * (p : ℚ) / (j : ℚ)) + ((p : ℚ) ^ 2 / (j : ℚ) ^ 2))) -
              (1 + (∑ j ∈ Ico 1 k, (-2 * (p : ℚ) / (j : ℚ))) +
                (∑ j ∈ Ico 1 k, ((p : ℚ) ^ 2 / (j : ℚ) ^ 2)) +
                (((∑ j ∈ Ico 1 k, (-2 * (p : ℚ) / (j : ℚ))) ^ 2 -
                  ∑ j ∈ Ico 1 k, (-2 * (p : ℚ) / (j : ℚ)) ^ 2) / 2))) := by
        simp only [harmH, S12, S112, S22, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [mem_Ico] at hk
        have hch := choose_p_exact_prod p k hp (by omega) hk.1 hk.2
        have hneg : ((-1 : ℚ) ^ (k - 1)) ^ 2 = 1 := by
          rw [← pow_mul, mul_comm (k - 1) 2, pow_mul]; norm_num
        have hsq : (Nat.choose p k : ℚ) ^ 2 = ((p : ℚ) ^ 2 / (k : ℚ) ^ 2) *
            ∏ j ∈ Ico 1 k, (1 + (-2 * (p : ℚ) / (j : ℚ)) + ((p : ℚ) ^ 2 / (j : ℚ) ^ 2)) := by
          rw [hch, mul_pow, mul_pow, hneg, one_mul, div_pow, ← Finset.prod_pow]
          congr 1; refine Finset.prod_congr rfl fun j _ => by ring
        have hS1_eq : ∑ j ∈ Ico 1 k, (-2 * (p : ℚ) / (j : ℚ)) = -2 * (p : ℚ) * harmh 1 (k - 1) := by
          simp only [harmh, show k - 1 + 1 = k by omega, pow_one, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [div_eq_mul_inv]
        have hS2_eq : ∑ j ∈ Ico 1 k, (-2 * (p : ℚ) / (j : ℚ)) ^ 2 = 4 * (p : ℚ) ^ 2 * harmh 2 (k - 1) := by
          simp only [harmh, show k - 1 + 1 = k by omega, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [div_pow, div_eq_mul_inv]; ring
        have hG1_eq : ∑ j ∈ Ico 1 k, ((p : ℚ) ^ 2 / (j : ℚ) ^ 2) = (p : ℚ) ^ 2 * harmh 2 (k - 1) := by
          simp only [harmh, show k - 1 + 1 = k by omega, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [div_eq_mul_inv]
        rw [hsq, hS1_eq, hS2_eq, hG1_eq]; simp only [div_eq_mul_inv]; ring
      rw [hrew]
      refine PVal.sum hp fun k hk => ?_
      rw [mem_Ico] at hk
      have hbase : PVal p 2 ((p : ℚ) ^ 2 / (k : ℚ) ^ 2) := by
        simpa only [Nat.cast_pow] using (PVal.of_pow_p (e := 2) hp).div_nat hp
          (fun h => not_dvd_of_lt_prime hp hk.1 hk.2 (hp.dvd_of_dvd_pow h))
      have hdeg : PVal p 3 ((∏ j ∈ Ico 1 k, (1 + (-2 * (p : ℚ) / (j : ℚ)) + ((p : ℚ) ^ 2 / (j : ℚ) ^ 2))) -
          (1 + (∑ j ∈ Ico 1 k, (-2 * (p : ℚ) / (j : ℚ))) +
            (∑ j ∈ Ico 1 k, ((p : ℚ) ^ 2 / (j : ℚ) ^ 2)) +
            (((∑ j ∈ Ico 1 k, (-2 * (p : ℚ) / (j : ℚ))) ^ 2 -
              ∑ j ∈ Ico 1 k, (-2 * (p : ℚ) / (j : ℚ)) ^ 2) / 2))) :=
        PVal.prod_one_add_deg2 hp hnd2
          (fun j hj => by
            rw [mem_Ico] at hj
            have h1 : PVal p 1 (-2 * (p : ℚ)) := by
              simpa using (PVal.int hp (-2)).zero_mul hp (PVal.of_p hp)
            exact h1.div_nat hp (not_dvd_of_lt_prime hp hj.1 (by omega)))
          (fun j hj => by
            rw [mem_Ico] at hj
            simpa only [Nat.cast_pow] using (PVal.of_pow_p (e := 2) hp).div_nat hp
              (fun h => not_dvd_of_lt_prime hp hj.1 (by omega) (hp.dvd_of_dvd_pow h)))
      exact hbase.mul hp hdeg
    rw [hvand] at hterm
    have hS22 : PVal p 5 ((p : ℚ) ^ 4 * S22 p) := (PVal.of_pow_p (e := 4) hp).mul hp (S22_mod_p p hp hp7)
    have hcomb := ((hterm.sub hp h2p).add hp (p2_harmH2_mod_p5 p hp hp7)).sub hp hS22
    convert hcomb using 1; ring
  have hY : PVal p 5 ((p : ℚ) ^ 4 * S112 p) := by
    have h := heq1.sub hp heq2; convert h using 1; ring
  have hS112 : PVal p 1 (S112 p) := by
    have h1 := hY.div_pow_p (e := 1) (m := 4) hp
    have hp0 : (p : ℚ) ^ 4 ≠ 0 := pow_ne_zero 4 (Nat.cast_ne_zero.mpr hp.ne_zero)
    rwa [mul_div_cancel_left₀ _ hp0] at h1
  have h2X : PVal p 5 ((2 : ℕ) * ((p : ℚ) ^ 3 * S12 p + 3 * (p : ℚ) * harmH p 1)) := by
    have h := heq1.add hp hY; convert h using 1; push_cast; ring
  exact ⟨hS112, PVal.div_of_mul_nat hp hnd2 h2X⟩

private lemma sum_range_succ_split (p : ℕ) (hp : 1 ≤ p) (f : ℕ → ℚ) :
    ∑ k ∈ range (p + 1), f k = f 0 + f p + ∑ k ∈ Ico 1 p, f k := by
  rw [Finset.sum_range_succ, Finset.sum_range_eq_add_Ico _ hp]; ring

/-- Exact identity: C(4*p - k, p - k) = (prod_{s=1}^{p-1} (1 + 3*p/s)) * prod_{j=1}^{k-1} ((1 - p/j)/(1 - 4*p/j)). -/
private lemma choose_4p_sub_exact (p k : ℕ) (hp : p.Prime) (hk1 : 1 ≤ k) (hkp : k < p) :
    (Nat.choose (4 * p - k) (p - k) : ℚ) =
      (∏ s ∈ Ico 1 p, (1 + 3 * (p : ℚ) / (s : ℚ))) *
        ∏ j ∈ Ico 1 k, ((1 - (p : ℚ) / (j : ℚ)) / (1 - 4 * (p : ℚ) / (j : ℚ))) := by
  induction k, hk1 using Nat.le_induction with
  | base =>
    simp only [Ico_self, prod_empty, mul_one]
    have hrel : 4 * p * Nat.choose (4 * p - 1) (p - 1) = p * Nat.choose (4 * p) p := by
      have h := Nat.add_one_mul_choose_eq (4 * p - 1) (p - 1)
      rw [show 4 * p - 1 + 1 = 4 * p by omega, show p - 1 + 1 = p by omega] at h; linarith
    have hq : (4 * (p : ℚ)) * (Nat.choose (4 * p - 1) (p - 1) : ℚ) = (p : ℚ) * (Nat.choose (4 * p) p : ℚ) := by
      exact_mod_cast hrel
    have h4p := choose_mul_p_exact p 4 hp (by decide)
    have h4p0 : (4 * (p : ℚ)) ≠ 0 := mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hp.ne_zero)
    apply mul_left_cancel₀ h4p0
    rw [hq, h4p]; norm_num; ring
  | succ k hk1 ih =>
    have hk_lt : k < p := by omega
    rw [Finset.prod_Ico_succ_top hk1, ← mul_assoc, ← ih hk_lt]
    have hrel : (4 * p - k) * Nat.choose (4 * p - (k + 1)) (p - (k + 1)) =
        (p - k) * Nat.choose (4 * p - k) (p - k) := by
      have h := Nat.add_one_mul_choose_eq (4 * p - (k + 1)) (p - (k + 1))
      rw [show 4 * p - (k + 1) + 1 = 4 * p - k by omega,
        show p - (k + 1) + 1 = p - k by omega] at h; linarith
    have hq : ((4 * p - k : ℕ) : ℚ) * (Nat.choose (4 * p - (k + 1)) (p - (k + 1)) : ℚ) =
        ((p - k : ℕ) : ℚ) * (Nat.choose (4 * p - k) (p - k) : ℚ) := by exact_mod_cast hrel
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h4pk0 : ((4 * p - k : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hden0 : 1 - 4 * (p : ℚ) / (k : ℚ) ≠ 0 := by
      intro h0
      have : (k : ℚ) = 4 * (p : ℚ) := by field_simp [hk0] at h0; linarith
      have : k = 4 * p := by exact_mod_cast this
      omega
    have hrat : ((p - k : ℕ) : ℚ) / ((4 * p - k : ℕ) : ℚ) =
        (1 - (p : ℚ) / (k : ℚ)) / (1 - 4 * (p : ℚ) / (k : ℚ)) := by
      have h4pk0' : (4 * (p : ℚ) - (k : ℚ)) ≠ 0 := by
        rwa [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat] at h4pk0
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat,
        div_eq_div_iff h4pk0' hden0]
      field_simp [hk0]; ring
    apply mul_left_cancel₀ h4pk0
    rw [hq, ← hrat]; field_simp [h4pk0]

/-- E4: a(p) - 7 == 33 * p * H_1 (mod p^5) for prime p >= 7. -/
private lemma a_p_mod_p5 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 5 ((OMA.S_oeis_a364114.a p : ℚ) - 7 - 33 * (p : ℚ) * harmH p 1) := by
  have hnd2 : ¬ p ∣ 2 := not_dvd_of_lt_prime hp (by decide) (by omega)
  have ⟨hS112, hS12⟩ := S112_and_S12_system p hp hp7
  have hS22 := S22_mod_p p hp hp7
  set F : ℕ → ℕ → ℕ → ℚ := fun k₁ k₂ k₃ =>
    if k₁ + k₂ + k₃ ≤ p then
      (Nat.choose (4 * p - (k₁ + k₂ + k₃)) (p - (k₁ + k₂ + k₃)) : ℚ) *
        (Nat.choose p k₁ : ℚ) ^ 2 * (Nat.choose p k₂ : ℚ) ^ 2 * (Nat.choose p k₃ : ℚ) ^ 2
    else 0
  have ha_eq : (OMA.S_oeis_a364114.a p : ℚ) =
      ∑ k₁ ∈ range (p + 1), ∑ k₂ ∈ range (p + 1), ∑ k₃ ∈ range (p + 1), F k₁ k₂ k₃ := by
    have hQ := congrArg (Int.cast : ℤ → ℚ) (a_eq_Q_rep p)
    simpa only [F, Int.cast_natCast, Int.cast_sum, Int.cast_ite, Int.cast_mul, Int.cast_pow,
      Int.cast_zero] using hQ
  have hsym12 : ∀ a b c, F a b c = F b a c := fun a b c => by
    simp only [F, show a + b + c = b + a + c by omega]; split_ifs <;> ring
  have hsym13 : ∀ a b c, F a b c = F c b a := fun a b c => by
    simp only [F, show a + b + c = c + b + a by omega]; split_ifs <;> ring
  -- Expand 3-fold sum using sum_range_succ_split
  have hsplit : (OMA.S_oeis_a364114.a p : ℚ) =
      ((Nat.choose (4 * p) p : ℚ) + 3) +
      3 * (∑ k ∈ Ico 1 p, (Nat.choose (4 * p - k) (p - k) : ℚ) * (Nat.choose p k : ℚ) ^ 2) +
      3 * (∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p, F k₁ k₂ 0) +
      (∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p, ∑ k₃ ∈ Ico 1 p, F k₁ k₂ k₃) := by
    rw [ha_eq, sum_range_succ_split p hp.pos]
    simp_rw [sum_range_succ_split p hp.pos, Finset.sum_add_distrib]
    have h000 : F 0 0 0 = (Nat.choose (4 * p) p : ℚ) := by simp [F]
    have hp00 : F p 0 0 = 1 := by simp [F]
    have h0p0 : F 0 p 0 = 1 := by simp [F]
    have h00p : F 0 0 p = 1 := by simp [F]
    have hpp0 : F p p 0 = 0 := by simp [F]; omega
    have hp0p : F p 0 p = 0 := by simp [F]; omega
    have h0pp : F 0 p p = 0 := by simp [F]; omega
    have hppp : F p p p = 0 := by simp [F]; omega
    have hz1 : ∀ k ∈ Ico 1 p, F p 0 k = 0 ∧ F 0 p k = 0 ∧ F p p k = 0 ∧
        F p k 0 = 0 ∧ F p k p = 0 ∧ F 0 k p = 0 ∧ F k p 0 = 0 ∧ F k 0 p = 0 ∧ F k p p = 0 := by
      intro k hk; rw [mem_Ico] at hk; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (simp [F]; omega)
    have hz2 : ∀ k₁ ∈ Ico 1 p, ∀ k₂ ∈ Ico 1 p, F p k₁ k₂ = 0 ∧ F k₁ p k₂ = 0 ∧ F k₁ k₂ p = 0 := by
      intro k₁ hk1 k₂ hk2; rw [mem_Ico] at hk1 hk2; refine ⟨?_, ?_, ?_⟩ <;> (simp [F]; omega)
    have hs_zero1 : ∀ g : ℕ → ℚ, (∀ k ∈ Ico 1 p, g k = 0) → ∑ k ∈ Ico 1 p, g k = 0 :=
      fun _ h => Finset.sum_eq_zero h
    have hs_zero2 : ∀ g : ℕ → ℕ → ℚ, (∀ k₁ ∈ Ico 1 p, ∀ k₂ ∈ Ico 1 p, g k₁ k₂ = 0) →
        ∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p, g k₁ k₂ = 0 :=
      fun _ h => Finset.sum_eq_zero fun k₁ hk1 => Finset.sum_eq_zero fun k₂ hk2 => h k₁ hk1 k₂ hk2
    have h1a : ∑ k ∈ Ico 1 p, F 0 0 k = ∑ k ∈ Ico 1 p, (Nat.choose (4 * p - k) (p - k) : ℚ) * (Nat.choose p k : ℚ) ^ 2 :=
      Finset.sum_congr rfl fun k hk => by rw [mem_Ico] at hk; simp [F, show k ≤ p by omega]
    have h1b : ∑ k ∈ Ico 1 p, F 0 k 0 = ∑ k ∈ Ico 1 p, F 0 0 k :=
      Finset.sum_congr rfl fun k _ => by rw [hsym12, hsym13, hsym12]
    have h1c : ∑ k ∈ Ico 1 p, F k 0 0 = ∑ k ∈ Ico 1 p, F 0 0 k :=
      Finset.sum_congr rfl fun k _ => hsym13 k 0 0
    have h2a : ∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p, F 0 k₁ k₂ = ∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p, F k₁ k₂ 0 := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k₂ _ => Finset.sum_congr rfl fun k₁ _ => by rw [hsym13, hsym12]
    have h2b : ∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p, F k₁ 0 k₂ = ∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p, F k₁ k₂ 0 :=
      Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ => by rw [hsym12, hsym13, hsym12]
    rw [h000, hp00, h0p0, h00p, hpp0, hp0p, h0pp, hppp,
      hs_zero1 (fun k => F p 0 k) (fun k hk => (hz1 k hk).1),
      hs_zero1 (fun k => F 0 p k) (fun k hk => (hz1 k hk).2.1),
      hs_zero1 (fun k => F p p k) (fun k hk => (hz1 k hk).2.2.1),
      hs_zero1 (fun k => F p k 0) (fun k hk => (hz1 k hk).2.2.2.1),
      hs_zero1 (fun k => F p k p) (fun k hk => (hz1 k hk).2.2.2.2.1),
      hs_zero1 (fun k => F 0 k p) (fun k hk => (hz1 k hk).2.2.2.2.2.1),
      hs_zero1 (fun k => F k p 0) (fun k hk => (hz1 k hk).2.2.2.2.2.2.1),
      hs_zero1 (fun k => F k 0 p) (fun k hk => (hz1 k hk).2.2.2.2.2.2.2.1),
      hs_zero1 (fun k => F k p p) (fun k hk => (hz1 k hk).2.2.2.2.2.2.2.2),
      hs_zero2 (fun k₁ k₂ => F p k₁ k₂) (fun k₁ hk1 k₂ hk2 => (hz2 k₁ hk1 k₂ hk2).1),
      hs_zero2 (fun k₁ k₂ => F k₁ p k₂) (fun k₁ hk1 k₂ hk2 => (hz2 k₁ hk1 k₂ hk2).2.1),
      hs_zero2 (fun k₁ k₂ => F k₁ k₂ p) (fun k₁ hk1 k₂ hk2 => (hz2 k₁ hk1 k₂ hk2).2.2),
      h1b, h1c, h1a, h2a, h2b]
    ring
  -- Bucket u = 0: C(4p, p) + 3 - 7 == 48 * p * H_1 (mod p^5)
  have hq0 : PVal p 5 (((Nat.choose (4 * p) p : ℚ) + 3) - 7 - 48 * (p : ℚ) * harmH p 1) := by
    have h4p := choose_mul_p_exact p 4 hp (by decide)
    have hE2 := prod_one_add_ap_mod_p5 p 3 hp hp7
    have hrew : ((Nat.choose (4 * p) p : ℚ) + 3) - 7 - 48 * (p : ℚ) * harmH p 1 =
        4 * ((∏ s ∈ Ico 1 p, (1 + ((3 : ℤ) : ℚ) * (p : ℚ) / (s : ℚ))) - 1 -
          (((3 : ℤ) : ℚ) + ((3 : ℤ) : ℚ) ^ 2) * (p : ℚ) * harmH p 1) := by
      rw [h4p]; norm_num; ring
    rw [hrew]; exact (PVal.nat hp 4).zero_mul hp hE2
  -- Bucket u = 1: 3 * sum C(4p-k, p-k) * C(p, k)^2 == -15 * p * H_1 (mod p^5)
  have hq1 : PVal p 5 (3 * (∑ k ∈ Ico 1 p, (Nat.choose (4 * p - k) (p - k) : ℚ) * (Nat.choose p k : ℚ) ^ 2) +
      15 * (p : ℚ) * harmH p 1) := by
    have hP3_mod3 : PVal p 3 ((∏ s ∈ Ico 1 p, (1 + 3 * (p : ℚ) / (s : ℚ))) - 1) := by
      have hE2 := (prod_one_add_ap_mod_p5 p 3 hp hp7).mono (by decide : 3 ≤ 5)
      have hH1 := (PVal.nat hp 12).zero_mul hp ((PVal.of_pow_p (e := 1) hp).mul hp (harmH1_mod_p2 p hp hp7))
      have hsum := hE2.add hp hH1
      convert hsum using 1; norm_num; ring
    have hterm : PVal p 5 ((∑ k ∈ Ico 1 p, (Nat.choose (4 * p - k) (p - k) : ℚ) * (Nat.choose p k : ℚ) ^ 2) -
        ((p : ℚ) ^ 2 * harmH p 2 + (p : ℚ) ^ 3 * S12 p +
          (p : ℚ) ^ 4 * S112 p / 2 + 13 * (p : ℚ) ^ 4 * S22 p / 2)) := by
      have hrew : (∑ k ∈ Ico 1 p, (Nat.choose (4 * p - k) (p - k) : ℚ) * (Nat.choose p k : ℚ) ^ 2) -
          ((p : ℚ) ^ 2 * harmH p 2 + (p : ℚ) ^ 3 * S12 p +
            (p : ℚ) ^ 4 * S112 p / 2 + 13 * (p : ℚ) ^ 4 * S22 p / 2) =
          ∑ k ∈ Ico 1 p, ((Nat.choose (4 * p - k) (p - k) : ℚ) * (Nat.choose p k : ℚ) ^ 2 -
            ((p : ℚ) ^ 2 / (k : ℚ) ^ 2) *
              (1 + (p : ℚ) * harmh 1 (k - 1) + (p : ℚ) ^ 2 * (harmh 1 (k - 1)) ^ 2 / 2 +
                13 * (p : ℚ) ^ 2 * harmh 2 (k - 1) / 2)) := by
        simp only [harmH, S12, S112, S22, Finset.mul_sum, Finset.sum_div,
          ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => by simp only [div_eq_mul_inv]; ring
      rw [hrew]
      refine PVal.sum hp fun k hk => ?_
      rw [mem_Ico] at hk
      have h4k := choose_4p_sub_exact p k hp hk.1 hk.2
      have hpk := choose_p_exact_prod p k hp (by omega) hk.1 hk.2
      have hneg : ((-1 : ℚ) ^ (k - 1)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm (k - 1) 2, pow_mul]; norm_num
      set P3 := ∏ s ∈ Ico 1 p, (1 + 3 * (p : ℚ) / (s : ℚ))
      set R := ∏ j ∈ Ico 1 k, ((1 - (p : ℚ) / (j : ℚ)) ^ 3 / (1 - 4 * (p : ℚ) / (j : ℚ)))
      set R' := ∏ j ∈ Ico 1 k, (1 + (p : ℚ) / (j : ℚ) + 7 * (p : ℚ) ^ 2 / (j : ℚ) ^ 2)
      have hfac : (Nat.choose (4 * p - k) (p - k) : ℚ) * (Nat.choose p k : ℚ) ^ 2 =
          ((p : ℚ) ^ 2 / (k : ℚ) ^ 2) * (P3 * R) := by
        rw [h4k, hpk, mul_pow, mul_pow, hneg, one_mul, div_pow]
        have hcomb : (∏ j ∈ Ico 1 k, ((1 - (p : ℚ) / (j : ℚ)) / (1 - 4 * (p : ℚ) / (j : ℚ)))) *
            (∏ j ∈ Ico 1 k, (1 - (p : ℚ) / (j : ℚ))) ^ 2 = R := by
          rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun j _ => by ring
        calc P3 * (∏ j ∈ Ico 1 k, ((1 - (p : ℚ) / (j : ℚ)) / (1 - 4 * (p : ℚ) / (j : ℚ)))) *
              ((p : ℚ) ^ 2 / (k : ℚ) ^ 2 * (∏ j ∈ Ico 1 k, (1 - (p : ℚ) / (j : ℚ))) ^ 2)
            = ((p : ℚ) ^ 2 / (k : ℚ) ^ 2) * (P3 * ((∏ j ∈ Ico 1 k, ((1 - (p : ℚ) / (j : ℚ)) / (1 - 4 * (p : ℚ) / (j : ℚ)))) *
              (∏ j ∈ Ico 1 k, (1 - (p : ℚ) / (j : ℚ))) ^ 2)) := by ring
          _ = _ := by rw [hcomb]
      have hRR' : PVal p 3 (R - R') := by
        refine PVal.prod_sub_prod hp ?_ ?_ ?_
        · intro j hj; rw [mem_Ico] at hj
          have hndj := not_dvd_of_lt_prime hp hj.1 (by omega)
          have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have hnd_den : ¬ (p : ℤ) ∣ (j : ℤ) - 4 * (p : ℤ) := fun h =>
            hndj (Int.natCast_dvd_natCast.mp (by have := dvd_add h (dvd_mul_left (p : ℤ) 4); simpa [mul_comm] using this))
          have heq : (1 - (p : ℚ) / (j : ℚ)) ^ 3 / (1 - 4 * (p : ℚ) / (j : ℚ)) =
              ((j : ℚ) * (1 - (p : ℚ) / (j : ℚ)) ^ 3) / (((j : ℤ) - 4 * (p : ℤ) : ℤ) : ℚ) := by
            push_cast; field_simp [hj0]
          rw [heq]
          have hnum : PVal p 0 ((j : ℚ) * (1 - (p : ℚ) / (j : ℚ)) ^ 3) :=
            (PVal.nat hp j).mul_zero hp (by simpa using ((PVal.nat hp 1).sub hp
              ((PVal.nat hp p).div_nat hp hndj)).pow hp 3)
          exact hnum.div_int hp hnd_den
        · intro j hj; rw [mem_Ico] at hj
          have hndj := not_dvd_of_lt_prime hp hj.1 (by omega)
          have h7 : PVal p 0 (7 * (p : ℚ) ^ 2 / (j : ℚ) ^ 2) := by
            simpa only [Nat.cast_pow, Nat.cast_ofNat] using
              ((PVal.nat hp 7).mul_zero hp (by simpa using (PVal.nat hp p).pow hp 2)).div_nat hp
                (fun h => hndj (hp.dvd_of_dvd_pow h))
          exact ((PVal.nat hp 1).add hp ((PVal.nat hp p).div_nat hp hndj)).add hp h7
        · intro j hj; rw [mem_Ico] at hj
          have hndj := not_dvd_of_lt_prime hp hj.1 (by omega)
          have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have hden0 : 1 - 4 * (p : ℚ) / (j : ℚ) ≠ 0 := by
            intro h0
            have : (j : ℚ) = 4 * (p : ℚ) := by field_simp [hj0] at h0; linarith
            have : j = 4 * p := by exact_mod_cast this
            omega
          have hden' : (j : ℚ) - 4 * (p : ℚ) ≠ 0 := by
            intro h0; have : j = 4 * p := by exact_mod_cast (show (j : ℚ) = 4 * (p : ℚ) by linarith)
            omega
          have hnd_den : ¬ (p : ℤ) ∣ (j : ℤ) - 4 * (p : ℤ) := fun h =>
            hndj (Int.natCast_dvd_natCast.mp (by have := dvd_add h (dvd_mul_left (p : ℤ) 4); simpa [mul_comm] using this))
          have heq : (1 - (p : ℚ) / (j : ℚ)) ^ 3 / (1 - 4 * (p : ℚ) / (j : ℚ)) -
              (1 + (p : ℚ) / (j : ℚ) + 7 * (p : ℚ) ^ 2 / (j : ℚ) ^ 2) =
              ((27 * (p : ℚ) ^ 3) / ((j ^ 2 : ℕ) : ℚ)) / (((j : ℤ) - 4 * (p : ℤ) : ℤ) : ℚ) := by
            have hne : (j : ℚ) ^ 2 * ((j : ℚ) - 4 * (p : ℚ)) ≠ 0 := mul_ne_zero (pow_ne_zero 2 hj0) hden'
            have h1 : (1 - (p : ℚ) / (j : ℚ)) ^ 3 / (1 - 4 * (p : ℚ) / (j : ℚ)) =
                ((j : ℚ) - (p : ℚ)) ^ 3 / ((j : ℚ) ^ 2 * ((j : ℚ) - 4 * (p : ℚ))) := by
              rw [div_eq_div_iff hden0 hne]; field_simp [hj0]
            rw [h1]; push_cast
            rw [div_div, sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', ← sub_div, div_eq_iff hne,
              ← mul_assoc, add_mul, add_mul, add_mul, one_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hj0),
              show (p : ℚ) / (j : ℚ) * (j : ℚ) ^ 2 = (p : ℚ) * (j : ℚ) by
                rw [sq, ← mul_assoc, div_mul_cancel₀ _ hj0]]
            ring
          rw [heq]
          exact (((PVal.nat hp 27).zero_mul hp (PVal.of_pow_p (e := 3) hp)).div_nat hp
            (fun h => hndj (hp.dvd_of_dvd_pow h))).div_int hp hnd_den
      have hR'_deg : PVal p 3 ((∏ j ∈ Ico 1 k, (1 + (p : ℚ) / (j : ℚ) + 7 * (p : ℚ) ^ 2 / (j : ℚ) ^ 2)) -
          (1 + (∑ j ∈ Ico 1 k, (p : ℚ) / (j : ℚ)) +
            (∑ j ∈ Ico 1 k, 7 * (p : ℚ) ^ 2 / (j : ℚ) ^ 2) +
            (((∑ j ∈ Ico 1 k, (p : ℚ) / (j : ℚ)) ^ 2 - ∑ j ∈ Ico 1 k, ((p : ℚ) / (j : ℚ)) ^ 2) / 2))) :=
        PVal.prod_one_add_deg2 hp hnd2
          (fun j hj => by rw [mem_Ico] at hj; exact (PVal.of_p hp).div_nat hp (not_dvd_of_lt_prime hp hj.1 (by omega)))
          (fun j hj => by
            rw [mem_Ico] at hj
            have h1 : PVal p 2 (7 * (p : ℚ) ^ 2) := (PVal.nat hp 7).zero_mul hp (PVal.of_pow_p (e := 2) hp)
            simpa only [Nat.cast_pow] using h1.div_nat hp
              (fun h => not_dvd_of_lt_prime hp hj.1 (by omega) (hp.dvd_of_dvd_pow h)))
      have hR'_eq : 1 + (∑ j ∈ Ico 1 k, (p : ℚ) / (j : ℚ)) +
          (∑ j ∈ Ico 1 k, 7 * (p : ℚ) ^ 2 / (j : ℚ) ^ 2) +
          (((∑ j ∈ Ico 1 k, (p : ℚ) / (j : ℚ)) ^ 2 - ∑ j ∈ Ico 1 k, ((p : ℚ) / (j : ℚ)) ^ 2) / 2) =
          1 + (p : ℚ) * harmh 1 (k - 1) + (p : ℚ) ^ 2 * (harmh 1 (k - 1)) ^ 2 / 2 +
            13 * (p : ℚ) ^ 2 * harmh 2 (k - 1) / 2 := by
        have h1 : ∑ j ∈ Ico 1 k, (p : ℚ) / (j : ℚ) = (p : ℚ) * harmh 1 (k - 1) := by
          simp only [harmh, show k - 1 + 1 = k by omega, pow_one, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [div_eq_mul_inv]
        have h2 : ∑ j ∈ Ico 1 k, 7 * (p : ℚ) ^ 2 / (j : ℚ) ^ 2 = 7 * (p : ℚ) ^ 2 * harmh 2 (k - 1) := by
          simp only [harmh, show k - 1 + 1 = k by omega, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [div_eq_mul_inv]
        have h3 : ∑ j ∈ Ico 1 k, ((p : ℚ) / (j : ℚ)) ^ 2 = (p : ℚ) ^ 2 * harmh 2 (k - 1) := by
          simp only [harmh, show k - 1 + 1 = k by omega, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by rw [div_pow, div_eq_mul_inv]
        rw [h1, h2, h3]; ring
      rw [hR'_eq] at hR'_deg
      have hR0 : PVal p 0 R := PVal.prod_zero hp fun j hj => by
        rw [mem_Ico] at hj
        have hndj := not_dvd_of_lt_prime hp hj.1 (by omega)
        have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hnd_den : ¬ (p : ℤ) ∣ (j : ℤ) - 4 * (p : ℤ) := fun h =>
          hndj (Int.natCast_dvd_natCast.mp (by have := dvd_add h (dvd_mul_left (p : ℤ) 4); simpa [mul_comm] using this))
        have heq : (1 - (p : ℚ) / (j : ℚ)) ^ 3 / (1 - 4 * (p : ℚ) / (j : ℚ)) =
            ((j : ℚ) * (1 - (p : ℚ) / (j : ℚ)) ^ 3) / (((j : ℤ) - 4 * (p : ℤ) : ℤ) : ℚ) := by
          push_cast; field_simp [hj0]
        rw [heq]
        exact ((PVal.nat hp j).mul_zero hp (by simpa using ((PVal.nat hp 1).sub hp
          ((PVal.nat hp p).div_nat hp hndj)).pow hp 3)).div_int hp hnd_den
      have hP3R : PVal p 3 (P3 * R - (1 + (p : ℚ) * harmh 1 (k - 1) +
          (p : ℚ) ^ 2 * (harmh 1 (k - 1)) ^ 2 / 2 + 13 * (p : ℚ) ^ 2 * harmh 2 (k - 1) / 2)) := by
        have h1 : PVal p 3 (P3 * R - R) := by
          rw [show P3 * R - R = (P3 - 1) * R by ring]; exact hP3_mod3.mul_zero hp hR0
        exact h1.sub_trans hp (hRR'.sub_trans hp hR'_deg)
      have hbase : PVal p 2 ((p : ℚ) ^ 2 / (k : ℚ) ^ 2) := by
        simpa only [Nat.cast_pow] using (PVal.of_pow_p (e := 2) hp).div_nat hp
          (fun h => not_dvd_of_lt_prime hp hk.1 hk.2 (hp.dvd_of_dvd_pow h))
      rw [hfac, ← mul_sub]
      exact hbase.mul hp hP3R
    have h4a : PVal p 5 ((p : ℚ) ^ 4 * S112 p / 2) := by
      simpa only [Nat.cast_ofNat] using ((PVal.of_pow_p (e := 4) hp).mul hp hS112).div_nat hp hnd2
    have h4b : PVal p 5 (13 * (p : ℚ) ^ 4 * S22 p / 2) := by
      have h1 := ((PVal.nat hp 13).zero_mul hp (PVal.of_pow_p (e := 4) hp)).mul hp hS22
      simpa only [Nat.cast_ofNat, mul_assoc] using h1.div_nat hp hnd2
    have h1 := (((hterm.add hp (p2_harmH2_mod_p5 p hp hp7)).add hp hS12).add hp h4a).add hp h4b
    have h3 := (PVal.nat hp 3).zero_mul hp h1
    convert h3 using 1; ring
  -- Bucket u = 2: 3 * sum_{k1, k2 in Ico 1 p} F k1 k2 0 in p^5 Z_(p)
  have hq2 : PVal p 5 (3 * (∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p, F k₁ k₂ 0)) := by
    have hchoose4 : ∀ s, 1 ≤ s → s ≤ p → PVal p 1 ((Nat.choose (4 * p - s) (p - s) : ℚ) - 1) := by
      intro s hs1 hsp
      by_cases hse : s = p
      · subst hse; simp; exact PVal.zero hp
      · have hdesc : (Nat.choose (4 * p - s) (p - s) : ℚ) =
            ∏ j ∈ Ico 1 (p - s + 1), (1 + 3 * (p : ℚ) / (j : ℚ)) := by
          have h1 := Nat.descFactorial_eq_factorial_mul_choose (4 * p - s) (p - s)
          rw [Nat.descFactorial_eq_prod_range] at h1
          have hfac : (p - s).factorial = ∏ j ∈ Ico 1 (p - s + 1), j := by
            clear h1
            suffices ∀ m, m.factorial = ∏ j ∈ Ico 1 (m + 1), j from this (p - s)
            intro m; induction m with
            | zero => simp
            | succ m ih => rw [Finset.prod_Ico_succ_top (by omega), Nat.factorial_succ, ih, mul_comm]
          have hnum : ∏ i ∈ range (p - s), (4 * p - s - i) = ∏ j ∈ Ico 1 (p - s + 1), (3 * p + j) := by
            refine Finset.prod_bij (fun i _ => p - s - i) ?_ ?_ ?_ ?_
            · intro i hi; rw [mem_range] at hi; rw [mem_Ico]; omega
            · intro a ha b hb hab; rw [mem_range] at ha hb; omega
            · intro j hj; rw [mem_Ico] at hj; exact ⟨p - s - j, by rw [mem_range]; omega, by omega⟩
            · intro i hi; rw [mem_range] at hi; omega
          rw [hnum, hfac] at h1
          have hq : (∏ j ∈ Ico 1 (p - s + 1), ((3 * p + j : ℕ) : ℚ)) =
              (∏ j ∈ Ico 1 (p - s + 1), (j : ℚ)) * (Nat.choose (4 * p - s) (p - s) : ℚ) := by
            have := congrArg (Nat.cast : ℕ → ℚ) h1
            simpa only [Nat.cast_prod, Nat.cast_mul] using this
          have hprod0 : (∏ j ∈ Ico 1 (p - s + 1), (j : ℚ)) ≠ 0 :=
            Finset.prod_ne_zero_iff.mpr fun j hj => by rw [mem_Ico] at hj; exact Nat.cast_ne_zero.mpr (by omega)
          apply mul_left_cancel₀ hprod0
          rw [← hq, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun j hj => ?_
          rw [mem_Ico] at hj
          have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          push_cast; field_simp [hj0]; ring
        rw [hdesc]
        refine PVal.prod_one_add hp fun j hj => ?_
        rw [mem_Ico] at hj
        exact ((PVal.nat hp 3).zero_mul hp (PVal.of_p hp)).div_nat hp
          (not_dvd_of_lt_prime hp hj.1 (by omega))
    have hchp_sq : ∀ k ∈ Ico 1 p, PVal p 3 ((Nat.choose p k : ℚ) ^ 2 - (p : ℚ) ^ 2 / (k : ℚ) ^ 2) := by
      intro k hk; rw [mem_Ico] at hk
      have hch := choose_p_exact_prod p k hp (by omega) hk.1 hk.2
      have hneg : ((-1 : ℚ) ^ (k - 1)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm (k - 1) 2, pow_mul]; norm_num
      set P := ∏ j ∈ Ico 1 k, (1 - (p : ℚ) / (j : ℚ))
      have hP : PVal p 1 (P - 1) := by
        have h := PVal.prod_one_add hp (s := Ico 1 k) (f := fun j => -(p : ℚ) / (j : ℚ)) fun j hj => by
          rw [mem_Ico] at hj; exact (PVal.neg_of_p hp).div_nat hp
            (not_dvd_of_lt_prime hp hj.1 (by omega))
        convert h using 3 with j _; ring
      have hP2 : PVal p 1 (P ^ 2 - 1) := by
        rw [show P ^ 2 - 1 = (P - 1) * ((P - 1) + 2) by ring]
        exact hP.mul_zero hp ((hP.mono (Nat.zero_le _)).add hp (PVal.nat hp 2))
      have heq : (Nat.choose p k : ℚ) ^ 2 - (p : ℚ) ^ 2 / (k : ℚ) ^ 2 =
          ((p : ℚ) ^ 2 / (k : ℚ) ^ 2) * (P ^ 2 - 1) := by
        rw [hch, mul_pow, mul_pow, hneg, one_mul, div_pow]; ring
      rw [heq]
      have hbase : PVal p 2 ((p : ℚ) ^ 2 / (k : ℚ) ^ 2) := by
        simpa only [Nat.cast_pow] using (PVal.of_pow_p (e := 2) hp).div_nat hp
          (fun h => not_dvd_of_lt_prime hp hk.1 hk.2 (hp.dvd_of_dvd_pow h))
      exact hbase.mul hp hP2
    have happrox : PVal p 5 ((∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p, F k₁ k₂ 0) -
        (p : ℚ) ^ 4 * ∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p,
          if k₁ + k₂ ≤ p then (((k₁ : ℚ) ^ 2 * (k₂ : ℚ) ^ 2))⁻¹ else 0) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine PVal.sum hp fun k₁ hk1 => PVal.sum hp fun k₂ hk2 => ?_
      rw [mem_Ico] at hk1 hk2
      simp only [F, add_zero, Nat.choose_zero_right, Nat.cast_one, one_pow, mul_one]
      split_ifs with hle
      · have hc4 := hchoose4 (k₁ + k₂) (by omega) hle
        have h1 := hchp_sq k₁ (mem_Ico.mpr hk1)
        have h2 := hchp_sq k₂ (mem_Ico.mpr hk2)
        have hpk1 : PVal p 2 ((Nat.choose p k₁ : ℚ) ^ 2) := by
          have : p ^ 2 ∣ (Nat.choose p k₁) ^ 2 := pow_dvd_pow_of_dvd (hp.dvd_choose_self (by omega) hk1.2) 2
          simpa only [Nat.cast_pow] using PVal.of_dvd_nat hp this
        have hpk2 : PVal p 2 ((Nat.choose p k₂ : ℚ) ^ 2) := by
          have : p ^ 2 ∣ (Nat.choose p k₂) ^ 2 := pow_dvd_pow_of_dvd (hp.dvd_choose_self (by omega) hk2.2) 2
          simpa only [Nat.cast_pow] using PVal.of_dvd_nat hp this
        have hb2 : PVal p 2 ((p : ℚ) ^ 2 / (k₂ : ℚ) ^ 2) := by
          simpa only [Nat.cast_pow] using (PVal.of_pow_p (e := 2) hp).div_nat hp
            (fun h => not_dvd_of_lt_prime hp hk2.1 hk2.2 (hp.dvd_of_dvd_pow h))
        set C4 := (Nat.choose (4 * p - (k₁ + k₂)) (p - (k₁ + k₂)) : ℚ)
        set A1 := (Nat.choose p k₁ : ℚ) ^ 2
        set A2 := (Nat.choose p k₂ : ℚ) ^ 2
        set B1 := (p : ℚ) ^ 2 / (k₁ : ℚ) ^ 2
        set B2 := (p : ℚ) ^ 2 / (k₂ : ℚ) ^ 2
        have hrew : C4 * A1 * A2 - (p : ℚ) ^ 4 * (((k₁ : ℚ) ^ 2 * (k₂ : ℚ) ^ 2))⁻¹ =
            (C4 - 1) * (A1 * A2) + A1 * (A2 - B2) + (A1 - B1) * B2 := by
          simp only [B1, B2, div_eq_mul_inv, mul_inv]; ring
        rw [hrew]
        exact ((hc4.mul hp (hpk1.mul hp hpk2)).add hp (hpk1.mul hp h2)).add hp (h1.mul hp hb2)
      · simp; exact PVal.zero hp
    -- Show sum_{k1+k2 <= p} 1/(k1^2*k2^2) in p * Z_(p)
    have hsum_mod : PVal p 1 (∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p,
        if k₁ + k₂ ≤ p then (((k₁ : ℚ) ^ 2 * (k₂ : ℚ) ^ 2))⁻¹ else 0) := by
      have hsplit_le : (∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p,
            if k₁ + k₂ ≤ p then (((k₁ : ℚ) ^ 2 * (k₂ : ℚ) ^ 2))⁻¹ else 0) =
          (∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p, if k₁ + k₂ = p then (((k₁ : ℚ) ^ 2 * (k₂ : ℚ) ^ 2))⁻¹ else 0) +
          (∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p, if k₁ + k₂ < p then (((k₁ : ℚ) ^ 2 * (k₂ : ℚ) ^ 2))⁻¹ else 0) := by
        simp only [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ => ?_
        by_cases hlt : k₁ + k₂ < p
        · simp [hlt, show k₁ + k₂ ≤ p by omega, show k₁ + k₂ ≠ p by omega]
        · by_cases heq : k₁ + k₂ = p
          · simp [heq]
          · simp [hlt, heq, show ¬ k₁ + k₂ ≤ p by omega]
      have heq_part : PVal p 1 (∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p,
          if k₁ + k₂ = p then (((k₁ : ℚ) ^ 2 * (k₂ : ℚ) ^ 2))⁻¹ else 0) := by
        have h1 : (∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p,
              if k₁ + k₂ = p then (((k₁ : ℚ) ^ 2 * (k₂ : ℚ) ^ 2))⁻¹ else 0) =
            ∑ k ∈ Ico 1 p, (((k : ℚ) ^ 2 * ((p - k : ℕ) : ℚ) ^ 2))⁻¹ := by
          refine Finset.sum_congr rfl fun k₁ hk1 => ?_
          rw [mem_Ico] at hk1
          have hmem : p - k₁ ∈ Ico 1 p := by rw [mem_Ico]; omega
          rw [← Finset.add_sum_erase _ _ hmem]
          have hrest : ∑ k₂ ∈ (Ico 1 p).erase (p - k₁),
              (if k₁ + k₂ = p then (((k₁ : ℚ) ^ 2 * (k₂ : ℚ) ^ 2))⁻¹ else 0) = 0 :=
            Finset.sum_eq_zero fun k₂ hk2 => by rw [mem_erase] at hk2; simp [show k₁ + k₂ ≠ p by omega]
          rw [hrest, add_zero, if_pos (by omega)]
        rw [h1]
        have hdiff : PVal p 1 ((∑ k ∈ Ico 1 p, (((k : ℚ) ^ 2 * ((p - k : ℕ) : ℚ) ^ 2))⁻¹) - harmH p 4) := by
          rw [harmH, ← Finset.sum_sub_distrib]
          refine PVal.sum hp fun k hk => ?_
          rw [mem_Ico] at hk
          have hndk := not_dvd_of_lt_prime hp hk.1 hk.2
          have hndpk := not_dvd_of_lt_prime hp (by omega : 1 ≤ p - k) (by omega : p - k < p)
          have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have hpk0 : ((p - k : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have heq : (((k : ℚ) ^ 2 * ((p - k : ℕ) : ℚ) ^ 2))⁻¹ - ((k : ℚ) ^ 4)⁻¹ =
              (p : ℚ) * (2 * (k : ℚ) - (p : ℚ)) / (((k ^ 4 * (p - k) ^ 2 : ℕ) : ℚ)) := by
            push_cast; rw [Nat.cast_sub (by omega)] at hpk0 ⊢; field_simp [hk0, hpk0]; ring
          rw [heq]
          have hnd : ¬ p ∣ k ^ 4 * (p - k) ^ 2 := fun h => by
            rcases hp.dvd_mul.mp h with h1 | h2
            · exact hndk (hp.dvd_of_dvd_pow h1)
            · exact hndpk (hp.dvd_of_dvd_pow h2)
          have hnum : PVal p 1 ((p : ℚ) * (2 * (k : ℚ) - (p : ℚ))) :=
            (PVal.of_p hp).mul_zero hp
              (((PVal.nat hp 2).mul_zero hp (PVal.nat hp k)).sub hp (PVal.nat hp p))
          exact hnum.div_nat hp hnd
        simpa using hdiff.add hp (harmH_four_mod_p p hp hp7)
      have hlt_part : PVal p 1 (∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p,
          if k₁ + k₂ < p then (((k₁ : ℚ) ^ 2 * (k₂ : ℚ) ^ 2))⁻¹ else 0) := by
        set Slt := ∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p,
          if k₁ + k₂ < p then (((k₁ : ℚ) ^ 2 * (k₂ : ℚ) ^ 2))⁻¹ else 0
        set Sgt := ∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p,
          if p < k₁ + k₂ then (((k₁ : ℚ) ^ 2 * (k₂ : ℚ) ^ 2))⁻¹ else 0
        set Seq := ∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p,
          if k₁ + k₂ = p then (((k₁ : ℚ) ^ 2 * (k₂ : ℚ) ^ 2))⁻¹ else 0
        have htot : Slt + Seq + Sgt = (harmH p 2) ^ 2 := by
          have hsq : (harmH p 2) ^ 2 = ∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p, (((k₁ : ℚ) ^ 2 * (k₂ : ℚ) ^ 2))⁻¹ := by
            rw [sq, harmH, Finset.sum_mul]
            refine Finset.sum_congr rfl fun k₁ _ => ?_
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k₂ _ => by rw [mul_inv]
          rw [hsq]; simp only [Slt, Seq, Sgt, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun k₁ _ => Finset.sum_congr rfl fun k₂ _ => ?_
          by_cases h1 : k₁ + k₂ < p
          · simp [h1, show k₁ + k₂ ≠ p by omega, show ¬ p < k₁ + k₂ by omega]
          · by_cases h2 : k₁ + k₂ = p
            · simp [h2]
            · simp [h1, h2, show p < k₁ + k₂ by omega]
        have hlt_gt : PVal p 1 (Slt - Sgt) := by
          have hSgt_ref : Sgt = ∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p,
              if k₁ + k₂ < p then ((((p - k₁ : ℕ) : ℚ) ^ 2 * ((p - k₂ : ℕ) : ℚ) ^ 2))⁻¹ else 0 := by
            simp only [Sgt]
            rw [← sum_Ico_reflect p]
            refine Finset.sum_congr rfl fun k₁ hk1 => ?_
            rw [← sum_Ico_reflect p]
            refine Finset.sum_congr rfl fun k₂ hk2 => ?_
            rw [mem_Ico] at hk1 hk2
            have hcond : (p < (p - k₁) + (p - k₂)) ↔ (k₁ + k₂ < p) := by omega
            simp [hcond]
          rw [hSgt_ref]; simp only [Slt, ← Finset.sum_sub_distrib]
          refine PVal.sum hp fun k₁ hk1 => PVal.sum hp fun k₂ hk2 => ?_
          rw [mem_Ico] at hk1 hk2
          split_ifs
          · have hnd1 := not_dvd_of_lt_prime hp hk1.1 hk1.2
            have hnd2 := not_dvd_of_lt_prime hp hk2.1 hk2.2
            have hndp1 := not_dvd_of_lt_prime hp (by omega : 1 ≤ p - k₁) (by omega : p - k₁ < p)
            have hndp2 := not_dvd_of_lt_prime hp (by omega : 1 ≤ p - k₂) (by omega : p - k₂ < p)
            have h1 := inv_sub_inv_pval hp (fun h => hnd1 (hp.dvd_of_dvd_pow h))
              (fun h => hndp1 (hp.dvd_of_dvd_pow h)) (by
                have heq : (((p - k₁) ^ 2 : ℕ) : ℤ) - ((k₁ ^ 2 : ℕ) : ℤ) = (p : ℤ) * ((p : ℤ) - 2 * (k₁ : ℤ)) := by
                  push_cast; rw [Nat.cast_sub (by omega)]; ring
                exact Int.modEq_iff_dvd.mpr ⟨(p : ℤ) - 2 * (k₁ : ℤ), heq⟩)
            have h2 := inv_sub_inv_pval hp (fun h => hnd2 (hp.dvd_of_dvd_pow h))
              (fun h => hndp2 (hp.dvd_of_dvd_pow h)) (by
                have heq : (((p - k₂) ^ 2 : ℕ) : ℤ) - ((k₂ ^ 2 : ℕ) : ℤ) = (p : ℤ) * ((p : ℤ) - 2 * (k₂ : ℤ)) := by
                  push_cast; rw [Nat.cast_sub (by omega)]; ring
                exact Int.modEq_iff_dvd.mpr ⟨(p : ℤ) - 2 * (k₂ : ℤ), heq⟩)
            have hrew : (((k₁ : ℚ) ^ 2 * (k₂ : ℚ) ^ 2))⁻¹ - ((((p - k₁ : ℕ) : ℚ) ^ 2 * ((p - k₂ : ℕ) : ℚ) ^ 2))⁻¹ =
                (((k₁ ^ 2 : ℕ) : ℚ)⁻¹ - (((p - k₁) ^ 2 : ℕ) : ℚ)⁻¹) * (((k₂ ^ 2 : ℕ) : ℚ)⁻¹) +
                (((p - k₁) ^ 2 : ℕ) : ℚ)⁻¹ * ((((k₂ ^ 2 : ℕ) : ℚ)⁻¹ - (((p - k₂) ^ 2 : ℕ) : ℚ)⁻¹)) := by
              push_cast; simp only [mul_inv]; ring
            rw [hrew]
            exact (h1.mul_zero hp (PVal.inv_nat fun h => hnd2 (hp.dvd_of_dvd_pow h))).add hp
              ((PVal.inv_nat fun h => hndp1 (hp.dvd_of_dvd_pow h)).zero_mul hp h2)
          · simp; exact PVal.zero hp
        have h2S : PVal p 1 ((2 : ℕ) * Slt) := by
          have hH2sq : PVal p 1 ((harmH p 2) ^ 2) := ((harmH_two_mod_p p hp hp7).pow hp 2).mono (by decide)
          have hcomb := (hH2sq.sub hp heq_part).add hp hlt_gt
          convert hcomb using 1; push_cast; linarith
        exact PVal.div_of_mul_nat hp hnd2 h2S
      rw [hsplit_le]; exact heq_part.add hp hlt_part
    have hmain := happrox.add hp ((PVal.of_pow_p (e := 4) hp).mul hp hsum_mod)
    exact (PVal.nat hp 3).zero_mul hp (by simpa using hmain)
  -- Bucket u = 3: divisible by p^6 term-by-term
  have hq3 : PVal p 5 (∑ k₁ ∈ Ico 1 p, ∑ k₂ ∈ Ico 1 p, ∑ k₃ ∈ Ico 1 p, F k₁ k₂ k₃) := by
    refine PVal.sum hp fun k₁ hk1 => PVal.sum hp fun k₂ hk2 => PVal.sum hp fun k₃ hk3 => ?_
    rw [mem_Ico] at hk1 hk2 hk3
    simp only [F]
    split_ifs
    · have h1 : PVal p 2 ((Nat.choose p k₁ : ℚ) ^ 2) := by
        simpa only [Nat.cast_pow] using PVal.of_dvd_nat hp (pow_dvd_pow_of_dvd (hp.dvd_choose_self (by omega) hk1.2) 2)
      have h2 : PVal p 2 ((Nat.choose p k₂ : ℚ) ^ 2) := by
        simpa only [Nat.cast_pow] using PVal.of_dvd_nat hp (pow_dvd_pow_of_dvd (hp.dvd_choose_self (by omega) hk2.2) 2)
      have h3 : PVal p 2 ((Nat.choose p k₃ : ℚ) ^ 2) := by
        simpa only [Nat.cast_pow] using PVal.of_dvd_nat hp (pow_dvd_pow_of_dvd (hp.dvd_choose_self (by omega) hk3.2) 2)
      exact ((((PVal.nat hp _).zero_mul hp h1).mul hp h2).mul hp h3).mono (by decide)
    · exact PVal.zero hp
  rw [hsplit]
  have hcomb := ((hq0.add hp hq1).add hp hq2).add hp hq3
  convert hcomb using 1; ring

private lemma PVal.prod_one_add_deg1 {ι : Type*} {s : Finset ι} {p : ℕ} (hp : p.Prime)
    {f : ι → ℚ} (hf : ∀ i ∈ s, PVal p 1 (f i)) :
    PVal p 2 ((∏ i ∈ s, (1 + f i)) - (1 + ∑ i ∈ s, f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PVal.zero hp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfa := hf a (mem_insert_self a s)
    have hih := ih fun i hi => hf i (mem_insert_of_mem hi)
    have hS : PVal p 1 (∑ i ∈ s, f i) := PVal.sum hp fun i hi => hf i (mem_insert_of_mem hi)
    have h1fa : PVal p 0 (1 + f a) := (PVal.nat hp 1).add hp (hfa.mono (Nat.zero_le _))
    have heq : (1 + f a) * (∏ i ∈ s, (1 + f i)) - (1 + (f a + ∑ i ∈ s, f i)) =
        (1 + f a) * ((∏ i ∈ s, (1 + f i)) - (1 + ∑ i ∈ s, f i)) + f a * (∑ i ∈ s, f i) := by ring
    rw [heq]
    exact (h1fa.zero_mul hp hih).add hp (hfa.mul hp hS)

private lemma choose_pm1_add_exact (p j : ℕ) (hp : p.Prime) (hj1 : 1 ≤ j) (hjp : j < p) :
    (Nat.choose (p - 1 + j) j : ℚ) =
      ((p : ℚ) / (j : ℚ)) * ∏ i ∈ Ico 1 j, (1 + (p : ℚ) / (i : ℚ)) := by
  have h := choose_pred_add_ndiv_exact p 1 0 j hp (by decide) hj1 hjp
  have hfilt : (Ico 1 j).filter (fun i => ¬ p ∣ i) = Ico 1 j :=
    Finset.filter_true_of_mem fun i hi => by
      rw [mem_Ico] at hi; exact not_dvd_of_lt_prime hp hi.1 (by omega)
  simpa [hfilt] using h

private lemma cJ_pm1_exact (p j : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hj1 : 1 ≤ j) (hjp : j < p) :
    (cJ (p - 1) j : ℚ) =
      (-1 : ℚ) ^ j * ((p : ℚ) * ((j : ℚ) - (p : ℚ)) / (j : ℚ) ^ 2) *
        ∏ i ∈ Ico 1 j, (1 - (p : ℚ) ^ 2 / (i : ℚ) ^ 2) := by
  have hf1 := choose_pred_p_shift_general p 1 j hp (by omega) (by omega)
  have hf2 := choose_pm1_add_exact p j hp hj1 hjp
  have hdiv : j / p = 0 := Nat.div_eq_of_lt hjp
  have hmod : j % p = j := Nat.mod_eq_of_lt hjp
  have hfilt : (Ico 1 (j + 1)).filter (fun i => ¬ p ∣ i) = Ico 1 (j + 1) :=
    Finset.filter_true_of_mem fun i hi => by
      rw [mem_Ico] at hi; exact not_dvd_of_lt_prime hp hi.1 (by omega)
  rw [hdiv, hmod, hfilt] at hf1
  simp only [one_mul, Nat.sub_self, Nat.choose_zero_right, Nat.cast_one, mul_one] at hf1
  rw [Finset.prod_Ico_succ_top hj1] at hf1
  simp only [cJ, Int.cast_mul, Int.cast_natCast]
  rw [hf1, hf2]
  have hprod_comb : (∏ i ∈ Ico 1 j, (1 - (p : ℚ) / (i : ℚ))) * (∏ i ∈ Ico 1 j, (1 + (p : ℚ) / (i : ℚ))) =
      ∏ i ∈ Ico 1 j, (1 - (p : ℚ) ^ 2 / (i : ℚ) ^ 2) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => by ring
  have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hfac : (1 - (p : ℚ) / (j : ℚ)) * ((p : ℚ) / (j : ℚ)) =
      (p : ℚ) * ((j : ℚ) - (p : ℚ)) / (j : ℚ) ^ 2 := by field_simp [hj0]
  calc (-1 : ℚ) ^ j * ((∏ i ∈ Ico 1 j, (1 - (p : ℚ) / (i : ℚ))) * (1 - (p : ℚ) / (j : ℚ))) *
        ((p : ℚ) / (j : ℚ) * ∏ i ∈ Ico 1 j, (1 + (p : ℚ) / (i : ℚ)))
      = (-1 : ℚ) ^ j * ((1 - (p : ℚ) / (j : ℚ)) * ((p : ℚ) / (j : ℚ))) *
          ((∏ i ∈ Ico 1 j, (1 - (p : ℚ) / (i : ℚ))) * (∏ i ∈ Ico 1 j, (1 + (p : ℚ) / (i : ℚ)))) := by ring
    _ = _ := by rw [hfac, hprod_comb]

private lemma cJ_pm1_mod_p5 (p j : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hj1 : 1 ≤ j) (hjp : j < p) :
    PVal p 5 ((-1 : ℚ) ^ j * (cJ (p - 1) j : ℚ) -
      ((p : ℚ) / (j : ℚ) - (p : ℚ) ^ 2 / (j : ℚ) ^ 2) * (1 - (p : ℚ) ^ 2 * harmh 2 (j - 1))) := by
  have hex := cJ_pm1_exact p j hp hp7 hj1 hjp
  have hneg : (-1 : ℚ) ^ j * (-1 : ℚ) ^ j = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hndj := not_dvd_of_lt_prime hp hj1 hjp
  have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpre : (p : ℚ) * ((j : ℚ) - (p : ℚ)) / (j : ℚ) ^ 2 = (p : ℚ) / (j : ℚ) - (p : ℚ) ^ 2 / (j : ℚ) ^ 2 := by
    field_simp [hj0]
  have hprod : PVal p 4 ((∏ i ∈ Ico 1 j, (1 - (p : ℚ) ^ 2 / (i : ℚ) ^ 2)) - (1 - (p : ℚ) ^ 2 * harmh 2 (j - 1))) := by
    have h1 := PVal.prod_one_add_deg1_sq hp (s := Ico 1 j) (f := fun i => -((p : ℚ) ^ 2 / (i : ℚ) ^ 2)) fun i hi => by
      rw [mem_Ico] at hi
      simpa only [Nat.cast_pow] using ((PVal.of_pow_p (e := 2) hp).div_nat hp
        (fun h => not_dvd_of_lt_prime hp hi.1 (by omega) (hp.dvd_of_dvd_pow h))).neg
    have heq1 : ∏ i ∈ Ico 1 j, (1 + -((p : ℚ) ^ 2 / (i : ℚ) ^ 2)) =
        ∏ i ∈ Ico 1 j, (1 - (p : ℚ) ^ 2 / (i : ℚ) ^ 2) :=
      Finset.prod_congr rfl fun i _ => by ring
    have heq2 : 1 + ∑ i ∈ Ico 1 j, -((p : ℚ) ^ 2 / (i : ℚ) ^ 2) = 1 - (p : ℚ) ^ 2 * harmh 2 (j - 1) := by
      simp only [harmh, show j - 1 + 1 = j by omega, Finset.mul_sum, Finset.sum_neg_distrib, div_eq_mul_inv]; ring
    rwa [heq1, heq2] at h1
  have hbase : PVal p 1 ((p : ℚ) / (j : ℚ) - (p : ℚ) ^ 2 / (j : ℚ) ^ 2) := by
    have h2 : PVal p 2 ((p : ℚ) ^ 2 / (j : ℚ) ^ 2) := by
      simpa only [Nat.cast_pow] using (PVal.of_pow_p (e := 2) hp).div_nat hp (fun h => hndj (hp.dvd_of_dvd_pow h))
    exact ((PVal.of_p hp).div_nat hp hndj).sub hp (h2.mono (by decide))
  have hrew : (-1 : ℚ) ^ j * (cJ (p - 1) j : ℚ) -
      ((p : ℚ) / (j : ℚ) - (p : ℚ) ^ 2 / (j : ℚ) ^ 2) * (1 - (p : ℚ) ^ 2 * harmh 2 (j - 1)) =
      ((p : ℚ) / (j : ℚ) - (p : ℚ) ^ 2 / (j : ℚ) ^ 2) *
        ((∏ i ∈ Ico 1 j, (1 - (p : ℚ) ^ 2 / (i : ℚ) ^ 2)) - (1 - (p : ℚ) ^ 2 * harmh 2 (j - 1))) := by
    rw [hex, hpre, ← mul_assoc, ← mul_assoc, hneg, one_mul]; ring
  rw [hrew]; exact hbase.mul hp hprod

private lemma cJ_pm1_mod_p3 (p j : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hj1 : 1 ≤ j) (hjp : j < p) :
    PVal p 3 ((-1 : ℚ) ^ j * (cJ (p - 1) j : ℚ) - ((p : ℚ) / (j : ℚ) - (p : ℚ) ^ 2 / (j : ℚ) ^ 2)) := by
  have h5 := (cJ_pm1_mod_p5 p j hp hp7 hj1 hjp).mono (by decide : 3 ≤ 5)
  have hndj := not_dvd_of_lt_prime hp hj1 hjp
  have hbase : PVal p 1 ((p : ℚ) / (j : ℚ) - (p : ℚ) ^ 2 / (j : ℚ) ^ 2) := by
    have h2 : PVal p 2 ((p : ℚ) ^ 2 / (j : ℚ) ^ 2) := by
      simpa only [Nat.cast_pow] using (PVal.of_pow_p (e := 2) hp).div_nat hp (fun h => hndj (hp.dvd_of_dvd_pow h))
    exact ((PVal.of_p hp).div_nat hp hndj).sub hp (h2.mono (by decide))
  have hrem : PVal p 3 (((p : ℚ) / (j : ℚ) - (p : ℚ) ^ 2 / (j : ℚ) ^ 2) * ((p : ℚ) ^ 2 * harmh 2 (j - 1))) :=
    hbase.mul hp ((PVal.of_pow_p (e := 2) hp).mul_zero hp (harmh_pval_zero p 2 (j - 1) hp (by omega)))
  have hcomb := h5.sub hp hrem
  convert hcomb using 1; ring

private lemma cJ_pm1_mod_p2 (p j : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hj1 : 1 ≤ j) (hjp : j < p) :
    PVal p 2 ((-1 : ℚ) ^ j * (cJ (p - 1) j : ℚ) - (p : ℚ) / (j : ℚ)) := by
  have h3 := (cJ_pm1_mod_p3 p j hp hp7 hj1 hjp).mono (by decide : 2 ≤ 3)
  have hndj := not_dvd_of_lt_prime hp hj1 hjp
  have hp2 : PVal p 2 ((p : ℚ) ^ 2 / (j : ℚ) ^ 2) := by
    simpa only [Nat.cast_pow] using (PVal.of_pow_p (e := 2) hp).div_nat hp (fun h => hndj (hp.dvd_of_dvd_pow h))
  have hcomb := h3.sub hp hp2
  convert hcomb using 1; ring

private lemma cJ_pm1_reflect_mod_p3 (p a : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (ha1 : 1 ≤ a) (hap : a < p) :
    PVal p 3 ((-1 : ℚ) ^ (p - a) * (cJ (p - 1) (p - a) : ℚ) +
      ((p : ℚ) / (a : ℚ) + 2 * (p : ℚ) ^ 2 / (a : ℚ) ^ 2)) := by
  have h3 := cJ_pm1_mod_p3 p (p - a) hp hp7 (by omega) (by omega)
  have ha0 : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpa0 : ((p - a : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnda := not_dvd_of_lt_prime hp ha1 hap
  have hndpa := not_dvd_of_lt_prime hp (by omega : 1 ≤ p - a) (by omega : p - a < p)
  have hrat : ((p : ℚ) / ((p - a : ℕ) : ℚ) - (p : ℚ) ^ 2 / ((p - a : ℕ) : ℚ) ^ 2) +
      ((p : ℚ) / (a : ℚ) + 2 * (p : ℚ) ^ 2 / (a : ℚ) ^ 2) =
      (p : ℚ) ^ 3 * (2 * (p : ℚ) - 3 * (a : ℚ)) / (((a ^ 2 * (p - a) ^ 2 : ℕ) : ℚ)) := by
    push_cast; rw [Nat.cast_sub (by omega)] at hpa0 ⊢; field_simp [ha0, hpa0]; ring
  have hdiff : PVal p 3 (((p : ℚ) / ((p - a : ℕ) : ℚ) - (p : ℚ) ^ 2 / ((p - a : ℕ) : ℚ) ^ 2) +
      ((p : ℚ) / (a : ℚ) + 2 * (p : ℚ) ^ 2 / (a : ℚ) ^ 2)) := by
    rw [hrat]
    have hnd : ¬ p ∣ a ^ 2 * (p - a) ^ 2 := fun h => by
      rcases hp.dvd_mul.mp h with h1 | h2
      · exact hnda (hp.dvd_of_dvd_pow h1)
      · exact hndpa (hp.dvd_of_dvd_pow h2)
    have hnum : PVal p 3 ((p : ℚ) ^ 3 * (2 * (p : ℚ) - 3 * (a : ℚ))) :=
      (PVal.of_pow_p (e := 3) hp).mul_zero hp
        (((PVal.nat hp 2).mul_zero hp (PVal.nat hp p)).sub hp ((PVal.nat hp 3).mul_zero hp (PVal.nat hp a)))
    exact hnum.div_nat hp hnd
  have hcomb := h3.add hp hdiff
  convert hcomb using 1; ring

/-- Exact mod-p^3 expansion of C(3*p - 1 - s, 2*p - s) for 1 <= s < p. -/
private lemma choose_3p_sub_s_mod_p3 (p s : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) (hs1 : 1 ≤ s) (hsp : s < p) :
    PVal p 3 ((Nat.choose (3 * p - 1 - s) (2 * p - s) : ℚ) +
      (2 * (p : ℚ) / (s : ℚ)) * (1 + (p : ℚ) * (harmh 1 (s - 1) + 3 / (s : ℚ)))) := by
  set u := p - s
  have hu1 : 1 ≤ u := by omega
  have hup : u < p := by omega
  have hidx1 : 3 * p - 1 - s = p - 1 + (1 * p + u) := by omega
  have hidx2 : 2 * p - s = 1 * p + u := by omega
  rw [hidx1, hidx2]
  have hex := choose_pred_add_ndiv_exact p 1 1 u hp (by decide) hu1 hup
  have hfilt : (Ico 1 (1 * p + u)).filter (fun i => ¬ p ∣ i) =
      Ico 1 p ∪ (Ico 1 u).image (fun i => p + i) := by
    ext x
    simp only [mem_filter, mem_Ico, mem_union, mem_image]
    constructor
    · rintro ⟨⟨hx1, hxu⟩, hnd⟩
      by_cases hxp : x < p
      · left; exact ⟨hx1, hxp⟩
      · right
        have hne : x ≠ p := fun h => hnd (h ▸ dvd_refl p)
        exact ⟨x - p, ⟨by omega, by omega⟩, by omega⟩
    · rintro (⟨hx1, hxp⟩ | ⟨i, ⟨hi1, hiu⟩, rfl⟩)
      · exact ⟨⟨hx1, by omega⟩, not_dvd_of_lt_prime hp hx1 hxp⟩
      · exact ⟨⟨by omega, by omega⟩, fun h => not_dvd_of_lt_prime hp hi1 (by omega)
          ((Nat.dvd_add_right (dvd_refl p)).mp h)⟩
  have hdisj : Disjoint (Ico 1 p) ((Ico 1 u).image (fun i => p + i)) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    rw [mem_Ico] at hx1; rw [mem_image] at hx2
    obtain ⟨i, hi, rfl⟩ := hx2; rw [mem_Ico] at hi; omega
  have hprod_split : ∏ i ∈ (Ico 1 (1 * p + u)).filter (fun i => ¬ p ∣ i), (1 + (p : ℚ) / (i : ℚ)) =
      (∏ i ∈ Ico 1 p, (1 + (p : ℚ) / (i : ℚ))) * ∏ i ∈ Ico 1 u, (1 + (p : ℚ) / ((p + i : ℕ) : ℚ)) := by
    rw [hfilt, Finset.prod_union hdisj]
    congr 1
    rw [Finset.prod_image (fun a _ b _ hab => by omega)]
  set Pp := ∏ i ∈ Ico 1 p, (1 + (p : ℚ) / (i : ℚ))
  set Qu := ∏ i ∈ Ico 1 u, (1 + (p : ℚ) / ((p + i : ℕ) : ℚ))
  have hex' : (Nat.choose (p - 1 + (1 * p + u)) (1 * p + u) : ℚ) =
      (2 * (p : ℚ) / ((p + u : ℕ) : ℚ)) * (Pp * Qu) := by
    have h1 := hex
    simp only [one_mul, Nat.cast_one, show Nat.choose (1 + 1) 1 = 2 by decide, Nat.cast_ofNat] at h1
    simp only [one_mul] at hprod_split ⊢
    rw [h1, hprod_split]; ring
  have hPp : PVal p 2 (Pp - 1) := by
    have hE2 := (prod_one_add_ap_mod_p5 p 1 hp hp7).mono (by decide : 2 ≤ 5)
    have hH1 : PVal p 2 (2 * (p : ℚ) * harmH p 1) := by
      simpa [mul_assoc] using
        ((PVal.nat hp 2).zero_mul hp ((PVal.of_p hp).mul hp (harmH1_mod_p2 p hp hp7))).mono (by decide : 2 ≤ 3)
    have hcomb := hE2.add hp hH1
    convert hcomb using 1; simp only [Pp]; norm_num
  have hQu_rep : PVal p 2 (Qu - ∏ i ∈ Ico 1 u, (1 + (p : ℚ) / (i : ℚ))) := by
    refine PVal.prod_sub_prod hp ?_ ?_ ?_
    · intro i hi; rw [mem_Ico] at hi
      have hnd : ¬ p ∣ p + i := fun h => not_dvd_of_lt_prime hp hi.1 (by omega) ((Nat.dvd_add_right (dvd_refl p)).mp h)
      exact (PVal.nat hp 1).add hp ((PVal.nat hp p).div_nat hp hnd)
    · intro i hi; rw [mem_Ico] at hi
      exact (PVal.nat hp 1).add hp ((PVal.nat hp p).div_nat hp (not_dvd_of_lt_prime hp hi.1 (by omega)))
    · intro i hi; rw [mem_Ico] at hi
      have hi0 : (i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hpi0 : ((p + i : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have heq : (1 + (p : ℚ) / ((p + i : ℕ) : ℚ)) - (1 + (p : ℚ) / (i : ℚ)) =
          -((p : ℚ) ^ 2 / (((p + i) * i : ℕ) : ℚ)) := by
        push_cast; field_simp [hi0, hpi0]; ring
      rw [heq]
      have hnd : ¬ p ∣ (p + i) * i := fun h => by
        rcases hp.dvd_mul.mp h with h1 | h2
        · exact not_dvd_of_lt_prime hp hi.1 (by omega) ((Nat.dvd_add_right (dvd_refl p)).mp h1)
        · exact not_dvd_of_lt_prime hp hi.1 (by omega) h2
      exact ((PVal.of_pow_p (e := 2) hp).div_nat hp hnd).neg
  have hQu_lin : PVal p 2 ((∏ i ∈ Ico 1 u, (1 + (p : ℚ) / (i : ℚ))) - (1 + (p : ℚ) * harmh 1 (u - 1))) := by
    have h1 := PVal.prod_one_add_deg1 hp (s := Ico 1 u) (f := fun i => (p : ℚ) / (i : ℚ)) fun i hi => by
      rw [mem_Ico] at hi
      exact (PVal.of_p hp).div_nat hp (not_dvd_of_lt_prime hp hi.1 (by omega))
    have hsum : ∑ i ∈ Ico 1 u, (p : ℚ) / (i : ℚ) = (p : ℚ) * harmh 1 (u - 1) := by
      simp only [harmh, show u - 1 + 1 = u by omega, pow_one, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]
    rwa [hsum] at h1
  have hQu : PVal p 2 (Qu - (1 + (p : ℚ) * harmh 1 (u - 1))) := hQu_rep.sub_trans hp hQu_lin
  have hQu0 : PVal p 0 Qu := PVal.prod_zero hp fun i hi => by
    rw [mem_Ico] at hi
    have hnd : ¬ p ∣ p + i := fun h => not_dvd_of_lt_prime hp hi.1 (by omega) ((Nat.dvd_add_right (dvd_refl p)).mp h)
    exact (PVal.nat hp 1).add hp ((PVal.nat hp p).div_nat hp hnd)
  have hPQ : PVal p 2 (Pp * Qu - (1 + (p : ℚ) * harmh 1 (u - 1))) := by
    have h1 : PVal p 2 (Pp * Qu - Qu) := by rw [show Pp * Qu - Qu = (Pp - 1) * Qu by ring]; exact hPp.mul_zero hp hQu0
    exact h1.sub_trans hp hQu
  -- Factor 2*p/(p+u) = 2*p/(2*p - s) == -(2*p/s)*(1 + 2*p/s) (mod p^3)
  have hnds := not_dvd_of_lt_prime hp hs1 hsp
  have hndpu : ¬ p ∣ p + u := fun h => not_dvd_of_lt_prime hp hu1 hup ((Nat.dvd_add_right (dvd_refl p)).mp h)
  have hpre_diff : PVal p 3 (2 * (p : ℚ) / ((p + u : ℕ) : ℚ) + (2 * (p : ℚ) / (s : ℚ)) * (1 + 2 * (p : ℚ) / (s : ℚ))) := by
    have hs0 : (s : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpu0 : ((p + u : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpu_eq : ((p + u : ℕ) : ℚ) = 2 * (p : ℚ) - (s : ℚ) := by
      simp only [u]; rw [Nat.cast_add, Nat.cast_sub (by omega)]; ring
    have heq : 2 * (p : ℚ) / ((p + u : ℕ) : ℚ) + (2 * (p : ℚ) / (s : ℚ)) * (1 + 2 * (p : ℚ) / (s : ℚ)) =
        (8 * (p : ℚ) ^ 3) / ((((p + u) * s ^ 2 : ℕ) : ℚ)) := by
      rw [hpu_eq] at hpu0; rw [Nat.cast_mul, Nat.cast_pow, hpu_eq]; field_simp [hs0, hpu0]; ring
    rw [heq]
    have hnd : ¬ p ∣ (p + u) * s ^ 2 := fun h => by
      rcases hp.dvd_mul.mp h with h1 | h2
      · exact hndpu h1
      · exact hnds (hp.dvd_of_dvd_pow h2)
    exact ((PVal.nat hp 8).zero_mul hp (PVal.of_pow_p (e := 3) hp)).div_nat hp hnd
  -- Also harmh 1 (u - 1) - (harmh 1 (s - 1) + 1/s) in p Z_(p)
  have hhref : PVal p 1 (harmh 1 (u - 1) - (harmh 1 (s - 1) + ((s : ℚ))⁻¹)) := by
    have hstep : harmh 1 u = harmh 1 (u - 1) + ((u : ℚ))⁻¹ := by
      simp only [harmh, show u - 1 + 1 = u by omega, pow_one]; exact Finset.sum_Ico_succ_top hu1 _
    have hinv : PVal p 1 (((u : ℚ))⁻¹ + ((s : ℚ))⁻¹) := by
      have hs0 : (s : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have heq : ((u : ℚ))⁻¹ + ((s : ℚ))⁻¹ = (p : ℚ) / (((u * s : ℕ) : ℚ)) := by
        rw [Nat.cast_mul]; simp only [u]; rw [Nat.cast_sub (by omega)] at hu0 ⊢; field_simp [hs0, hu0]; ring
      rw [heq]
      have hnd : ¬ p ∣ u * s := fun h => by rcases hp.dvd_mul.mp h with h1 | h2; exact not_dvd_of_lt_prime hp hu1 hup h1; exact hnds h2
      exact (PVal.of_p hp).div_nat hp hnd
    have hrew : harmh 1 (u - 1) - (harmh 1 (s - 1) + ((s : ℚ))⁻¹) =
        (harmh 1 (p - s) - harmh 1 (s - 1)) - (((u : ℚ))⁻¹ + ((s : ℚ))⁻¹) := by simp only [u] at hstep ⊢; linarith
    rw [hrew]; exact (harmh1_reflect p s hp hp7 hs1 hsp).sub hp hinv
  have hstep1 : PVal p 3 ((2 * (p : ℚ) / ((p + u : ℕ) : ℚ)) * (Pp * Qu) -
      (2 * (p : ℚ) / ((p + u : ℕ) : ℚ)) * (1 + (p : ℚ) * harmh 1 (u - 1))) := by
    rw [← mul_sub]
    have hpre1 : PVal p 1 (2 * (p : ℚ) / ((p + u : ℕ) : ℚ)) :=
      ((PVal.nat hp 2).zero_mul hp (PVal.of_p hp)).div_nat hp hndpu
    exact hpre1.mul hp hPQ
  have hstep2 : PVal p 3 ((2 * (p : ℚ) / ((p + u : ℕ) : ℚ)) * (1 + (p : ℚ) * harmh 1 (u - 1)) +
      (2 * (p : ℚ) / (s : ℚ)) * (1 + 2 * (p : ℚ) / (s : ℚ)) * (1 + (p : ℚ) * harmh 1 (u - 1))) := by
    rw [← add_mul]
    have h1hu : PVal p 0 (1 + (p : ℚ) * harmh 1 (u - 1)) :=
      (PVal.nat hp 1).add hp ((PVal.nat hp p).mul_zero hp (harmh_pval_zero p 1 (u - 1) hp (by omega)))
    exact hpre_diff.mul_zero hp h1hu
  have hstep3 : PVal p 3 (-((2 * (p : ℚ) / (s : ℚ)) * (1 + 2 * (p : ℚ) / (s : ℚ)) * (1 + (p : ℚ) * harmh 1 (u - 1))) +
      (2 * (p : ℚ) / (s : ℚ)) * (1 + (p : ℚ) * (harmh 1 (s - 1) + 3 / (s : ℚ)))) := by
    have hrew : -((2 * (p : ℚ) / (s : ℚ)) * (1 + 2 * (p : ℚ) / (s : ℚ)) * (1 + (p : ℚ) * harmh 1 (u - 1))) +
        (2 * (p : ℚ) / (s : ℚ)) * (1 + (p : ℚ) * (harmh 1 (s - 1) + 3 / (s : ℚ))) =
        -(2 * (p : ℚ) ^ 2 / (s : ℚ)) * (harmh 1 (u - 1) - (harmh 1 (s - 1) + ((s : ℚ))⁻¹)) -
        4 * (p : ℚ) ^ 3 / (s : ℚ) ^ 2 * harmh 1 (u - 1) := by
      simp only [div_eq_mul_inv]; ring
    rw [hrew]
    have ht1 : PVal p 3 (-(2 * (p : ℚ) ^ 2 / (s : ℚ)) * (harmh 1 (u - 1) - (harmh 1 (s - 1) + ((s : ℚ))⁻¹))) :=
      (((PVal.nat hp 2).zero_mul hp (PVal.of_pow_p (e := 2) hp)).div_nat hp hnds).neg.mul hp hhref
    have ht2 : PVal p 3 (4 * (p : ℚ) ^ 3 / (s : ℚ) ^ 2 * harmh 1 (u - 1)) := by
      have h1 : PVal p 3 (4 * (p : ℚ) ^ 3 / (s : ℚ) ^ 2) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using ((PVal.nat hp 4).zero_mul hp (PVal.of_pow_p (e := 3) hp)).div_nat hp
          (fun h => hnds (hp.dvd_of_dvd_pow h))
      exact h1.mul_zero hp (harmh_pval_zero p 1 (u - 1) hp (by omega))
    exact ht1.sub hp ht2
  rw [hex']
  have hcomb := (hstep1.add hp hstep2).add hp hstep3
  convert hcomb using 1; ring

/-- Reindexing: sum_{a in Ico 1 p} sum_{b in Ico 1 (p - a)} f a b = sum_{s in Ico 1 p} sum_{a in Ico 1 s} f a (s - a). -/
private lemma sum_lt_p_eq_sum_s (p : ℕ) (f : ℕ → ℕ → ℚ) :
    ∑ a ∈ Ico 1 p, ∑ b ∈ Ico 1 (p - a), f a b =
      ∑ s ∈ Ico 1 p, ∑ a ∈ Ico 1 s, f a (s - a) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij (fun x _ => (⟨x.1 + x.2, x.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro x hx; rw [mem_sigma, mem_Ico, mem_Ico] at hx; rw [mem_sigma, mem_Ico, mem_Ico]; dsimp; omega
  · intro x₁ hx₁ x₂ hx₂ heq
    rcases x₁ with ⟨a₁, b₁⟩; rcases x₂ with ⟨a₂, b₂⟩
    dsimp at heq
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
    exact Sigma.ext heq.2 (heq_of_eq (by dsimp; omega))
  · rintro ⟨s, a⟩ hy; rw [mem_sigma, mem_Ico, mem_Ico] at hy; dsimp at hy
    refine ⟨⟨a, s - a⟩, ?_, ?_⟩
    · rw [mem_sigma, mem_Ico, mem_Ico]; dsimp; omega
    · exact Sigma.ext (by dsimp; omega) (heq_of_eq rfl)
  · intro x _; dsimp; simp only [Nat.add_sub_cancel_left]

private lemma pf_inner_1 (s : ℕ) :
    ∑ a ∈ Ico 1 s, (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ)))⁻¹ =
      2 * harmh 1 (s - 1) / (s : ℚ) ^ 2 := by
  by_cases hs : s ≤ 1
  · have : Ico 1 s = ∅ := Finset.Ico_eq_empty (by omega)
    have : harmh 1 (s - 1) = 0 := by simp [harmh, show s - 1 = 0 by omega]
    simp_all
  · have hs1 : 1 ≤ s := by omega
    have hsplit : ∑ a ∈ Ico 1 s, (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ)))⁻¹ =
        ((s : ℚ) ^ 2)⁻¹ * ((∑ a ∈ Ico 1 s, ((a : ℚ))⁻¹) + ∑ a ∈ Ico 1 s, (((s - a : ℕ) : ℚ))⁻¹) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [mem_Ico] at ha
      have ha0 : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hsa0 : ((s - a : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hs0 : (s : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [Nat.cast_sub (by omega)] at hsa0 ⊢; field_simp [ha0, hsa0, hs0]; ring
    rw [hsplit, sum_Ico_reflect s (fun a => ((a : ℚ))⁻¹)]
    have hh : ∑ a ∈ Ico 1 s, ((a : ℚ))⁻¹ = harmh 1 (s - 1) := by
      simp only [harmh, show s - 1 + 1 = s by omega, pow_one]
    rw [hh, div_eq_mul_inv]; ring

private lemma pf_sum_1 (p : ℕ) :
    ∑ s ∈ Ico 1 p, ∑ a ∈ Ico 1 s, (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ)))⁻¹ = 2 * S12 p := by
  simp only [pf_inner_1, S12, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => by ring

private lemma pf_sum_2 (p : ℕ) :
    ∑ s ∈ Ico 1 p, ∑ a ∈ Ico 1 s, harmh 1 (s - 1) * (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ)))⁻¹ =
      2 * S112 p := by
  rw [S112, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_sum, pf_inner_1]; ring

private lemma pf_sum_3 (p : ℕ) :
    ∑ s ∈ Ico 1 p, ∑ a ∈ Ico 1 s, ((s : ℚ))⁻¹ * (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ)))⁻¹ =
      2 * S13 p := by
  rw [S13, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.mul_sum, pf_inner_1]; simp only [div_eq_mul_inv]; ring

private lemma pf_sum_4 (p : ℕ) :
    ∑ s ∈ Ico 1 p, ∑ a ∈ Ico 1 s,
        (((a : ℚ))⁻¹ + (((s - a : ℕ) : ℚ))⁻¹) * (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ)))⁻¹ =
      2 * S22 p + 4 * S13 p := by
  have hinner : ∀ s ∈ Ico 1 p,
      ∑ a ∈ Ico 1 s, (((a : ℚ))⁻¹ + (((s - a : ℕ) : ℚ))⁻¹) * (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ)))⁻¹ =
        2 * (harmh 2 (s - 1) / (s : ℚ) ^ 2) + 4 * (harmh 1 (s - 1) / (s : ℚ) ^ 3) := by
    intro s hs; rw [mem_Ico] at hs
    by_cases hs1 : s = 1
    · subst hs1; simp [harmh]
    · have h2 : ∑ a ∈ Ico 1 s, (((a : ℚ))⁻¹ + (((s - a : ℕ) : ℚ))⁻¹) * (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ)))⁻¹ =
          2 * ∑ a ∈ Ico 1 s, (((s : ℚ) * (a : ℚ) ^ 2 * ((s - a : ℕ) : ℚ)))⁻¹ := by
        have hsp : ∑ a ∈ Ico 1 s, (((a : ℚ))⁻¹ + (((s - a : ℕ) : ℚ))⁻¹) * (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ)))⁻¹ =
            (∑ a ∈ Ico 1 s, (((s : ℚ) * (a : ℚ) ^ 2 * ((s - a : ℕ) : ℚ)))⁻¹) +
            ∑ a ∈ Ico 1 s, (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ) ^ 2))⁻¹ := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => by simp only [mul_inv, sq]; ring
        have href : ∑ a ∈ Ico 1 s, (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ) ^ 2))⁻¹ =
            ∑ a ∈ Ico 1 s, (((s : ℚ) * (a : ℚ) ^ 2 * ((s - a : ℕ) : ℚ)))⁻¹ := by
          rw [← sum_Ico_reflect s (fun a => (((s : ℚ) * (a : ℚ) ^ 2 * ((s - a : ℕ) : ℚ)))⁻¹)]
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [mem_Ico] at ha; rw [show s - (s - a) = a by omega]; ring_nf
        rw [hsp, href]; ring
      rw [h2]
      have hpf : ∑ a ∈ Ico 1 s, (((s : ℚ) * (a : ℚ) ^ 2 * ((s - a : ℕ) : ℚ)))⁻¹ =
          harmh 2 (s - 1) / (s : ℚ) ^ 2 + 2 * harmh 1 (s - 1) / (s : ℚ) ^ 3 := by
        have hpart : ∑ a ∈ Ico 1 s, (((s : ℚ) * (a : ℚ) ^ 2 * ((s - a : ℕ) : ℚ)))⁻¹ =
            ((s : ℚ) ^ 2)⁻¹ * (∑ a ∈ Ico 1 s, ((a : ℚ) ^ 2)⁻¹) +
            ((s : ℚ) ^ 3)⁻¹ * ((∑ a ∈ Ico 1 s, ((a : ℚ))⁻¹) + ∑ a ∈ Ico 1 s, (((s - a : ℕ) : ℚ))⁻¹) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [mem_Ico] at ha
          have ha0 : (a : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have hsa0 : ((s - a : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have hs0 : (s : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          rw [Nat.cast_sub (by omega)] at hsa0 ⊢; field_simp [ha0, hsa0, hs0]; ring
        rw [hpart, sum_Ico_reflect s (fun a => ((a : ℚ))⁻¹)]
        have hh1 : ∑ a ∈ Ico 1 s, ((a : ℚ))⁻¹ = harmh 1 (s - 1) := by
          simp only [harmh, show s - 1 + 1 = s by omega, pow_one]
        have hh2 : ∑ a ∈ Ico 1 s, ((a : ℚ) ^ 2)⁻¹ = harmh 2 (s - 1) := by
          simp only [harmh, show s - 1 + 1 = s by omega]
        rw [hh1, hh2, div_eq_mul_inv, div_eq_mul_inv]; ring
      rw [hpf]; ring
  rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rfl

/-- E5 Bucket 1 (b1): 3 * sum (-1)^j C(p-1+j, j) c(p-1, j) == -15 * p * H_1 (mod p^5). -/
private lemma e5_b1 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 5 (3 * (∑ j ∈ Ico 1 p, (-1 : ℚ) ^ j * (Nat.choose (p - 1 + j) j : ℚ) * (cJ (p - 1) j : ℚ)) +
      15 * (p : ℚ) * harmH p 1) := by
  have hnd2 : ¬ p ∣ 2 := not_dvd_of_lt_prime hp (by decide) (by omega)
  have ⟨hS112, hS12⟩ := S112_and_S12_system p hp hp7
  have hS22 := S22_mod_p p hp hp7
  have hS13 := S13_mod_p p hp hp7
  have hH3 := harmH_three_mod_p2 p hp hp7
  have hterm : PVal p 5 ((∑ j ∈ Ico 1 p, (-1 : ℚ) ^ j * (Nat.choose (p - 1 + j) j : ℚ) * (cJ (p - 1) j : ℚ)) -
      ((p : ℚ) ^ 2 * harmH p 2 + (p : ℚ) ^ 3 * (S12 p - harmH p 3) +
        (p : ℚ) ^ 4 * (S112 p / 2 - 3 * S22 p / 2 - S13 p))) := by
    have hrew : (∑ j ∈ Ico 1 p, (-1 : ℚ) ^ j * (Nat.choose (p - 1 + j) j : ℚ) * (cJ (p - 1) j : ℚ)) -
        ((p : ℚ) ^ 2 * harmH p 2 + (p : ℚ) ^ 3 * (S12 p - harmH p 3) +
          (p : ℚ) ^ 4 * (S112 p / 2 - 3 * S22 p / 2 - S13 p)) =
        ∑ j ∈ Ico 1 p, (((Nat.choose (p - 1 + j) j : ℚ) * ((-1 : ℚ) ^ j * (cJ (p - 1) j : ℚ))) -
          ((p : ℚ) ^ 2 / (j : ℚ) ^ 2) *
            (1 + (p : ℚ) * (harmh 1 (j - 1) - ((j : ℚ))⁻¹) +
              (p : ℚ) ^ 2 * (((harmh 1 (j - 1)) ^ 2 - 3 * harmh 2 (j - 1)) / 2 - harmh 1 (j - 1) / (j : ℚ)))) := by
      simp only [harmH, S12, S112, S22, S13, mul_sub, mul_add, Finset.mul_sum, Finset.sum_div,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => by simp only [div_eq_mul_inv]; ring
    rw [hrew]
    refine PVal.sum hp fun j hj => ?_
    rw [mem_Ico] at hj
    have hndj := not_dvd_of_lt_prime hp hj.1 hj.2
    have hA_eq := choose_pm1_add_exact p j hp hj.1 hj.2
    have hA_deg2 : PVal p 3 ((∏ i ∈ Ico 1 j, (1 + (p : ℚ) / (i : ℚ) + 0)) -
        (1 + (∑ i ∈ Ico 1 j, (p : ℚ) / (i : ℚ)) + (∑ i ∈ Ico 1 j, (0 : ℚ)) +
          (((∑ i ∈ Ico 1 j, (p : ℚ) / (i : ℚ)) ^ 2 - ∑ i ∈ Ico 1 j, ((p : ℚ) / (i : ℚ)) ^ 2) / 2))) :=
      PVal.prod_one_add_deg2 hp hnd2
        (fun i hi => by rw [mem_Ico] at hi; exact (PVal.of_p hp).div_nat hp (not_dvd_of_lt_prime hp hi.1 (by omega)))
        (fun _ _ => PVal.zero hp)
    set A := (Nat.choose (p - 1 + j) j : ℚ)
    set A' := ((p : ℚ) / (j : ℚ)) * (1 + (p : ℚ) * harmh 1 (j - 1) + (p : ℚ) ^ 2 * ((harmh 1 (j - 1)) ^ 2 - harmh 2 (j - 1)) / 2)
    have hAA' : PVal p 4 (A - A') := by
      have hS1 : ∑ i ∈ Ico 1 j, (p : ℚ) / (i : ℚ) = (p : ℚ) * harmh 1 (j - 1) := by
        simp only [harmh, show j - 1 + 1 = j by omega, pow_one, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]
      have hS2 : ∑ i ∈ Ico 1 j, ((p : ℚ) / (i : ℚ)) ^ 2 = (p : ℚ) ^ 2 * harmh 2 (j - 1) := by
        simp only [harmh, show j - 1 + 1 = j by omega, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by rw [div_pow, div_eq_mul_inv]
      have hprod_eq : ∏ i ∈ Ico 1 j, (1 + (p : ℚ) / (i : ℚ) + 0) = ∏ i ∈ Ico 1 j, (1 + (p : ℚ) / (i : ℚ)) :=
        Finset.prod_congr rfl fun i _ => by ring
      rw [hprod_eq, hS1, hS2, Finset.sum_const_zero] at hA_deg2
      have h1 : PVal p 1 ((p : ℚ) / (j : ℚ)) := (PVal.of_p hp).div_nat hp hndj
      have hmul := h1.mul hp hA_deg2
      convert hmul using 1; simp only [A, A', hA_eq]; ring
    set B := (-1 : ℚ) ^ j * (cJ (p - 1) j : ℚ)
    set B' := ((p : ℚ) / (j : ℚ) - (p : ℚ) ^ 2 / (j : ℚ) ^ 2) * (1 - (p : ℚ) ^ 2 * harmh 2 (j - 1))
    have hBB' : PVal p 5 (B - B') := cJ_pm1_mod_p5 p j hp hp7 hj.1 hj.2
    have hA1 : PVal p 1 A := by
      have : PVal p 1 ((p : ℚ) / (j : ℚ)) := (PVal.of_p hp).div_nat hp hndj
      have hP0 : PVal p 0 (∏ i ∈ Ico 1 j, (1 + (p : ℚ) / (i : ℚ))) := PVal.prod_zero hp fun i hi => by
        rw [mem_Ico] at hi; exact (PVal.nat hp 1).add hp ((PVal.nat hp p).div_nat hp (not_dvd_of_lt_prime hp hi.1 (by omega)))
      simpa only [A, hA_eq] using this.mul_zero hp hP0
    have hp2_0 : PVal p 0 ((p : ℚ) ^ 2) := by simpa using (PVal.nat hp p).pow hp 2
    have hB'1 : PVal p 1 B' := by
      have h1 : PVal p 1 ((p : ℚ) / (j : ℚ) - (p : ℚ) ^ 2 / (j : ℚ) ^ 2) := by
        have h2' : PVal p 2 ((p : ℚ) ^ 2 / (j : ℚ) ^ 2) := by
          simpa only [Nat.cast_pow] using (PVal.of_pow_p (e := 2) hp).div_nat hp (fun h => hndj (hp.dvd_of_dvd_pow h))
        exact ((PVal.of_p hp).div_nat hp hndj).sub hp (h2'.mono (by decide))
      have h2 : PVal p 0 (1 - (p : ℚ) ^ 2 * harmh 2 (j - 1)) :=
        (PVal.nat hp 1).sub hp (hp2_0.mul_zero hp (harmh_pval_zero p 2 (j - 1) hp (by omega)))
      exact h1.mul_zero hp h2
    have hAB : PVal p 5 (A * B - A' * B') := by
      rw [show A * B - A' * B' = A * (B - B') + (A - A') * B' by ring]
      exact ((hA1.mul hp hBB').mono (by decide)).add hp (hAA'.mul hp hB'1)
    have htail : PVal p 5 (A' * B' - ((p : ℚ) ^ 2 / (j : ℚ) ^ 2) *
        (1 + (p : ℚ) * (harmh 1 (j - 1) - ((j : ℚ))⁻¹) +
          (p : ℚ) ^ 2 * (((harmh 1 (j - 1)) ^ 2 - 3 * harmh 2 (j - 1)) / 2 - harmh 1 (j - 1) / (j : ℚ)))) := by
      set h1 := harmh 1 (j - 1)
      set h2 := harmh 2 (j - 1)
      have hh1 : PVal p 0 h1 := harmh_pval_zero p 1 (j - 1) hp (by omega)
      have hh2 : PVal p 0 h2 := harmh_pval_zero p 2 (j - 1) hp (by omega)
      have hjinv : PVal p 0 (((j : ℚ))⁻¹) := PVal.inv_nat hndj
      have hrew : A' * B' - ((p : ℚ) ^ 2 / (j : ℚ) ^ 2) *
          (1 + (p : ℚ) * (h1 - ((j : ℚ))⁻¹) + (p : ℚ) ^ 2 * ((h1 ^ 2 - 3 * h2) / 2 - h1 / (j : ℚ))) =
          (p : ℚ) ^ 5 * (((j : ℚ))⁻¹ ^ 2 *
            (-((j : ℚ))⁻¹ * (h1 ^ 2 - h2) / 2 - h2 * (h1 - ((j : ℚ))⁻¹) -
              (p : ℚ) * h2 * ((h1 ^ 2 - h2) / 2 - h1 * ((j : ℚ))⁻¹) +
              (p : ℚ) ^ 2 * ((j : ℚ))⁻¹ * h2 * (h1 ^ 2 - h2) / 2)) := by
        simp only [A', B', div_eq_mul_inv]; ring
      rw [hrew]
      have hh1_2 : PVal p 0 (h1 ^ 2) := by simpa using hh1.pow hp 2
      have he2 : PVal p 0 ((h1 ^ 2 - h2) / 2) := by
        simpa only [Nat.cast_ofNat] using (hh1_2.sub hp hh2).div_nat hp hnd2
      have hc0 : PVal p 0 (((j : ℚ))⁻¹ ^ 2 *
          (-((j : ℚ))⁻¹ * (h1 ^ 2 - h2) / 2 - h2 * (h1 - ((j : ℚ))⁻¹) -
            (p : ℚ) * h2 * ((h1 ^ 2 - h2) / 2 - h1 * ((j : ℚ))⁻¹) +
            (p : ℚ) ^ 2 * ((j : ℚ))⁻¹ * h2 * (h1 ^ 2 - h2) / 2)) := by
        have ht1 : PVal p 0 (-((j : ℚ))⁻¹ * (h1 ^ 2 - h2) / 2) := by
          have : -((j : ℚ))⁻¹ * (h1 ^ 2 - h2) / 2 = -((j : ℚ))⁻¹ * ((h1 ^ 2 - h2) / 2) := by ring
          rw [this]; exact hjinv.neg.mul_zero hp he2
        have ht2 : PVal p 0 (h2 * (h1 - ((j : ℚ))⁻¹)) := hh2.mul_zero hp (hh1.sub hp hjinv)
        have ht3 : PVal p 0 ((p : ℚ) * h2 * ((h1 ^ 2 - h2) / 2 - h1 * ((j : ℚ))⁻¹)) :=
          ((PVal.nat hp p).mul_zero hp hh2).mul_zero hp (he2.sub hp (hh1.mul_zero hp hjinv))
        have ht4 : PVal p 0 ((p : ℚ) ^ 2 * ((j : ℚ))⁻¹ * h2 * (h1 ^ 2 - h2) / 2) := by
          have : (p : ℚ) ^ 2 * ((j : ℚ))⁻¹ * h2 * (h1 ^ 2 - h2) / 2 =
              ((p : ℚ) ^ 2 * ((j : ℚ))⁻¹ * h2) * ((h1 ^ 2 - h2) / 2) := by ring
          rw [this]
          exact ((hp2_0.mul_zero hp hjinv).mul_zero hp hh2).mul_zero hp he2
        exact (by simpa using hjinv.pow hp 2 : PVal p 0 _).mul_zero hp (((ht1.sub hp ht2).sub hp ht3).add hp ht4)
      exact (PVal.of_pow_p (e := 5) hp).mul_zero hp hc0
    exact hAB.sub_trans hp htail
  have hH3p : PVal p 5 ((p : ℚ) ^ 3 * harmH p 3) := (PVal.of_pow_p (e := 3) hp).mul hp hH3
  have h4s : PVal p 5 ((p : ℚ) ^ 4 * (S112 p / 2 - 3 * S22 p / 2 - S13 p)) := by
    have ha : PVal p 1 (S112 p / 2) := by simpa only [Nat.cast_ofNat] using hS112.div_nat hp hnd2
    have hb : PVal p 1 (3 * S22 p / 2) := by simpa only [Nat.cast_ofNat] using ((PVal.nat hp 3).zero_mul hp hS22).div_nat hp hnd2
    exact (PVal.of_pow_p (e := 4) hp).mul hp ((ha.sub hp hb).sub hp hS13)
  have h1 := (((hterm.add hp (p2_harmH2_mod_p5 p hp hp7)).add hp hS12).sub hp hH3p).add hp h4s
  have h3 := (PVal.nat hp 3).zero_mul hp h1
  convert h3 using 1; ring

/-- E5 Bucket 2a (b2_eq): 3 * sum (-1)^p C(2p-1, p) c(p-1, j) c(p-1, p-j) == 6 * p * H_1 (mod p^5). -/
private lemma e5_b2_eq (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 5 (3 * (∑ j ∈ Ico 1 p, (-1 : ℚ) ^ p * (Nat.choose (2 * p - 1) p : ℚ) *
      (cJ (p - 1) j : ℚ) * (cJ (p - 1) (p - j) : ℚ)) - 6 * (p : ℚ) * harmH p 1) := by
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  have h2p1 : PVal p 3 ((Nat.choose (2 * p - 1) p : ℚ) - 1) := by
    have h := kazandzidis_pred_add p 1 1 hp (by omega) (by decide) (by decide)
    have hidx : 1 * p - 1 + p * 1 = 2 * p - 1 := by omega
    rw [hidx, mul_one] at h; simpa using h.mono (by omega : 3 ≤ 3 + 2 * vp p 1)
  have hsum_id : ∑ j ∈ Ico 1 p, (p : ℚ) ^ 2 / ((j : ℚ) * ((p - j : ℕ) : ℚ)) = 2 * (p : ℚ) * harmH p 1 := by
    have h1 : ∑ j ∈ Ico 1 p, (p : ℚ) ^ 2 / ((j : ℚ) * ((p - j : ℕ) : ℚ)) =
        (p : ℚ) * ((∑ j ∈ Ico 1 p, ((j : ℚ))⁻¹) + ∑ j ∈ Ico 1 p, (((p - j : ℕ) : ℚ))⁻¹) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [mem_Ico] at hj
      have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hpj0 : ((p - j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [Nat.cast_sub (by omega)] at hpj0 ⊢; field_simp [hj0, hpj0]; ring
    rw [h1, sum_Ico_reflect p (fun j => ((j : ℚ))⁻¹)]
    simp only [harmH, pow_one]; ring
  have hterm : PVal p 5 ((∑ j ∈ Ico 1 p, (-1 : ℚ) ^ p * (Nat.choose (2 * p - 1) p : ℚ) *
        (cJ (p - 1) j : ℚ) * (cJ (p - 1) (p - j) : ℚ)) -
      (2 * (p : ℚ) * harmH p 1 - (p : ℚ) ^ 4 * harmH p 4)) := by
    rw [← hsum_id, harmH, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine PVal.sum hp fun j hj => ?_
    rw [mem_Ico] at hj
    have hndj := not_dvd_of_lt_prime hp hj.1 hj.2
    have hndpj := not_dvd_of_lt_prime hp (by omega : 1 ≤ p - j) (by omega : p - j < p)
    have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpj0 : ((p - j : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1 := cJ_pm1_exact p j hp hp7 hj.1 hj.2
    have h2 := cJ_pm1_exact p (p - j) hp hp7 (by omega) (by omega)
    set Q1 := ∏ i ∈ Ico 1 j, (1 - (p : ℚ) ^ 2 / (i : ℚ) ^ 2)
    set Q2 := ∏ i ∈ Ico 1 (p - j), (1 - (p : ℚ) ^ 2 / (i : ℚ) ^ 2)
    have hprod_c : (-1 : ℚ) ^ p * (cJ (p - 1) j : ℚ) * (cJ (p - 1) (p - j) : ℚ) =
        ((p : ℚ) ^ 2 / ((j : ℚ) * ((p - j : ℕ) : ℚ))) * (Q1 * Q2) := by
      rw [h1, h2]
      have hs : (-1 : ℚ) ^ p * (-1 : ℚ) ^ j * (-1 : ℚ) ^ (p - j) = 1 := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_of_le (by omega), ← pow_add, ← two_mul, pow_mul]; norm_num
      have hrat : ((p : ℚ) * ((j : ℚ) - (p : ℚ)) / (j : ℚ) ^ 2) *
          ((p : ℚ) * (((p - j : ℕ) : ℚ) - (p : ℚ)) / ((p - j : ℕ) : ℚ) ^ 2) =
          (p : ℚ) ^ 2 / ((j : ℚ) * ((p - j : ℕ) : ℚ)) := by
        rw [Nat.cast_sub (by omega)] at hpj0 ⊢; field_simp [hj0, hpj0]; ring
      calc (-1 : ℚ) ^ p * ((-1 : ℚ) ^ j * ((p : ℚ) * ((j : ℚ) - (p : ℚ)) / (j : ℚ) ^ 2) * Q1) *
            ((-1 : ℚ) ^ (p - j) * ((p : ℚ) * (((p - j : ℕ) : ℚ) - (p : ℚ)) / ((p - j : ℕ) : ℚ) ^ 2) * Q2)
          = ((-1 : ℚ) ^ p * (-1 : ℚ) ^ j * (-1 : ℚ) ^ (p - j)) *
            (((p : ℚ) * ((j : ℚ) - (p : ℚ)) / (j : ℚ) ^ 2) *
              ((p : ℚ) * (((p - j : ℕ) : ℚ) - (p : ℚ)) / ((p - j : ℕ) : ℚ) ^ 2)) * (Q1 * Q2) := by ring
        _ = _ := by rw [hs, one_mul, hrat]
    have hQ1 : PVal p 4 (Q1 - (1 - (p : ℚ) ^ 2 * harmh 2 (j - 1))) := by
      have h := PVal.prod_one_add_deg1_sq hp (s := Ico 1 j) (f := fun i => -((p : ℚ) ^ 2 / (i : ℚ) ^ 2)) fun i hi => by
        rw [mem_Ico] at hi; simpa only [Nat.cast_pow] using ((PVal.of_pow_p (e := 2) hp).div_nat hp
          (fun h => not_dvd_of_lt_prime hp hi.1 (by omega) (hp.dvd_of_dvd_pow h))).neg
      convert h using 2
      · exact Finset.prod_congr rfl fun i _ => by ring
      · simp only [harmh, show j - 1 + 1 = j by omega, Finset.mul_sum, Finset.sum_neg_distrib, div_eq_mul_inv]; ring
    have hQ2 : PVal p 4 (Q2 - (1 - (p : ℚ) ^ 2 * harmh 2 (p - j - 1))) := by
      have h := PVal.prod_one_add_deg1_sq hp (s := Ico 1 (p - j)) (f := fun i => -((p : ℚ) ^ 2 / (i : ℚ) ^ 2)) fun i hi => by
        rw [mem_Ico] at hi; simpa only [Nat.cast_pow] using ((PVal.of_pow_p (e := 2) hp).div_nat hp
          (fun h => not_dvd_of_lt_prime hp hi.1 (by omega) (hp.dvd_of_dvd_pow h))).neg
      convert h using 2
      · exact Finset.prod_congr rfl fun i _ => by ring
      · simp only [harmh, show p - j - 1 + 1 = p - j by omega, Finset.mul_sum, Finset.sum_neg_distrib, div_eq_mul_inv]; ring
    have hp2_0 : PVal p 0 ((p : ℚ) ^ 2) := by simpa using (PVal.nat hp p).pow hp 2
    have hQ1_0 : PVal p 0 Q1 := PVal.prod_zero hp fun i hi => by
      rw [mem_Ico] at hi
      have hpi : PVal p 0 ((p : ℚ) ^ 2 / (i : ℚ) ^ 2) := by
        simpa only [Nat.cast_pow] using hp2_0.div_nat hp (d := i ^ 2)
          (fun h => not_dvd_of_lt_prime hp hi.1 (by omega) (hp.dvd_of_dvd_pow h))
      exact (PVal.nat hp 1).sub hp hpi
    have hQ2_0 : PVal p 0 Q2 := PVal.prod_zero hp fun i hi => by
      rw [mem_Ico] at hi
      have hpi : PVal p 0 ((p : ℚ) ^ 2 / (i : ℚ) ^ 2) := by
        simpa only [Nat.cast_pow] using hp2_0.div_nat hp (d := i ^ 2)
          (fun h => not_dvd_of_lt_prime hp hi.1 (by omega) (hp.dvd_of_dvd_pow h))
      exact (PVal.nat hp 1).sub hp hpi
    have hQ12 : PVal p 3 (Q1 * Q2 - (1 + (p : ℚ) ^ 2 / (j : ℚ) ^ 2)) := by
      have h1 : PVal p 3 (Q1 * Q2 - (1 - (p : ℚ) ^ 2 * harmh 2 (j - 1)) * (1 - (p : ℚ) ^ 2 * harmh 2 (p - j - 1))) := by
        rw [show Q1 * Q2 - (1 - (p : ℚ) ^ 2 * harmh 2 (j - 1)) * (1 - (p : ℚ) ^ 2 * harmh 2 (p - j - 1)) =
            Q1 * (Q2 - (1 - (p : ℚ) ^ 2 * harmh 2 (p - j - 1))) +
            (Q1 - (1 - (p : ℚ) ^ 2 * harmh 2 (j - 1))) * (1 - (p : ℚ) ^ 2 * harmh 2 (p - j - 1)) by ring]
        have hf2 : PVal p 0 (1 - (p : ℚ) ^ 2 * harmh 2 (p - j - 1)) :=
          (PVal.nat hp 1).sub hp (hp2_0.mul_zero hp (harmh_pval_zero p 2 (p - j - 1) hp (by omega)))
        exact ((hQ1_0.zero_mul hp hQ2).mono (by decide)).add hp ((hQ1.mul_zero hp hf2).mono (by decide))
      have hh2_sum : PVal p 1 (harmh 2 (j - 1) + harmh 2 (p - j - 1) + ((j : ℚ) ^ 2)⁻¹) := by
        have hstep : harmh 2 (p - j) = harmh 2 (p - j - 1) + (((p - j : ℕ) : ℚ) ^ 2)⁻¹ := by
          simp only [harmh, show p - j - 1 + 1 = p - j by omega]; exact Finset.sum_Ico_succ_top (by omega) _
        have hinv := inv_sub_inv_pval hp (fun h => hndj (hp.dvd_of_dvd_pow h))
          (fun h => hndpj (hp.dvd_of_dvd_pow h)) (by
            have heq : (((p - j) ^ 2 : ℕ) : ℤ) - ((j ^ 2 : ℕ) : ℤ) = (p : ℤ) * ((p : ℤ) - 2 * (j : ℤ)) := by
              push_cast; rw [Nat.cast_sub (by omega)]; ring
            exact Int.modEq_iff_dvd.mpr ⟨(p : ℤ) - 2 * (j : ℤ), heq⟩)
        have hrew : harmh 2 (j - 1) + harmh 2 (p - j - 1) + ((j : ℚ) ^ 2)⁻¹ =
            (harmh 2 (p - j) + harmh 2 (j - 1)) + (((j ^ 2 : ℕ) : ℚ)⁻¹ - (((p - j) ^ 2 : ℕ) : ℚ)⁻¹) := by
          push_cast; linarith
        rw [hrew]; exact (harmh2_reflect p j hp hp7 hj.1 hj.2).add hp hinv
      have h2 : PVal p 3 ((1 - (p : ℚ) ^ 2 * harmh 2 (j - 1)) * (1 - (p : ℚ) ^ 2 * harmh 2 (p - j - 1)) -
          (1 + (p : ℚ) ^ 2 / (j : ℚ) ^ 2)) := by
        have hrew : (1 - (p : ℚ) ^ 2 * harmh 2 (j - 1)) * (1 - (p : ℚ) ^ 2 * harmh 2 (p - j - 1)) -
            (1 + (p : ℚ) ^ 2 / (j : ℚ) ^ 2) =
            -(p : ℚ) ^ 2 * (harmh 2 (j - 1) + harmh 2 (p - j - 1) + ((j : ℚ) ^ 2)⁻¹) +
            (p : ℚ) ^ 4 * (harmh 2 (j - 1) * harmh 2 (p - j - 1)) := by simp only [div_eq_mul_inv]; ring
        rw [hrew]
        exact ((PVal.of_pow_p (e := 2) hp).neg.mul hp hh2_sum).add hp
          (((PVal.of_pow_p (e := 4) hp).mul_zero hp ((harmh_pval_zero p 2 (j - 1) hp (by omega)).mul_zero hp
            (harmh_pval_zero p 2 (p - j - 1) hp (by omega)))).mono (by decide))
      exact h1.sub_trans hp h2
    have hbase : PVal p 2 ((p : ℚ) ^ 2 / ((j : ℚ) * ((p - j : ℕ) : ℚ))) := by
      have hnd : ¬ p ∣ j * (p - j) := fun h => by rcases hp.dvd_mul.mp h with h1 | h2; exact hndj h1; exact hndpj h2
      simpa only [Nat.cast_mul] using (PVal.of_pow_p (e := 2) hp).div_nat hp hnd
    have hQ0 : PVal p 0 (Q1 * Q2) := hQ1_0.mul_zero hp hQ2_0
    have hmain_eq : (-1 : ℚ) ^ p * (Nat.choose (2 * p - 1) p : ℚ) * (cJ (p - 1) j : ℚ) * (cJ (p - 1) (p - j) : ℚ) -
        ((p : ℚ) ^ 2 / ((j : ℚ) * ((p - j : ℕ) : ℚ)) - (p : ℚ) ^ 4 * ((j : ℚ) ^ 4)⁻¹) =
        ((Nat.choose (2 * p - 1) p : ℚ) - 1) * (((p : ℚ) ^ 2 / ((j : ℚ) * ((p - j : ℕ) : ℚ))) * (Q1 * Q2)) +
        ((p : ℚ) ^ 2 / ((j : ℚ) * ((p - j : ℕ) : ℚ))) * (Q1 * Q2 - (1 + (p : ℚ) ^ 2 / (j : ℚ) ^ 2)) +
        (p : ℚ) ^ 5 / (((j ^ 4 * (p - j) : ℕ) : ℚ)) := by
      have hcomm : (-1 : ℚ) ^ p * (Nat.choose (2 * p - 1) p : ℚ) * (cJ (p - 1) j : ℚ) * (cJ (p - 1) (p - j) : ℚ) =
          (Nat.choose (2 * p - 1) p : ℚ) * ((-1 : ℚ) ^ p * (cJ (p - 1) j : ℚ) * (cJ (p - 1) (p - j) : ℚ)) := by ring
      rw [hcomm, hprod_c]
      push_cast; rw [Nat.cast_sub (by omega)] at hpj0 ⊢; field_simp [hj0, hpj0]; ring
    rw [hmain_eq]
    have htail : PVal p 5 ((p : ℚ) ^ 5 / (((j ^ 4 * (p - j) : ℕ) : ℚ))) := by
      have hnd : ¬ p ∣ j ^ 4 * (p - j) := fun h => by
        rcases hp.dvd_mul.mp h with h1 | h2
        · exact hndj (hp.dvd_of_dvd_pow h1)
        · exact hndpj h2
      exact (PVal.of_pow_p (e := 5) hp).div_nat hp hnd
    exact ((h2p1.mul hp (hbase.mul_zero hp hQ0)).add hp (hbase.mul hp hQ12)).add hp htail
  have hH4p : PVal p 5 ((p : ℚ) ^ 4 * harmH p 4) := (PVal.of_pow_p (e := 4) hp).mul hp (harmH_four_mod_p p hp hp7)
  have h3 := (PVal.nat hp 3).zero_mul hp (hterm.sub hp hH4p)
  convert h3 using 1; ring

/-- E5 Bucket 2b (b2_lt): 3 * sum_{j1+j2 < p} ... == -18 * p * H_1 (mod p^5). -/
private lemma e5_b2_lt (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 5 (3 * (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁),
      (-1 : ℚ) ^ (j₁ + j₂) * (Nat.choose (p - 1 + (j₁ + j₂)) (j₁ + j₂) : ℚ) *
        (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ)) + 18 * (p : ℚ) * harmH p 1) := by
  have ⟨hS112, hS12⟩ := S112_and_S12_system p hp hp7
  have hS22 := S22_mod_p p hp hp7
  have hS13 := S13_mod_p p hp hp7
  rw [sum_lt_p_eq_sum_s p]
  have hterm : PVal p 5 ((∑ s ∈ Ico 1 p, ∑ a ∈ Ico 1 s,
        (-1 : ℚ) ^ (a + (s - a)) * (Nat.choose (p - 1 + (a + (s - a))) (a + (s - a)) : ℚ) *
          (cJ (p - 1) a : ℚ) * (cJ (p - 1) (s - a) : ℚ)) -
      ((p : ℚ) ^ 3 * (2 * S12 p) + (p : ℚ) ^ 4 * (2 * S112 p - (2 * S22 p + 4 * S13 p)))) := by
    rw [← pf_sum_1 p, ← pf_sum_2 p, ← pf_sum_4 p]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine PVal.sum hp fun s hs => PVal.sum hp fun a ha => ?_
    rw [mem_Ico] at hs ha
    have has : a + (s - a) = s := by omega
    rw [has]
    have hnds := not_dvd_of_lt_prime hp hs.1 hs.2
    have hnda := not_dvd_of_lt_prime hp ha.1 (by omega)
    have hndb := not_dvd_of_lt_prime hp (by omega : 1 ≤ s - a) (by omega : s - a < p)
    set A := (Nat.choose (p - 1 + s) s : ℚ)
    set A' := ((p : ℚ) / (s : ℚ)) * (1 + (p : ℚ) * harmh 1 (s - 1))
    set B1 := (-1 : ℚ) ^ a * (cJ (p - 1) a : ℚ)
    set B1' := ((p : ℚ) / (a : ℚ)) * (1 - (p : ℚ) / (a : ℚ))
    set B2 := (-1 : ℚ) ^ (s - a) * (cJ (p - 1) (s - a) : ℚ)
    set B2' := ((p : ℚ) / ((s - a : ℕ) : ℚ)) * (1 - (p : ℚ) / ((s - a : ℕ) : ℚ))
    have hAA' : PVal p 3 (A - A') := by
      have hex := choose_pm1_add_exact p s hp hs.1 hs.2
      have hdeg1 := PVal.prod_one_add_deg1 hp (s := Ico 1 s) (f := fun i => (p : ℚ) / (i : ℚ)) fun i hi => by
        rw [mem_Ico] at hi; exact (PVal.of_p hp).div_nat hp (not_dvd_of_lt_prime hp hi.1 (by omega))
      have hS1 : ∑ i ∈ Ico 1 s, (p : ℚ) / (i : ℚ) = (p : ℚ) * harmh 1 (s - 1) := by
        simp only [harmh, show s - 1 + 1 = s by omega, pow_one, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]
      rw [hS1] at hdeg1
      have hmul := ((PVal.of_p hp).div_nat hp hnds).mul hp hdeg1
      convert hmul using 1; simp only [A, A', hex]; ring
    have hB1' : PVal p 3 (B1 - B1') := by
      have h := cJ_pm1_mod_p3 p a hp hp7 ha.1 (by omega); convert h using 1; simp only [B1, B1']; ring
    have hB2' : PVal p 3 (B2 - B2') := by
      have h := cJ_pm1_mod_p3 p (s - a) hp hp7 (by omega) (by omega); convert h using 1; simp only [B2, B2']; ring
    have hA1 : PVal p 1 A := by
      have hex := choose_pm1_add_exact p s hp hs.1 hs.2
      have hP0 : PVal p 0 (∏ i ∈ Ico 1 s, (1 + (p : ℚ) / (i : ℚ))) := PVal.prod_zero hp fun i hi => by
        rw [mem_Ico] at hi; exact (PVal.nat hp 1).add hp ((PVal.nat hp p).div_nat hp (not_dvd_of_lt_prime hp hi.1 (by omega)))
      simpa only [A, hex] using ((PVal.of_p hp).div_nat hp hnds).mul_zero hp hP0
    have hB1_1 : PVal p 1 B1 := by
      have h := (cJ_pm1_mod_p2 p a hp hp7 ha.1 (by omega)).mono (by decide : 1 ≤ 2)
      have h2 : PVal p 1 ((p : ℚ) / (a : ℚ)) := (PVal.of_p hp).div_nat hp hnda
      simpa [B1] using h.add hp h2
    have hB1'_1 : PVal p 1 B1' := ((PVal.of_p hp).div_nat hp hnda).mul_zero hp
      ((PVal.nat hp 1).sub hp ((PVal.nat hp p).div_nat hp hnda))
    have hB2'_1 : PVal p 1 B2' := ((PVal.of_p hp).div_nat hp hndb).mul_zero hp
      ((PVal.nat hp 1).sub hp ((PVal.nat hp p).div_nat hp hndb))
    have hprod_eq : (-1 : ℚ) ^ s * (Nat.choose (p - 1 + s) s : ℚ) * (cJ (p - 1) a : ℚ) * (cJ (p - 1) (s - a) : ℚ) =
        A * B1 * B2 := by
      have hs_pow : (-1 : ℚ) ^ s = (-1 : ℚ) ^ a * (-1 : ℚ) ^ (s - a) := by rw [← pow_add, has]
      simp only [A, B1, B2]; rw [hs_pow]; ring
    have h3prod : PVal p 5 (A * B1 * B2 - A' * B1' * B2') := by
      rw [show A * B1 * B2 - A' * B1' * B2' = A * B1 * (B2 - B2') + A * (B1 - B1') * B2' + (A - A') * (B1' * B2') by ring]
      exact (((hA1.mul hp hB1_1).mul hp hB2').add hp ((hA1.mul hp hB1').mul hp hB2'_1)).add hp
        (hAA'.mul hp (hB1'_1.mul hp hB2'_1))
    have htail : PVal p 5 (A' * B1' * B2' -
        ((p : ℚ) ^ 3 * (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ)))⁻¹ +
          ((p : ℚ) ^ 4 * (harmh 1 (s - 1) * (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ)))⁻¹) -
           (p : ℚ) ^ 4 * ((((a : ℚ))⁻¹ + (((s - a : ℕ) : ℚ))⁻¹) * (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ)))⁻¹)))) := by
      set h1 := harmh 1 (s - 1)
      have hrew : A' * B1' * B2' -
          ((p : ℚ) ^ 3 * (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ)))⁻¹ +
            ((p : ℚ) ^ 4 * (h1 * (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ)))⁻¹) -
             (p : ℚ) ^ 4 * ((((a : ℚ))⁻¹ + (((s - a : ℕ) : ℚ))⁻¹) * (((s : ℚ) * (a : ℚ) * ((s - a : ℕ) : ℚ)))⁻¹))) =
          (p : ℚ) ^ 5 * ((((s : ℚ))⁻¹ * ((a : ℚ))⁻¹ * (((s - a : ℕ) : ℚ))⁻¹) *
            (((a : ℚ))⁻¹ * (((s - a : ℕ) : ℚ))⁻¹ - h1 * (((a : ℚ))⁻¹ + (((s - a : ℕ) : ℚ))⁻¹) +
              (p : ℚ) * h1 * ((a : ℚ))⁻¹ * (((s - a : ℕ) : ℚ))⁻¹)) := by
        simp only [A', B1', B2', div_eq_mul_inv, mul_inv]; ring
      rw [hrew]
      have hh1 := harmh_pval_zero p 1 (s - 1) hp (by omega)
      have his := PVal.inv_nat hnds
      have hia := PVal.inv_nat hnda
      have hib := PVal.inv_nat hndb
      have hc0 : PVal p 0 ((((s : ℚ))⁻¹ * ((a : ℚ))⁻¹ * (((s - a : ℕ) : ℚ))⁻¹) *
          (((a : ℚ))⁻¹ * (((s - a : ℕ) : ℚ))⁻¹ - h1 * (((a : ℚ))⁻¹ + (((s - a : ℕ) : ℚ))⁻¹) +
            (p : ℚ) * h1 * ((a : ℚ))⁻¹ * (((s - a : ℕ) : ℚ))⁻¹)) :=
        ((his.mul_zero hp hia).mul_zero hp hib).mul_zero hp
          (((hia.mul_zero hp hib).sub hp (hh1.mul_zero hp (hia.add hp hib))).add hp
            ((((PVal.nat hp p).mul_zero hp hh1).mul_zero hp hia).mul_zero hp hib))
      exact (PVal.of_pow_p (e := 5) hp).mul_zero hp hc0
    rw [hprod_eq]; convert h3prod.sub_trans hp htail using 1; ring
  have h4s : PVal p 5 ((p : ℚ) ^ 4 * (2 * S112 p - (2 * S22 p + 4 * S13 p))) :=
    (PVal.of_pow_p (e := 4) hp).mul hp (((PVal.nat hp 2).zero_mul hp hS112).sub hp
      (((PVal.nat hp 2).zero_mul hp hS22).add hp ((PVal.nat hp 4).zero_mul hp hS13)))
  have h1 := (hterm.add hp ((PVal.nat hp 2).zero_mul hp hS12)).add hp h4s
  have h3 := (PVal.nat hp 3).zero_mul hp h1
  convert h3 using 1; ring

/-- E5 Bucket 2c (b2_gt): 3 * sum_{j1+j2 > p} ... == 36 * p * H_1 (mod p^5). -/
private lemma e5_b2_gt (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 5 (3 * (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico (p - j₁ + 1) p,
      (-1 : ℚ) ^ (j₁ + j₂) * (Nat.choose (p - 1 + (j₁ + j₂)) (j₁ + j₂) : ℚ) *
        (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ)) - 36 * (p : ℚ) * harmH p 1) := by
  have ⟨hS112, hS12⟩ := S112_and_S12_system p hp hp7
  have hS22 := S22_mod_p p hp hp7
  have hS13 := S13_mod_p p hp hp7
  -- Reindex j1 = p - a, j2 = p - b with a in Ico 1 p, b in Ico 1 (p - a)
  have hreidx : ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico (p - j₁ + 1) p,
        (-1 : ℚ) ^ (j₁ + j₂) * (Nat.choose (p - 1 + (j₁ + j₂)) (j₁ + j₂) : ℚ) *
          (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ) =
      ∑ s ∈ Ico 1 p, ∑ a ∈ Ico 1 s,
        (-1 : ℚ) ^ ((p - a) + (p - (s - a))) *
          (Nat.choose (3 * p - 1 - s) (2 * p - s) : ℚ) *
          (cJ (p - 1) (p - a) : ℚ) * (cJ (p - 1) (p - (s - a)) : ℚ) := by
    have hs_add : ∑ s ∈ Ico 1 p, ∑ a ∈ Ico 1 s,
          (-1 : ℚ) ^ ((p - a) + (p - (s - a))) * (Nat.choose (3 * p - 1 - s) (2 * p - s) : ℚ) *
            (cJ (p - 1) (p - a) : ℚ) * (cJ (p - 1) (p - (s - a)) : ℚ) =
        ∑ s ∈ Ico 1 p, ∑ a ∈ Ico 1 s,
          (-1 : ℚ) ^ ((p - a) + (p - (s - a))) * (Nat.choose (3 * p - 1 - (a + (s - a))) (2 * p - (a + (s - a))) : ℚ) *
            (cJ (p - 1) (p - a) : ℚ) * (cJ (p - 1) (p - (s - a)) : ℚ) :=
      Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a ha => by
        rw [mem_Ico] at ha; rw [show a + (s - a) = s by omega]
    rw [hs_add, ← sum_lt_p_eq_sum_s p (fun a b =>
      (-1 : ℚ) ^ ((p - a) + (p - b)) * (Nat.choose (3 * p - 1 - (a + b)) (2 * p - (a + b)) : ℚ) *
        (cJ (p - 1) (p - a) : ℚ) * (cJ (p - 1) (p - b) : ℚ))]
    rw [← sum_Ico_reflect p]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [mem_Ico] at ha
    refine Finset.sum_bij (fun j₂ _ => p - j₂) ?_ ?_ ?_ ?_
    · intro j₂ hj₂; rw [mem_Ico] at hj₂ ⊢; omega
    · intro x hx y hy hxy; rw [mem_Ico] at hx hy; omega
    · intro b hb; rw [mem_Ico] at hb; exact ⟨p - b, by rw [mem_Ico]; omega, by omega⟩
    · intro j₂ hj₂; rw [mem_Ico] at hj₂
      have h1 : p - (p - j₂) = j₂ := by omega
      have h2 : p - 1 + (p - a + j₂) = 3 * p - 1 - (a + (p - j₂)) := by omega
      have h3 : p - a + j₂ = 2 * p - (a + (p - j₂)) := by omega
      rw [h1, h2, h3]
  rw [hreidx]
  have hterm : PVal p 5 ((∑ s ∈ Ico 1 p, ∑ a ∈ Ico 1 s,
        (-1 : ℚ) ^ ((p - a) + (p - (s - a))) * (Nat.choose (3 * p - 1 - s) (2 * p - s) : ℚ) *
          (cJ (p - 1) (p - a) : ℚ) * (cJ (p - 1) (p - (s - a)) : ℚ)) -
      (-2 * (p : ℚ) ^ 3 * (2 * S12 p) - 2 * (p : ℚ) ^ 4 * (2 * S112 p + 3 * (2 * S13 p) + 2 * (2 * S22 p + 4 * S13 p)))) := by
    rw [← pf_sum_1 p, ← pf_sum_2 p, ← pf_sum_3 p, ← pf_sum_4 p]
    simp only [mul_add, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine PVal.sum hp fun s hs => PVal.sum hp fun a ha => ?_
    rw [mem_Ico] at hs ha
    set b := s - a
    have hnds := not_dvd_of_lt_prime hp hs.1 hs.2
    have hnda := not_dvd_of_lt_prime hp ha.1 (by omega)
    have hndb := not_dvd_of_lt_prime hp (by omega : 1 ≤ b) (by omega : b < p)
    set A := (Nat.choose (3 * p - 1 - s) (2 * p - s) : ℚ)
    set A' := -(2 * (p : ℚ) / (s : ℚ)) * (1 + (p : ℚ) * (harmh 1 (s - 1) + 3 / (s : ℚ)))
    set B1 := (-1 : ℚ) ^ (p - a) * (cJ (p - 1) (p - a) : ℚ)
    set B1' := -((p : ℚ) / (a : ℚ)) * (1 + 2 * (p : ℚ) / (a : ℚ))
    set B2 := (-1 : ℚ) ^ (p - b) * (cJ (p - 1) (p - b) : ℚ)
    set B2' := -((p : ℚ) / (b : ℚ)) * (1 + 2 * (p : ℚ) / (b : ℚ))
    have hAA' : PVal p 3 (A - A') := by
      have h := choose_3p_sub_s_mod_p3 p s hp hp7 hs.1 hs.2; convert h using 1; simp only [A, A']; ring
    have hB1' : PVal p 3 (B1 - B1') := by
      have h := cJ_pm1_reflect_mod_p3 p a hp hp7 ha.1 (by omega); convert h using 1; simp only [B1, B1']; ring
    have hB2' : PVal p 3 (B2 - B2') := by
      have h := cJ_pm1_reflect_mod_p3 p b hp hp7 (by omega) (by omega); convert h using 1; simp only [B2, B2']; ring
    have hA'_1 : PVal p 1 A' :=
      (((PVal.nat hp 2).zero_mul hp (PVal.of_p hp)).div_nat hp hnds).neg.mul_zero hp
        ((PVal.nat hp 1).add hp ((PVal.nat hp p).mul_zero hp
          ((harmh_pval_zero p 1 (s - 1) hp (by omega)).add hp ((PVal.nat hp 3).div_nat hp hnds))))
    have hA1 : PVal p 1 A := by simpa using (hAA'.mono (by decide : 1 ≤ 3)).add hp hA'_1
    have hB1'_1 : PVal p 1 B1' :=
      ((PVal.of_p hp).div_nat hp hnda).neg.mul_zero hp
        ((PVal.nat hp 1).add hp (((PVal.nat hp 2).mul_zero hp (PVal.nat hp p)).div_nat hp hnda))
    have hB2'_1 : PVal p 1 B2' :=
      ((PVal.of_p hp).div_nat hp hndb).neg.mul_zero hp
        ((PVal.nat hp 1).add hp (((PVal.nat hp 2).mul_zero hp (PVal.nat hp p)).div_nat hp hndb))
    have hB1_1 : PVal p 1 B1 := by simpa using (hB1'.mono (by decide : 1 ≤ 3)).add hp hB1'_1
    have hprod_eq : (-1 : ℚ) ^ ((p - a) + (p - b)) * A * (cJ (p - 1) (p - a) : ℚ) * (cJ (p - 1) (p - b) : ℚ) =
        A * B1 * B2 := by simp only [B1, B2, pow_add]; ring
    have h3prod : PVal p 5 (A * B1 * B2 - A' * B1' * B2') := by
      rw [show A * B1 * B2 - A' * B1' * B2' = A * B1 * (B2 - B2') + A * (B1 - B1') * B2' + (A - A') * (B1' * B2') by ring]
      exact (((hA1.mul hp hB1_1).mul hp hB2').add hp ((hA1.mul hp hB1').mul hp hB2'_1)).add hp
        (hAA'.mul hp (hB1'_1.mul hp hB2'_1))
    have htail : PVal p 5 (A' * B1' * B2' -
        (-2 * (p : ℚ) ^ 3 * (((s : ℚ) * (a : ℚ) * (b : ℚ)))⁻¹ -
          (2 * (p : ℚ) ^ 4 * (harmh 1 (s - 1) * (((s : ℚ) * (a : ℚ) * (b : ℚ)))⁻¹) +
            2 * (p : ℚ) ^ 4 * (3 * (((s : ℚ))⁻¹ * (((s : ℚ) * (a : ℚ) * (b : ℚ)))⁻¹)) +
            2 * (p : ℚ) ^ 4 * (2 * ((((a : ℚ))⁻¹ + ((b : ℚ))⁻¹) * (((s : ℚ) * (a : ℚ) * (b : ℚ)))⁻¹))))) := by
      set cS := harmh 1 (s - 1) + 3 * ((s : ℚ))⁻¹
      have hrew : A' * B1' * B2' -
          (-2 * (p : ℚ) ^ 3 * (((s : ℚ) * (a : ℚ) * (b : ℚ)))⁻¹ -
            (2 * (p : ℚ) ^ 4 * (harmh 1 (s - 1) * (((s : ℚ) * (a : ℚ) * (b : ℚ)))⁻¹) +
              2 * (p : ℚ) ^ 4 * (3 * (((s : ℚ))⁻¹ * (((s : ℚ) * (a : ℚ) * (b : ℚ)))⁻¹)) +
              2 * (p : ℚ) ^ 4 * (2 * ((((a : ℚ))⁻¹ + ((b : ℚ))⁻¹) * (((s : ℚ) * (a : ℚ) * (b : ℚ)))⁻¹)))) =
          -2 * (p : ℚ) ^ 5 * ((((s : ℚ))⁻¹ * ((a : ℚ))⁻¹ * ((b : ℚ))⁻¹) *
            (4 * ((a : ℚ))⁻¹ * ((b : ℚ))⁻¹ + 2 * cS * (((a : ℚ))⁻¹ + ((b : ℚ))⁻¹) +
              4 * (p : ℚ) * cS * ((a : ℚ))⁻¹ * ((b : ℚ))⁻¹)) := by
        simp only [A', B1', B2', cS, div_eq_mul_inv, mul_inv]; ring
      rw [hrew]
      have his := PVal.inv_nat hnds
      have hia := PVal.inv_nat hnda
      have hib := PVal.inv_nat hndb
      have hcS : PVal p 0 cS := (harmh_pval_zero p 1 (s - 1) hp (by omega)).add hp ((PVal.nat hp 3).mul_zero hp his)
      have hc0 : PVal p 0 ((((s : ℚ))⁻¹ * ((a : ℚ))⁻¹ * ((b : ℚ))⁻¹) *
          (4 * ((a : ℚ))⁻¹ * ((b : ℚ))⁻¹ + 2 * cS * (((a : ℚ))⁻¹ + ((b : ℚ))⁻¹) +
            4 * (p : ℚ) * cS * ((a : ℚ))⁻¹ * ((b : ℚ))⁻¹)) :=
        ((his.mul_zero hp hia).mul_zero hp hib).mul_zero hp
          (((((PVal.nat hp 4).mul_zero hp hia).mul_zero hp hib).add hp
            (((PVal.nat hp 2).mul_zero hp hcS).mul_zero hp (hia.add hp hib))).add hp
            (((((PVal.nat hp 4).mul_zero hp (PVal.nat hp p)).mul_zero hp hcS).mul_zero hp hia).mul_zero hp hib))
      exact ((PVal.int hp (-2)).zero_mul hp (PVal.of_pow_p (e := 5) hp)).mul_zero hp hc0
    rw [hprod_eq]; convert h3prod.sub_trans hp htail using 1
  have h4s : PVal p 5 (2 * (p : ℚ) ^ 4 * (2 * S112 p + 3 * (2 * S13 p) + 2 * (2 * S22 p + 4 * S13 p))) :=
    ((PVal.nat hp 2).zero_mul hp (PVal.of_pow_p (e := 4) hp)).mul hp
      ((((PVal.nat hp 2).zero_mul hp hS112).add hp ((PVal.nat hp 3).zero_mul hp ((PVal.nat hp 2).zero_mul hp hS13))).add hp
        ((PVal.nat hp 2).zero_mul hp (((PVal.nat hp 2).zero_mul hp hS22).add hp ((PVal.nat hp 4).zero_mul hp hS13))))
  have h1 := (hterm.sub hp ((PVal.nat hp 4).zero_mul hp hS12)).sub hp h4s
  have h3 := (PVal.nat hp 3).zero_mul hp h1
  convert h3 using 1; ring

/-- E5 Bucket 3a (b3_div): triples in Ico 1 p with p | (j1 + j2 + j3) vanish mod p^5. -/
private lemma e5_b3_div (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 5 (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => p ∣ j₁ + j₂ + j₃),
      (-1 : ℚ) ^ (j₁ + j₂ + j₃) * (Nat.choose (p - 1 + (j₁ + j₂ + j₃)) (j₁ + j₂ + j₃) : ℚ) *
        (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ) * (cJ (p - 1) j₃ : ℚ)) := by
  set g : ℕ → ℕ → ℕ → ℚ := fun j₁ j₂ j₃ =>
    (-1 : ℚ) ^ (j₁ + j₂ + j₃) * (Nat.choose (p - 1 + (j₁ + j₂ + j₃)) (j₁ + j₂ + j₃) : ℚ) *
      (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ) * (cJ (p - 1) j₃ : ℚ)
  -- Split p | (j1+j2+j3) into j1+j2+j3 = p and j1+j2+j3 = 2*p, then pair via (p-j1, p-j2, p-j3)
  have hsplit : (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => p ∣ j₁ + j₂ + j₃), g j₁ j₂ j₃) =
      ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁),
        (g j₁ j₂ (p - j₁ - j₂) + g (p - j₁) (p - j₂) (p - (p - j₁ - j₂))) := by
    have hp1 : ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => j₁ + j₂ + j₃ = p), g j₁ j₂ j₃ =
        ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁), g j₁ j₂ (p - j₁ - j₂) := by
      refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
      rw [mem_Ico] at hj₁
      symm; rw [← Finset.sum_subset (Finset.Ico_subset_Ico_right (by omega : p - j₁ ≤ p))]
      · refine Finset.sum_congr rfl fun j₂ hj₂ => ?_
        rw [mem_Ico] at hj₂
        have hmem : p - j₁ - j₂ ∈ (Ico 1 p).filter (fun j₃ => j₁ + j₂ + j₃ = p) := by
          rw [mem_filter, mem_Ico]; omega
        rw [← Finset.add_sum_erase _ _ hmem]
        have hz : ∑ j₃ ∈ ((Ico 1 p).filter (fun j₃ => j₁ + j₂ + j₃ = p)).erase (p - j₁ - j₂), g j₁ j₂ j₃ = 0 :=
          Finset.sum_eq_zero fun j₃ hj₃ => by rw [mem_erase, mem_filter] at hj₃; omega
        rw [hz, add_zero]
      · intro j₂ hj₂ hnot; rw [mem_Ico] at hj₂ hnot
        refine Finset.sum_eq_zero fun j₃ hj₃ => ?_
        rw [mem_filter, mem_Ico] at hj₃; omega
    have hp2 : ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => j₁ + j₂ + j₃ = 2 * p), g j₁ j₂ j₃ =
        ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁), g (p - j₁) (p - j₂) (p - (p - j₁ - j₂)) := by
      rw [← sum_Ico_reflect p]
      refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
      rw [← sum_Ico_reflect p]
      rw [mem_Ico] at hj₁
      symm; rw [← Finset.sum_subset (Finset.Ico_subset_Ico_right (by omega : p - j₁ ≤ p))]
      · refine Finset.sum_congr rfl fun j₂ hj₂ => ?_
        rw [mem_Ico] at hj₂
        have hmem : p - (p - j₁ - j₂) ∈ (Ico 1 p).filter (fun j₃ => (p - j₁) + (p - j₂) + j₃ = 2 * p) := by
          rw [mem_filter, mem_Ico]; omega
        rw [← Finset.add_sum_erase _ _ hmem]
        have hz : ∑ j₃ ∈ ((Ico 1 p).filter (fun j₃ => (p - j₁) + (p - j₂) + j₃ = 2 * p)).erase (p - (p - j₁ - j₂)),
            g (p - j₁) (p - j₂) j₃ = 0 :=
          Finset.sum_eq_zero fun j₃ hj₃ => by rw [mem_erase, mem_filter] at hj₃; omega
        rw [hz, add_zero]
      · intro j₂ hj₂ hnot; rw [mem_Ico] at hj₂ hnot
        refine Finset.sum_eq_zero fun j₃ hj₃ => ?_
        rw [mem_filter, mem_Ico] at hj₃; omega
    have hpart : ∀ j₁ ∈ Ico 1 p, ∀ j₂ ∈ Ico 1 p,
        ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => p ∣ j₁ + j₂ + j₃), g j₁ j₂ j₃ =
        (∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => j₁ + j₂ + j₃ = p), g j₁ j₂ j₃) +
        (∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => j₁ + j₂ + j₃ = 2 * p), g j₁ j₂ j₃) := by
      intro j₁ hj₁ j₂ hj₂; rw [mem_Ico] at hj₁ hj₂
      rw [← Finset.sum_union (Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega)]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext j₃; simp only [mem_filter, mem_union, mem_Ico]
      constructor
      · rintro ⟨⟨h1, h2⟩, ⟨k, hk⟩⟩
        have hk12 : k = 1 ∨ k = 2 := by
          by_contra hnot
          have : k = 0 ∨ 3 ≤ k := by omega
          rcases this with rfl | h3
          · simp at hk; omega
          · nlinarith
        rcases hk12 with rfl | rfl
        · left; exact ⟨⟨h1, h2⟩, by linarith⟩
        · right; exact ⟨⟨h1, h2⟩, by linarith⟩
      · rintro (⟨h12, h⟩ | ⟨h12, h⟩)
        · exact ⟨h12, ⟨1, by linarith⟩⟩
        · exact ⟨h12, ⟨2, by linarith⟩⟩
    calc _ = ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p,
          ((∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => j₁ + j₂ + j₃ = p), g j₁ j₂ j₃) +
           (∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => j₁ + j₂ + j₃ = 2 * p), g j₁ j₂ j₃)) :=
          Finset.sum_congr rfl fun j₁ hj₁ => Finset.sum_congr rfl fun j₂ hj₂ => hpart j₁ hj₁ j₂ hj₂
      _ = (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => j₁ + j₂ + j₃ = p), g j₁ j₂ j₃) +
          (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => j₁ + j₂ + j₃ = 2 * p), g j₁ j₂ j₃) := by
          simp only [Finset.sum_add_distrib]
      _ = _ := by rw [hp1, hp2]; simp only [← Finset.sum_add_distrib]
  rw [hsplit]
  have h2p : PVal p 2 ((Nat.choose (2 * p - 1) p : ℚ) - 1) := by
    have h := kazandzidis_pred_add p 1 1 hp (by omega) (by decide) (by decide)
    rw [show 1 * p - 1 + p * 1 = 2 * p - 1 by omega, mul_one] at h
    simpa using h.mono (by omega : 2 ≤ 3 + 2 * vp p 1)
  have h3p : PVal p 2 ((Nat.choose (3 * p - 1) (2 * p) : ℚ) - 1) := by
    have h := kazandzidis_pred_add p 1 2 hp (by omega) (by decide) (by decide)
    rw [show 1 * p - 1 + p * 2 = 3 * p - 1 by omega, show p * 2 = 2 * p by ring] at h
    simpa using h.mono (by omega : 2 ≤ 3 + 2 * vp p 1)
  -- Each pair g(j1, j2, j3) + g(p-j1, p-j2, p-j3) == -3 * p^4 * (1/j1 + 1/j2 + 1/j3)/(j1*j2*j3) (mod p^5)
  have hpair_approx : PVal p 5 ((∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁),
        (g j₁ j₂ (p - j₁ - j₂) + g (p - j₁) (p - j₂) (p - (p - j₁ - j₂)))) +
      3 * (p : ℚ) ^ 4 * ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁),
        (((j₁ : ℚ))⁻¹ + ((j₂ : ℚ))⁻¹ + (((p - j₁ - j₂ : ℕ) : ℚ))⁻¹) /
          ((j₁ : ℚ) * (j₂ : ℚ) * ((p - j₁ - j₂ : ℕ) : ℚ))) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine PVal.sum hp fun j₁ hj₁ => PVal.sum hp fun j₂ hj₂ => ?_
    rw [mem_Ico] at hj₁ hj₂
    set j₃ := p - j₁ - j₂
    have hj123 : j₁ + j₂ + j₃ = p := by omega
    have hj3_1 : 1 ≤ j₃ := by omega
    have hj3_p : j₃ < p := by omega
    have hnd1 := not_dvd_of_lt_prime hp hj₁.1 hj₁.2
    have hnd2 := not_dvd_of_lt_prime hp hj₂.1 (by omega)
    have hnd3 := not_dvd_of_lt_prime hp hj3_1 hj3_p
    -- First term: g j1 j2 j3 == (p^3/(j1*j2*j3)) * (1 - p*(1/j1+1/j2+1/j3)) (mod p^5)
    have hg1 : PVal p 5 (g j₁ j₂ j₃ - ((p : ℚ) ^ 3 / ((j₁ : ℚ) * (j₂ : ℚ) * (j₃ : ℚ))) *
        (1 - (p : ℚ) * (((j₁ : ℚ))⁻¹ + ((j₂ : ℚ))⁻¹ + ((j₃ : ℚ))⁻¹))) := by
      set B1 := (-1 : ℚ) ^ j₁ * (cJ (p - 1) j₁ : ℚ)
      set B2 := (-1 : ℚ) ^ j₂ * (cJ (p - 1) j₂ : ℚ)
      set B3 := (-1 : ℚ) ^ j₃ * (cJ (p - 1) j₃ : ℚ)
      set L1 := ((p : ℚ) / (j₁ : ℚ)) * (1 - (p : ℚ) / (j₁ : ℚ))
      set L2 := ((p : ℚ) / (j₂ : ℚ)) * (1 - (p : ℚ) / (j₂ : ℚ))
      set L3 := ((p : ℚ) / (j₃ : ℚ)) * (1 - (p : ℚ) / (j₃ : ℚ))
      have heq_g : g j₁ j₂ j₃ = (Nat.choose (2 * p - 1) p : ℚ) * (B1 * B2 * B3) := by
        simp only [g, B1, B2, B3, hj123, show p - 1 + p = 2 * p - 1 by omega]
        rw [← hj123, pow_add, pow_add]; ring
      have hB1 : PVal p 3 (B1 - L1) := by have h := cJ_pm1_mod_p3 p j₁ hp hp7 hj₁.1 hj₁.2; convert h using 1; simp only [B1, L1]; ring
      have hB2 : PVal p 3 (B2 - L2) := by have h := cJ_pm1_mod_p3 p j₂ hp hp7 hj₂.1 (by omega); convert h using 1; simp only [B2, L2]; ring
      have hB3 : PVal p 3 (B3 - L3) := by have h := cJ_pm1_mod_p3 p j₃ hp hp7 hj3_1 hj3_p; convert h using 1; simp only [B3, L3]; ring
      have hL1 : PVal p 1 L1 := ((PVal.of_p hp).div_nat hp hnd1).mul_zero hp ((PVal.nat hp 1).sub hp ((PVal.nat hp p).div_nat hp hnd1))
      have hL2 : PVal p 1 L2 := ((PVal.of_p hp).div_nat hp hnd2).mul_zero hp ((PVal.nat hp 1).sub hp ((PVal.nat hp p).div_nat hp hnd2))
      have hL3 : PVal p 1 L3 := ((PVal.of_p hp).div_nat hp hnd3).mul_zero hp ((PVal.nat hp 1).sub hp ((PVal.nat hp p).div_nat hp hnd3))
      have hB1_1 : PVal p 1 B1 := by simpa using (hB1.mono (by decide : 1 ≤ 3)).add hp hL1
      have hB2_1 : PVal p 1 B2 := by simpa using (hB2.mono (by decide : 1 ≤ 3)).add hp hL2
      have hB3_1 : PVal p 1 B3 := by simpa using (hB3.mono (by decide : 1 ≤ 3)).add hp hL3
      have h1 : PVal p 5 (g j₁ j₂ j₃ - B1 * B2 * B3) := by
        rw [heq_g, show (Nat.choose (2 * p - 1) p : ℚ) * (B1 * B2 * B3) - B1 * B2 * B3 =
            ((Nat.choose (2 * p - 1) p : ℚ) - 1) * (B1 * B2 * B3) by ring]
        exact h2p.mul hp ((hB1_1.mul hp hB2_1).mul hp hB3_1)
      have h2 : PVal p 5 (B1 * B2 * B3 - L1 * L2 * L3) := by
        rw [show B1 * B2 * B3 - L1 * L2 * L3 = B1 * B2 * (B3 - L3) + B1 * (B2 - L2) * L3 + (B1 - L1) * (L2 * L3) by ring]
        exact (((hB1_1.mul hp hB2_1).mul hp hB3).add hp ((hB1_1.mul hp hB2).mul hp hL3)).add hp (hB1.mul hp (hL2.mul hp hL3))
      have h3 : PVal p 5 (L1 * L2 * L3 - ((p : ℚ) ^ 3 / ((j₁ : ℚ) * (j₂ : ℚ) * (j₃ : ℚ))) *
          (1 - (p : ℚ) * (((j₁ : ℚ))⁻¹ + ((j₂ : ℚ))⁻¹ + ((j₃ : ℚ))⁻¹))) := by
        have hrew : L1 * L2 * L3 - ((p : ℚ) ^ 3 / ((j₁ : ℚ) * (j₂ : ℚ) * (j₃ : ℚ))) *
            (1 - (p : ℚ) * (((j₁ : ℚ))⁻¹ + ((j₂ : ℚ))⁻¹ + ((j₃ : ℚ))⁻¹)) =
            (p : ℚ) ^ 5 * (((j₁ : ℚ))⁻¹ * ((j₂ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹ *
              (((j₁ : ℚ))⁻¹ * ((j₂ : ℚ))⁻¹ + ((j₁ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹ + ((j₂ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹ -
                (p : ℚ) * ((j₁ : ℚ))⁻¹ * ((j₂ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹)) := by
          simp only [L1, L2, L3, div_eq_mul_inv, mul_inv]; ring
        rw [hrew]
        have i1 := PVal.inv_nat hnd1; have i2 := PVal.inv_nat hnd2; have i3 := PVal.inv_nat hnd3
        have hc0 : PVal p 0 (((j₁ : ℚ))⁻¹ * ((j₂ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹ *
            (((j₁ : ℚ))⁻¹ * ((j₂ : ℚ))⁻¹ + ((j₁ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹ + ((j₂ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹ -
              (p : ℚ) * ((j₁ : ℚ))⁻¹ * ((j₂ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹)) :=
          ((i1.mul_zero hp i2).mul_zero hp i3).mul_zero hp
            ((((i1.mul_zero hp i2).add hp (i1.mul_zero hp i3)).add hp (i2.mul_zero hp i3)).sub hp
              ((((PVal.nat hp p).mul_zero hp i1).mul_zero hp i2).mul_zero hp i3))
        exact (PVal.of_pow_p (e := 5) hp).mul_zero hp hc0
      exact h1.sub_trans hp (h2.sub_trans hp h3)
    -- Second term: g (p-j1) (p-j2) (p-j3) == -(p^3/(j1*j2*j3)) * (1 + 2*p*(1/j1+1/j2+1/j3)) (mod p^5)
    have hg2 : PVal p 5 (g (p - j₁) (p - j₂) (p - j₃) + ((p : ℚ) ^ 3 / ((j₁ : ℚ) * (j₂ : ℚ) * (j₃ : ℚ))) *
        (1 + 2 * (p : ℚ) * (((j₁ : ℚ))⁻¹ + ((j₂ : ℚ))⁻¹ + ((j₃ : ℚ))⁻¹))) := by
      set B1 := (-1 : ℚ) ^ (p - j₁) * (cJ (p - 1) (p - j₁) : ℚ)
      set B2 := (-1 : ℚ) ^ (p - j₂) * (cJ (p - 1) (p - j₂) : ℚ)
      set B3 := (-1 : ℚ) ^ (p - j₃) * (cJ (p - 1) (p - j₃) : ℚ)
      set L1 := -((p : ℚ) / (j₁ : ℚ)) * (1 + 2 * (p : ℚ) / (j₁ : ℚ))
      set L2 := -((p : ℚ) / (j₂ : ℚ)) * (1 + 2 * (p : ℚ) / (j₂ : ℚ))
      set L3 := -((p : ℚ) / (j₃ : ℚ)) * (1 + 2 * (p : ℚ) / (j₃ : ℚ))
      have hsum2p : (p - j₁) + (p - j₂) + (p - j₃) = 2 * p := by omega
      have heq_g : g (p - j₁) (p - j₂) (p - j₃) = (Nat.choose (3 * p - 1) (2 * p) : ℚ) * (B1 * B2 * B3) := by
        simp only [g, B1, B2, B3, hsum2p, show p - 1 + 2 * p = 3 * p - 1 by omega]
        rw [← hsum2p, pow_add, pow_add]; ring
      have hB1 : PVal p 3 (B1 - L1) := by have h := cJ_pm1_reflect_mod_p3 p j₁ hp hp7 hj₁.1 hj₁.2; convert h using 1; simp only [B1, L1]; ring
      have hB2 : PVal p 3 (B2 - L2) := by have h := cJ_pm1_reflect_mod_p3 p j₂ hp hp7 hj₂.1 (by omega); convert h using 1; simp only [B2, L2]; ring
      have hB3 : PVal p 3 (B3 - L3) := by have h := cJ_pm1_reflect_mod_p3 p j₃ hp hp7 hj3_1 hj3_p; convert h using 1; simp only [B3, L3]; ring
      have hL1 : PVal p 1 L1 := ((PVal.of_p hp).div_nat hp hnd1).neg.mul_zero hp ((PVal.nat hp 1).add hp (((PVal.nat hp 2).mul_zero hp (PVal.nat hp p)).div_nat hp hnd1))
      have hL2 : PVal p 1 L2 := ((PVal.of_p hp).div_nat hp hnd2).neg.mul_zero hp ((PVal.nat hp 1).add hp (((PVal.nat hp 2).mul_zero hp (PVal.nat hp p)).div_nat hp hnd2))
      have hL3 : PVal p 1 L3 := ((PVal.of_p hp).div_nat hp hnd3).neg.mul_zero hp ((PVal.nat hp 1).add hp (((PVal.nat hp 2).mul_zero hp (PVal.nat hp p)).div_nat hp hnd3))
      have hB1_1 : PVal p 1 B1 := by simpa using (hB1.mono (by decide : 1 ≤ 3)).add hp hL1
      have hB2_1 : PVal p 1 B2 := by simpa using (hB2.mono (by decide : 1 ≤ 3)).add hp hL2
      have hB3_1 : PVal p 1 B3 := by simpa using (hB3.mono (by decide : 1 ≤ 3)).add hp hL3
      have h1 : PVal p 5 (g (p - j₁) (p - j₂) (p - j₃) - B1 * B2 * B3) := by
        rw [heq_g, show (Nat.choose (3 * p - 1) (2 * p) : ℚ) * (B1 * B2 * B3) - B1 * B2 * B3 =
            ((Nat.choose (3 * p - 1) (2 * p) : ℚ) - 1) * (B1 * B2 * B3) by ring]
        exact h3p.mul hp ((hB1_1.mul hp hB2_1).mul hp hB3_1)
      have h2 : PVal p 5 (B1 * B2 * B3 - L1 * L2 * L3) := by
        rw [show B1 * B2 * B3 - L1 * L2 * L3 = B1 * B2 * (B3 - L3) + B1 * (B2 - L2) * L3 + (B1 - L1) * (L2 * L3) by ring]
        exact (((hB1_1.mul hp hB2_1).mul hp hB3).add hp ((hB1_1.mul hp hB2).mul hp hL3)).add hp (hB1.mul hp (hL2.mul hp hL3))
      have h3 : PVal p 5 (L1 * L2 * L3 + ((p : ℚ) ^ 3 / ((j₁ : ℚ) * (j₂ : ℚ) * (j₃ : ℚ))) *
          (1 + 2 * (p : ℚ) * (((j₁ : ℚ))⁻¹ + ((j₂ : ℚ))⁻¹ + ((j₃ : ℚ))⁻¹))) := by
        have hrew : L1 * L2 * L3 + ((p : ℚ) ^ 3 / ((j₁ : ℚ) * (j₂ : ℚ) * (j₃ : ℚ))) *
            (1 + 2 * (p : ℚ) * (((j₁ : ℚ))⁻¹ + ((j₂ : ℚ))⁻¹ + ((j₃ : ℚ))⁻¹)) =
            -(p : ℚ) ^ 5 * (((j₁ : ℚ))⁻¹ * ((j₂ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹ *
              (4 * (((j₁ : ℚ))⁻¹ * ((j₂ : ℚ))⁻¹ + ((j₁ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹ + ((j₂ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹) +
                8 * (p : ℚ) * ((j₁ : ℚ))⁻¹ * ((j₂ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹)) := by
          simp only [L1, L2, L3, div_eq_mul_inv, mul_inv]; ring
        rw [hrew]
        have i1 := PVal.inv_nat hnd1; have i2 := PVal.inv_nat hnd2; have i3 := PVal.inv_nat hnd3
        have hc0 : PVal p 0 (((j₁ : ℚ))⁻¹ * ((j₂ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹ *
            (4 * (((j₁ : ℚ))⁻¹ * ((j₂ : ℚ))⁻¹ + ((j₁ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹ + ((j₂ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹) +
              8 * (p : ℚ) * ((j₁ : ℚ))⁻¹ * ((j₂ : ℚ))⁻¹ * ((j₃ : ℚ))⁻¹)) :=
          ((i1.mul_zero hp i2).mul_zero hp i3).mul_zero hp
            (((PVal.nat hp 4).mul_zero hp (((i1.mul_zero hp i2).add hp (i1.mul_zero hp i3)).add hp (i2.mul_zero hp i3))).add hp
              (((((PVal.nat hp 8).mul_zero hp (PVal.nat hp p)).mul_zero hp i1).mul_zero hp i2).mul_zero hp i3))
        exact (PVal.of_pow_p (e := 5) hp).neg.mul_zero hp hc0
      have hcomb := (h1.add hp h2).add hp h3
      convert hcomb using 1; ring
    have hsum := hg1.add hp hg2
    convert hsum using 1; ring
  -- Now show the p^4 sum is 0 mod p^5
  have hsum_zero : PVal p 1 (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁),
      (((j₁ : ℚ))⁻¹ + ((j₂ : ℚ))⁻¹ + (((p - j₁ - j₂ : ℕ) : ℚ))⁻¹) /
        ((j₁ : ℚ) * (j₂ : ℚ) * ((p - j₁ - j₂ : ℕ) : ℚ))) := by
    -- By symmetry of the 3 terms (each equals sum_{j1+j2+j3=p} 1/(j1^2*j2*j3))
    set T := ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁),
      (((j₁ : ℚ) ^ 2 * (j₂ : ℚ) * ((p - j₁ - j₂ : ℕ) : ℚ)))⁻¹
    have h3T : (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁),
        (((j₁ : ℚ))⁻¹ + ((j₂ : ℚ))⁻¹ + (((p - j₁ - j₂ : ℕ) : ℚ))⁻¹) /
          ((j₁ : ℚ) * (j₂ : ℚ) * ((p - j₁ - j₂ : ℕ) : ℚ))) = 3 * T := by
      have hsp : (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁),
          (((j₁ : ℚ))⁻¹ + ((j₂ : ℚ))⁻¹ + (((p - j₁ - j₂ : ℕ) : ℚ))⁻¹) /
            ((j₁ : ℚ) * (j₂ : ℚ) * ((p - j₁ - j₂ : ℕ) : ℚ))) =
          T + (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁), (((j₁ : ℚ) * (j₂ : ℚ) ^ 2 * ((p - j₁ - j₂ : ℕ) : ℚ)))⁻¹) +
          (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁), (((j₁ : ℚ) * (j₂ : ℚ) * ((p - j₁ - j₂ : ℕ) : ℚ) ^ 2))⁻¹) := by
        simp only [T, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
        simp only [div_eq_mul_inv, mul_inv, sq]; ring
      have hT2 : (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁), (((j₁ : ℚ) * (j₂ : ℚ) ^ 2 * ((p - j₁ - j₂ : ℕ) : ℚ)))⁻¹) = T := by
        simp only [T]; rw [Finset.sum_sigma', Finset.sum_sigma']
        refine Finset.sum_bij (fun x _ => (⟨x.2, x.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
        · intro x hx; rw [mem_sigma, mem_Ico, mem_Ico] at hx; rw [mem_sigma, mem_Ico, mem_Ico]; dsimp; omega
        · intro x₁ _ x₂ _ heq
          rcases x₁ with ⟨a₁, b₁⟩; rcases x₂ with ⟨a₂, b₂⟩
          simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq; exact Sigma.ext heq.2 (heq_of_eq heq.1)
        · rintro ⟨a, b⟩ hy; rw [mem_sigma, mem_Ico, mem_Ico] at hy; dsimp at hy
          exact ⟨⟨b, a⟩, by rw [mem_sigma, mem_Ico, mem_Ico]; dsimp; omega, rfl⟩
        · intro x hx; rw [mem_sigma, mem_Ico, mem_Ico] at hx; dsimp
          rw [show p - x.1 - x.2 = p - x.2 - x.1 by omega]; ring_nf
      have hT3 : (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁), (((j₁ : ℚ) * (j₂ : ℚ) * ((p - j₁ - j₂ : ℕ) : ℚ) ^ 2))⁻¹) = T := by
        simp only [T]; rw [Finset.sum_sigma', Finset.sum_sigma']
        refine Finset.sum_bij (fun x _ => (⟨p - x.1 - x.2, x.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
        · intro x hx; rw [mem_sigma, mem_Ico, mem_Ico] at hx; rw [mem_sigma, mem_Ico, mem_Ico]; dsimp; omega
        · intro x₁ hx₁ x₂ hx₂ heq
          rcases x₁ with ⟨a₁, b₁⟩; rcases x₂ with ⟨a₂, b₂⟩
          rw [mem_sigma, mem_Ico, mem_Ico] at hx₁ hx₂
          dsimp at hx₁ hx₂ heq
          simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
          exact Sigma.ext (by dsimp; omega) (heq_of_eq heq.2)
        · rintro ⟨a, b⟩ hy; rw [mem_sigma, mem_Ico, mem_Ico] at hy; dsimp at hy
          refine ⟨⟨p - a - b, b⟩, ?_, ?_⟩
          · rw [mem_sigma, mem_Ico, mem_Ico]; dsimp; omega
          · exact Sigma.ext (by dsimp; omega) (heq_of_eq rfl)
        · intro x hx; rw [mem_sigma, mem_Ico, mem_Ico] at hx; dsimp
          rw [show p - (p - x.1 - x.2) - x.2 = x.1 by omega]; ring_nf
      rw [hsp, hT2, hT3]; ring
    rw [h3T]
    have hT_eq : T = 2 * ∑ j₁ ∈ Ico 1 p, harmh 1 (p - j₁ - 1) / ((j₁ : ℚ) ^ 2 * ((p - j₁ : ℕ) : ℚ)) := by
      simp only [T, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
      rw [mem_Ico] at hj₁
      have hpf := pf_inner_1 (p - j₁)
      have hrew : ∑ j₂ ∈ Ico 1 (p - j₁), (((j₁ : ℚ) ^ 2 * (j₂ : ℚ) * ((p - j₁ - j₂ : ℕ) : ℚ)))⁻¹ =
          ((p - j₁ : ℕ) : ℚ) / (j₁ : ℚ) ^ 2 *
            ∑ j₂ ∈ Ico 1 (p - j₁), ((((p - j₁ : ℕ) : ℚ) * (j₂ : ℚ) * (((p - j₁) - j₂ : ℕ) : ℚ)))⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j₂ _ => ?_
        have hpj0 : ((p - j₁ : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hj10 : (j₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp [hpj0, hj10]
      rw [hrew, hpf]
      have hpj0 : ((p - j₁ : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hj10 : (j₁ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      field_simp [hpj0, hj10]
    have hT_mod : PVal p 1 ((∑ j₁ ∈ Ico 1 p, harmh 1 (p - j₁ - 1) / ((j₁ : ℚ) ^ 2 * ((p - j₁ : ℕ) : ℚ))) +
        (S13 p + harmH p 4)) := by
      simp only [S13, harmH, ← Finset.sum_add_distrib]
      refine PVal.sum hp fun k hk => ?_
      rw [mem_Ico] at hk
      have hndk := not_dvd_of_lt_prime hp hk.1 hk.2
      have hndpk := not_dvd_of_lt_prime hp (by omega : 1 ≤ p - k) (by omega : p - k < p)
      have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hpk0 : ((p - k : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hnum_diff : PVal p 1 (harmh 1 (p - k - 1) - (harmh 1 (k - 1) + ((k : ℚ))⁻¹)) := by
        have hstep : harmh 1 (p - k) = harmh 1 (p - k - 1) + (((p - k : ℕ) : ℚ))⁻¹ := by
          simp only [harmh, show p - k - 1 + 1 = p - k by omega, pow_one]; exact Finset.sum_Ico_succ_top (by omega) _
        have hinv : PVal p 1 ((((p - k : ℕ) : ℚ))⁻¹ + ((k : ℚ))⁻¹) := by
          have h1 : (((p - k : ℕ) : ℚ))⁻¹ + ((k : ℚ))⁻¹ = (p : ℚ) / (((p - k) * k : ℕ) : ℚ) := by
            rw [Nat.cast_mul]; rw [Nat.cast_sub (by omega)] at hpk0 ⊢; field_simp [hk0, hpk0]; ring
          rw [h1]
          have hnd : ¬ p ∣ (p - k) * k := fun h => by rcases hp.dvd_mul.mp h with h1 | h2; exact hndpk h1; exact hndk h2
          exact (PVal.of_p hp).div_nat hp hnd
        have hrew : harmh 1 (p - k - 1) - (harmh 1 (k - 1) + ((k : ℚ))⁻¹) =
            (harmh 1 (p - k) - harmh 1 (k - 1)) - ((((p - k : ℕ) : ℚ))⁻¹ + ((k : ℚ))⁻¹) := by linarith
        rw [hrew]; exact (harmh1_reflect p k hp hp7 hk.1 hk.2).sub hp hinv
      have hden_sum : PVal p 1 ((((k : ℚ) ^ 2 * ((p - k : ℕ) : ℚ)))⁻¹ + ((k : ℚ) ^ 3)⁻¹) := by
        have h1 : (((k : ℚ) ^ 2 * ((p - k : ℕ) : ℚ)))⁻¹ + ((k : ℚ) ^ 3)⁻¹ =
            (p : ℚ) / (((k ^ 3 * (p - k) : ℕ) : ℚ)) := by
          push_cast; rw [Nat.cast_sub (by omega)] at hpk0 ⊢; field_simp [hk0, hpk0]; ring
        rw [h1]
        have hnd : ¬ p ∣ k ^ 3 * (p - k) := fun h => by
          rcases hp.dvd_mul.mp h with h1 | h2; exact hndk (hp.dvd_of_dvd_pow h1); exact hndpk h2
        exact (PVal.of_p hp).div_nat hp hnd
      have hsplit : harmh 1 (p - k - 1) / ((k : ℚ) ^ 2 * ((p - k : ℕ) : ℚ)) +
          (harmh 1 (k - 1) / (k : ℚ) ^ 3 + ((k : ℚ) ^ 4)⁻¹) =
          (harmh 1 (p - k - 1) - (harmh 1 (k - 1) + ((k : ℚ))⁻¹)) * (((k : ℚ) ^ 2 * ((p - k : ℕ) : ℚ)))⁻¹ +
          (harmh 1 (k - 1) + ((k : ℚ))⁻¹) * ((((k : ℚ) ^ 2 * ((p - k : ℕ) : ℚ)))⁻¹ + ((k : ℚ) ^ 3)⁻¹) := by
        field_simp [hk0, hpk0]; ring
      rw [hsplit]
      have hden0 : PVal p 0 ((((k : ℚ) ^ 2 * ((p - k : ℕ) : ℚ)))⁻¹) := by
        have hnd : ¬ p ∣ k ^ 2 * (p - k) := fun h => by
          rcases hp.dvd_mul.mp h with h1 | h2; exact hndk (hp.dvd_of_dvd_pow h1); exact hndpk h2
        simpa only [Nat.cast_mul, Nat.cast_pow] using PVal.inv_nat hnd
      have hnum0 : PVal p 0 (harmh 1 (k - 1) + ((k : ℚ))⁻¹) :=
        (harmh_pval_zero p 1 (k - 1) hp (by omega)).add hp (PVal.inv_nat hndk)
      exact (hnum_diff.mul_zero hp hden0).add hp (hnum0.zero_mul hp hden_sum)
    have hT1 : PVal p 1 T := by
      rw [hT_eq]
      exact (PVal.nat hp 2).zero_mul hp (by simpa using hT_mod.sub hp ((S13_mod_p p hp hp7).add hp (harmH_four_mod_p p hp hp7)))
    exact (PVal.nat hp 3).zero_mul hp hT1
  have h4 := ((PVal.nat hp 3).zero_mul hp (PVal.of_pow_p (e := 4) hp)).mul hp hsum_zero
  simpa using hpair_approx.sub hp h4

/-- E5 Bucket 3b (b3_ndiv): triples in Ico 1 p with ¬ p | (j1 + j2 + j3) vanish mod p^5. -/
private lemma e5_b3_ndiv (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 5 (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => ¬ p ∣ j₁ + j₂ + j₃),
      (-1 : ℚ) ^ (j₁ + j₂ + j₃) * (Nat.choose (p - 1 + (j₁ + j₂ + j₃)) (j₁ + j₂ + j₃) : ℚ) *
        (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ) * (cJ (p - 1) j₃ : ℚ)) := by
  have hnd2 : ¬ p ∣ 2 := not_dvd_of_lt_prime hp (by decide) (by omega)
  have hnd15 : ¬ p ∣ 15 := fun h => by
    rcases hp.dvd_mul.mp (show p ∣ 3 * 5 by simpa using h) with h3 | h5
    · exact not_dvd_of_lt_prime hp (by decide) (by omega) h3
    · exact not_dvd_of_lt_prime hp (by decide) (by omega) h5
  -- Approximate each term mod p^5 by p^4 * ((s/p + 1) / (s * j1 * j2 * j3))
  have happrox : PVal p 5 ((∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => ¬ p ∣ j₁ + j₂ + j₃),
        (-1 : ℚ) ^ (j₁ + j₂ + j₃) * (Nat.choose (p - 1 + (j₁ + j₂ + j₃)) (j₁ + j₂ + j₃) : ℚ) *
          (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ) * (cJ (p - 1) j₃ : ℚ)) -
      (p : ℚ) ^ 4 * ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => ¬ p ∣ j₁ + j₂ + j₃),
        ((((j₁ + j₂ + j₃) / p + 1 : ℕ) : ℚ)) / (((j₁ + j₂ + j₃ : ℕ) : ℚ) * (j₁ : ℚ) * (j₂ : ℚ) * (j₃ : ℚ))) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine PVal.sum hp fun j₁ hj₁ => PVal.sum hp fun j₂ hj₂ => PVal.sum hp fun j₃ hj₃ => ?_
    rw [mem_filter] at hj₃
    have hnd_s : ¬ p ∣ j₁ + j₂ + j₃ := hj₃.2
    rw [mem_Ico] at hj₁ hj₂; have hj3_ico := mem_Ico.mp hj₃.1
    set s := j₁ + j₂ + j₃
    set q := s / p
    set r := s % p
    have hr1 : 1 ≤ r := Nat.pos_of_ne_zero fun h0 => hnd_s (Nat.dvd_of_mod_eq_zero h0)
    have hrp : r < p := Nat.mod_lt s hp.pos
    have hs_eq : q * p + r = s := by simp only [q, r]; rw [mul_comm]; exact Nat.div_add_mod s p
    have hA_mod : PVal p 2 ((Nat.choose (p - 1 + s) s : ℚ) - ((q + 1 : ℕ) : ℚ) * (p : ℚ) / (s : ℚ)) := by
      have hex := choose_pred_add_ndiv_exact p 1 q r hp (by decide) hr1 hrp
      rw [hs_eq] at hex
      have hch1q : Nat.choose (1 + q) q = q + 1 := by
        rw [add_comm 1 q, Nat.choose_succ_self_right]
      rw [hch1q] at hex
      set P := ∏ i ∈ (Ico 1 s).filter (fun i => ¬ p ∣ i), (1 + (p : ℚ) / (i : ℚ))
      have hP : PVal p 1 (P - 1) := PVal.prod_one_add hp fun i hi =>
        (PVal.of_p hp).div_nat hp (Finset.mem_filter.mp hi).2
      have hbase : PVal p 1 (((q + 1 : ℕ) : ℚ) * (p : ℚ) / (s : ℚ)) :=
        ((PVal.nat hp (q + 1)).zero_mul hp (PVal.of_p hp)).div_nat hp hnd_s
      have hrew : (Nat.choose (p - 1 + s) s : ℚ) - ((q + 1 : ℕ) : ℚ) * (p : ℚ) / (s : ℚ) =
          (((q + 1 : ℕ) : ℚ) * (p : ℚ) / (s : ℚ)) * (P - 1) := by
        simp only [one_mul, Nat.cast_one] at hex
        rw [hex]; simp only [P]; ring
      rw [hrew]; exact hbase.mul hp hP
    set A := (Nat.choose (p - 1 + s) s : ℚ)
    set A' := ((q + 1 : ℕ) : ℚ) * (p : ℚ) / (s : ℚ)
    set B1 := (-1 : ℚ) ^ j₁ * (cJ (p - 1) j₁ : ℚ)
    set B2 := (-1 : ℚ) ^ j₂ * (cJ (p - 1) j₂ : ℚ)
    set B3 := (-1 : ℚ) ^ j₃ * (cJ (p - 1) j₃ : ℚ)
    set L1 := (p : ℚ) / (j₁ : ℚ)
    set L2 := (p : ℚ) / (j₂ : ℚ)
    set L3 := (p : ℚ) / (j₃ : ℚ)
    have hB1 := cJ_pm1_mod_p2 p j₁ hp hp7 hj₁.1 hj₁.2
    have hB2 := cJ_pm1_mod_p2 p j₂ hp hp7 hj₂.1 hj₂.2
    have hB3 := cJ_pm1_mod_p2 p j₃ hp hp7 hj3_ico.1 hj3_ico.2
    have hL1 : PVal p 1 L1 := (PVal.of_p hp).div_nat hp (not_dvd_of_lt_prime hp hj₁.1 hj₁.2)
    have hL2 : PVal p 1 L2 := (PVal.of_p hp).div_nat hp (not_dvd_of_lt_prime hp hj₂.1 hj₂.2)
    have hL3 : PVal p 1 L3 := (PVal.of_p hp).div_nat hp (not_dvd_of_lt_prime hp hj3_ico.1 hj3_ico.2)
    have hA'1 : PVal p 1 A' := ((PVal.nat hp (q + 1)).zero_mul hp (PVal.of_p hp)).div_nat hp hnd_s
    have hA1 : PVal p 1 A := by simpa using (hA_mod.mono (by decide : 1 ≤ 2)).add hp hA'1
    have hB1_1 : PVal p 1 B1 := by simpa only [B1, L1, sub_add_cancel] using (hB1.mono (by decide : 1 ≤ 2)).add hp hL1
    have hB2_1 : PVal p 1 B2 := by simpa only [B2, L2, sub_add_cancel] using (hB2.mono (by decide : 1 ≤ 2)).add hp hL2
    have hrew : (-1 : ℚ) ^ s * A * (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ) * (cJ (p - 1) j₃ : ℚ) -
        (p : ℚ) ^ 4 * (((q + 1 : ℕ) : ℚ) / ((s : ℚ) * (j₁ : ℚ) * (j₂ : ℚ) * (j₃ : ℚ))) =
        A * B1 * B2 * (B3 - L3) + A * B1 * (B2 - L2) * L3 + A * (B1 - L1) * (L2 * L3) +
        (A - A') * (L1 * L2 * L3) := by
      have h4 : A * B1 * B2 * B3 = (-1 : ℚ) ^ s * A * (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ) * (cJ (p - 1) j₃ : ℚ) := by
        simp only [B1, B2, B3, s, pow_add]; ring
      have h5 : A' * L1 * L2 * L3 = (p : ℚ) ^ 4 * (((q + 1 : ℕ) : ℚ) / ((s : ℚ) * (j₁ : ℚ) * (j₂ : ℚ) * (j₃ : ℚ))) := by
        simp only [A', L1, L2, L3, div_eq_mul_inv, mul_inv]; ring
      rw [← h4, ← h5]; ring
    rw [hrew]
    exact (((((hA1.mul hp hB1_1).mul hp hB2_1).mul hp hB3).add hp
      (((hA1.mul hp hB1_1).mul hp hB2).mul hp hL3)).add hp
      ((hA1.mul hp hB1).mul hp (hL2.mul hp hL3))).add hp
      (hA_mod.mul hp ((hL1.mul hp hL2).mul hp hL3))
  -- Show the p^4 sum vanishes mod p via involution + scaling by 2
  set S_wt := ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => ¬ p ∣ j₁ + j₂ + j₃),
    ((((j₁ + j₂ + j₃) / p + 1 : ℕ) : ℚ)) / (((j₁ + j₂ + j₃ : ℕ) : ℚ) * (j₁ : ℚ) * (j₂ : ℚ) * (j₃ : ℚ))
  set S_unwt := ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => ¬ p ∣ j₁ + j₂ + j₃),
    ((((j₁ + j₂ + j₃ : ℕ) : ℚ) * (j₁ : ℚ) * (j₂ : ℚ) * (j₃ : ℚ)))⁻¹
  have h2wt : PVal p 1 (2 * S_wt - 4 * S_unwt) := by
    have href : S_wt = ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => ¬ p ∣ j₁ + j₂ + j₃),
        (((3 * p - (j₁ + j₂ + j₃)) / p + 1 : ℕ) : ℚ) /
          (((3 * p - (j₁ + j₂ + j₃) : ℕ) : ℚ) * ((p - j₁ : ℕ) : ℚ) * ((p - j₂ : ℕ) : ℚ) * ((p - j₃ : ℕ) : ℚ)) := by
      simp only [S_wt]
      rw [← sum_Ico_reflect p]
      refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
      rw [← sum_Ico_reflect p]
      refine Finset.sum_congr rfl fun j₂ hj₂ => ?_
      rw [mem_Ico] at hj₁ hj₂
      rw [Finset.sum_filter, ← sum_Ico_reflect p, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j₃ hj₃ => ?_
      rw [mem_Ico] at hj₃
      have hsum : (p - j₁) + (p - j₂) + (p - j₃) = 3 * p - (j₁ + j₂ + j₃) := by omega
      have hdiv_iff : (p ∣ 3 * p - (j₁ + j₂ + j₃)) ↔ (p ∣ j₁ + j₂ + j₃) := by
        constructor <;> intro hd
        · have : j₁ + j₂ + j₃ = 3 * p - (3 * p - (j₁ + j₂ + j₃)) := by omega
          rw [this]; exact Nat.dvd_sub (dvd_mul_left p 3) hd
        · exact Nat.dvd_sub (dvd_mul_left p 3) hd
      simp only [hsum, hdiv_iff]
    rw [two_mul]; nth_rw 2 [href]
    simp only [S_wt, S_unwt, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine PVal.sum hp fun j₁ hj₁ => PVal.sum hp fun j₂ hj₂ => PVal.sum hp fun j₃ hj₃ => ?_
    rw [mem_filter] at hj₃
    have hnd_s : ¬ p ∣ j₁ + j₂ + j₃ := hj₃.2
    rw [mem_Ico] at hj₁ hj₂; have hj3_ico := mem_Ico.mp hj₃.1
    set s := j₁ + j₂ + j₃
    have hq_sum : (s / p + 1) + ((3 * p - s) / p + 1) = 4 := by
      have hr1 : 1 ≤ s % p := Nat.pos_of_ne_zero fun h0 => hnd_s (Nat.dvd_of_mod_eq_zero h0)
      have hrp : s % p < p := Nat.mod_lt s hp.pos
      have hq_le : s / p ≤ 2 := by
        have : s < 3 * p := by omega
        exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by linarith))
      have heq : 3 * p - s = (2 - s / p) * p + (p - s % p) := by
        have hdm := Nat.div_add_mod s p
        zify [show s ≤ 3 * p by omega, hq_le, show s % p ≤ p by omega]; linarith
      have hdiv : (3 * p - s) / p = 2 - s / p := by
        rw [heq, mul_comm (2 - s / p) p, Nat.mul_add_div hp.pos,
          Nat.div_eq_of_lt (by omega : p - s % p < p), add_zero]
      omega
    have hnd_sp : ¬ p ∣ 3 * p - s := fun hd => by
      have : s = 3 * p - (3 * p - s) := by omega
      rw [this] at hnd_s; exact hnd_s (Nat.dvd_sub (dvd_mul_left p 3) hd)
    have hnd_prod1 : ¬ p ∣ s * j₁ * j₂ * j₃ := fun h => by
      rcases hp.dvd_mul.mp h with h1 | h4
      · rcases hp.dvd_mul.mp h1 with h2 | h3
        · rcases hp.dvd_mul.mp h2 with hs' | h1'
          · exact hnd_s hs'
          · exact not_dvd_of_lt_prime hp hj₁.1 hj₁.2 h1'
        · exact not_dvd_of_lt_prime hp hj₂.1 hj₂.2 h3
      · exact not_dvd_of_lt_prime hp hj3_ico.1 hj3_ico.2 h4
    have hnd_prod2 : ¬ p ∣ (3 * p - s) * (p - j₁) * (p - j₂) * (p - j₃) := fun h => by
      rcases hp.dvd_mul.mp h with h1 | h4
      · rcases hp.dvd_mul.mp h1 with h2 | h3
        · rcases hp.dvd_mul.mp h2 with hs' | h1'
          · exact hnd_sp hs'
          · exact not_dvd_of_lt_prime hp (by omega) (by omega) h1'
        · exact not_dvd_of_lt_prime hp (by omega) (by omega) h3
      · exact not_dvd_of_lt_prime hp (by omega) (by omega) h4
    have hcong : (((3 * p - s) * (p - j₁) * (p - j₂) * (p - j₃) : ℕ) : ℤ) ≡
        ((s * j₁ * j₂ * j₃ : ℕ) : ℤ) [ZMOD (p : ℤ)] := by
      have h0 : ((3 * p - s : ℕ) : ℤ) ≡ -(s : ℤ) [ZMOD (p : ℤ)] :=
        Int.modEq_iff_dvd.mpr ⟨-3, by zify [show s ≤ 3 * p by omega]; ring⟩
      have h1 : ((p - j₁ : ℕ) : ℤ) ≡ -(j₁ : ℤ) [ZMOD (p : ℤ)] :=
        Int.modEq_iff_dvd.mpr ⟨-1, by zify [show j₁ ≤ p by omega]; ring⟩
      have h2 : ((p - j₂ : ℕ) : ℤ) ≡ -(j₂ : ℤ) [ZMOD (p : ℤ)] :=
        Int.modEq_iff_dvd.mpr ⟨-1, by zify [show j₂ ≤ p by omega]; ring⟩
      have h3 : ((p - j₃ : ℕ) : ℤ) ≡ -(j₃ : ℤ) [ZMOD (p : ℤ)] :=
        Int.modEq_iff_dvd.mpr ⟨-1, by zify [show j₃ ≤ p by omega]; ring⟩
      have hm := ((h0.mul h1).mul h2).mul h3
      push_cast; convert hm using 1; ring
    have hinv := inv_sub_inv_pval hp hnd_prod2 hnd_prod1 hcong
    have hq_cast : ((s / p + 1 : ℕ) : ℚ) + (((3 * p - s) / p + 1 : ℕ) : ℚ) = 4 := by exact_mod_cast hq_sum
    have hrew : ((s / p + 1 : ℕ) : ℚ) / ((s : ℚ) * (j₁ : ℚ) * (j₂ : ℚ) * (j₃ : ℚ)) +
        (((3 * p - s) / p + 1 : ℕ) : ℚ) / (((3 * p - s : ℕ) : ℚ) * ((p - j₁ : ℕ) : ℚ) * ((p - j₂ : ℕ) : ℚ) * ((p - j₃ : ℕ) : ℚ)) -
        4 * (((s : ℚ) * (j₁ : ℚ) * (j₂ : ℚ) * (j₃ : ℚ)))⁻¹ =
        (((3 * p - s) / p + 1 : ℕ) : ℚ) *
          (((((3 * p - s) * (p - j₁) * (p - j₂) * (p - j₃) : ℕ) : ℚ))⁻¹ - (((s * j₁ * j₂ * j₃ : ℕ) : ℚ))⁻¹) := by
      push_cast at hq_cast ⊢; simp only [div_eq_mul_inv]
      linear_combination (((s : ℚ) * (j₁ : ℚ) * (j₂ : ℚ) * (j₃ : ℚ)))⁻¹ * hq_cast
    rw [hrew]; exact (PVal.nat hp _).zero_mul hp hinv
  -- Scaling (j1, j2, j3) |-> ((2*j1)%p, (2*j2)%p, (2*j3)%p) kills S_unwt mod p!
  have hS_unwt : PVal p 1 S_unwt := by
    have hscale : S_unwt = ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => ¬ p ∣ j₁ + j₂ + j₃),
        (((((2 * j₁) % p + (2 * j₂) % p + (2 * j₃) % p : ℕ) : ℚ) *
          (((2 * j₁) % p : ℕ) : ℚ) * (((2 * j₂) % p : ℕ) : ℚ) * (((2 * j₃) % p : ℕ) : ℚ)))⁻¹ := by
      simp only [S_unwt]
      rw [← sum_Ico_mul_two_mod p hp (by omega)]
      refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
      rw [← sum_Ico_mul_two_mod p hp (by omega)]
      refine Finset.sum_congr rfl fun j₂ hj₂ => ?_
      rw [Finset.sum_filter, ← sum_Ico_mul_two_mod p hp (by omega), Finset.sum_filter]
      refine Finset.sum_congr rfl fun j₃ hj₃ => ?_
      have hdiv_iff : (¬ p ∣ (2 * j₁) % p + (2 * j₂) % p + (2 * j₃) % p) ↔ (¬ p ∣ j₁ + j₂ + j₃) := by
        have hmod : ((2 * j₁) % p + (2 * j₂) % p + (2 * j₃) % p) % p = (2 * (j₁ + j₂ + j₃)) % p := by
          have h1 : (2 * j₁) % p ≡ 2 * j₁ [MOD p] := Nat.mod_modEq _ _
          have h2 : (2 * j₂) % p ≡ 2 * j₂ [MOD p] := Nat.mod_modEq _ _
          have h3 : (2 * j₃) % p ≡ 2 * j₃ [MOD p] := Nat.mod_modEq _ _
          simpa only [Nat.ModEq, show 2 * j₁ + 2 * j₂ + 2 * j₃ = 2 * (j₁ + j₂ + j₃) by ring] using (h1.add h2).add h3
        constructor <;> intro h hd <;> apply h
        · exact Nat.dvd_of_mod_eq_zero (by rw [hmod]; exact Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right hd 2))
        · have h2d : p ∣ 2 * (j₁ + j₂ + j₃) := Nat.dvd_of_mod_eq_zero (by rw [← hmod]; exact Nat.mod_eq_zero_of_dvd hd)
          rcases hp.dvd_mul.mp h2d with h2 | hs
          · exact False.elim (hnd2 h2)
          · exact hs
      simp [hdiv_iff]
    have hdiff : PVal p 1 (S_unwt - (16 : ℚ)⁻¹ * S_unwt) := by
      nth_rw 1 [hscale]
      simp only [S_unwt, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine PVal.sum hp fun j₁ hj₁ => PVal.sum hp fun j₂ hj₂ => PVal.sum hp fun j₃ hj₃ => ?_
      rw [mem_filter] at hj₃
      have hnd_s : ¬ p ∣ j₁ + j₂ + j₃ := hj₃.2
      rw [mem_Ico] at hj₁ hj₂; have hj3_ico := mem_Ico.mp hj₃.1
      set a1 := (2 * j₁) % p
      set a2 := (2 * j₂) % p
      set a3 := (2 * j₃) % p
      have hnda : ∀ x ∈ Ico 1 p, ¬ p ∣ (2 * x) % p := fun x hx => by
        rw [mem_Ico] at hx
        have hne : (2 * x) % p ≠ 0 := fun h0 => by
          rcases hp.dvd_mul.mp (Nat.dvd_of_mod_eq_zero h0) with h2 | hx'
          · exact hnd2 h2
          · exact not_dvd_of_lt_prime hp hx.1 hx.2 hx'
        exact not_dvd_of_lt_prime hp (Nat.pos_of_ne_zero hne) (Nat.mod_lt _ hp.pos)
      have hnd_as : ¬ p ∣ a1 + a2 + a3 := fun hd => by
        have hmod : (a1 + a2 + a3) % p = (2 * (j₁ + j₂ + j₃)) % p := by
          have h1 : a1 ≡ 2 * j₁ [MOD p] := Nat.mod_modEq _ _
          have h2 : a2 ≡ 2 * j₂ [MOD p] := Nat.mod_modEq _ _
          have h3 : a3 ≡ 2 * j₃ [MOD p] := Nat.mod_modEq _ _
          simpa only [Nat.ModEq, show 2 * j₁ + 2 * j₂ + 2 * j₃ = 2 * (j₁ + j₂ + j₃) by ring] using (h1.add h2).add h3
        have h2d : p ∣ 2 * (j₁ + j₂ + j₃) := Nat.dvd_of_mod_eq_zero (by rw [← hmod]; exact Nat.mod_eq_zero_of_dvd hd)
        rcases hp.dvd_mul.mp h2d with h2 | hs
        · exact hnd2 h2
        · exact hnd_s hs
      have hnd_L : ¬ p ∣ (a1 + a2 + a3) * a1 * a2 * a3 := fun h => by
        rcases hp.dvd_mul.mp h with h1 | h4
        · rcases hp.dvd_mul.mp h1 with h2 | h3
          · rcases hp.dvd_mul.mp h2 with hs' | h1'
            · exact hnd_as hs'
            · exact hnda j₁ (mem_Ico.mpr hj₁) h1'
          · exact hnda j₂ (mem_Ico.mpr hj₂) h3
        · exact hnda j₃ (mem_Ico.mpr hj3_ico) h4
      have hnd_R : ¬ p ∣ 16 * ((j₁ + j₂ + j₃) * j₁ * j₂ * j₃) := fun h => by
        rcases hp.dvd_mul.mp h with h16 | hr
        · exact hnd2 (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 4 by simpa using h16))
        · rcases hp.dvd_mul.mp hr with h1 | h4
          · rcases hp.dvd_mul.mp h1 with h2 | h3
            · rcases hp.dvd_mul.mp h2 with hs' | h1'
              · exact hnd_s hs'
              · exact not_dvd_of_lt_prime hp hj₁.1 hj₁.2 h1'
            · exact not_dvd_of_lt_prime hp hj₂.1 hj₂.2 h3
          · exact not_dvd_of_lt_prime hp hj3_ico.1 hj3_ico.2 h4
      have hcong : (((a1 + a2 + a3) * a1 * a2 * a3 : ℕ) : ℤ) ≡
          ((16 * ((j₁ + j₂ + j₃) * j₁ * j₂ * j₃) : ℕ) : ℤ) [ZMOD (p : ℤ)] := by
        have hc : ∀ x : ℕ, (((2 * x) % p : ℕ) : ℤ) ≡ 2 * (x : ℤ) [ZMOD (p : ℤ)] := fun x => by
          simpa only [Int.ModEq, Int.natCast_mod, Nat.cast_mul, Nat.cast_ofNat] using Int.emod_emod (2 * (x : ℤ)) (p : ℤ)
        have h1 := hc j₁; have h2 := hc j₂; have h3 := hc j₃
        have hs := (h1.add h2).add h3
        have hm := ((hs.mul h1).mul h2).mul h3
        push_cast; convert hm using 1; ring
      have hinv := inv_sub_inv_pval hp hnd_L hnd_R hcong
      convert hinv using 1; push_cast; simp only [mul_inv]
    have h15 : PVal p 1 ((15 : ℕ) * S_unwt) := by
      have h16 := (PVal.nat hp 16).zero_mul hp hdiff
      convert h16 using 1; push_cast; ring
    exact PVal.div_of_mul_nat hp hnd15 h15
  have hS_wt : PVal p 1 S_wt := by
    have h2 : PVal p 1 ((2 : ℕ) * S_wt) := by
      simpa using h2wt.add hp ((PVal.nat hp 4).zero_mul hp hS_unwt)
    exact PVal.div_of_mul_nat hp hnd2 h2
  have h4 := (PVal.of_pow_p (e := 4) hp).mul hp hS_wt
  simpa using happrox.add hp h4

private lemma sum_range_zero_add_Ico (p : ℕ) (hp : 1 ≤ p) (f : ℕ → ℚ) :
    ∑ j ∈ range p, f j = f 0 + ∑ j ∈ Ico 1 p, f j :=
  Finset.sum_range_eq_add_Ico f hp

/-- E5: a(p - 1) - 1 == 9 * p * H_1 (mod p^5) for prime p >= 7. -/
private lemma a_pm1_mod_p5 (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    PVal p 5 ((OMA.S_oeis_a364114.a (p - 1) : ℚ) - 1 - 9 * (p : ℚ) * harmH p 1) := by
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  have hev : Even (3 * (p - 1)) := by obtain ⟨t, ht⟩ := hp_odd; exact ⟨3 * t, by omega⟩
  set g : ℕ → ℕ → ℕ → ℚ := fun j₁ j₂ j₃ =>
    (-1 : ℚ) ^ (j₁ + j₂ + j₃) * (Nat.choose (p - 1 + (j₁ + j₂ + j₃)) (j₁ + j₂ + j₃) : ℚ) *
      (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ) * (cJ (p - 1) j₃ : ℚ)
  have ha_eq : (OMA.S_oeis_a364114.a (p - 1) : ℚ) =
      ∑ j₁ ∈ range p, ∑ j₂ ∈ range p, ∑ j₃ ∈ range p, g j₁ j₂ j₃ := by
    have h := congrArg (Int.cast : ℤ → ℚ) (a_eq_dual_rep (p - 1))
    rw [Nat.sub_add_cancel hp.pos, hev.neg_one_pow, one_mul] at h
    simpa only [g, Int.cast_natCast, Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using h
  have hsym12 : ∀ a b c, g a b c = g b a c := fun a b c => by simp only [g, show a + b + c = b + a + c by omega]; ring
  have hsym13 : ∀ a b c, g a b c = g c b a := fun a b c => by simp only [g, show a + b + c = c + b + a by omega]; ring
  have hsplit_all : (OMA.S_oeis_a364114.a (p - 1) : ℚ) - 1 =
      3 * (∑ j ∈ Ico 1 p, (-1 : ℚ) ^ j * (Nat.choose (p - 1 + j) j : ℚ) * (cJ (p - 1) j : ℚ)) +
      3 * (∑ j ∈ Ico 1 p, (-1 : ℚ) ^ p * (Nat.choose (2 * p - 1) p : ℚ) * (cJ (p - 1) j : ℚ) * (cJ (p - 1) (p - j) : ℚ)) +
      3 * (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁), (-1 : ℚ) ^ (j₁ + j₂) *
        (Nat.choose (p - 1 + (j₁ + j₂)) (j₁ + j₂) : ℚ) * (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ)) +
      3 * (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico (p - j₁ + 1) p, (-1 : ℚ) ^ (j₁ + j₂) *
        (Nat.choose (p - 1 + (j₁ + j₂)) (j₁ + j₂) : ℚ) * (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ)) +
      (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => p ∣ j₁ + j₂ + j₃), g j₁ j₂ j₃) +
      (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => ¬ p ∣ j₁ + j₂ + j₃), g j₁ j₂ j₃) := by
    have h8 : (OMA.S_oeis_a364114.a (p - 1) : ℚ) =
        1 + 3 * (∑ j ∈ Ico 1 p, g j 0 0) + 3 * (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, g j₁ j₂ 0) +
        (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ Ico 1 p, g j₁ j₂ j₃) := by
      rw [ha_eq, sum_range_zero_add_Ico p hp.pos]
      simp_rw [sum_range_zero_add_Ico p hp.pos, Finset.sum_add_distrib]
      have h000 : g 0 0 0 = 1 := by simp [g, cJ]
      have h1a : ∑ j ∈ Ico 1 p, g 0 j 0 = ∑ j ∈ Ico 1 p, g j 0 0 :=
        Finset.sum_congr rfl fun j _ => hsym12 0 j 0
      have h1b : ∑ j ∈ Ico 1 p, g 0 0 j = ∑ j ∈ Ico 1 p, g j 0 0 :=
        Finset.sum_congr rfl fun j _ => hsym13 0 0 j
      have h2a : ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, g 0 j₁ j₂ = ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, g j₁ j₂ 0 := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j₂ _ => Finset.sum_congr rfl fun j₁ _ => by rw [hsym13, hsym12]
      have h2b : ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, g j₁ 0 j₂ = ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, g j₁ j₂ 0 :=
        Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => by rw [hsym12, hsym13, hsym12]
      rw [h000, h1a, h1b, h2a, h2b]; ring
    have hb1_eq : ∑ j ∈ Ico 1 p, g j 0 0 =
        ∑ j ∈ Ico 1 p, (-1 : ℚ) ^ j * (Nat.choose (p - 1 + j) j : ℚ) * (cJ (p - 1) j : ℚ) :=
      Finset.sum_congr rfl fun j _ => by simp [g, cJ]
    have hb2_split : ∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, g j₁ j₂ 0 =
        (∑ j ∈ Ico 1 p, (-1 : ℚ) ^ p * (Nat.choose (2 * p - 1) p : ℚ) * (cJ (p - 1) j : ℚ) * (cJ (p - 1) (p - j) : ℚ)) +
        (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 (p - j₁), (-1 : ℚ) ^ (j₁ + j₂) *
          (Nat.choose (p - 1 + (j₁ + j₂)) (j₁ + j₂) : ℚ) * (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ)) +
        (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico (p - j₁ + 1) p, (-1 : ℚ) ^ (j₁ + j₂) *
          (Nat.choose (p - 1 + (j₁ + j₂)) (j₁ + j₂) : ℚ) * (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ)) := by
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
      rw [mem_Ico] at hj₁
      have hcon1 := Finset.sum_Ico_consecutive (fun j₂ => g j₁ j₂ 0) (by omega : 1 ≤ p - j₁) (by omega : p - j₁ ≤ p)
      have hcon2 := Finset.sum_Ico_consecutive (fun j₂ => g j₁ j₂ 0) (by omega : p - j₁ ≤ p - j₁ + 1) (by omega : p - j₁ + 1 ≤ p)
      rw [← hcon1, ← hcon2]
      have hmid : ∑ j₂ ∈ Ico (p - j₁) (p - j₁ + 1), g j₁ j₂ 0 =
          (-1 : ℚ) ^ p * (Nat.choose (2 * p - 1) p : ℚ) * (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) (p - j₁) : ℚ) := by
        simp [g, cJ, show j₁ + (p - j₁) = p by omega, show p - 1 + p = 2 * p - 1 by omega]
      have hlt : ∑ j₂ ∈ Ico 1 (p - j₁), g j₁ j₂ 0 =
          ∑ j₂ ∈ Ico 1 (p - j₁), (-1 : ℚ) ^ (j₁ + j₂) * (Nat.choose (p - 1 + (j₁ + j₂)) (j₁ + j₂) : ℚ) *
            (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ) :=
        Finset.sum_congr rfl fun j₂ _ => by simp [g, cJ]
      have hgt : ∑ j₂ ∈ Ico (p - j₁ + 1) p, g j₁ j₂ 0 =
          ∑ j₂ ∈ Ico (p - j₁ + 1) p, (-1 : ℚ) ^ (j₁ + j₂) * (Nat.choose (p - 1 + (j₁ + j₂)) (j₁ + j₂) : ℚ) *
            (cJ (p - 1) j₁ : ℚ) * (cJ (p - 1) j₂ : ℚ) :=
        Finset.sum_congr rfl fun j₂ _ => by simp [g, cJ]
      rw [hmid, hlt, hgt]; ring
    have hb3_split : (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ Ico 1 p, g j₁ j₂ j₃) =
        (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => p ∣ j₁ + j₂ + j₃), g j₁ j₂ j₃) +
        (∑ j₁ ∈ Ico 1 p, ∑ j₂ ∈ Ico 1 p, ∑ j₃ ∈ (Ico 1 p).filter (fun j₃ => ¬ p ∣ j₁ + j₂ + j₃), g j₁ j₂ j₃) := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ =>
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    rw [h8, hb1_eq, hb2_split, hb3_split]; ring
  rw [hsplit_all]
  have hcomb := (((((e5_b1 p hp hp7).add hp (e5_b2_eq p hp hp7)).add hp (e5_b2_lt p hp hp7)).add hp
    (e5_b2_gt p hp hp7)).add hp (e5_b3_div p hp hp7)).add hp (e5_b3_ndiv p hp hp7)
  convert hcomb using 1; ring

/-- E6 (Theorem P3): 3 * a(p) == 10 + 11 * a(p - 1) [MOD p^5] for prime p >= 7. -/
private lemma part3_main (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    Nat.ModEq (p ^ 5) (3 * OMA.S_oeis_a364114.a p) (10 + 11 * OMA.S_oeis_a364114.a (p - 1)) := by
  have hpv : PVal p 5 ((((3 * OMA.S_oeis_a364114.a p : ℕ) : ℤ) : ℚ) -
      (((10 + 11 * OMA.S_oeis_a364114.a (p - 1) : ℕ) : ℤ) : ℚ)) := by
    have h1 := (PVal.nat hp 3).zero_mul hp (a_p_mod_p5 p hp hp7)
    have h2 := (PVal.nat hp 11).zero_mul hp (a_pm1_mod_p5 p hp hp7)
    have hsub := h1.sub hp h2
    convert hsub using 1; push_cast; ring
  have hz := PVal.modEq_of_sub hp hpv
  exact Int.natCast_modEq_iff.mp (by simpa [Nat.cast_pow] using hz)

private lemma a_zero : OMA.S_oeis_a364114.a 0 = 1 := by
  have h := a_eq_Q_rep 0
  norm_num [Finset.sum_range_succ] at h
  exact_mod_cast h

private lemma a_one : OMA.S_oeis_a364114.a 1 = 7 := by
  have h := a_eq_Q_rep 1
  norm_num [Finset.sum_range_succ] at h
  exact_mod_cast h

/-- Helper: (c + x)^k == c^k + k * c^(k - 1) * x [ZMOD p^5] when p^3 | x. -/
private lemma pow_add_mod_p5 (p : ℕ) (c x : ℤ) (k : ℕ) (hk : 1 ≤ k) (hx : (p : ℤ) ^ 3 ∣ x) :
    (c + x) ^ k ≡ c ^ k + (k : ℤ) * c ^ (k - 1) * x [ZMOD (p : ℤ) ^ 5] := by
  rw [add_comm c x, add_pow]
  have hsplit : ∑ m ∈ range (k + 1), x ^ m * c ^ (k - m) * (Nat.choose k m : ℤ) =
      c ^ k + (k : ℤ) * c ^ (k - 1) * x +
      ∑ m ∈ Ico 2 (k + 1), x ^ m * c ^ (k - m) * (Nat.choose k m : ℤ) := by
    by_cases hk1 : k = 1
    · subst hk1; simp [Finset.sum_range_succ]
    · have h2 : 2 ≤ k + 1 := by omega
      have hc := Finset.sum_Ico_consecutive (fun m => x ^ m * c ^ (k - m) * (Nat.choose k m : ℤ))
        (by decide : 0 ≤ 2) h2
      rw [Finset.range_eq_Ico, ← hc, Finset.sum_Ico_succ_top (by decide : 0 ≤ 1),
        Finset.sum_Ico_succ_top (by decide : 0 ≤ 0)]
      simp only [Finset.Ico_self, Finset.sum_empty, zero_add, pow_zero, pow_one,
        Nat.sub_zero, Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, one_mul, mul_one]
      ring
  rw [hsplit]
  have htail : (p : ℤ) ^ 5 ∣ ∑ m ∈ Ico 2 (k + 1), x ^ m * c ^ (k - m) * (Nat.choose k m : ℤ) := by
    refine Finset.dvd_sum fun m hm => ?_
    rw [mem_Ico] at hm
    have hxm : (p : ℤ) ^ 5 ∣ x ^ m := by
      have h1 : (p : ℤ) ^ 6 ∣ x ^ 2 := by
        simpa [← pow_mul] using pow_dvd_pow_of_dvd hx 2
      exact dvd_trans (pow_dvd_pow (p : ℤ) (by decide : 5 ≤ 6)) (dvd_trans h1 (pow_dvd_pow x hm.1))
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hxm _) _
  have hd : (c ^ k + (k : ℤ) * c ^ (k - 1) * x) -
      (c ^ k + (k : ℤ) * c ^ (k - 1) * x + ∑ m ∈ Ico 2 (k + 1), x ^ m * c ^ (k - m) * (Nat.choose k m : ℤ)) =
      -(∑ m ∈ Ico 2 (k + 1), x ^ m * c ^ (k - m) * (Nat.choose k m : ℤ)) := by ring
  exact Int.modEq_iff_dvd.mpr (by rw [hd]; exact dvd_neg.mpr htail)

/-- E7 (Theorem P4): a(p)^21 == 7^21 * a(p - 1)^11 [MOD p^5] for prime p >= 7. -/
private lemma part4_main (p : ℕ) (hp : p.Prime) (hp7 : 7 ≤ p) :
    Nat.ModEq (p ^ 5) ((OMA.S_oeis_a364114.a p) ^ 21) (7 ^ 21 * (OMA.S_oeis_a364114.a (p - 1)) ^ 11) := by
  have hp1 := part1_main p 1 1 hp (by omega) one_pos one_pos
  have hp2 := part2_main p 1 1 hp (by omega) one_pos one_pos
  have hp3 := part3_main p hp hp7
  simp only [pow_one, one_mul, Nat.sub_self, pow_zero, mul_one, a_one, a_zero] at hp1 hp2
  have hd1 : (p : ℤ) ^ 3 ∣ (OMA.S_oeis_a364114.a p : ℤ) - 7 := by
    have hz := Int.natCast_modEq_iff.mpr hp1
    simpa [Nat.cast_pow] using Int.modEq_iff_dvd.mp hz.symm
  have hd2 : (p : ℤ) ^ 3 ∣ (OMA.S_oeis_a364114.a (p - 1) : ℤ) - 1 := by
    have hz := Int.natCast_modEq_iff.mpr hp2
    simpa [Nat.cast_pow] using Int.modEq_iff_dvd.mp hz.symm
  have hd3 : (p : ℤ) ^ 5 ∣ 3 * (OMA.S_oeis_a364114.a p : ℤ) - (10 + 11 * (OMA.S_oeis_a364114.a (p - 1) : ℤ)) := by
    have hz := Int.natCast_modEq_iff.mpr hp3
    simpa [Nat.cast_pow, Nat.cast_mul, Nat.cast_add] using Int.modEq_iff_dvd.mp hz.symm
  set x : ℤ := (OMA.S_oeis_a364114.a p : ℤ) - 7
  set y : ℤ := (OMA.S_oeis_a364114.a (p - 1) : ℤ) - 1
  have hxp : (OMA.S_oeis_a364114.a p : ℤ) = 7 + x := by ring
  have hyp : (OMA.S_oeis_a364114.a (p - 1) : ℤ) = 1 + y := by ring
  have h1 := pow_add_mod_p5 p 7 x 21 (by decide) hd1
  have h2 := (pow_add_mod_p5 p 1 y 11 (by decide) hd2).mul_left ((7 : ℤ) ^ 21)
  have hdiff_lin : ((7 : ℤ) ^ 21 + 21 * (7 : ℤ) ^ 20 * x) ≡
      (7 : ℤ) ^ 21 * ((1 : ℤ) ^ 11 + 11 * (1 : ℤ) ^ 10 * y) [ZMOD (p : ℤ) ^ 5] := by
    refine Int.modEq_iff_dvd.mpr ?_
    have heq : (7 : ℤ) ^ 21 * ((1 : ℤ) ^ 11 + 11 * (1 : ℤ) ^ 10 * y) -
        ((7 : ℤ) ^ 21 + 21 * (7 : ℤ) ^ 20 * x) =
        -(7 : ℤ) ^ 21 * (3 * (OMA.S_oeis_a364114.a p : ℤ) - (10 + 11 * (OMA.S_oeis_a364114.a (p - 1) : ℤ))) := by
      simp only [x, y]; ring
    rw [heq]; exact dvd_mul_of_dvd_right hd3 _
  have hfin : (OMA.S_oeis_a364114.a p : ℤ) ^ 21 ≡
      (7 : ℤ) ^ 21 * (OMA.S_oeis_a364114.a (p - 1) : ℤ) ^ 11 [ZMOD (p : ℤ) ^ 5] := by
    rw [hxp, hyp]
    exact (h1.trans (by simpa using hdiff_lin)).trans h2.symm
  exact Int.natCast_modEq_iff.mp (by simpa [Nat.cast_pow, Nat.cast_mul] using hfin)

end OMA.S_oeis_a364114.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a364114.main :=
  ⟨fun p n r hp hp5 hn hr =>
      ⟨OMA.S_oeis_a364114.Proof.part1_main p n r hp hp5 hn hr,
       OMA.S_oeis_a364114.Proof.part2_main p n r hp hp5 hn hr⟩,
   fun p hp hp7 =>
      ⟨OMA.S_oeis_a364114.Proof.part3_main p hp hp7,
       OMA.S_oeis_a364114.Proof.part4_main p hp hp7⟩⟩
