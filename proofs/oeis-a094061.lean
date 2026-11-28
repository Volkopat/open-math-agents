import OMAStatements.S_oeis_a094061

namespace OeisA094061

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
-- Block 1: Exact Polynomial and Binomial Identities for Closed King Walks
-- ============================================================================

private def f (r : ℕ) : ℕ := Nat.choose (2 * r) r

private def M (N r s : ℕ) : ℤ :=
  (-1 : ℤ) ^ (r + s) * (Nat.choose N r : ℤ) * (Nat.choose r (N - s) : ℤ)

private noncomputable def T (n m : ℕ) : ℕ :=
  ((1 + X + X ^ 2 : ℕ[X]) ^ n).coeff m

private noncomputable def B (N s : ℕ) : ℤ :=
  (((1 + X + X ^ 2 : ℤ[X]) ^ s * (1 + X : ℤ[X]) ^ (2 * (N - s)))).coeff N

private lemma T_cast_int (n m : ℕ) :
    ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff m = (T n m : ℤ) := by
  have hmap : ((1 + X + X ^ 2 : ℕ[X]) ^ n).map (Nat.castRingHom ℤ) =
      (1 + X + X ^ 2 : ℤ[X]) ^ n := by
    simp [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, Polynomial.map_X]
  rw [← hmap, Polynomial.coeff_map]
  rfl

private lemma one_add_X_pow_coeff (n k : ℕ) :
    ((1 + X : ℤ[X]) ^ n).coeff k = (Nat.choose n k : ℤ) := by
  rw [add_comm, add_pow, Polynomial.finsetSum_coeff]
  by_cases hk : k ≤ n
  · have hmem : k ∈ range (n + 1) := mem_range.mpr (by omega)
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hne
      simp [Polynomial.coeff_X_pow, Ne.symm hne]
    · intro h; exact absurd hmem h
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i < n + 1 := mem_range.mp hi
    have hne : k ≠ i := by omega
    simp [Polynomial.coeff_X_pow, hne]

private lemma one_add_X_pow_coeff_nat (n k : ℕ) :
    ((1 + X : ℕ[X]) ^ n).coeff k = Nat.choose n k := by
  have h := one_add_X_pow_coeff n k
  have hmap : ((1 + X : ℕ[X]) ^ n).map (Nat.castRingHom ℤ) = (1 + X : ℤ[X]) ^ n := by
    simp [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, Polynomial.map_X]
  rw [← hmap, Polynomial.coeff_map] at h
  exact Nat.cast_injective (R := ℤ) h

private lemma T_zero_left (m : ℕ) : T 0 m = if m = 0 then 1 else 0 := by
  unfold T
  simp [Polynomial.coeff_one]

private lemma T_zero_right (n : ℕ) : T n 0 = 1 := by
  unfold T
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp

private lemma T_eq_zero_of_gt (n m : ℕ) (hm : 2 * n < m) : T n m = 0 := by
  unfold T
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have h1 : (1 + X + X ^ 2 : ℕ[X]).natDegree ≤ 2 := by
    have h1x : (1 + X : ℕ[X]).natDegree ≤ 1 :=
      le_trans (Polynomial.natDegree_add_le _ _) (by simp)
    calc (1 + X + X ^ 2 : ℕ[X]).natDegree
        ≤ max (1 + X : ℕ[X]).natDegree (X ^ 2 : ℕ[X]).natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 2 := max_le (by omega) (by simp)
  have h2 : ((1 + X + X ^ 2 : ℕ[X]) ^ n).natDegree ≤ 2 * n := by
    calc ((1 + X + X ^ 2 : ℕ[X]) ^ n).natDegree
        ≤ n * (1 + X + X ^ 2 : ℕ[X]).natDegree := Polynomial.natDegree_pow_le
      _ ≤ n * 2 := Nat.mul_le_mul_left n h1
      _ = 2 * n := by ring
  omega

private lemma T_two_mul_self (n : ℕ) : T n (2 * n) = 1 := by
  unfold T
  have hlt : (X + 1 : ℕ[X]).natDegree < (X ^ 2 : ℕ[X]).natDegree := by
    have : (X + 1 : ℕ[X]).natDegree ≤ 1 :=
      le_trans (Polynomial.natDegree_add_le _ _) (by simp)
    simp only [Polynomial.natDegree_X_pow]
    omega
  have hmon : (1 + X + X ^ 2 : ℕ[X]).Monic := by
    have hrew : (1 + X + X ^ 2 : ℕ[X]) = X ^ 2 + (X + 1) := by ring
    rw [hrew]
    apply Polynomial.monic_X_pow_add
    exact lt_of_lt_of_eq (Polynomial.degree_lt_degree hlt) (Polynomial.degree_X_pow 2)
  have hdeg : (1 + X + X ^ 2 : ℕ[X]).natDegree = 2 := by
    have hrew : (1 + X + X ^ 2 : ℕ[X]) = X ^ 2 + (X + 1) := by ring
    rw [hrew, Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
  have hpow_mon : ((1 + X + X ^ 2 : ℕ[X]) ^ n).Monic := hmon.pow n
  have hpow_deg : ((1 + X + X ^ 2 : ℕ[X]) ^ n).natDegree = 2 * n := by
    rw [hmon.natDegree_pow, hdeg]; ring
  rw [← hpow_deg]
  exact hpow_mon.leadingCoeff

private lemma T_add (n₁ n₂ m : ℕ) :
    T (n₁ + n₂) m =
      ∑ a ∈ range (2 * n₂ + 1), if a ≤ m then T n₁ (m - a) * T n₂ a else 0 := by
  unfold T
  rw [add_comm n₁ n₂, pow_add, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have h1 : ∑ a ∈ range (m + 1),
      ((1 + X + X ^ 2 : ℕ[X]) ^ n₂).coeff a * ((1 + X + X ^ 2 : ℕ[X]) ^ n₁).coeff (m - a) =
      ∑ a ∈ range (max m (2 * n₂) + 1),
        if a ≤ m then
          ((1 + X + X ^ 2 : ℕ[X]) ^ n₁).coeff (m - a) * ((1 + X + X ^ 2 : ℕ[X]) ^ n₂).coeff a
        else 0 := by
    symm
    rw [← Finset.sum_filter]
    have hfilt : (range (max m (2 * n₂) + 1)).filter (fun a => a ≤ m) = range (m + 1) := by
      ext a; simp only [mem_filter, mem_range]; omega
    rw [hfilt]
    refine Finset.sum_congr rfl fun a _ => by ring
  have h2 : ∑ a ∈ range (2 * n₂ + 1),
      (if a ≤ m then
        ((1 + X + X ^ 2 : ℕ[X]) ^ n₁).coeff (m - a) * ((1 + X + X ^ 2 : ℕ[X]) ^ n₂).coeff a
      else 0) =
      ∑ a ∈ range (max m (2 * n₂) + 1),
        if a ≤ m then
          ((1 + X + X ^ 2 : ℕ[X]) ^ n₁).coeff (m - a) * ((1 + X + X ^ 2 : ℕ[X]) ^ n₂).coeff a
        else 0 := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun a ha hnot => ?_
    rw [mem_range] at ha hnot
    split_ifs with hle
    · have hz : ((1 + X + X ^ 2 : ℕ[X]) ^ n₂).coeff a = 0 := T_eq_zero_of_gt n₂ a (by omega)
      rw [hz, mul_zero]
    · rfl
  rw [h1, ← h2]

private lemma T_multinom_sum (N M : ℕ) :
    T N M = ∑ c ∈ range (N + 1),
      if 2 * c ≤ M then Nat.choose N c * Nat.choose (N - c) (M - 2 * c) else 0 := by
  unfold T
  have hrew : (1 + X + X ^ 2 : ℕ[X]) ^ N =
      ∑ c ∈ range (N + 1), (X ^ 2 : ℕ[X]) ^ c * (1 + X : ℕ[X]) ^ (N - c) * (Nat.choose N c : ℕ[X]) := by
    rw [show (1 + X + X ^ 2 : ℕ[X]) = X ^ 2 + (1 + X) by ring, add_pow]
  rw [hrew, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hterm : (X ^ 2 : ℕ[X]) ^ c * (1 + X : ℕ[X]) ^ (N - c) * (Nat.choose N c : ℕ[X]) =
      X ^ (2 * c) * (C (Nat.choose N c) * (1 + X : ℕ[X]) ^ (N - c)) := by
    have hC : (Nat.choose N c : ℕ[X]) = C (Nat.choose N c) := (Polynomial.C_eq_natCast (N.choose c)).symm
    rw [← pow_mul, hC]; ring
  rw [hterm, Polynomial.coeff_X_pow_mul']
  split_ifs with hle
  · rw [Polynomial.coeff_C_mul, one_add_X_pow_coeff_nat]
  · rfl

private noncomputable def invPoly (M N : ℕ) : ℤ[X] :=
  ∑ m ∈ range (M + 1), C (((N + m - 1).choose m : ℤ)) * X ^ m

private lemma coeff_invPoly (M N d : ℕ) :
    (invPoly M N).coeff d = if d ≤ M then ((N + d - 1).choose d : ℤ) else 0 := by
  simp only [invPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  by_cases hd : d ≤ M
  · simp only [hd, ↓reduceIte]
    rw [Finset.sum_eq_single d]
    · simp
    · intro m _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (mem_range.mpr (by omega)) h
  · simp only [hd, ↓reduceIte]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hmM : m < M + 1 := mem_range.mp hm
    have hne : d ≠ m := by omega
    simp [hne]

private lemma coeff_mul_congr_right (P Q₁ Q₂ : ℤ[X]) (d : ℕ)
    (h : ∀ j ≤ d, Q₁.coeff j = Q₂.coeff j) :
    (P * Q₁).coeff d = (P * Q₂).coeff d := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h (d - i) (Nat.sub_le d i)]

private lemma coeff_one_sub_X_mul (Q : ℤ[X]) (d : ℕ) :
    ((1 - X : ℤ[X]) * Q).coeff d = Q.coeff d - (if d = 0 then 0 else Q.coeff (d - 1)) := by
  rw [sub_mul, one_mul, Polynomial.coeff_sub]
  cases d with
  | zero => simp
  | succ d => simp [Polynomial.coeff_X_mul]

private lemma coeff_one_sub_X_mul_invPoly (M N d : ℕ) (hN : 1 ≤ N) (hd : d ≤ M) :
    ((1 - X : ℤ[X]) * invPoly M (N + 1)).coeff d = (invPoly M N).coeff d := by
  rw [coeff_one_sub_X_mul]
  cases d with
  | zero => simp [coeff_invPoly]
  | succ d' =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
    rw [coeff_invPoly, coeff_invPoly, coeff_invPoly]
    have hd1 : d' + 1 ≤ M := hd
    have hd2 : d' ≤ M := by omega
    simp only [hd1, hd2, ↓reduceIte]
    have hpas : (N + 1 + (d' + 1) - 1).choose (d' + 1) =
        (N + 1 + d' - 1).choose d' + (N + (d' + 1) - 1).choose (d' + 1) := by
      have h1 : N + 1 + (d' + 1) - 1 = (N + d') + 1 := by omega
      have h2 : N + 1 + d' - 1 = N + d' := by omega
      have h3 : N + (d' + 1) - 1 = N + d' := by omega
      rw [h1, h2, h3, Nat.choose_succ_succ]
    have hpas_z : ((N + 1 + (d' + 1) - 1).choose (d' + 1) : ℤ) =
        ((N + 1 + d' - 1).choose d' : ℤ) + ((N + (d' + 1) - 1).choose (d' + 1) : ℤ) := by
      exact_mod_cast hpas
    linarith

private lemma coeff_one_sub_X_pow_mul_invPoly (M N : ℕ) (hN : 1 ≤ N) :
    ∀ d ≤ M, ((1 - X : ℤ[X]) ^ N * invPoly M N).coeff d = if d = 0 then 1 else 0 := by
  obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  clear hN
  induction N' with
  | zero =>
    intro d hd
    simp only [pow_one]
    rw [coeff_one_sub_X_mul, coeff_invPoly]
    cases d with
    | zero => simp
    | succ d' =>
      have hd1 : d' + 1 ≤ M := hd
      have hd2 : d' ≤ M := by omega
      simp [coeff_invPoly, hd1, hd2]
  | succ N' ih =>
    intro d hd
    have hmul : (1 - X : ℤ[X]) ^ (N' + 1 + 1) * invPoly M (N' + 1 + 1) =
        (1 - X : ℤ[X]) ^ (N' + 1) * ((1 - X : ℤ[X]) * invPoly M (N' + 1 + 1)) := by
      rw [pow_succ]; ring
    rw [hmul]
    rw [coeff_mul_congr_right _ _ (invPoly M (N' + 1)) d
      (fun j hj => coeff_one_sub_X_mul_invPoly M (N' + 1) j (by omega) (by omega))]
    exact ih d hd

private lemma coeff_one_sub_X_cube_pow (N d : ℕ) :
    ((1 - X ^ 3 : ℤ[X]) ^ N).coeff d =
      if 3 ∣ d then (-1 : ℤ) ^ (d / 3) * (N.choose (d / 3) : ℤ) else 0 := by
  have hexp : (1 - X ^ 3 : ℤ[X]) ^ N =
      ∑ r ∈ range (N + 1), C ((-1 : ℤ) ^ r * (N.choose r : ℤ)) * X ^ (3 * r) := by
    have hadd := add_pow (-X ^ 3 : ℤ[X]) 1 N
    rw [show (1 - X ^ 3 : ℤ[X]) = -X ^ 3 + 1 by ring, hadd]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [one_pow, mul_one]
    rw [show (-X ^ 3 : ℤ[X]) = C (-1 : ℤ) * X ^ 3 by simp, mul_pow, ← map_pow, ← pow_mul]
    rw [show (N.choose r : ℤ[X]) = C (N.choose r : ℤ) by simp]
    rw [map_mul]
    ring
  rw [hexp, finsetSum_coeff]
  simp_rw [coeff_C_mul, coeff_X_pow]
  by_cases h3 : 3 ∣ d
  · simp only [h3, ↓reduceIte]
    obtain ⟨q, rfl⟩ := h3
    have hqdiv : 3 * q / 3 = q := Nat.mul_div_cancel_left q (by decide)
    rw [hqdiv]
    by_cases hqN : q ≤ N
    · rw [Finset.sum_eq_single q]
      · simp
      · intro r _ hne
        have : 3 * q ≠ 3 * r := by omega
        simp [this]
      · intro h; exact absurd (mem_range.mpr (by omega)) h
    · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, mul_zero]
      refine Finset.sum_eq_zero fun r hr => ?_
      have hrN : r < N + 1 := mem_range.mp hr
      have : 3 * q ≠ 3 * r := by omega
      simp [this]
  · simp only [h3, ↓reduceIte]
    refine Finset.sum_eq_zero fun r _ => ?_
    have : d ≠ 3 * r := by intro heq; exact h3 ⟨r, heq⟩
    simp [this]

private lemma T_eq_conv (N M : ℕ) (hN : 1 ≤ N) :
    (T N M : ℤ) =
      ∑ r ∈ range (M / 3 + 1),
        (-1 : ℤ) ^ r * (N.choose r : ℤ) * ((N + (M - 3 * r) - 1).choose (M - 3 * r) : ℤ) := by
  rw [← T_cast_int]
  have hid : ((1 - X : ℤ[X]) ^ N * invPoly M N) * (1 + X + X ^ 2 : ℤ[X]) ^ N =
      (1 - X ^ 3 : ℤ[X]) ^ N * invPoly M N := by
    have hbase : (1 - X : ℤ[X]) * (1 + X + X ^ 2 : ℤ[X]) = 1 - X ^ 3 := by ring
    calc ((1 - X : ℤ[X]) ^ N * invPoly M N) * (1 + X + X ^ 2 : ℤ[X]) ^ N
        = ((1 - X : ℤ[X]) * (1 + X + X ^ 2 : ℤ[X])) ^ N * invPoly M N := by rw [mul_pow]; ring
      _ = (1 - X ^ 3 : ℤ[X]) ^ N * invPoly M N := by rw [hbase]
  have hcoeff := congrArg (fun P : ℤ[X] => P.coeff M) hid
  have hLHS : (((1 - X : ℤ[X]) ^ N * invPoly M N) * (1 + X + X ^ 2 : ℤ[X]) ^ N).coeff M =
      ((1 + X + X ^ 2 : ℤ[X]) ^ N).coeff M := by
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_eq_single 0]
    · rw [coeff_one_sub_X_pow_mul_invPoly M N hN 0 (Nat.zero_le M)]; simp
    · intro i hi hne
      rw [mem_range] at hi
      rw [coeff_one_sub_X_pow_mul_invPoly M N hN i (by omega)]
      simp [hne]
    · intro h; exact absurd (mem_range.mpr (Nat.zero_lt_succ M)) h
  have hRHS : ((1 - X ^ 3 : ℤ[X]) ^ N * invPoly M N).coeff M =
      ∑ r ∈ range (M / 3 + 1),
        (-1 : ℤ) ^ r * (N.choose r : ℤ) * ((N + (M - 3 * r) - 1).choose (M - 3 * r) : ℤ) := by
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun i : ℕ => 3 ∣ i)]
    have hnot : ∑ i ∈ (range (M + 1)).filter (fun i : ℕ => ¬ 3 ∣ i),
        ((1 - X ^ 3 : ℤ[X]) ^ N).coeff i * (invPoly M N).coeff (M - i) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hnd : ¬ 3 ∣ i := (Finset.mem_filter.mp hi).2
      rw [coeff_one_sub_X_cube_pow]; simp [hnd]
    rw [hnot, add_zero]
    symm
    refine Finset.sum_bij (fun r _ => 3 * r) ?_ ?_ ?_ ?_
    · intro r hr
      have hr' : r < M / 3 + 1 := mem_range.mp hr
      rw [Finset.mem_filter, mem_range]
      exact ⟨by omega, ⟨r, rfl⟩⟩
    · intro r₁ _ r₂ _ heq; omega
    · intro i hi
      rw [Finset.mem_filter, mem_range] at hi
      obtain ⟨hi', ⟨r, rfl⟩⟩ := hi
      exact ⟨r, mem_range.mpr (by omega), rfl⟩
    · intro r hr
      have hr' : r < M / 3 + 1 := mem_range.mp hr
      rw [coeff_one_sub_X_cube_pow, coeff_invPoly]
      have h3 : 3 ∣ 3 * r := ⟨r, rfl⟩
      have hdiv : 3 * r / 3 = r := Nat.mul_div_cancel_left r (by decide)
      have hle : M - 3 * r ≤ M := Nat.sub_le M (3 * r)
      simp only [h3, hdiv, hle, ↓reduceIte]
  rw [← hLHS, hcoeff, hRHS]

private lemma neg_one_pow_eq_of_even_add (a b : ℕ) (h : Even (a + b)) :
    (-1 : ℤ) ^ a = (-1 : ℤ) ^ b := by
  rcases h with ⟨t, ht⟩
  have h1 : (-1 : ℤ) ^ (a + b) = 1 := by
    rw [ht, show t + t = 2 * t by ring, pow_mul]; norm_num
  have h2 : (-1 : ℤ) ^ a * (-1 : ℤ) ^ b = 1 := by rwa [← pow_add]
  have h3 : (-1 : ℤ) ^ b * (-1 : ℤ) ^ b = 1 := by
    rw [← pow_add, show b + b = 2 * b by ring, pow_mul]; norm_num
  have h4 := congrArg (fun x => x * (-1 : ℤ) ^ b) h2
  simp only [mul_assoc, h3, mul_one, one_mul] at h4
  exact h4

private lemma neg_one_pow_mul_odd (p a : ℕ) (hp : Odd p) :
    (-1 : ℤ) ^ (p * a) = (-1 : ℤ) ^ a := by
  rw [pow_mul, hp.neg_one_pow]

private lemma M_symm (N r s : ℕ) (hr : r ≤ N) (hs : s ≤ N) : M N r s = M N s r := by
  unfold M
  rw [add_comm s r]
  by_cases hrs : N ≤ r + s
  · have h1 : Nat.choose N r * Nat.choose r (N - s) =
        Nat.choose N (N - s) * Nat.choose (N - (N - s)) (r - (N - s)) :=
      Nat.choose_mul (n := N) (by omega : N - s ≤ r)
    have h2 : Nat.choose N (N - s) = Nat.choose N s := Nat.choose_symm hs
    have h3 : N - (N - s) = s := by omega
    have h4 : Nat.choose s (r - (N - s)) = Nat.choose s (N - r) := by
      have hsym := Nat.choose_symm (n := s) (k := N - r) (by omega)
      have hsub : s - (N - r) = r - (N - s) := by omega
      rwa [hsub] at hsym
    rw [h2, h3, h4] at h1
    have hcast : ((Nat.choose N r : ℤ) * (Nat.choose r (N - s) : ℤ)) =
        ((Nat.choose N s : ℤ) * (Nat.choose s (N - r) : ℤ)) := by exact_mod_cast h1
    calc (-1 : ℤ) ^ (r + s) * (N.choose r : ℤ) * (r.choose (N - s) : ℤ)
        = (-1 : ℤ) ^ (r + s) * ((N.choose r : ℤ) * (r.choose (N - s) : ℤ)) := by ring
      _ = (-1 : ℤ) ^ (r + s) * ((N.choose s : ℤ) * (s.choose (N - r) : ℤ)) := by rw [hcast]
      _ = (-1 : ℤ) ^ (r + s) * (N.choose s : ℤ) * (s.choose (N - r) : ℤ) := by ring
  · have h1 : Nat.choose r (N - s) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : Nat.choose s (N - r) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h1, h2]

private lemma M_eq_zero_of_lt (N r s : ℕ) (hrs : r + s < N) : M N r s = 0 := by
  unfold M
  have h : Nat.choose r (N - s) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [h]

private lemma B_eq_trinom (N s : ℕ) :
    B N s = ∑ m ∈ range (2 * s + 1),
      if m ≤ N then (Nat.choose (2 * (N - s)) (N - m) : ℤ) * (T s m : ℤ) else 0 := by
  unfold B
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have h1 : ∑ m ∈ range (N + 1),
      ((1 + X + X ^ 2 : ℤ[X]) ^ s).coeff m * ((1 + X : ℤ[X]) ^ (2 * (N - s))).coeff (N - m) =
      ∑ m ∈ range (max N (2 * s) + 1),
        if m ≤ N then (Nat.choose (2 * (N - s)) (N - m) : ℤ) * (T s m : ℤ) else 0 := by
    symm
    rw [← Finset.sum_filter]
    have hfilt : (range (max N (2 * s) + 1)).filter (fun m => m ≤ N) = range (N + 1) := by
      ext m; simp only [mem_filter, mem_range]; omega
    rw [hfilt]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [T_cast_int, one_add_X_pow_coeff, mul_comm]
  have h2 : ∑ m ∈ range (2 * s + 1),
      (if m ≤ N then (Nat.choose (2 * (N - s)) (N - m) : ℤ) * (T s m : ℤ) else 0) =
      ∑ m ∈ range (max N (2 * s) + 1),
        if m ≤ N then (Nat.choose (2 * (N - s)) (N - m) : ℤ) * (T s m : ℤ) else 0 := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun m hm hnot => ?_
    rw [mem_range] at hm hnot
    split_ifs with hle
    · have hz : T s m = 0 := T_eq_zero_of_gt s m (by omega)
      simp [hz]
    · rfl
  -- Note Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk puts (m, N - m)
  rw [h1, ← h2]

private lemma B_eq_binom (N s : ℕ) (hs : s ≤ N) :
    B N s = ∑ j ∈ range (s + 1), (-1 : ℤ) ^ j * (Nat.choose s j : ℤ) * (f (N - j) : ℤ) := by
  unfold B
  have hrew : (1 + X + X ^ 2 : ℤ[X]) = (-X) + (1 + X) ^ 2 := by ring
  rw [hrew, add_pow, Finset.sum_mul, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjs : j ≤ s := by rw [mem_range] at hj; omega
  have hpow : (-X : ℤ[X]) ^ j * ((1 + X : ℤ[X]) ^ 2) ^ (s - j) * (Nat.choose s j : ℤ[X]) *
      (1 + X : ℤ[X]) ^ (2 * (N - s)) =
      X ^ j * (C ((-1 : ℤ) ^ j * (Nat.choose s j : ℤ)) * (1 + X : ℤ[X]) ^ (2 * (N - j))) := by
    have hneg : (-X : ℤ[X]) ^ j = C ((-1 : ℤ) ^ j) * X ^ j := by
      rw [show (-X : ℤ[X]) = C (-1 : ℤ) * X by simp, mul_pow, ← map_pow]
    have hexp : 2 * (s - j) + 2 * (N - s) = 2 * (N - j) := by omega
    rw [hneg, ← pow_mul, ← Polynomial.C_eq_natCast, map_mul]
    calc C ((-1 : ℤ) ^ j) * X ^ j * (1 + X : ℤ[X]) ^ (2 * (s - j)) * C (Nat.choose s j : ℤ) *
          (1 + X : ℤ[X]) ^ (2 * (N - s))
        = X ^ j * (C ((-1 : ℤ) ^ j) * C (Nat.choose s j : ℤ) *
            ((1 + X : ℤ[X]) ^ (2 * (s - j)) * (1 + X : ℤ[X]) ^ (2 * (N - s)))) := by ring
      _ = X ^ j * (C ((-1 : ℤ) ^ j) * C (Nat.choose s j : ℤ) * (1 + X : ℤ[X]) ^ (2 * (N - j))) := by
            rw [← pow_add, hexp]
  rw [hpow, Polynomial.coeff_X_pow_mul']
  have hjN : j ≤ N := by omega
  simp only [hjN, ↓reduceIte, Polynomial.coeff_C_mul, one_add_X_pow_coeff, f]

private lemma sum_M_mul_f_eq (N s : ℕ) (hs : s ≤ N) :
    ∑ r ∈ range (N + 1), M N r s * (f r : ℤ) =
      (-1 : ℤ) ^ (N - s) * (Nat.choose N s : ℤ) * B N s := by
  rw [B_eq_binom N s hs, Finset.mul_sum]
  have hfilt : ∑ r ∈ range (N + 1), M N r s * (f r : ℤ) =
      ∑ r ∈ (range (N + 1)).filter (fun r => N - s ≤ r), M N r s * (f r : ℤ) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun r hr hnot => ?_
    have hnot' : ¬ (N - s ≤ r) := fun h => hnot (mem_filter.mpr ⟨hr, h⟩)
    have hlt : r + s < N := by rw [mem_range] at hr; omega
    rw [M_eq_zero_of_lt N r s hlt, zero_mul]
  rw [hfilt]
  refine Finset.sum_bij (fun r _ => N - r) ?_ ?_ ?_ ?_
  · intro r hr
    rw [mem_filter, mem_range] at hr
    rw [mem_range]; omega
  · intro r₁ hr₁ r₂ hr₂ heq
    rw [mem_filter, mem_range] at hr₁ hr₂
    omega
  · intro j hj
    rw [mem_range] at hj
    refine ⟨N - j, ?_, by omega⟩
    rw [mem_filter, mem_range]; omega
  · intro r hr
    rw [mem_filter, mem_range] at hr
    have hsub : N - (N - r) = r := by omega
    rw [hsub, M_symm N r s (by omega) hs]
    unfold M
    have hsign : (-1 : ℤ) ^ (s + r) = (-1 : ℤ) ^ (N - s) * (-1 : ℤ) ^ (N - r) := by
      rw [← pow_add]
      apply neg_one_pow_eq_of_even_add
      refine ⟨N, by omega⟩
    rw [hsign]
    ring

private lemma king_walks_eq_FB (N : ℕ) :
    (OMA.S_oeis_a094061.a N : ℤ) =
      ∑ s ∈ range (N + 1), (-1 : ℤ) ^ (N - s) * (Nat.choose N s : ℤ) * (f s : ℤ) * B N s := by
  set X₁ : Polynomial (Polynomial ℤ) := Polynomial.C Polynomial.X
  set Y₁ : Polynomial (Polynomial ℤ) := Polynomial.X
  set K : Polynomial (Polynomial ℤ) :=
    ∑ v ∈ OMA.S_oeis_a094061.moves, X₁ ^ (v.1 + 1).toNat * Y₁ ^ (v.2 + 1).toNat
  have hK_pow : K ^ N =
      ∑ w ∈ Fintype.piFinset (fun _ : Fin N => OMA.S_oeis_a094061.moves),
        X₁ ^ (∑ i : Fin N, ((w i).1 + 1).toNat) * Y₁ ^ (∑ i : Fin N, ((w i).2 + 1).toNat) := by
    rw [show K = ∑ v ∈ OMA.S_oeis_a094061.moves, X₁ ^ (v.1 + 1).toNat * Y₁ ^ (v.2 + 1).toNat from rfl,
      Finset.sum_pow']
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  have hcoeff_XY : ∀ a b : ℕ, ((X₁ ^ a * Y₁ ^ b).coeff N).coeff N =
      if a = N ∧ b = N then 1 else 0 := by
    intro a b
    have hX : X₁ ^ a = Polynomial.C (Polynomial.X ^ a) := by simp [X₁]
    rw [hX, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hb : b = N
    · subst hb
      simp [Polynomial.coeff_X_pow, eq_comm]
    · simp [Ne.symm hb, hb]
  have ha_poly : (OMA.S_oeis_a094061.a N : ℤ) = ((K ^ N).coeff N).coeff N := by
    rw [hK_pow, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
    have hstep : ∀ w ∈ Fintype.piFinset (fun _ : Fin N => OMA.S_oeis_a094061.moves),
        ((X₁ ^ (∑ i : Fin N, ((w i).1 + 1).toNat) *
          Y₁ ^ (∑ i : Fin N, ((w i).2 + 1).toNat)).coeff N).coeff N =
        if ∑ i : Fin N, w i = 0 then (1 : ℤ) else 0 := by
      intro w hw
      rw [hcoeff_XY]
      have hmem : ∀ i : Fin N, w i ∈ OMA.S_oeis_a094061.moves := fun i =>
        Fintype.mem_piFinset.mp hw i
      have h1nonneg : ∀ i : Fin N, 0 ≤ (w i).1 + 1 := by
        intro i
        have hi := hmem i
        simp only [OMA.S_oeis_a094061.moves, mem_insert, mem_singleton] at hi
        rcases hi with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
      have h2nonneg : ∀ i : Fin N, 0 ≤ (w i).2 + 1 := by
        intro i
        have hi := hmem i
        simp only [OMA.S_oeis_a094061.moves, mem_insert, mem_singleton] at hi
        rcases hi with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
      have hiff : ((∑ i : Fin N, ((w i).1 + 1).toNat) = N ∧
          (∑ i : Fin N, ((w i).2 + 1).toNat) = N) ↔ (∑ i : Fin N, w i = 0) := by
        have hs1 : ((∑ i : Fin N, ((w i).1 + 1).toNat : ℕ) : ℤ) =
            (∑ i : Fin N, (w i).1) + (N : ℤ) := by
          push_cast
          have heq : ∑ i : Fin N, (((w i).1 + 1).toNat : ℤ) = ∑ i : Fin N, ((w i).1 + 1) :=
            Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (h1nonneg i)
          rw [heq, Finset.sum_add_distrib]
          simp
        have hs2 : ((∑ i : Fin N, ((w i).2 + 1).toNat : ℕ) : ℤ) =
            (∑ i : Fin N, (w i).2) + (N : ℤ) := by
          push_cast
          have heq : ∑ i : Fin N, (((w i).2 + 1).toNat : ℤ) = ∑ i : Fin N, ((w i).2 + 1) :=
            Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (h2nonneg i)
          rw [heq, Finset.sum_add_distrib]
          simp
        have hp1 : (∑ i : Fin N, w i).1 = ∑ i : Fin N, (w i).1 := by
          simpa using (Prod.fst_sum (s := Finset.univ) (f := w))
        have hp2 : (∑ i : Fin N, w i).2 = ∑ i : Fin N, (w i).2 := by
          simpa using (Prod.snd_sum (s := Finset.univ) (f := w))
        constructor
        · rintro ⟨ha, hb⟩
          have ha' : (∑ i : Fin N, (w i).1) + (N : ℤ) = (N : ℤ) := by
            rw [← hs1]; exact_mod_cast ha
          have hb' : (∑ i : Fin N, (w i).2) + (N : ℤ) = (N : ℤ) := by
            rw [← hs2]; exact_mod_cast hb
          ext
          · simp [hp1]; linarith
          · simp [hp2]; linarith
        · intro h0
          have h10 : ∑ i : Fin N, (w i).1 = 0 := by
            rw [← hp1, h0]; rfl
          have h20 : ∑ i : Fin N, (w i).2 = 0 := by
            rw [← hp2, h0]; rfl
          constructor
          · have : ((∑ i : Fin N, ((w i).1 + 1).toNat : ℕ) : ℤ) = (N : ℤ) := by
              rw [hs1, h10, zero_add]
            exact_mod_cast this
          · have : ((∑ i : Fin N, ((w i).2 + 1).toNat : ℕ) : ℤ) = (N : ℤ) := by
              rw [hs2, h20, zero_add]
            exact_mod_cast this
      simp only [hiff]
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rfl
  have hK_fac : K = (1 + X₁) ^ 2 * (1 + Y₁ + Y₁ ^ 2) + (-(X₁ * (1 + Y₁) ^ 2)) := by
    have hmoves : OMA.S_oeis_a094061.moves =
        insert (-1, -1) (insert (-1, 0) (insert (-1, 1) (insert (0, -1)
          (insert (0, 1) (insert (1, -1) (insert (1, 0) {(1, 1)})))))) := rfl
    simp only [K, hmoves]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num
    simp only [show Int.toNat 2 = 2 from rfl]
    ring
  rw [ha_poly, hK_fac, add_pow, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsN : s ≤ N := by rw [mem_range] at hs; omega
  have hterm :
      ((1 + X₁) ^ 2 * (1 + Y₁ + Y₁ ^ 2)) ^ s * (-(X₁ * (1 + Y₁) ^ 2)) ^ (N - s) *
        (Nat.choose N s : Polynomial (Polynomial ℤ)) =
      Polynomial.C (Polynomial.C ((-1 : ℤ) ^ (N - s) * (Nat.choose N s : ℤ)) *
          ((1 + X : ℤ[X]) ^ (2 * s) * X ^ (N - s))) *
        (((1 + X + X ^ 2 : ℤ[X]) ^ s * (1 + X : ℤ[X]) ^ (2 * (N - s))).map Polynomial.C) := by
    have hmap : (((1 + X + X ^ 2 : ℤ[X]) ^ s * (1 + X : ℤ[X]) ^ (2 * (N - s))).map Polynomial.C) =
        (1 + Y₁ + Y₁ ^ 2) ^ s * (1 + Y₁) ^ (2 * (N - s)) := by
      simp [Y₁, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one,
        Polynomial.map_X]
    have hC_X : Polynomial.C ((1 + X : ℤ[X]) ^ (2 * s) * X ^ (N - s)) =
        (1 + X₁) ^ (2 * s) * X₁ ^ (N - s) := by
      simp [X₁, map_mul, map_pow, map_add, map_one]
    have hneg : (-(X₁ * (1 + Y₁) ^ 2)) ^ (N - s) =
        Polynomial.C (Polynomial.C ((-1 : ℤ) ^ (N - s))) * X₁ ^ (N - s) * (1 + Y₁) ^ (2 * (N - s)) := by
      have h1 : -(X₁ * (1 + Y₁) ^ 2) = Polynomial.C (Polynomial.C (-1 : ℤ)) * (X₁ * (1 + Y₁) ^ 2) := by
        simp; ring
      rw [h1, mul_pow, mul_pow, ← pow_mul, ← map_pow, ← map_pow]
      ring
    have hch : (Nat.choose N s : Polynomial (Polynomial ℤ)) =
        Polynomial.C (Polynomial.C (Nat.choose N s : ℤ)) := by simp
    have hsm : Polynomial.C (Polynomial.C ((-1 : ℤ) ^ (N - s) * (Nat.choose N s : ℤ)) *
        ((1 + X : ℤ[X]) ^ (2 * s) * X ^ (N - s))) =
        Polynomial.C (Polynomial.C ((-1 : ℤ) ^ (N - s))) *
          Polynomial.C (Polynomial.C (Nat.choose N s : ℤ)) *
          ((1 + X₁) ^ (2 * s) * X₁ ^ (N - s)) := by
      rw [map_mul, map_mul, map_mul, hC_X]
    rw [hmap, hsm, hneg, hch, mul_pow, ← pow_mul]
    ring
  rw [hterm, Polynomial.coeff_C_mul, Polynomial.coeff_map, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul]
  have hXcoeff : ((1 + X : ℤ[X]) ^ (2 * s) * X ^ (N - s)).coeff N = (f s : ℤ) := by
    rw [mul_comm, Polynomial.coeff_X_pow_mul']
    have hle : N - s ≤ N := Nat.sub_le N s
    simp only [hle, ↓reduceIte, show N - (N - s) = s by omega, one_add_X_pow_coeff, f]
  rw [hXcoeff]
  simp only [B]

private lemma king_walks_eq_double_sum (N : ℕ) :
    (OMA.S_oeis_a094061.a N : ℤ) =
      ∑ r ∈ range (N + 1), ∑ s ∈ range (N + 1), M N r s * (f r : ℤ) * (f s : ℤ) := by
  rw [king_walks_eq_FB N, Finset.sum_comm]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsN : s ≤ N := by rw [mem_range] at hs; omega
  have h1 := sum_M_mul_f_eq N s hsN
  rw [← Finset.sum_mul, h1]
  ring

-- ============================================================================
-- Block 2: Exact Z-Decomposition of a(p * A) - a(A)
-- ============================================================================

private lemma sum_range_p_mul_split (p A : ℕ) (hp : 0 < p) (g : ℕ → ℤ) :
    ∑ r ∈ range (p * A + 1), g r =
      (∑ r' ∈ range (A + 1), g (p * r')) +
      (∑ r ∈ (range (p * A + 1)).filter (fun r => ¬ p ∣ r), g r) := by
  rw [← Finset.sum_filter_add_sum_filter_not (range (p * A + 1)) (fun r => p ∣ r)]
  congr 1
  symm
  refine Finset.sum_bij (fun r' _ => p * r') ?_ ?_ ?_ ?_
  · intro r' hr'
    rw [mem_range] at hr'
    rw [mem_filter, mem_range]
    exact ⟨by nlinarith, dvd_mul_right p r'⟩
  · intro r₁ _ r₂ _ heq
    exact Nat.eq_of_mul_eq_mul_left hp heq
  · intro r hr
    rw [mem_filter, mem_range] at hr
    rcases hr.2 with ⟨r', rfl⟩
    refine ⟨r', ?_, rfl⟩
    rw [mem_range]
    nlinarith
  · intro _ _; rfl

private lemma a_sub_decomp (p A : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (OMA.S_oeis_a094061.a (p * A) : ℤ) - (OMA.S_oeis_a094061.a A : ℤ) =
      (∑ r ∈ (range (p * A + 1)).filter (fun r => ¬ p ∣ r),
        ∑ s ∈ (range (p * A + 1)).filter (fun s => ¬ p ∣ s),
          M (p * A) r s * (f r : ℤ) * (f s : ℤ)) +
      (2 * ∑ s' ∈ range (A + 1),
        (-1 : ℤ) ^ (A - s') * ((Nat.choose (p * A) (p * s') : ℤ) - (Nat.choose A s' : ℤ)) *
          (f (p * s') : ℤ) * B (p * A) (p * s')) +
      (-(∑ r' ∈ range (A + 1), ∑ s' ∈ range (A + 1),
        (M (p * A) (p * r') (p * s') - M A r' s') * (f (p * r') : ℤ) * (f (p * s') : ℤ))) +
      (-(∑ r' ∈ range (A + 1), ∑ s' ∈ range (A + 1),
        M A r' s' * ((f (p * r') : ℤ) - (f r' : ℤ)) * ((f (p * s') : ℤ) - (f s' : ℤ)))) +
      (2 * ∑ s' ∈ range (A + 1),
        (-1 : ℤ) ^ (A - s') * (Nat.choose A s' : ℤ) * (f (p * s') : ℤ) *
          (B (p * A) (p * s') - B A s')) := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  set N := p * A
  set NN : ℤ := ∑ r ∈ (range (N + 1)).filter (fun r => ¬ p ∣ r),
    ∑ s ∈ (range (N + 1)).filter (fun s => ¬ p ∣ s), M N r s * (f r : ℤ) * (f s : ℤ)
  set PP : ℤ := ∑ r' ∈ range (A + 1), ∑ s' ∈ range (A + 1),
    M N (p * r') (p * s') * (f (p * r') : ℤ) * (f (p * s') : ℤ)
  set PM : ℤ := ∑ r ∈ (range (N + 1)).filter (fun r => ¬ p ∣ r),
    ∑ s' ∈ range (A + 1), M N r (p * s') * (f r : ℤ) * (f (p * s') : ℤ)
  set MP : ℤ := ∑ r' ∈ range (A + 1),
    ∑ s ∈ (range (N + 1)).filter (fun s => ¬ p ∣ s), M N (p * r') s * (f (p * r') : ℤ) * (f s : ℤ)
  set FB : ℤ := ∑ s' ∈ range (A + 1),
    (-1 : ℤ) ^ (A - s') * (Nat.choose N (p * s') : ℤ) * (f (p * s') : ℤ) * B N (p * s')
  have hMP_eq_PM : MP = PM := by
    simp only [MP, PM]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun s' hs' => ?_
    rw [mem_filter, mem_range] at hr
    rw [mem_range] at hs'
    rw [M_symm N (p * s') r (Nat.mul_le_mul_left p (by omega)) (by omega)]
    ring
  have haN_split : (OMA.S_oeis_a094061.a N : ℤ) = PP + MP + PM + NN := by
    rw [king_walks_eq_double_sum N]
    have h1 : ∀ r : ℕ,
        ∑ s ∈ range (N + 1), M N r s * (f r : ℤ) * (f s : ℤ) =
          (∑ s' ∈ range (A + 1), M N r (p * s') * (f r : ℤ) * (f (p * s') : ℤ)) +
          (∑ s ∈ (range (N + 1)).filter (fun s => ¬ p ∣ s), M N r s * (f r : ℤ) * (f s : ℤ)) :=
      fun r => sum_range_p_mul_split p A hp.pos (fun s => M N r s * (f r : ℤ) * (f s : ℤ))
    simp_rw [h1, Finset.sum_add_distrib]
    rw [sum_range_p_mul_split p A hp.pos (fun r => ∑ s' ∈ range (A + 1), M N r (p * s') * (f r : ℤ) * (f (p * s') : ℤ)),
      sum_range_p_mul_split p A hp.pos (fun r => ∑ s ∈ (range (N + 1)).filter (fun s => ¬ p ∣ s), M N r s * (f r : ℤ) * (f s : ℤ))]
    simp only [PP, MP, PM, NN]
    ring
  have hFB_eq : FB = PP + PM := by
    have hterm : ∀ s' ∈ range (A + 1),
        (-1 : ℤ) ^ (A - s') * (Nat.choose N (p * s') : ℤ) * (f (p * s') : ℤ) * B N (p * s') =
          ∑ r ∈ range (N + 1), M N r (p * s') * (f r : ℤ) * (f (p * s') : ℤ) := by
      intro s' hs'
      have hs'A : s' ≤ A := by rw [mem_range] at hs'; omega
      have hM := sum_M_mul_f_eq N (p * s') (Nat.mul_le_mul_left p hs'A)
      rw [← Finset.sum_mul, hM]
      have hsign : (-1 : ℤ) ^ (N - p * s') = (-1 : ℤ) ^ (A - s') := by
        rw [show N - p * s' = p * (A - s') by simp only [N]; rw [Nat.mul_sub]]
        exact neg_one_pow_mul_odd p (A - s') hpodd
      rw [hsign]
      ring
    calc FB = ∑ s' ∈ range (A + 1), ∑ r ∈ range (N + 1), M N r (p * s') * (f r : ℤ) * (f (p * s') : ℤ) :=
            Finset.sum_congr rfl hterm
      _ = ∑ r ∈ range (N + 1), ∑ s' ∈ range (A + 1), M N r (p * s') * (f r : ℤ) * (f (p * s') : ℤ) :=
            Finset.sum_comm
      _ = PP + PM := sum_range_p_mul_split p A hp.pos _
  have haN_2FB : (OMA.S_oeis_a094061.a N : ℤ) = 2 * FB - PP + NN := by
    linarith
  have hlin_cancel :
      ∑ r' ∈ range (A + 1), ∑ s' ∈ range (A + 1),
        M A r' s' * ((f (p * r') : ℤ) - (f r' : ℤ)) * (f s' : ℤ) =
      ∑ s' ∈ range (A + 1),
        (-1 : ℤ) ^ (A - s') * (Nat.choose A s' : ℤ) * ((f (p * s') : ℤ) - (f s' : ℤ)) * B A s' := by
    refine Finset.sum_congr rfl fun r' hr' => ?_
    have hr'A : r' ≤ A := by rw [mem_range] at hr'; omega
    have h1 : ∑ s' ∈ range (A + 1), M A r' s' * ((f (p * r') : ℤ) - (f r' : ℤ)) * (f s' : ℤ) =
        ((f (p * r') : ℤ) - (f r' : ℤ)) * ∑ s' ∈ range (A + 1), M A s' r' * (f s' : ℤ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' hs' => ?_
      have hs'A : s' ≤ A := by rw [mem_range] at hs'; omega
      rw [M_symm A r' s' hr'A hs'A]
      ring
    rw [h1, sum_M_mul_f_eq A r' hr'A]
    ring
  have hlin_cancel2 :
      ∑ r' ∈ range (A + 1), ∑ s' ∈ range (A + 1),
        M A r' s' * (f r' : ℤ) * ((f (p * s') : ℤ) - (f s' : ℤ)) =
      ∑ s' ∈ range (A + 1),
        (-1 : ℤ) ^ (A - s') * (Nat.choose A s' : ℤ) * ((f (p * s') : ℤ) - (f s' : ℤ)) * B A s' := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s' hs' => ?_
    have hs'A : s' ≤ A := by rw [mem_range] at hs'; omega
    rw [← Finset.sum_mul, sum_M_mul_f_eq A s' hs'A]
    ring
  have hFB_sub : FB - (OMA.S_oeis_a094061.a A : ℤ) =
      (∑ s' ∈ range (A + 1),
        (-1 : ℤ) ^ (A - s') * ((Nat.choose N (p * s') : ℤ) - (Nat.choose A s' : ℤ)) *
          (f (p * s') : ℤ) * B N (p * s')) +
      (∑ s' ∈ range (A + 1),
        (-1 : ℤ) ^ (A - s') * (Nat.choose A s' : ℤ) * (f (p * s') : ℤ) * (B N (p * s') - B A s')) +
      (∑ s' ∈ range (A + 1),
        (-1 : ℤ) ^ (A - s') * (Nat.choose A s' : ℤ) * ((f (p * s') : ℤ) - (f s' : ℤ)) * B A s') := by
    rw [king_walks_eq_FB A]
    simp only [FB, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s' _ => by ring
  have hPP_sub : PP - (OMA.S_oeis_a094061.a A : ℤ) =
      (∑ r' ∈ range (A + 1), ∑ s' ∈ range (A + 1),
        (M N (p * r') (p * s') - M A r' s') * (f (p * r') : ℤ) * (f (p * s') : ℤ)) +
      (∑ r' ∈ range (A + 1), ∑ s' ∈ range (A + 1),
        M A r' s' * ((f (p * r') : ℤ) - (f r' : ℤ)) * ((f (p * s') : ℤ) - (f s' : ℤ))) +
      2 * (∑ s' ∈ range (A + 1),
        (-1 : ℤ) ^ (A - s') * (Nat.choose A s' : ℤ) * ((f (p * s') : ℤ) - (f s' : ℤ)) * B A s') := by
    rw [king_walks_eq_double_sum A]
    have hsplit : PP - ∑ r' ∈ range (A + 1), ∑ s' ∈ range (A + 1), M A r' s' * (f r' : ℤ) * (f s' : ℤ) =
        (∑ r' ∈ range (A + 1), ∑ s' ∈ range (A + 1),
          (M N (p * r') (p * s') - M A r' s') * (f (p * r') : ℤ) * (f (p * s') : ℤ)) +
        (∑ r' ∈ range (A + 1), ∑ s' ∈ range (A + 1),
          M A r' s' * ((f (p * r') : ℤ) - (f r' : ℤ)) * ((f (p * s') : ℤ) - (f s' : ℤ))) +
        (∑ r' ∈ range (A + 1), ∑ s' ∈ range (A + 1),
          M A r' s' * ((f (p * r') : ℤ) - (f r' : ℤ)) * (f s' : ℤ)) +
        (∑ r' ∈ range (A + 1), ∑ s' ∈ range (A + 1),
          M A r' s' * (f r' : ℤ) * ((f (p * s') : ℤ) - (f s' : ℤ))) := by
      simp only [PP, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r' _ => Finset.sum_congr rfl fun s' _ => by ring
    rw [hsplit, hlin_cancel, hlin_cancel2]
    ring
  linarith

-- ============================================================================
-- Block 3: Legendre Key Carry Lemma and Pieces NN, 1a, 1b, 2
-- ============================================================================

private lemma pow_dvd_choose_of_not_dvd {p k N r : ℕ} (hp : p.Prime)
    (hN : p ^ k ∣ N) (hr : ¬ p ∣ r) : p ^ k ∣ N.choose r := by
  have hrpos : 1 ≤ r := by
    by_contra h
    have : r = 0 := by omega
    subst this; exact hr (dvd_zero p)
  by_cases hN0 : N = 0
  · subst hN0
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact dvd_zero _
  · have hab : r * N.choose r = N * (N - 1).choose (r - 1) := by
      have h := Nat.add_one_mul_choose_eq (N - 1) (r - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ N), Nat.sub_add_cancel hrpos] at h
      linarith
    have hdvd : p ^ k ∣ r * N.choose r := by
      rw [hab]; exact dvd_mul_of_dvd_left hN _
    have hcop : Nat.Coprime (p ^ k) r := (hp.coprime_iff_not_dvd.mpr hr).pow_left k
    exact hcop.dvd_of_dvd_mul_left hdvd

private lemma pow_dvd_multichoose_of_not_dvd {p k N m : ℕ} (hp : p.Prime)
    (hN1 : 1 ≤ N) (hN : p ^ k ∣ N) (hm : ¬ p ∣ m) : p ^ k ∣ (N + m - 1).choose m := by
  have hmpos : 1 ≤ m := by
    by_contra h
    have : m = 0 := by omega
    subst this; exact hm (dvd_zero p)
  have hab : m * (N + m - 1).choose m = N * (N + m - 1).choose (m - 1) := by
    have h := Nat.choose_succ_right_eq (N + m - 1) (m - 1)
    rw [Nat.sub_add_cancel hmpos] at h
    have hsub : N + m - 1 - (m - 1) = N := by omega
    rw [hsub] at h
    linarith
  have hdvd : p ^ k ∣ m * (N + m - 1).choose m := by
    rw [hab]; exact dvd_mul_of_dvd_left hN _
  have hcop : Nat.Coprime (p ^ k) m := (hp.coprime_iff_not_dvd.mpr hm).pow_left k
  exact hcop.dvd_of_dvd_mul_left hdvd

private lemma vp_mul_eq {p a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    vp p (a * b) = vp p a + vp p b := by
  dsimp [vp]
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply]

private lemma vp_le_vp_add_vp_choose {p A s : ℕ} (hs : 1 ≤ s) (hsA : s ≤ A) :
    vp p A ≤ vp p s + vp p (A.choose s) := by
  have hA0 : A ≠ 0 := by omega
  have hs0 : s ≠ 0 := by omega
  have hch0 : A.choose s ≠ 0 := (Nat.choose_pos hsA).ne'
  have hab : s * A.choose s = A * (A - 1).choose (s - 1) := by
    have h := Nat.add_one_mul_choose_eq (A - 1) (s - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ A), Nat.sub_add_cancel hs] at h
    linarith
  have hch2 : (A - 1).choose (s - 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hv := congrArg (vp p) hab
  rw [vp_mul_eq hs0 hch0, vp_mul_eq hA0 hch2] at hv
  omega

private lemma vp_le_vp_add_vp_multichoose {p A C : ℕ} (hA : 1 ≤ A) (hC : 1 ≤ C) :
    vp p A ≤ vp p C + vp p ((A + C - 1).choose C) := by
  have hA0 : A ≠ 0 := by omega
  have hC0 : C ≠ 0 := by omega
  have hch0 : (A + C - 1).choose C ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hch2 : (A + C - 1).choose (C - 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hab : C * (A + C - 1).choose C = A * (A + C - 1).choose (C - 1) := by
    have h := Nat.choose_succ_right_eq (A + C - 1) (C - 1)
    rw [Nat.sub_add_cancel hC, show A + C - 1 - (C - 1) = A by omega] at h
    linarith
  have hv := congrArg (vp p) hab
  rw [vp_mul_eq hC0 hch0, vp_mul_eq hA0 hch2] at hv
  omega

private lemma choose_mul_p_sub_dvd {p m b : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hb : 1 ≤ b) (hbm : b < m) :
    (p : ℤ) ^ (3 + vp p b + vp p (m - b) + vp p m + vp p (m.choose b)) ∣
      (((p * m).choose (p * b) : ℤ) - (m.choose b : ℤ)) := by
  have hc1 : 1 ≤ m - b := by omega
  have hbc : b + (m - b) = m := by omega
  have hkaz := kazandzidis_ratio p b (m - b) hp hp5 hb hc1
  rw [hbc, mul_comm m p, mul_comm b p] at hkaz
  have hch_pos : m.choose b ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hch_q : (m.choose b : ℚ) ≠ 0 := by exact_mod_cast hch_pos
  have hch_pv : PVal p (vp p (m.choose b)) (m.choose b : ℚ) :=
    PVal.of_dvd_nat hp (vp_dvd hp hch_pos)
  have hmul := hkaz.mul hp hch_pv
  have hdiff_eq :
      ((Nat.choose (p * m) (p * b) : ℚ) / (Nat.choose m b : ℚ) - 1) * (Nat.choose m b : ℚ) =
      ((((p * m).choose (p * b) : ℤ) - (m.choose b : ℤ) : ℤ) : ℚ) := by
    push_cast; field_simp [hch_q]
  rw [hdiff_eq] at hmul
  exact PVal.int_dvd hp hmul

private lemma choose_pA_ps_dvd {p k A s : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hA : 1 ≤ A) (hAk : p ^ (k - 1) ∣ A) :
    (p : ℤ) ^ (2 * k) ∣ (((p * A).choose (p * s) : ℤ) - (A.choose s : ℤ)) := by
  by_cases hs0 : s = 0
  · subst hs0; simp
  · by_cases hsA : A ≤ s
    · by_cases heq : s = A
      · subst heq; simp
      · have hlt : A < s := by omega
        have hplt : p * A < p * s := Nat.mul_lt_mul_of_pos_left hlt hp.pos
        simp [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt hplt]
    · have hs1 : 1 ≤ s := by omega
      have hd := choose_mul_p_sub_dvd (m := A) (b := s) hp hp5 hs1 (by omega)
      have hvpA : k - 1 ≤ vp p A := vp_le_of_dvd hp (by omega) hAk
      have hvp_ineq := vp_le_vp_add_vp_choose (p := p) hs1 (by omega : s ≤ A)
      have hexp : 2 * k ≤ 3 + vp p s + vp p (A - s) + vp p A + vp p (A.choose s) := by omega
      exact dvd_trans (pow_dvd_pow (p : ℤ) hexp) hd

private lemma multichoose_pA_pC_modEq {p k A C : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hA : 1 ≤ A) (hAk : p ^ (k - 1) ∣ A) :
    ((p * A + p * C - 1).choose (p * C) : ℤ) ≡
      ((A + C - 1).choose C : ℤ) [ZMOD (p : ℤ) ^ (2 * k)] := by
  by_cases hC0 : C = 0
  · subst hC0; simp
  · have hC1 : 1 ≤ C := by omega
    have hkaz := kazandzidis_ratio p C A hp hp5 hC1 hA
    have hrel1 : (A + C) * (A + C - 1).choose C = A * (A + C).choose C := by
      have h := Nat.add_one_mul_choose_eq (A + C - 1) (A - 1)
      have h1 : A + C - 1 + 1 = A + C := by omega
      have h2 : A - 1 + 1 = A := by omega
      rw [h1, h2] at h
      have hsym1 : (A + C - 1).choose (A - 1) = (A + C - 1).choose C := by
        have hs := (Nat.choose_symm (by omega : A - 1 ≤ A + C - 1)).symm
        rwa [show A + C - 1 - (A - 1) = C by omega] at hs
      have hsym2 : (A + C).choose A = (A + C).choose C := by
        have hs := (Nat.choose_symm (by omega : A ≤ A + C)).symm
        rwa [show A + C - A = C by omega] at hs
      rw [hsym1, hsym2] at h
      linarith
    have hrel2 : (p * A + p * C) * (p * A + p * C - 1).choose (p * C) =
        (p * A) * (p * A + p * C).choose (p * C) := by
      have hpA1 : 1 ≤ p * A := Nat.mul_pos hp.pos hA
      have h := Nat.add_one_mul_choose_eq (p * A + p * C - 1) (p * A - 1)
      have h1 : p * A + p * C - 1 + 1 = p * A + p * C := by omega
      have h2 : p * A - 1 + 1 = p * A := by omega
      rw [h1, h2] at h
      have hsym1 : (p * A + p * C - 1).choose (p * A - 1) = (p * A + p * C - 1).choose (p * C) := by
        have hs := (Nat.choose_symm (by omega : p * A - 1 ≤ p * A + p * C - 1)).symm
        rwa [show p * A + p * C - 1 - (p * A - 1) = p * C by omega] at hs
      have hsym2 : (p * A + p * C).choose (p * A) = (p * A + p * C).choose (p * C) := by
        have hs := (Nat.choose_symm (by omega : p * A ≤ p * A + p * C)).symm
        rwa [show p * A + p * C - p * A = p * C by omega] at hs
      rw [hsym1, hsym2] at h
      linarith
    have hq1 : ((A + C : ℕ) : ℚ) * ((A + C - 1).choose C : ℚ) =
        (A : ℚ) * ((A + C).choose C : ℚ) := by exact_mod_cast hrel1
    have hq2 : ((p * A + p * C : ℕ) : ℚ) * ((p * A + p * C - 1).choose (p * C) : ℚ) =
        ((p * A : ℕ) : ℚ) * ((p * A + p * C).choose (p * C) : ℚ) := by exact_mod_cast hrel2
    have hch1_pos : (A + C - 1).choose C ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hch2_pos : (A + C).choose C ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hch1_q : ((A + C - 1).choose C : ℚ) ≠ 0 := by exact_mod_cast hch1_pos
    have hch2_q : ((A + C).choose C : ℚ) ≠ 0 := by exact_mod_cast hch2_pos
    have hA_q : (A : ℚ) ≠ 0 := by exact_mod_cast (by omega : A ≠ 0)
    have hAC_q : ((A + C : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : A + C ≠ 0)
    have hp_q : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hratio_eq :
        (((p * A + p * C - 1).choose (p * C) : ℚ) / ((A + C - 1).choose C : ℚ)) =
        (((C + A) * p).choose (C * p) : ℚ) / ((C + A).choose C : ℚ) := by
      have hcomm1 : (C + A) * p = p * A + p * C := by ring
      have hcomm2 : C * p = p * C := by ring
      have hcomm3 : C + A = A + C := by omega
      rw [hcomm1, hcomm2, hcomm3]
      have h1 : ((A + C - 1).choose C : ℚ) = (A : ℚ) / ((A + C : ℕ) : ℚ) * ((A + C).choose C : ℚ) := by
        field_simp [hAC_q]; linarith
      have h2 : ((p * A + p * C - 1).choose (p * C) : ℚ) =
          (A : ℚ) / ((A + C : ℕ) : ℚ) * ((p * A + p * C).choose (p * C) : ℚ) := by
        have h2' : (p : ℚ) * ((A + C : ℕ) : ℚ) * ((p * A + p * C - 1).choose (p * C) : ℚ) =
            (p : ℚ) * (A : ℚ) * ((p * A + p * C).choose (p * C) : ℚ) := by
          push_cast at hq2 ⊢; linarith
        have h2'' : ((A + C : ℕ) : ℚ) * ((p * A + p * C - 1).choose (p * C) : ℚ) =
            (A : ℚ) * ((p * A + p * C).choose (p * C) : ℚ) := by
          apply mul_left_cancel₀ hp_q; linarith
        field_simp [hAC_q]; linarith
      rw [h1, h2]
      field_simp [hA_q, hAC_q, hch2_q]
    rw [← hratio_eq] at hkaz
    have hch_pv : PVal p (vp p ((A + C - 1).choose C)) (((A + C - 1).choose C : ℚ)) :=
      PVal.of_dvd_nat hp (vp_dvd hp hch1_pos)
    have hmul := hkaz.mul hp hch_pv
    have hdiff_eq :
        (((p * A + p * C - 1).choose (p * C) : ℚ) / ((A + C - 1).choose C : ℚ) - 1) *
          ((A + C - 1).choose C : ℚ) =
        ((((p * A + p * C - 1).choose (p * C) : ℤ) : ℚ) - (((A + C - 1).choose C : ℤ) : ℚ)) := by
      push_cast; field_simp [hch1_q]
    rw [hdiff_eq] at hmul
    have hvpA : k - 1 ≤ vp p A := vp_le_of_dvd hp (by omega) hAk
    have hvp_ineq := vp_le_vp_add_vp_multichoose (p := p) hA hC1
    have hexp : 2 * k ≤ 3 + vp p C + vp p A + vp p (C + A) + vp p ((A + C - 1).choose C) := by
      omega
    exact PVal.modEq_of_sub hp (hmul.mono hexp)

private lemma f_mul_p_sub_dvd {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hm : 1 ≤ m) :
    (p : ℤ) ^ (3 + 3 * vp p m + vp p (f m)) ∣ ((f (p * m) : ℤ) - (f m : ℤ)) := by
  have hd := choose_mul_p_sub_dvd (m := 2 * m) (b := m) hp hp5 hm (by omega)
  have hsub : 2 * m - m = m := by omega
  have h2m : vp p (2 * m) = vp p m := vp_mul_two hp hp5 (by omega)
  have hmul : p * (2 * m) = 2 * (p * m) := by ring
  rw [hsub, h2m, hmul] at hd
  have hexp : 3 + 3 * vp p m + vp p (f m) = 3 + vp p m + vp p m + vp p m + vp p ((2 * m).choose m) := by
    simp only [f]; omega
  rwa [hexp]

private lemma vp_f_mul_p_ge {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    vp p (f m) ≤ vp p (f (p * m)) := by
  by_cases hm : m = 0
  · subst hm; simp [f]
  · have hm1 : 1 ≤ m := by omega
    have hd := f_mul_p_sub_dvd hp hp5 hm1
    have hd1 : (p : ℤ) ^ vp p (f m) ∣ ((f (p * m) : ℤ) - (f m : ℤ)) :=
      dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hd
    have hd2 : (p : ℤ) ^ vp p (f m) ∣ (f m : ℤ) := by
      exact_mod_cast vp_dvd hp (Nat.choose_pos (by omega : m ≤ 2 * m)).ne'
    have hd3 : (p : ℤ) ^ vp p (f m) ∣ (f (p * m) : ℤ) := by
      have h := dvd_add hd1 hd2
      simpa using h
    have hd3_nat : p ^ vp p (f m) ∣ f (p * m) := by exact_mod_cast hd3
    exact vp_le_of_dvd hp (Nat.choose_pos (by omega : p * m ≤ 2 * (p * m))).ne' hd3_nat

private lemma vp_ge_card_dvd {p X K : ℕ} (hp : p.Prime) (hX : X ≠ 0) :
    ∑ t ∈ Ico 1 K, (if p ^ t ∣ X then 1 else 0) ≤ vp p X := by
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
  have hsub : (Ico 1 K).filter (fun t => p ^ t ∣ X) ⊆ Ico 1 (vp p X + 1) := by
    intro t ht
    rw [mem_filter, mem_Ico] at ht
    rw [mem_Ico]
    exact ⟨ht.1.1, Nat.lt_succ_of_le (vp_le_of_dvd hp hX ht.2)⟩
  calc ((Ico 1 K).filter (fun t => p ^ t ∣ X)).card
      ≤ (Ico 1 (vp p X + 1)).card := Finset.card_le_card hsub
    _ = vp p X := by simp

private lemma vp_factorial {p n b : ℕ} (hp : p.Prime) (hnb : Nat.log p n < b) :
    vp p n.factorial = ∑ i ∈ Ico 1 b, n / p ^ i := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← padicValNat_factorial (p := p) hnb]
  have hne : n.factorial ≠ 0 := Nat.factorial_ne_zero n
  apply le_antisymm
  · exact (padicValNat_dvd_iff_le hne).mp (vp_dvd hp hne)
  · exact vp_le_of_dvd hp hne pow_padicValNat_dvd

private lemma choose_div_sub_eq {n a d : ℕ} (ha : a ≤ n) (hd : 0 < d) :
    n / d = a / d + (n - a) / d + (if n % d < a % d then 1 else 0) := by
  have hn := Nat.div_add_mod n d
  have ha' := Nat.div_add_mod a d
  have hna := Nat.div_add_mod (n - a) d
  have hml1 : n % d < d := Nat.mod_lt n hd
  have hml2 : a % d < d := Nat.mod_lt a hd
  have hml3 : (n - a) % d < d := Nat.mod_lt (n - a) hd
  have hadd : a + (n - a) = n := Nat.add_sub_of_le ha
  have hcomb : d * (n / d) + n % d = d * (a / d + (n - a) / d) + (a % d + (n - a) % d) := by
    rw [mul_add]; omega
  split_ifs with hlt
  · have hsum_rem : a % d + (n - a) % d = d + n % d := by
      by_contra hne
      have h1 : d * (n / d) + n % d = d * (a / d + (n - a) / d) + (a % d + (n - a) % d) := hcomb
      have hle_q : n / d ≤ a / d + (n - a) / d + 1 := by
        by_contra hgt
        have : d * (a / d + (n - a) / d + 2) ≤ d * (n / d) := Nat.mul_le_mul_left d (by omega)
        rw [mul_add] at this; omega
      have hge_q : a / d + (n - a) / d + 1 ≤ n / d := by
        by_contra hltq
        have : d * (n / d) ≤ d * (a / d + (n - a) / d) := Nat.mul_le_mul_left d (by omega)
        omega
      have hqeq : n / d = a / d + (n - a) / d + 1 := by omega
      rw [hqeq, mul_add, mul_one] at h1
      omega
    have hmul : d * (n / d) = d * (a / d + (n - a) / d + 1) := by
      rw [mul_add, mul_one]; omega
    exact Nat.eq_of_mul_eq_mul_left hd hmul
  · have hmul : d * (n / d) = d * (a / d + (n - a) / d) := by
      have hle_q : n / d ≤ a / d + (n - a) / d := by
        by_contra hgt
        have : d * (a / d + (n - a) / d + 1) ≤ d * (n / d) := Nat.mul_le_mul_left d (by omega)
        rw [mul_add, mul_one] at this; omega
      have hge_q : a / d + (n - a) / d ≤ n / d := by
        by_contra hltq
        have : d * (n / d + 1) ≤ d * (a / d + (n - a) / d) := Nat.mul_le_mul_left d (by omega)
        rw [mul_add, mul_one] at this; omega
      have hqeq : n / d = a / d + (n - a) / d := by omega
      rw [hqeq]
    exact Nat.eq_of_mul_eq_mul_left hd hmul

private lemma vp_choose_ge_carry {p n a B0 : ℕ} (hp : p.Prime) (ha : a ≤ n) :
    ∑ t ∈ Ico 1 B0, (if n % p ^ t < a % p ^ t then 1 else 0) ≤ vp p (n.choose a) := by
  set B := max B0 (Nat.log p n + 1)
  have hlogn : Nat.log p n < B := by omega
  have hloga : Nat.log p a < B := lt_of_le_of_lt (Nat.log_mono_right ha) hlogn
  have hlogna : Nat.log p (n - a) < B := lt_of_le_of_lt (Nat.log_mono_right (Nat.sub_le n a)) hlogn
  have hfac : n.choose a * a.factorial * (n - a).factorial = n.factorial :=
    Nat.choose_mul_factorial_mul_factorial ha
  have hch_ne : n.choose a ≠ 0 := (Nat.choose_pos ha).ne'
  have hv := congrArg (vp p) hfac
  rw [vp_mul_eq (Nat.mul_ne_zero hch_ne (Nat.factorial_ne_zero a)) (Nat.factorial_ne_zero _),
    vp_mul_eq hch_ne (Nat.factorial_ne_zero a),
    vp_factorial hp hlogn, vp_factorial hp hloga, vp_factorial hp hlogna] at hv
  have hsum_eq : ∑ t ∈ Ico 1 B, n / p ^ t =
      (∑ t ∈ Ico 1 B, a / p ^ t) + (∑ t ∈ Ico 1 B, (n - a) / p ^ t) +
      (∑ t ∈ Ico 1 B, if n % p ^ t < a % p ^ t then 1 else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    exact choose_div_sub_eq ha (Nat.pow_pos hp.pos)
  have hvp_eq : vp p (n.choose a) = ∑ t ∈ Ico 1 B, if n % p ^ t < a % p ^ t then 1 else 0 := by
    omega
  rw [hvp_eq]
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right (by omega))

private lemma vp_f_ge_carry {p m B0 : ℕ} (hp : p.Prime) :
    ∑ t ∈ Ico 1 B0, (if p ^ t ≤ 2 * (m % p ^ t) then 1 else 0) ≤ vp p (f m) := by
  have h := vp_choose_ge_carry (p := p) (n := 2 * m) (a := m) (B0 := B0) hp (by omega)
  refine le_trans ?_ h
  refine Finset.sum_le_sum fun t _ => ?_
  have hpt : 0 < p ^ t := Nat.pow_pos hp.pos
  have hmod : (2 * m) % p ^ t = (2 * (m % p ^ t)) % p ^ t := by
    rw [Nat.mul_mod 2 m, Nat.mul_mod 2 (m % p ^ t), Nat.mod_mod]
  have hlt : m % p ^ t < p ^ t := Nat.mod_lt m hpt
  rw [hmod]
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso
    have hrem : (2 * (m % p ^ t)) % p ^ t = 2 * (m % p ^ t) - p ^ t := by
      have : 2 * (m % p ^ t) = p ^ t + (2 * (m % p ^ t) - p ^ t) := by omega
      conv_lhs => rw [this]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega
  · exact Nat.zero_le _
  · exact le_rfl

private lemma sub_mod_of_dvd {D A x : ℕ} (hD : 0 < D) (hDA : D ∣ A) (hx : x ≤ A)
    (hpos : 0 < x % D) : (A - x) % D = D - x % D := by
  obtain ⟨Q, rfl⟩ := hDA
  have hxdiv := Nat.div_add_mod x D
  have hmodlt : x % D < D := Nat.mod_lt x hD
  have hq : x / D < Q := by
    by_contra hge
    have : D * Q ≤ D * (x / D) := Nat.mul_le_mul_left D (by omega)
    omega
  have heq : D * Q - x = D * (Q - x / D - 1) + (D - x % D) := by
    have h2 : D * (Q - x / D - 1) + D = D * (Q - x / D) := by
      rw [← mul_add_one, show Q - x / D - 1 + 1 = Q - x / D by omega]
    have h3 : D * (Q - x / D) + D * (x / D) = D * Q := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
    omega
  rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]

private lemma key_carry_step {D L r s : ℕ} (hD : 0 < D) (hDL : D ∣ L)
    (hr : r ≤ L) (hs : s ≤ L) (hrs : L ≤ r + s) :
    (if 0 < r % D then 1 else 0) + (if 0 < s % D then 1 else 0) ≤
      (L / D - (L - r) / D - (L - s) / D - (r + s - L) / D) +
      ((2 * r) / D - 2 * (r / D)) + ((2 * s) / D - 2 * (s / D)) := by
  obtain ⟨Q, rfl⟩ := hDL
  have hLdiv : D * Q / D = Q := Nat.mul_div_cancel_left Q hD
  have hrdiv := Nat.div_add_mod r D
  have hsdiv := Nat.div_add_mod s D
  have hrm : r % D < D := Nat.mod_lt r hD
  have hsm : s % D < D := Nat.mod_lt s hD
  have hrq : r / D ≤ Q := by
    have h := Nat.div_le_div_right (c := D) hr
    rwa [hLdiv] at h
  have hsq : s / D ≤ Q := by
    have h := Nat.div_le_div_right (c := D) hs
    rwa [hLdiv] at h
  have hr_lt : 0 < r % D → r / D + 1 ≤ Q := by
    intro hrp
    by_contra hge
    have : D * Q ≤ D * (r / D) := Nat.mul_le_mul_left D (by omega)
    omega
  have hs_lt : 0 < s % D → s / D + 1 ≤ Q := by
    intro hsp
    by_contra hge
    have : D * Q ≤ D * (s / D) := Nat.mul_le_mul_left D (by omega)
    omega
  have hr_le : r / D + (if 0 < r % D then 1 else 0) ≤ Q := by
    split_ifs with h
    · exact hr_lt h
    · omega
  have hs_le : s / D + (if 0 < s % D then 1 else 0) ≤ Q := by
    split_ifs with h
    · exact hs_lt h
    · omega
  have hLr : (D * Q - r) / D = Q - r / D - (if 0 < r % D then 1 else 0) := by
    split_ifs with hrp
    · have hq : r / D < Q := by have := hr_lt hrp; omega
      have heq : D * Q - r = D * (Q - r / D - 1) + (D - r % D) := by
        have h2 : D * (Q - r / D - 1) + D = D * (Q - r / D) := by
          rw [← mul_add_one, show Q - r / D - 1 + 1 = Q - r / D by omega]
        have h3 : D * (Q - r / D) + D * (r / D) = D * Q := by
          rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
        omega
      have hdiv0 : (D - r % D) / D = 0 := Nat.div_eq_of_lt (by omega)
      rw [heq, Nat.mul_add_div hD, hdiv0, add_zero]
    · have hr0 : r % D = 0 := by omega
      have heq : D * Q - r = D * (Q - r / D) := by
        rw [Nat.mul_sub, show D * (r / D) = r by omega]
      rw [heq, Nat.mul_div_cancel_left _ hD]; omega
  have hLs : (D * Q - s) / D = Q - s / D - (if 0 < s % D then 1 else 0) := by
    split_ifs with hsp
    · have hq : s / D < Q := by have := hs_lt hsp; omega
      have heq : D * Q - s = D * (Q - s / D - 1) + (D - s % D) := by
        have h2 : D * (Q - s / D - 1) + D = D * (Q - s / D) := by
          rw [← mul_add_one, show Q - s / D - 1 + 1 = Q - s / D by omega]
        have h3 : D * (Q - s / D) + D * (s / D) = D * Q := by
          rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
        omega
      have hdiv0 : (D - s % D) / D = 0 := Nat.div_eq_of_lt (by omega)
      rw [heq, Nat.mul_add_div hD, hdiv0, add_zero]
    · have hs0 : s % D = 0 := by omega
      have heq : D * Q - s = D * (Q - s / D) := by
        rw [Nat.mul_sub, show D * (s / D) = s by omega]
      rw [heq, Nat.mul_div_cancel_left _ hD]; omega
  have h2r : (2 * r) / D - 2 * (r / D) = if D ≤ 2 * (r % D) then 1 else 0 := by
    have heq : 2 * r = D * (2 * (r / D)) + 2 * (r % D) := by linarith
    rw [heq, Nat.mul_add_div hD]
    split_ifs with hge
    · have hd1 : (2 * (r % D)) / D = 1 := by
        have : 2 * (r % D) = D * 1 + (2 * (r % D) - D) := by omega
        have h0 : (2 * (r % D) - D) / D = 0 := Nat.div_eq_of_lt (by omega)
        rw [this, Nat.mul_add_div hD, h0, add_zero]
      omega
    · have h0 : (2 * (r % D)) / D = 0 := Nat.div_eq_of_lt (by omega)
      omega
  have h2s : (2 * s) / D - 2 * (s / D) = if D ≤ 2 * (s % D) then 1 else 0 := by
    have heq : 2 * s = D * (2 * (s / D)) + 2 * (s % D) := by linarith
    rw [heq, Nat.mul_add_div hD]
    split_ifs with hge
    · have hd1 : (2 * (s % D)) / D = 1 := by
        have : 2 * (s % D) = D * 1 + (2 * (s % D) - D) := by omega
        have h0 : (2 * (s % D) - D) / D = 0 := Nat.div_eq_of_lt (by omega)
        rw [this, Nat.mul_add_div hD, h0, add_zero]
      omega
    · have h0 : (2 * (s % D)) / D = 0 := Nat.div_eq_of_lt (by omega)
      omega
  have hsum : (r + s - D * Q) / D + Q = r / D + s / D + (if D ≤ r % D + s % D then 1 else 0) := by
    have hD_add : D * (r / D) + D * (s / D) = D * (r / D + s / D) := (mul_add D (r / D) (s / D)).symm
    split_ifs with hge
    · have hq_le : Q ≤ r / D + s / D + 1 := by
        by_contra hgt
        have : D * (r / D + s / D + 2) ≤ D * Q := Nat.mul_le_mul_left D (by omega)
        rw [mul_add] at this; omega
      have heq : r + s - D * Q = D * (r / D + s / D + 1 - Q) + (r % D + s % D - D) := by
        have h1 : D * (r / D + s / D + 1 - Q) + D * Q = D * (r / D + s / D + 1) := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hq_le]
        rw [mul_add, mul_one] at h1
        omega
      have h0 : (r % D + s % D - D) / D = 0 := Nat.div_eq_of_lt (by omega)
      rw [heq, Nat.mul_add_div hD, h0, add_zero]
      omega
    · have hq_le : Q ≤ r / D + s / D := by
        by_contra hgt
        have : D * (r / D + s / D + 1) ≤ D * Q := Nat.mul_le_mul_left D (by omega)
        rw [mul_add, mul_one] at this; omega
      have heq : r + s - D * Q = D * (r / D + s / D - Q) + (r % D + s % D) := by
        have h1 : D * (r / D + s / D - Q) + D * Q = D * (r / D + s / D) := by
          rw [← Nat.mul_add, Nat.sub_add_cancel hq_le]
        omega
      have h0 : (r % D + s % D) / D = 0 := Nat.div_eq_of_lt (by omega)
      rw [heq, Nat.mul_add_div hD, h0, add_zero]
      omega
  rw [hLdiv, hLr, hLs, h2r, h2s]
  split_ifs at hsum hr_le hs_le ⊢ <;> omega

private lemma two_mul_mod_eq (x D : ℕ) : (2 * x) % D = (2 * (x % D)) % D := by
  rw [Nat.mul_mod 2 x, Nat.mul_mod 2 (x % D), Nat.mod_mod]

private lemma add3_div_le {D a b c L : ℕ} (hD : 0 < D) (h : a + b + c = L) :
    a / D + b / D + c / D ≤ L / D := by
  have h1 : D * (a / D + b / D + c / D) ≤ L := by
    have := Nat.div_add_mod a D
    have := Nat.div_add_mod b D
    have := Nat.div_add_mod c D
    rw [mul_add, mul_add]; omega
  exact (Nat.le_div_iff_mul_le hD).mpr (by rwa [mul_comm])

private lemma two_mul_div_le {D m : ℕ} (hD : 0 < D) : 2 * (m / D) ≤ (2 * m) / D := by
  have h1 : D * (2 * (m / D)) ≤ 2 * m := by
    have := Nat.div_add_mod m D
    have : D * (2 * (m / D)) = 2 * (D * (m / D)) := by ring
    omega
  exact (Nat.le_div_iff_mul_le hD).mpr (by rwa [mul_comm])

private lemma key_carry_bound {p L E r s : ℕ} (hp : p.Prime)
    (hEL : p ^ E ∣ L) (hr : r ≤ L) (hs : s ≤ L) (hrs : L ≤ r + s) :
    2 * E - (if r = 0 then E else min (vp p r) E) - (if s = 0 then E else min (vp p s) E) ≤
      vp p (L.choose r * r.choose (L - s) * f r * f s) := by
  set M0 := max L (max (2 * r) (2 * s))
  set B := max (E + 1) (Nat.log p M0 + 1)
  have hlogM : Nat.log p M0 < B := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have hlogL : Nat.log p L < B := lt_of_le_of_lt (Nat.log_mono_right (le_max_left _ _)) hlogM
  have hlogLr : Nat.log p (L - r) < B := lt_of_le_of_lt (Nat.log_mono_right (Nat.sub_le L r)) hlogL
  have hlogLs : Nat.log p (L - s) < B := lt_of_le_of_lt (Nat.log_mono_right (Nat.sub_le L s)) hlogL
  have hlogrsL : Nat.log p (r + s - L) < B := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hlogL
  have hlog2r : Nat.log p (2 * r) < B :=
    lt_of_le_of_lt (Nat.log_mono_right (le_trans (le_max_left _ _) (le_max_right _ _))) hlogM
  have hlog2s : Nat.log p (2 * s) < B :=
    lt_of_le_of_lt (Nat.log_mono_right (le_trans (le_max_right _ _) (le_max_right _ _))) hlogM
  have hlogr : Nat.log p r < B := lt_of_le_of_lt (Nat.log_mono_right (by omega : r ≤ 2 * r)) hlog2r
  have hlogs : Nat.log p s < B := lt_of_le_of_lt (Nat.log_mono_right (by omega : s ≤ 2 * s)) hlog2s
  have hM_fac : L.choose r * r.choose (L - s) * (L - r).factorial * (L - s).factorial *
      (r + s - L).factorial = L.factorial := by
    have h1 := Nat.choose_mul_factorial_mul_factorial hr
    have h2 := Nat.choose_mul_factorial_mul_factorial (by omega : L - s ≤ r)
    have hsub : r - (L - s) = r + s - L := by omega
    rw [hsub] at h2
    calc L.choose r * r.choose (L - s) * (L - r).factorial * (L - s).factorial * (r + s - L).factorial
        = L.choose r * (r.choose (L - s) * (L - s).factorial * (r + s - L).factorial) * (L - r).factorial := by ring
      _ = L.choose r * r.factorial * (L - r).factorial := by rw [h2]
      _ = L.factorial := h1
  have hf_r : f r * r.factorial * r.factorial = (2 * r).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (by omega : r ≤ 2 * r)
    rw [show 2 * r - r = r by omega] at h
    exact h
  have hf_s : f s * s.factorial * s.factorial = (2 * s).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (by omega : s ≤ 2 * s)
    rw [show 2 * s - s = s by omega] at h
    exact h
  have hM_ne : L.choose r * r.choose (L - s) ≠ 0 :=
    Nat.mul_ne_zero (Nat.choose_pos hr).ne' (Nat.choose_pos (by omega)).ne'
  have hfr_ne : f r ≠ 0 := (Nat.choose_pos (by omega : r ≤ 2 * r)).ne'
  have hfs_ne : f s ≠ 0 := (Nat.choose_pos (by omega : s ≤ 2 * s)).ne'
  have hvM : vp p (L.choose r * r.choose (L - s)) +
      (∑ t ∈ Ico 1 B, (L - r) / p ^ t) + (∑ t ∈ Ico 1 B, (L - s) / p ^ t) +
      (∑ t ∈ Ico 1 B, (r + s - L) / p ^ t) = ∑ t ∈ Ico 1 B, L / p ^ t := by
    have hv := congrArg (vp p) hM_fac
    repeat rw [vp_mul_eq (by positivity) (by positivity)] at hv
    rw [vp_factorial hp hlogL, vp_factorial hp hlogLr, vp_factorial hp hlogLs,
      vp_factorial hp hlogrsL] at hv
    omega
  have hvfr : vp p (f r) + 2 * (∑ t ∈ Ico 1 B, r / p ^ t) = ∑ t ∈ Ico 1 B, (2 * r) / p ^ t := by
    have hv := congrArg (vp p) hf_r
    repeat rw [vp_mul_eq (by positivity) (by positivity)] at hv
    rw [vp_factorial hp hlog2r, vp_factorial hp hlogr] at hv
    omega
  have hvfs : vp p (f s) + 2 * (∑ t ∈ Ico 1 B, s / p ^ t) = ∑ t ∈ Ico 1 B, (2 * s) / p ^ t := by
    have hv := congrArg (vp p) hf_s
    repeat rw [vp_mul_eq (by positivity) (by positivity)] at hv
    rw [vp_factorial hp hlog2s, vp_factorial hp hlogs] at hv
    omega
  have hterm_le1 : ∀ t : ℕ, (L - r) / p ^ t + (L - s) / p ^ t + (r + s - L) / p ^ t ≤ L / p ^ t :=
    fun t => add3_div_le (Nat.pow_pos hp.pos) (by omega)
  have hterm_le2 : ∀ m t : ℕ, 2 * (m / p ^ t) ≤ (2 * m) / p ^ t :=
    fun m t => two_mul_div_le (Nat.pow_pos hp.pos)
  have hvp_tot : vp p (L.choose r * r.choose (L - s) * f r * f s) =
      ∑ t ∈ Ico 1 B, ((L / p ^ t - (L - r) / p ^ t - (L - s) / p ^ t - (r + s - L) / p ^ t) +
        ((2 * r) / p ^ t - 2 * (r / p ^ t)) + ((2 * s) / p ^ t - 2 * (s / p ^ t))) := by
    rw [vp_mul_eq (Nat.mul_ne_zero hM_ne hfr_ne) hfs_ne, vp_mul_eq hM_ne hfr_ne]
    have hsum1 : ∑ t ∈ Ico 1 B, (L / p ^ t - (L - r) / p ^ t - (L - s) / p ^ t - (r + s - L) / p ^ t) +
        (∑ t ∈ Ico 1 B, (L - r) / p ^ t) + (∑ t ∈ Ico 1 B, (L - s) / p ^ t) +
        (∑ t ∈ Ico 1 B, (r + s - L) / p ^ t) = ∑ t ∈ Ico 1 B, L / p ^ t := by
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      have := hterm_le1 t; omega
    have hsum2 : ∑ t ∈ Ico 1 B, ((2 * r) / p ^ t - 2 * (r / p ^ t)) +
        2 * (∑ t ∈ Ico 1 B, r / p ^ t) = ∑ t ∈ Ico 1 B, (2 * r) / p ^ t := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      have := hterm_le2 r t; omega
    have hsum3 : ∑ t ∈ Ico 1 B, ((2 * s) / p ^ t - 2 * (s / p ^ t)) +
        2 * (∑ t ∈ Ico 1 B, s / p ^ t) = ∑ t ∈ Ico 1 B, (2 * s) / p ^ t := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      have := hterm_le2 s t; omega
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    omega
  rw [hvp_tot]
  have hsub_le : ∑ t ∈ Ico 1 (E + 1),
      ((if 0 < r % p ^ t then 1 else 0) + (if 0 < s % p ^ t then 1 else 0)) ≤
      ∑ t ∈ Ico 1 B, ((L / p ^ t - (L - r) / p ^ t - (L - s) / p ^ t - (r + s - L) / p ^ t) +
        ((2 * r) / p ^ t - 2 * (r / p ^ t)) + ((2 * s) / p ^ t - 2 * (s / p ^ t))) := by
    calc ∑ t ∈ Ico 1 (E + 1),
          ((if 0 < r % p ^ t then 1 else 0) + (if 0 < s % p ^ t then 1 else 0))
        ≤ ∑ t ∈ Ico 1 (E + 1),
          ((L / p ^ t - (L - r) / p ^ t - (L - s) / p ^ t - (r + s - L) / p ^ t) +
            ((2 * r) / p ^ t - 2 * (r / p ^ t)) + ((2 * s) / p ^ t - 2 * (s / p ^ t))) := by
          refine Finset.sum_le_sum fun t ht => ?_
          rw [mem_Ico] at ht
          have hptL : p ^ t ∣ L := dvd_trans (Nat.pow_dvd_pow p (by omega)) hEL
          exact key_carry_step (Nat.pow_pos hp.pos) hptL hr hs hrs
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right (le_max_left _ _))
  refine le_trans ?_ hsub_le
  rw [Finset.sum_add_distrib]
  have hcnt : ∀ m : ℕ, E - (if m = 0 then E else min (vp p m) E) ≤
      ∑ t ∈ Ico 1 (E + 1), if 0 < m % p ^ t then 1 else 0 := by
    intro m
    by_cases hm0 : m = 0
    · subst hm0; simp
    · simp only [hm0, ↓reduceIte]
      set e := min (vp p m) E
      have hsub : Ico (e + 1) (E + 1) ⊆ (Ico 1 (E + 1)).filter (fun t => 0 < m % p ^ t) := by
        intro t ht
        rw [mem_Ico] at ht
        rw [mem_filter, mem_Ico]
        refine ⟨⟨by omega, ht.2⟩, ?_⟩
        by_contra h0
        have hrem0 : m % p ^ t = 0 := Nat.eq_zero_of_not_pos h0
        have hdvd : p ^ t ∣ m := Nat.dvd_of_mod_eq_zero hrem0
        have hle := vp_le_of_dvd hp hm0 hdvd
        omega
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      calc E - e = (Ico (e + 1) (E + 1)).card := by simp
        _ ≤ ((Ico 1 (E + 1)).filter (fun t => 0 < m % p ^ t)).card := Finset.card_le_card hsub
  have h1 := hcnt r
  have h2 := hcnt s
  omega

private lemma piece_NN_dvd {p n k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (p : ℤ) ^ (2 * k) ∣
      ∑ r ∈ (range (p * (n * p ^ (k - 1)) + 1)).filter (fun r => ¬ p ∣ r),
        ∑ s ∈ (range (p * (n * p ^ (k - 1)) + 1)).filter (fun s => ¬ p ∣ s),
          M (p * (n * p ^ (k - 1))) r s * (f r : ℤ) * (f s : ℤ) := by
  set A := n * p ^ (k - 1)
  set N := p * A
  have hpkN : p ^ k ∣ N := by
    refine ⟨n, ?_⟩
    simp only [N, A]
    calc p * (n * p ^ (k - 1)) = (p ^ (k - 1) * p) * n := by ring
      _ = p ^ k * n := by rw [← pow_succ, Nat.sub_add_cancel hk]
  refine Finset.dvd_sum fun r hr => Finset.dvd_sum fun s hs => ?_
  rw [mem_filter, mem_range] at hr hs
  by_cases hrs : N ≤ r + s
  · have hr0 : r ≠ 0 := by intro h; subst h; exact hr.2 (dvd_zero p)
    have hs0 : s ≠ 0 := by intro h; subst h; exact hs.2 (dvd_zero p)
    have hvpr : vp p r = 0 := by
      by_contra hne
      exact hr.2 (dvd_trans (dvd_pow_self p hne) (vp_dvd hp hr0))
    have hvps : vp p s = 0 := by
      by_contra hne
      exact hs.2 (dvd_trans (dvd_pow_self p hne) (vp_dvd hp hs0))
    have hkb := key_carry_bound (p := p) (L := N) (E := k) (r := r) (s := s)
      hp hpkN (by omega) (by omega) hrs
    simp only [hr0, hs0, hvpr, hvps, ↓reduceIte, Nat.zero_min, Nat.sub_zero] at hkb
    have hne : N.choose r * r.choose (N - s) * f r * f s ≠ 0 := by
      have h1 := (Nat.choose_pos (by omega : r ≤ N)).ne'
      have h2 := (Nat.choose_pos (by omega : N - s ≤ r)).ne'
      have h3 : f r ≠ 0 := (Nat.choose_pos (by omega : r ≤ 2 * r)).ne'
      have h4 : f s ≠ 0 := (Nat.choose_pos (by omega : s ≤ 2 * s)).ne'
      positivity
    have hd_nat : p ^ (2 * k) ∣ N.choose r * r.choose (N - s) * f r * f s :=
      dvd_trans (Nat.pow_dvd_pow p hkb) (vp_dvd hp hne)
    have hd_int : (p : ℤ) ^ (2 * k) ∣ ((N.choose r * r.choose (N - s) * f r * f s : ℕ) : ℤ) := by
      exact_mod_cast hd_nat
    have hre : M N r s * (f r : ℤ) * (f s : ℤ) =
        (-1 : ℤ) ^ (r + s) * ((N.choose r * r.choose (N - s) * f r * f s : ℕ) : ℤ) := by
      unfold M; push_cast; ring
    rw [hre]
    exact dvd_mul_of_dvd_right hd_int _
  · rw [M_eq_zero_of_lt N r s (by omega), zero_mul, zero_mul]
    exact dvd_zero _

private lemma piece_1a_dvd {p n k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) :
    (p : ℤ) ^ (2 * k) ∣
      2 * ∑ s' ∈ range (n * p ^ (k - 1) + 1),
        (-1 : ℤ) ^ (n * p ^ (k - 1) - s') *
          (((p * (n * p ^ (k - 1))).choose (p * s') : ℤ) - ((n * p ^ (k - 1)).choose s' : ℤ)) *
          (f (p * s') : ℤ) * B (p * (n * p ^ (k - 1))) (p * s') := by
  set A := n * p ^ (k - 1)
  have hA1 : 1 ≤ A := Nat.mul_pos hn (Nat.pow_pos hp.pos)
  have hAk : p ^ (k - 1) ∣ A := dvd_mul_left _ n
  refine dvd_mul_of_dvd_right (Finset.dvd_sum fun s' _ => ?_) 2
  have hd := choose_pA_ps_dvd (k := k) (s := s') hp hp5 hA1 hAk
  have hre : (-1 : ℤ) ^ (A - s') * (((p * A).choose (p * s') : ℤ) - (A.choose s' : ℤ)) *
      (f (p * s') : ℤ) * B (p * A) (p * s') =
      (((p * A).choose (p * s') : ℤ) - (A.choose s' : ℤ)) *
        ((-1 : ℤ) ^ (A - s') * (f (p * s') : ℤ) * B (p * A) (p * s')) := by ring
  rw [hre]
  exact dvd_mul_of_dvd_left hd _

private lemma piece_1b_dvd {p n k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (2 * k) ∣
      -(∑ r' ∈ range (n * p ^ (k - 1) + 1), ∑ s' ∈ range (n * p ^ (k - 1) + 1),
        (M (p * (n * p ^ (k - 1))) (p * r') (p * s') - M (n * p ^ (k - 1)) r' s') *
          (f (p * r') : ℤ) * (f (p * s') : ℤ)) := by
  set A := n * p ^ (k - 1)
  have hA1 : 1 ≤ A := Nat.mul_pos hn (Nat.pow_pos hp.pos)
  have hAk : p ^ (k - 1) ∣ A := dvd_mul_left _ n
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  refine dvd_neg.mpr (Finset.dvd_sum fun r' hr' => Finset.dvd_sum fun s' hs' => ?_)
  have hr'A : r' ≤ A := by rw [mem_range] at hr'; omega
  have hs'A : s' ≤ A := by rw [mem_range] at hs'; omega
  by_cases hrs : A ≤ r' + s'
  · set b := A - s'
    have hsign : (-1 : ℤ) ^ (p * r' + p * s') = (-1 : ℤ) ^ (r' + s') := by
      rw [← mul_add]; exact neg_one_pow_mul_odd p (r' + s') hpodd
    have hsubp : p * A - p * s' = p * b := by simp only [b]; rw [Nat.mul_sub]
    have hMdiff : (M (p * A) (p * r') (p * s') - M A r' s') * (f (p * r') : ℤ) * (f (p * s') : ℤ) =
        (-1 : ℤ) ^ (r' + s') *
          ((((p * A).choose (p * r') : ℤ) - (A.choose r' : ℤ)) *
            ((p * r').choose (p * b) : ℤ) * (f (p * r') : ℤ) * (f (p * s') : ℤ) +
          (A.choose r' : ℤ) * (((p * r').choose (p * b) : ℤ) - (r'.choose b : ℤ)) *
            (f (p * r') : ℤ) * (f (p * s') : ℤ)) := by
      unfold M; rw [hsign, hsubp]; simp only [b]; ring
    rw [hMdiff]
    refine dvd_mul_of_dvd_right (dvd_add ?_ ?_) _
    · have hd1 := choose_pA_ps_dvd (k := k) (s := r') hp hp5 hA1 hAk
      have hre : (((p * A).choose (p * r') : ℤ) - (A.choose r' : ℤ)) *
          ((p * r').choose (p * b) : ℤ) * (f (p * r') : ℤ) * (f (p * s') : ℤ) =
          (((p * A).choose (p * r') : ℤ) - (A.choose r' : ℤ)) *
            (((p * r').choose (p * b) : ℤ) * (f (p * r') : ℤ) * (f (p * s') : ℤ)) := by ring
      rw [hre]; exact dvd_mul_of_dvd_left hd1 _
    · by_cases hb0 : b = 0
      · simp [hb0]
      · by_cases hbr : b = r'
        · simp [hbr]
        · have hb1 : 1 ≤ b := by omega
          have hblt : b < r' := by omega
          have hr'0 : r' ≠ 0 := by omega
          have hs'0 : s' ≠ 0 := by omega
          have hkaz := choose_mul_p_sub_dvd (m := r') (b := b) hp hp5 hb1 hblt
          have hprod_ne : A.choose r' * f (p * r') * f (p * s') ≠ 0 := by
            have h1 := (Nat.choose_pos hr'A).ne'
            have h2 : f (p * r') ≠ 0 := (Nat.choose_pos (by omega : p * r' ≤ 2 * (p * r'))).ne'
            have h3 : f (p * s') ≠ 0 := (Nat.choose_pos (by omega : p * s' ≤ 2 * (p * s'))).ne'
            positivity
          have hdv_prod : (p : ℤ) ^ vp p (A.choose r' * f (p * r') * f (p * s')) ∣
              ((A.choose r' : ℤ) * (f (p * r') : ℤ) * (f (p * s') : ℤ)) := by
            exact_mod_cast vp_dvd hp hprod_ne
          have hmul_dvd : (p : ℤ) ^ (vp p (A.choose r' * f (p * r') * f (p * s')) +
              (3 + vp p b + vp p (r' - b) + vp p r' + vp p (r'.choose b))) ∣
              ((A.choose r' : ℤ) * (f (p * r') : ℤ) * (f (p * s') : ℤ)) *
                (((p * r').choose (p * b) : ℤ) - (r'.choose b : ℤ)) := by
            rw [pow_add]; exact mul_dvd_mul hdv_prod hkaz
          have hre : (A.choose r' : ℤ) * (((p * r').choose (p * b) : ℤ) - (r'.choose b : ℤ)) *
              (f (p * r') : ℤ) * (f (p * s') : ℤ) =
              ((A.choose r' : ℤ) * (f (p * r') : ℤ) * (f (p * s') : ℤ)) *
                (((p * r').choose (p * b) : ℤ) - (r'.choose b : ℤ)) := by ring
          rw [hre]
          refine dvd_trans (pow_dvd_pow (p : ℤ) ?_) hmul_dvd
          have hkb := key_carry_bound (p := p) (L := A) (E := k - 1) (r := r') (s := s')
            hp hAk hr'A hs'A hrs
          simp only [hr'0, hs'0, ↓reduceIte, show A - s' = b from rfl] at hkb
          have hvp_fr := vp_f_mul_p_ge (m := r') hp hp5
          have hvp_fs := vp_f_mul_p_ge (m := s') hp hp5
          have hvp_split : vp p (A.choose r' * r'.choose b * f r' * f s') ≤
              vp p (A.choose r' * f (p * r') * f (p * s')) + vp p (r'.choose b) := by
            have h1 := (Nat.choose_pos hr'A).ne'
            have h2 := (Nat.choose_pos (by omega : b ≤ r')).ne'
            have h3 : f r' ≠ 0 := (Nat.choose_pos (by omega : r' ≤ 2 * r')).ne'
            have h4 : f s' ≠ 0 := (Nat.choose_pos (by omega : s' ≤ 2 * s')).ne'
            have h5 : f (p * r') ≠ 0 := (Nat.choose_pos (by omega : p * r' ≤ 2 * (p * r'))).ne'
            have h6 : f (p * s') ≠ 0 := (Nat.choose_pos (by omega : p * s' ≤ 2 * (p * s'))).ne'
            repeat rw [vp_mul_eq (by positivity) (by positivity)]
            omega
          have hmin_b : min (vp p s') (k - 1) ≤ vp p b := by
            set e2 := min (vp p s') (k - 1)
            have he2s : p ^ e2 ∣ s' := dvd_trans (Nat.pow_dvd_pow p (min_le_left _ _)) (vp_dvd hp hs'0)
            have he2A : p ^ e2 ∣ A := dvd_trans (Nat.pow_dvd_pow p (min_le_right _ _)) hAk
            have he2b : p ^ e2 ∣ b := Nat.dvd_sub he2A he2s
            exact vp_le_of_dvd hp hb0 he2b
          have hmin_r : min (vp p r') (k - 1) ≤ vp p r' := min_le_left _ _
          omega
  · have hlt : r' + s' < A := by omega
    have hplt : p * r' + p * s' < p * A := by
      rw [← mul_add]; exact Nat.mul_lt_mul_of_pos_left hlt hp.pos
    rw [M_eq_zero_of_lt (p * A) (p * r') (p * s') hplt, M_eq_zero_of_lt A r' s' hlt]
    simp

private lemma piece_2_dvd {p n k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    (p : ℤ) ^ (2 * k) ∣
      -(∑ r' ∈ range (n * p ^ (k - 1) + 1), ∑ s' ∈ range (n * p ^ (k - 1) + 1),
        M (n * p ^ (k - 1)) r' s' *
          ((f (p * r') : ℤ) - (f r' : ℤ)) * ((f (p * s') : ℤ) - (f s' : ℤ))) := by
  set A := n * p ^ (k - 1)
  have hAk : p ^ (k - 1) ∣ A := dvd_mul_left _ n
  refine dvd_neg.mpr (Finset.dvd_sum fun r' hr' => Finset.dvd_sum fun s' hs' => ?_)
  have hr'A : r' ≤ A := by rw [mem_range] at hr'; omega
  have hs'A : s' ≤ A := by rw [mem_range] at hs'; omega
  by_cases hrs : A ≤ r' + s'
  · by_cases hr'0 : r' = 0
    · subst hr'0; simp [f]
    · by_cases hs'0 : s' = 0
      · subst hs'0; simp [f]
      · have hfr := f_mul_p_sub_dvd (m := r') hp hp5 (by omega)
        have hfs := f_mul_p_sub_dvd (m := s') hp hp5 (by omega)
        have hM_ne : A.choose r' * r'.choose (A - s') ≠ 0 :=
          Nat.mul_ne_zero (Nat.choose_pos hr'A).ne' (Nat.choose_pos (by omega)).ne'
        have hM_dvd : (p : ℤ) ^ vp p (A.choose r' * r'.choose (A - s')) ∣ M A r' s' := by
          unfold M
          have hd : (p : ℤ) ^ vp p (A.choose r' * r'.choose (A - s')) ∣
              ((A.choose r' * r'.choose (A - s') : ℕ) : ℤ) := by
            exact_mod_cast vp_dvd hp hM_ne
          have hre : (-1 : ℤ) ^ (r' + s') * (A.choose r' : ℤ) * (r'.choose (A - s') : ℤ) =
              (-1 : ℤ) ^ (r' + s') * ((A.choose r' * r'.choose (A - s') : ℕ) : ℤ) := by
            push_cast; ring
          rw [hre]; exact dvd_mul_of_dvd_right hd _
        have hmul := mul_dvd_mul (mul_dvd_mul hM_dvd hfr) hfs
        rw [← pow_add, ← pow_add] at hmul
        refine dvd_trans (pow_dvd_pow (p : ℤ) ?_) hmul
        have hkb := key_carry_bound (p := p) (L := A) (E := k - 1) (r := r') (s := s')
          hp hAk hr'A hs'A hrs
        simp only [hr'0, hs'0, ↓reduceIte] at hkb
        have hvp_eq : vp p (A.choose r' * r'.choose (A - s') * f r' * f s') =
            vp p (A.choose r' * r'.choose (A - s')) + vp p (f r') + vp p (f s') := by
          have h3 : f r' ≠ 0 := (Nat.choose_pos (by omega : r' ≤ 2 * r')).ne'
          have h4 : f s' ≠ 0 := (Nat.choose_pos (by omega : s' ≤ 2 * s')).ne'
          rw [vp_mul_eq (Nat.mul_ne_zero hM_ne h3) h4, vp_mul_eq hM_ne h3]
        have hmin1 : min (vp p r') (k - 1) ≤ vp p r' := min_le_left _ _
        have hmin2 : min (vp p s') (k - 1) ≤ vp p s' := min_le_left _ _
        omega
  · rw [M_eq_zero_of_lt A r' s' (by omega), zero_mul, zero_mul]
    exact dvd_zero _

-- ============================================================================
-- Block 4: Trinomial Overflow Theorem, Enhanced Supercongruence, and Piece 3
-- ============================================================================

private def tauP (p L N M : ℕ) : ℕ :=
  ((Ico 1 L).filter fun t => 2 * (N % p ^ t) < p ^ t ∧ 2 * (N % p ^ t) < M % p ^ t).card

private lemma T_dvd_tauP {p L N M : ℕ} (hp : p.Prime) :
    p ^ tauP p L N M ∣ T N M := by
  by_cases hM : 2 * N < M
  · rw [T_eq_zero_of_gt N M hM]; exact dvd_zero _
  · rw [T_multinom_sum]
    refine Finset.dvd_sum fun c hc => ?_
    have hcN : c ≤ N := by rw [mem_range] at hc; omega
    split_ifs with h2c
    · by_cases hb : M - 2 * c ≤ N - c
      · set b := M - 2 * c
        set a := N - c - b
        have habc : a + b + c = N := by omega
        have hbcM : b + 2 * c = M := by omega
        have hfac : N.choose c * (N - c).choose b * a.factorial * b.factorial * c.factorial =
            N.factorial := by
          have h1 := Nat.choose_mul_factorial_mul_factorial hcN
          have h2 := Nat.choose_mul_factorial_mul_factorial hb
          have hsub : N - c - b = a := rfl
          rw [hsub] at h2
          calc N.choose c * (N - c).choose b * a.factorial * b.factorial * c.factorial
              = N.choose c * ((N - c).choose b * b.factorial * a.factorial) * c.factorial := by ring
            _ = N.choose c * (N - c).factorial * c.factorial := by rw [h2]
            _ = N.factorial := by rw [mul_right_comm]; exact h1
        have hch_ne : N.choose c * (N - c).choose b ≠ 0 :=
          Nat.mul_ne_zero (Nat.choose_pos hcN).ne' (Nat.choose_pos hb).ne'
        set B := max L (Nat.log p N + 1)
        have hlogN : Nat.log p N < B := by omega
        have hloga : Nat.log p a < B := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hlogN
        have hlogb : Nat.log p b < B := lt_of_le_of_lt (Nat.log_mono_right (by omega)) hlogN
        have hlogc : Nat.log p c < B := lt_of_le_of_lt (Nat.log_mono_right hcN) hlogN
        have hv := congrArg (vp p) hfac
        repeat rw [vp_mul_eq (by positivity) (by positivity)] at hv
        rw [vp_factorial hp hlogN, vp_factorial hp hloga, vp_factorial hp hlogb,
          vp_factorial hp hlogc] at hv
        have htle : ∀ t : ℕ, a / p ^ t + b / p ^ t + c / p ^ t ≤ N / p ^ t :=
          fun t => add3_div_le (Nat.pow_pos hp.pos) habc
        have hvp_eq : vp p (N.choose c * (N - c).choose b) =
            ∑ t ∈ Ico 1 B, (N / p ^ t - a / p ^ t - b / p ^ t - c / p ^ t) := by
          have hsum : ∑ t ∈ Ico 1 B, (N / p ^ t - a / p ^ t - b / p ^ t - c / p ^ t) +
              (∑ t ∈ Ico 1 B, a / p ^ t) + (∑ t ∈ Ico 1 B, b / p ^ t) +
              (∑ t ∈ Ico 1 B, c / p ^ t) = ∑ t ∈ Ico 1 B, N / p ^ t := by
            simp only [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun t _ => ?_
            have := htle t; omega
          omega
        have htau_le : tauP p L N M ≤ vp p (N.choose c * (N - c).choose b) := by
          rw [hvp_eq]
          unfold tauP
          set S := (Ico 1 L).filter fun t => 2 * (N % p ^ t) < p ^ t ∧ 2 * (N % p ^ t) < M % p ^ t
          have hsub : S ⊆ Ico 1 B := fun t ht => by
            have := (mem_filter.mp ht).1
            rw [mem_Ico] at this ⊢; omega
          calc S.card = ∑ _t ∈ S, 1 := by simp
            _ ≤ ∑ t ∈ S, (N / p ^ t - a / p ^ t - b / p ^ t - c / p ^ t) := by
                refine Finset.sum_le_sum fun t ht => ?_
                have hcond := (mem_filter.mp ht).2
                by_contra h0
                have hle_t := htle t
                have heq : N / p ^ t = a / p ^ t + b / p ^ t + c / p ^ t := by omega
                have h1 := Nat.div_add_mod a (p ^ t)
                have h2 := Nat.div_add_mod b (p ^ t)
                have h3 := Nat.div_add_mod c (p ^ t)
                have h4 := Nat.div_add_mod N (p ^ t)
                have hmul : p ^ t * (N / p ^ t) = p ^ t * (a / p ^ t) + p ^ t * (b / p ^ t) + p ^ t * (c / p ^ t) := by
                  rw [heq, mul_add, mul_add]
                have hrem : a % p ^ t + b % p ^ t + c % p ^ t = N % p ^ t := by omega
                have hMmod : M % p ^ t = (b % p ^ t + 2 * (c % p ^ t)) % p ^ t := by
                  rw [← hbcM]
                  calc (b + 2 * c) % p ^ t
                      = (b % p ^ t + (2 * c) % p ^ t) % p ^ t := Nat.add_mod _ _ _
                    _ = (b % p ^ t + (2 * (c % p ^ t)) % p ^ t) % p ^ t := by rw [two_mul_mod_eq]
                    _ = (b % p ^ t % p ^ t + (2 * (c % p ^ t)) % p ^ t) % p ^ t := by rw [Nat.mod_mod]
                    _ = (b % p ^ t + 2 * (c % p ^ t)) % p ^ t := (Nat.add_mod _ _ _).symm
                have h2N : b % p ^ t + 2 * (c % p ^ t) ≤ 2 * (N % p ^ t) := by
                  rw [← hrem]
                  linarith [Nat.zero_le (a % p ^ t), Nat.zero_le (b % p ^ t)]
                have hsmall : b % p ^ t + 2 * (c % p ^ t) < p ^ t := lt_of_le_of_lt h2N hcond.1
                rw [Nat.mod_eq_of_lt hsmall] at hMmod
                have hleM : M % p ^ t ≤ 2 * (N % p ^ t) := by rw [hMmod]; exact h2N
                exact absurd hcond.2 (not_lt_of_ge hleM)
            _ ≤ ∑ t ∈ Ico 1 B, (N / p ^ t - a / p ^ t - b / p ^ t - c / p ^ t) :=
                Finset.sum_le_sum_of_subset hsub
        exact dvd_trans (Nat.pow_dvd_pow p htau_le) (vp_dvd hp hch_ne)
      · have hz : (N - c).choose (M - 2 * c) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hz, mul_zero]; exact dvd_zero _
    · exact dvd_zero _

private lemma T_dvd_of_pow_dvd {p K N M : ℕ} (hp : p.Prime)
    (hN : p ^ K ∣ N) (hMpos : 0 < M) :
    p ^ (K - vp p M) ∣ T N M := by
  have htau : K - vp p M ≤ tauP p (K + 1) N M := by
    unfold tauP
    have hsub : Ico (vp p M + 1) (K + 1) ⊆
        (Ico 1 (K + 1)).filter fun t => 2 * (N % p ^ t) < p ^ t ∧ 2 * (N % p ^ t) < M % p ^ t := by
      intro t ht
      rw [mem_Ico] at ht
      rw [mem_filter, mem_Ico]
      refine ⟨⟨by omega, ht.2⟩, ?_⟩
      have hptN : p ^ t ∣ N := dvd_trans (Nat.pow_dvd_pow p (by omega)) hN
      have hNmod : N % p ^ t = 0 := Nat.mod_eq_zero_of_dvd hptN
      have hMmod : 0 < M % p ^ t := by
        by_contra h0
        have hrem0 : M % p ^ t = 0 := Nat.eq_zero_of_not_pos h0
        have hdvd : p ^ t ∣ M := Nat.dvd_of_mod_eq_zero hrem0
        have hle := vp_le_of_dvd hp (by omega) hdvd
        omega
      rw [hNmod]
      exact ⟨by simpa using Nat.pow_pos hp.pos (n := t), by omega⟩
    calc K - vp p M = (Ico (vp p M + 1) (K + 1)).card := by simp
      _ ≤ _ := Finset.card_le_card hsub
  exact dvd_trans (Nat.pow_dvd_pow p htau) (T_dvd_tauP (L := K + 1) hp)

private lemma base_trinom_supercong {p e s' j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hs' : 1 ≤ s') (he : p ^ e ∣ s') :
    (p : ℤ) ^ (2 * (e + 1)) ∣ ((T (p * s') (p * j) : ℤ) - (T s' j : ℤ)) := by
  set k := e + 1
  have hk_sub : k - 1 = e := by omega
  have hN1 : 1 ≤ p * s' := Nat.mul_pos hp.pos hs'
  have hN_dvd : p ^ k ∣ p * s' := by
    rw [show k = e + 1 by rfl, pow_succ, mul_comm (p ^ e) p]
    exact Nat.mul_dvd_mul_left p he
  rw [T_eq_conv (p * s') (p * j) hN1, T_eq_conv s' j hs']
  rw [← Finset.sum_filter_add_sum_filter_not (range (p * j / 3 + 1)) (fun r => p ∣ r)]
  have hnot_dvd : (p : ℤ) ^ (2 * k) ∣
      ∑ r ∈ (range (p * j / 3 + 1)).filter (fun r => ¬ p ∣ r),
        (-1 : ℤ) ^ r * ((p * s').choose r : ℤ) *
          ((p * s' + (p * j - 3 * r) - 1).choose (p * j - 3 * r) : ℤ) := by
    refine Finset.dvd_sum fun r hr => ?_
    rw [mem_filter, mem_range] at hr
    obtain ⟨hrle, hpr⟩ := hr
    have h3r : 3 * r ≤ p * j := by omega
    have hp3 : ¬ p ∣ 3 := by intro h; have := Nat.le_of_dvd (by decide) h; omega
    have hpm : ¬ p ∣ p * j - 3 * r := by
      intro hdiv
      have hsum : p ∣ (p * j - 3 * r) + 3 * r := by
        rw [Nat.sub_add_cancel h3r]; exact dvd_mul_right p j
      have h3r_dvd : p ∣ 3 * r := (Nat.dvd_add_right hdiv).mp hsum
      rcases hp.dvd_mul.mp h3r_dvd with h3 | hr'
      · exact hp3 h3
      · exact hpr hr'
    have hd1 : (p : ℤ) ^ k ∣ ((p * s').choose r : ℤ) := by
      exact_mod_cast pow_dvd_choose_of_not_dvd hp hN_dvd hpr
    have hd2 : (p : ℤ) ^ k ∣ ((p * s' + (p * j - 3 * r) - 1).choose (p * j - 3 * r) : ℤ) := by
      exact_mod_cast pow_dvd_multichoose_of_not_dvd hp hN1 hN_dvd hpm
    have hprod : (p : ℤ) ^ (2 * k) ∣ ((p * s').choose r : ℤ) *
        ((p * s' + (p * j - 3 * r) - 1).choose (p * j - 3 * r) : ℤ) := by
      rw [show 2 * k = k + k by ring, pow_add]; exact mul_dvd_mul hd1 hd2
    have hre : (-1 : ℤ) ^ r * ((p * s').choose r : ℤ) *
        ((p * s' + (p * j - 3 * r) - 1).choose (p * j - 3 * r) : ℤ) =
        (-1 : ℤ) ^ r * (((p * s').choose r : ℤ) *
          ((p * s' + (p * j - 3 * r) - 1).choose (p * j - 3 * r) : ℤ)) := by ring
    rw [hre]; exact dvd_mul_of_dvd_right hprod _
  have hdvd_eq :
      ∑ r ∈ (range (p * j / 3 + 1)).filter (fun r => p ∣ r),
        (-1 : ℤ) ^ r * ((p * s').choose r : ℤ) *
          ((p * s' + (p * j - 3 * r) - 1).choose (p * j - 3 * r) : ℤ) =
      ∑ r' ∈ range (j / 3 + 1),
        (-1 : ℤ) ^ (p * r') * ((p * s').choose (p * r') : ℤ) *
          ((p * s' + p * (j - 3 * r') - 1).choose (p * (j - 3 * r')) : ℤ) := by
    symm
    refine Finset.sum_bij (fun r' _ => p * r') ?_ ?_ ?_ ?_
    · intro r' hr'
      rw [mem_range] at hr'
      rw [mem_filter, mem_range]
      refine ⟨?_, dvd_mul_right p r'⟩
      have h3r : 3 * r' ≤ j := by omega
      have hmul : 3 * (p * r') ≤ p * j := by
        have := Nat.mul_le_mul_left p h3r; linarith
      omega
    · intro r₁ _ r₂ _ heq; exact Nat.eq_of_mul_eq_mul_left hp.pos heq
    · intro r hr
      rw [mem_filter, mem_range] at hr
      obtain ⟨hrlt, ⟨r', rfl⟩⟩ := hr
      have h3pr : 3 * (p * r') ≤ p * j := by omega
      have h3r : 3 * r' ≤ j := Nat.le_of_mul_le_mul_left (by linarith) hp.pos
      exact ⟨r', mem_range.mpr (by omega), rfl⟩
    · intro r' hr'
      have h3r : 3 * r' ≤ j := by have := mem_range.mp hr'; omega
      have hsub : p * j - 3 * (p * r') = p * (j - 3 * r') := by
        rw [show 3 * (p * r') = p * (3 * r') by ring, ← Nat.mul_sub_left_distrib]
      rw [hsub]
  rw [hdvd_eq]
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  have hpair_dvd : (p : ℤ) ^ (2 * k) ∣
      ((∑ r' ∈ range (j / 3 + 1),
        (-1 : ℤ) ^ (p * r') * ((p * s').choose (p * r') : ℤ) *
          ((p * s' + p * (j - 3 * r') - 1).choose (p * (j - 3 * r')) : ℤ)) -
      (∑ r' ∈ range (j / 3 + 1),
        (-1 : ℤ) ^ r' * (s'.choose r' : ℤ) *
          ((s' + (j - 3 * r') - 1).choose (j - 3 * r') : ℤ))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun r' _ => ?_
    have hsign := neg_one_pow_mul_odd p r' hp_odd
    rw [hsign]
    have h1 := choose_pA_ps_dvd (k := k) (s := r') hp hp5 hs' (by rwa [hk_sub])
    have h2m := multichoose_pA_pC_modEq (k := k) (C := j - 3 * r') hp hp5 hs' (by rwa [hk_sub])
    have h2 : (p : ℤ) ^ (2 * k) ∣
        (((p * s' + p * (j - 3 * r') - 1).choose (p * (j - 3 * r')) : ℤ) -
          ((s' + (j - 3 * r') - 1).choose (j - 3 * r') : ℤ)) :=
      Int.modEq_iff_dvd.mp h2m.symm
    have hre : (-1 : ℤ) ^ r' * ((p * s').choose (p * r') : ℤ) *
          ((p * s' + p * (j - 3 * r') - 1).choose (p * (j - 3 * r')) : ℤ) -
        (-1 : ℤ) ^ r' * (s'.choose r' : ℤ) *
          ((s' + (j - 3 * r') - 1).choose (j - 3 * r') : ℤ) =
        (-1 : ℤ) ^ r' *
          ((((p * s').choose (p * r') : ℤ) - (s'.choose r' : ℤ)) *
            ((p * s' + p * (j - 3 * r') - 1).choose (p * (j - 3 * r')) : ℤ) +
          (s'.choose r' : ℤ) *
            (((p * s' + p * (j - 3 * r') - 1).choose (p * (j - 3 * r')) : ℤ) -
              ((s' + (j - 3 * r') - 1).choose (j - 3 * r') : ℤ))) := by ring
    rw [hre]
    exact dvd_mul_of_dvd_right (dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right h2 _)) _
  have hre : (∑ r' ∈ range (j / 3 + 1),
        (-1 : ℤ) ^ (p * r') * ((p * s').choose (p * r') : ℤ) *
          ((p * s' + p * (j - 3 * r') - 1).choose (p * (j - 3 * r')) : ℤ)) +
      (∑ r ∈ (range (p * j / 3 + 1)).filter (fun r => ¬ p ∣ r),
        (-1 : ℤ) ^ r * ((p * s').choose r : ℤ) *
          ((p * s' + (p * j - 3 * r) - 1).choose (p * j - 3 * r) : ℤ)) -
      (∑ r' ∈ range (j / 3 + 1),
        (-1 : ℤ) ^ r' * (s'.choose r' : ℤ) *
          ((s' + (j - 3 * r') - 1).choose (j - 3 * r') : ℤ)) =
      ((∑ r' ∈ range (j / 3 + 1),
        (-1 : ℤ) ^ (p * r') * ((p * s').choose (p * r') : ℤ) *
          ((p * s' + p * (j - 3 * r') - 1).choose (p * (j - 3 * r')) : ℤ)) -
       (∑ r' ∈ range (j / 3 + 1),
        (-1 : ℤ) ^ r' * (s'.choose r' : ℤ) *
          ((s' + (j - 3 * r') - 1).choose (j - 3 * r') : ℤ))) +
      (∑ r ∈ (range (p * j / 3 + 1)).filter (fun r => ¬ p ∣ r),
        (-1 : ℤ) ^ r * ((p * s').choose r : ℤ) *
          ((p * s' + (p * j - 3 * r) - 1).choose (p * j - 3 * r) : ℤ)) := by ring
  rw [hre]
  exact dvd_add hpair_dvd hnot_dvd

private noncomputable def missK (K p s' j : ℕ) : ℕ :=
  ((Ico (min (vp p s') K + 1) (K + 1)).filter fun t =>
    2 * (s' % p ^ t) < p ^ t ∧ (j % p ^ t = 0 ∨ 2 * (s' % p ^ t) ≤ j % p ^ t)).card

private lemma missK_le (K p s' j : ℕ) : missK K p s' j ≤ K - min (vp p s') K := by
  unfold missK
  calc _ ≤ (Ico (min (vp p s') K + 1) (K + 1)).card := Finset.card_filter_le _ _
    _ = K - min (vp p s') K := by simp

private lemma enhanced_trinom_supercong {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ∀ K : ℕ, ∀ s' j : ℕ, 1 ≤ s' → j ≤ 2 * s' →
      (p : ℤ) ^ (2 + 2 * min (vp p s') K + missK K p s' j) ∣
        ((T (p * s') (p * j) : ℤ) - (T s' j : ℤ)) := by
  intro K
  induction K using Nat.strong_induction_on with
  | h K ih =>
    intro s' j hs' hj
    set e := min (vp p s') K
    by_cases heK : e = K
    · have hmiss0 : missK K p s' j = 0 := by
        unfold missK
        have hIco : Ico (min (vp p s') K + 1) (K + 1) = ∅ := by
          rw [Finset.Ico_eq_empty_iff]; omega
        simp [hIco]
      rw [hmiss0, add_zero, show 2 + 2 * min (vp p s') K = 2 * (e + 1) by omega]
      have hedvd : p ^ e ∣ s' := dvd_trans (Nat.pow_dvd_pow p (min_le_left _ _)) (vp_dvd hp (by omega))
      exact base_trinom_supercong hp hp5 hs' hedvd
    · have hKpos : 1 ≤ K := by omega
      have he_lt : e < K := by omega
      have hvps_eq : vp p s' = e := by omega
      have he_prev : min (vp p s') (K - 1) = e := by omega
      by_cases hKcond : 2 * (s' % p ^ K) < p ^ K ∧ (j % p ^ K = 0 ∨ 2 * (s' % p ^ K) ≤ j % p ^ K)
      · -- Active level K
        set sbar := s' % p ^ K
        set q := s' / p ^ K
        have hs'eq : s' = q * p ^ K + sbar := by
          simp only [q, sbar]
          rw [mul_comm]
          exact (Nat.div_add_mod s' (p ^ K)).symm
        have hsbar_pos : 1 ≤ sbar := by
          by_contra h0
          have hs0 : s' % p ^ K = 0 := by omega
          have hdvd : p ^ K ∣ s' := Nat.dvd_of_mod_eq_zero hs0
          have hle := vp_le_of_dvd hp (by omega) hdvd
          omega
        by_cases hq0 : q = 0
        · have hs'bar : s' = sbar := by simp [hs'eq, hq0]
          have hjlt : j < p ^ K := by omega
          have hjbar : j % p ^ K = j := Nat.mod_eq_of_lt hjlt
          rw [hjbar] at hKcond
          rcases hKcond.2 with hj0 | hj2
          · subst hj0; simp [T_zero_right]
          · have hjeq : j = 2 * s' := by omega
            subst hjeq
            have h1 : T (p * s') (p * (2 * s')) = 1 := by
              rw [show p * (2 * s') = 2 * (p * s') by ring]; exact T_two_mul_self _
            have h2 : T s' (2 * s') = 1 := T_two_mul_self _
            rw [h1, h2, sub_self]; exact dvd_zero _
        · -- q >= 1: split T(p*s', p*j) - T(s', j) = Sigma_1 + Sigma_2 + Sigma_3
          have hq1 : 1 ≤ q := Nat.pos_of_ne_zero hq0
          have hps'eq : p * s' = q * p ^ (K + 1) + p * sbar := by
            rw [hs'eq, pow_succ]; ring
          have hTbig : (T (p * s') (p * j) : ℤ) =
              ∑ a ∈ range (2 * (p * sbar) + 1),
                if a ≤ p * j then (T (q * p ^ (K + 1)) (p * j - a) : ℤ) * (T (p * sbar) a : ℤ) else 0 := by
            rw [hps'eq, T_add]
            push_cast
            refine Finset.sum_congr rfl fun a _ => ?_
            split_ifs <;> simp
          have hTsmall : (T s' j : ℤ) =
              ∑ b ∈ range (2 * sbar + 1),
                if b ≤ j then (T (q * p ^ K) (j - b) : ℤ) * (T sbar b : ℤ) else 0 := by
            rw [hs'eq, T_add]
            push_cast
            refine Finset.sum_congr rfl fun b _ => ?_
            split_ifs <;> simp
          have hbig_split : (T (p * s') (p * j) : ℤ) =
              (∑ b ∈ range (2 * sbar + 1),
                if b ≤ j then (T (q * p ^ (K + 1)) (p * (j - b)) : ℤ) * (T (p * sbar) (p * b) : ℤ) else 0) +
              (∑ a ∈ (range (2 * (p * sbar) + 1)).filter (fun a => ¬ p ∣ a),
                if a ≤ p * j then (T (q * p ^ (K + 1)) (p * j - a) : ℤ) * (T (p * sbar) a : ℤ) else 0) := by
            rw [hTbig, show 2 * (p * sbar) = p * (2 * sbar) by ring,
              sum_range_p_mul_split p (2 * sbar) hp.pos]
            congr 1
            refine Finset.sum_congr rfl fun b _ => ?_
            have hiff : p * b ≤ p * j ↔ b ≤ j := Nat.mul_le_mul_left_iff hp.pos
            simp only [hiff]
            split_ifs with hbj
            · rw [← Nat.mul_sub_left_distrib]
            · rfl
          have hdecomp : (T (p * s') (p * j) : ℤ) - (T s' j : ℤ) =
              (∑ a ∈ (range (2 * (p * sbar) + 1)).filter (fun a => ¬ p ∣ a),
                if a ≤ p * j then (T (q * p ^ (K + 1)) (p * j - a) : ℤ) * (T (p * sbar) a : ℤ) else 0) +
              (∑ b ∈ range (2 * sbar + 1),
                if b ≤ j then
                  ((T (q * p ^ (K + 1)) (p * (j - b)) : ℤ) - (T (q * p ^ K) (j - b) : ℤ)) *
                    (T (p * sbar) (p * b) : ℤ) else 0) +
              (∑ b ∈ range (2 * sbar + 1),
                if b ≤ j then
                  (T (q * p ^ K) (j - b) : ℤ) * ((T (p * sbar) (p * b) : ℤ) - (T sbar b : ℤ)) else 0) := by
            rw [hbig_split, hTsmall]
            have hpair :
                (∑ b ∈ range (2 * sbar + 1),
                  if b ≤ j then (T (q * p ^ (K + 1)) (p * (j - b)) : ℤ) * (T (p * sbar) (p * b) : ℤ) else 0) -
                (∑ b ∈ range (2 * sbar + 1),
                  if b ≤ j then (T (q * p ^ K) (j - b) : ℤ) * (T sbar b : ℤ) else 0) =
                (∑ b ∈ range (2 * sbar + 1),
                  if b ≤ j then
                    ((T (q * p ^ (K + 1)) (p * (j - b)) : ℤ) - (T (q * p ^ K) (j - b) : ℤ)) *
                      (T (p * sbar) (p * b) : ℤ) else 0) +
                (∑ b ∈ range (2 * sbar + 1),
                  if b ≤ j then
                    (T (q * p ^ K) (j - b) : ℤ) * ((T (p * sbar) (p * b) : ℤ) - (T sbar b : ℤ)) else 0) := by
              rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun b _ => ?_
              split_ifs <;> ring
            linarith
          have hmiss_le := missK_le K p s' j
          have he_sbar_dvd : p ^ e ∣ sbar := by
            have h1 : p ^ e ∣ s' := dvd_trans (Nat.pow_dvd_pow p (min_le_left _ _)) (vp_dvd hp (by omega))
            have h2 : p ^ e ∣ q * p ^ K := dvd_mul_of_dvd_right (Nat.pow_dvd_pow p (by omega)) q
            rw [show sbar = s' - q * p ^ K by omega]
            exact Nat.dvd_sub h1 h2
          rw [hdecomp]
          refine dvd_add (dvd_add ?_ ?_) ?_
          · -- Sigma_1
            refine Finset.dvd_sum fun a ha => ?_
            rw [mem_filter] at ha
            split_ifs with hapj
            · have ha_pos : 0 < a := Nat.pos_of_ne_zero fun h => ha.2 (h ▸ dvd_zero p)
              have hpa_not : ¬ p ∣ p * j - a := by
                intro hdiv
                apply ha.2
                have hsum : p ∣ (p * j - a) + a := by rw [Nat.sub_add_cancel hapj]; exact dvd_mul_right p j
                exact (Nat.dvd_add_right hdiv).mp hsum
              have hpja_pos : 0 < p * j - a := by
                by_contra h0; have : p * j - a = 0 := by omega
                rw [this] at hpa_not; exact hpa_not (dvd_zero p)
              have hvp1 : vp p (p * j - a) = 0 := by
                by_contra hne
                exact hpa_not (dvd_trans (dvd_pow_self p hne) (vp_dvd hp (by omega)))
              have hvp2 : vp p a = 0 := by
                by_contra hne
                exact ha.2 (dvd_trans (dvd_pow_self p hne) (vp_dvd hp (by omega)))
              have hd1 : p ^ (K + 1) ∣ T (q * p ^ (K + 1)) (p * j - a) := by
                have h := T_dvd_of_pow_dvd (K := K + 1) hp (dvd_mul_left _ q) hpja_pos
                simpa [hvp1] using h
              have hd2 : p ^ (e + 1) ∣ T (p * sbar) a := by
                have hpsbar : p ^ (e + 1) ∣ p * sbar := by
                  rw [pow_succ, mul_comm (p ^ e) p]; exact Nat.mul_dvd_mul_left p he_sbar_dvd
                have h := T_dvd_of_pow_dvd (K := e + 1) hp hpsbar ha_pos
                simpa [hvp2] using h
              have hd1z : (p : ℤ) ^ (K + 1) ∣ (T (q * p ^ (K + 1)) (p * j - a) : ℤ) := by exact_mod_cast hd1
              have hd2z : (p : ℤ) ^ (e + 1) ∣ (T (p * sbar) a : ℤ) := by exact_mod_cast hd2
              have hprod := mul_dvd_mul hd1z hd2z
              rw [← pow_add] at hprod
              exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hprod
            · exact dvd_zero _
          · -- Sigma_2
            refine Finset.dvd_sum fun b _ => ?_
            split_ifs with hbj
            · have hbase := base_trinom_supercong (e := K) (s' := q * p ^ K) (j := j - b)
                hp hp5 (Nat.mul_pos hq1 (Nat.pow_pos hp.pos)) (dvd_mul_left _ q)
              have hqp : p * (q * p ^ K) = q * p ^ (K + 1) := by rw [pow_succ]; ring
              rw [hqp] at hbase
              exact dvd_mul_of_dvd_left (dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hbase) _
            · exact dvd_zero _
          · -- Sigma_3
            refine Finset.dvd_sum fun b hb => ?_
            have hb_le : b ≤ 2 * sbar := by rw [mem_range] at hb; omega
            split_ifs with hbj
            · by_cases hb0 : b = 0
              · subst hb0; simp [T_zero_right]
              · by_cases hb2 : b = 2 * sbar
                · subst hb2
                  have h1 : T (p * sbar) (p * (2 * sbar)) = 1 := by
                    rw [show p * (2 * sbar) = 2 * (p * sbar) by ring]; exact T_two_mul_self _
                  have h2 : T sbar (2 * sbar) = 1 := T_two_mul_self _
                  rw [h1, h2, sub_self, mul_zero]; exact dvd_zero _
                · have hblt : b < 2 * sbar := by omega
                  have hbpos : 0 < b := by omega
                  have hnot_pK : ¬ p ^ K ∣ (j - b) := by
                    intro hdiv
                    have hmod_eq : j % p ^ K = b % p ^ K := by
                      have h1 : j = (j - b) + b := by omega
                      rw [h1, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv, zero_add, Nat.mod_mod]
                    rw [Nat.mod_eq_of_lt (by omega : b < p ^ K)] at hmod_eq
                    omega
                  have hjb_pos : 0 < j - b := by
                    by_contra h0; have : j - b = 0 := by omega
                    rw [this] at hnot_pK; exact hnot_pK (dvd_zero _)
                  set db := vp p (j - b)
                  have hdb_lt : db < K := by
                    by_contra hge
                    exact hnot_pK (dvd_trans (Nat.pow_dvd_pow p (by omega)) (vp_dvd hp (by omega)))
                  have hdT : (p : ℤ) ^ (K - db) ∣ (T (q * p ^ K) (j - b) : ℤ) := by
                    exact_mod_cast T_dvd_of_pow_dvd (K := K) hp (dvd_mul_left _ q) hjb_pos
                  by_cases hdb_e : db ≤ e
                  · have hbase := base_trinom_supercong (e := e) (s' := sbar) (j := b)
                      hp hp5 hsbar_pos he_sbar_dvd
                    have hprod := mul_dvd_mul hdT hbase
                    rw [← pow_add] at hprod
                    exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hprod
                  · -- e < db < K: apply strong IH at db < K
                    have hvp_sbar : vp p sbar = e := by
                      apply le_antisymm
                      · by_contra hgt
                        have hd_sbar : p ^ (e + 1) ∣ sbar :=
                          dvd_trans (Nat.pow_dvd_pow p (by omega)) (vp_dvd hp (by omega))
                        have hd_q : p ^ (e + 1) ∣ q * p ^ K :=
                          dvd_mul_of_dvd_right (Nat.pow_dvd_pow p (by omega)) q
                        have hd_s' : p ^ (e + 1) ∣ s' := by rw [hs'eq]; exact dvd_add hd_q hd_sbar
                        have := vp_le_of_dvd hp (by omega) hd_s'
                        omega
                      · exact vp_le_of_dvd hp (by omega) he_sbar_dvd
                    have hih := ih db hdb_lt sbar b hsbar_pos hb_le
                    have hmin_db : min (vp p sbar) db = e := by rw [hvp_sbar]; omega
                    have hmiss_eq : missK db p sbar b =
                        ((Ico (e + 1) (db + 1)).filter fun t =>
                          2 * (s' % p ^ t) < p ^ t ∧ (j % p ^ t = 0 ∨ 2 * (s' % p ^ t) ≤ j % p ^ t)).card := by
                      unfold missK
                      rw [hmin_db]
                      congr 1
                      refine Finset.filter_congr fun t ht => ?_
                      rw [mem_Ico] at ht
                      have hsmod : sbar % p ^ t = s' % p ^ t := by
                        have hpt : p ^ t ∣ p ^ K := Nat.pow_dvd_pow p (by omega)
                        simp only [sbar, Nat.mod_mod_of_dvd s' hpt]
                      have hbmod : b % p ^ t = j % p ^ t := by
                        have hpt_jb : p ^ t ∣ (j - b) :=
                          dvd_trans (Nat.pow_dvd_pow p (by omega)) (vp_dvd hp (by omega))
                        have hj1 : j = (j - b) + b := by omega
                        conv_rhs => rw [hj1]
                        rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hpt_jb, zero_add, Nat.mod_mod]
                      rw [hsmod, hbmod]
                    have hmiss_split : missK K p s' j ≤ missK db p sbar b + (K - db) := by
                      rw [hmiss_eq]
                      unfold missK
                      have he_eq : min (vp p s') K = e := rfl
                      rw [he_eq]
                      have hunion : Ico (e + 1) (K + 1) = Ico (e + 1) (db + 1) ∪ Ico (db + 1) (K + 1) :=
                        (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
                      rw [hunion, Finset.filter_union]
                      calc _ ≤ ((Ico (e + 1) (db + 1)).filter _).card + ((Ico (db + 1) (K + 1)).filter _).card :=
                              Finset.card_union_le _ _
                        _ ≤ ((Ico (e + 1) (db + 1)).filter _).card + (Ico (db + 1) (K + 1)).card :=
                              Nat.add_le_add_left (Finset.card_filter_le _ _) _
                        _ = _ := by simp
                    rw [hmin_db] at hih
                    have hprod := mul_dvd_mul hdT hih
                    rw [← pow_add] at hprod
                    exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hprod
            · exact dvd_zero _
      · -- Inactive level K: missK K = missK (K - 1), apply IH at K - 1
        have hmiss_eq : missK K p s' j = missK (K - 1) p s' j := by
          unfold missK
          rw [he_prev, show min (vp p s') K = e by rfl]
          have hIco : Ico (e + 1) (K + 1) = insert K (Ico (e + 1) K) := by
            ext t; simp only [mem_Ico, mem_insert]; omega
          rw [hIco, show K - 1 + 1 = K by omega, Finset.filter_insert]
          simp [hKcond]
        have hih := ih (K - 1) (by omega) s' j hs' hj
        rw [hmiss_eq]
        rwa [he_prev] at hih

private lemma piece_3a_dvd {p n k s' m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hk : 0 < k) (hs'lt : s' < n * p ^ (k - 1))
    (hm_nd : ¬ p ∣ m) (hm_le : m ≤ p * (n * p ^ (k - 1))) :
    (p : ℤ) ^ (2 * k) ∣
      (((n * p ^ (k - 1)).choose s' : ℤ) * (f (p * s') : ℤ) *
        ((2 * (p * (n * p ^ (k - 1)) - p * s')).choose (p * (n * p ^ (k - 1)) - m) : ℤ) *
        (T (p * s') m : ℤ)) := by
  set A := n * p ^ (k - 1)
  set d := A - s'
  set w := p * A - m
  have hAk : p ^ (k - 1) ∣ A := dvd_mul_left _ n
  have h2pd : 2 * (p * A - p * s') = 2 * p * d := by
    have : p * A - p * s' = p * d := by simp only [d]; rw [Nat.mul_sub]
    rw [this]; ring
  rw [h2pd]
  by_cases hw : w ≤ 2 * p * d
  · have hA_ne : A.choose s' ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hf_ne : f (p * s') ≠ 0 := (Nat.choose_pos (by omega : p * s' ≤ 2 * (p * s'))).ne'
    have hC_ne : (2 * p * d).choose w ≠ 0 := (Nat.choose_pos hw).ne'
    have hprod_ne : A.choose s' * f (p * s') * (2 * p * d).choose w ≠ 0 := by positivity
    have hdT : p ^ tauP p (k + 1) (p * s') m ∣ T (p * s') m := T_dvd_tauP hp
    have hd_all : p ^ (vp p (A.choose s' * f (p * s') * (2 * p * d).choose w) +
        tauP p (k + 1) (p * s') m) ∣
        A.choose s' * f (p * s') * (2 * p * d).choose w * T (p * s') m := by
      rw [pow_add]; exact mul_dvd_mul (vp_dvd hp hprod_ne) hdT
    have hexp : 2 * k ≤ vp p (A.choose s' * f (p * s') * (2 * p * d).choose w) +
        tauP p (k + 1) (p * s') m := by
      rw [vp_mul_eq (Nat.mul_ne_zero hA_ne hf_ne) hC_ne, vp_mul_eq hA_ne hf_ne]
      have h1 := vp_choose_ge_carry (p := p) (n := A) (a := s') (B0 := k) hp (by omega)
      have h2 := le_trans (vp_f_ge_carry (p := p) (m := s') (B0 := k) hp) (vp_f_mul_p_ge (m := s') hp hp5)
      have h3 := vp_choose_ge_carry (p := p) (n := 2 * p * d) (a := w) (B0 := k + 1) hp hw
      have h4 : tauP p (k + 1) (p * s') m = ∑ t ∈ Ico 1 (k + 1),
          if 2 * ((p * s') % p ^ t) < p ^ t ∧ 2 * ((p * s') % p ^ t) < m % p ^ t then 1 else 0 := by
        unfold tauP; rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
      have hsplit3 : ∑ t ∈ Ico 1 (k + 1), (if (2 * p * d) % p ^ t < w % p ^ t then 1 else 0) =
          (if (2 * p * d) % p < w % p then 1 else 0) +
          ∑ t' ∈ Ico 1 k, (if (2 * p * d) % p ^ (t' + 1) < w % p ^ (t' + 1) then 1 else 0) := by
        have hIco : Ico 1 (k + 1) = insert 1 (Ico 2 (k + 1)) := by
          ext x; simp only [mem_Ico, mem_insert]; omega
        rw [hIco, Finset.sum_insert (by simp), pow_one]
        congr 1
        refine Finset.sum_bij (fun t _ => t - 1) ?_ ?_ ?_ ?_
        · intro t ht; rw [mem_Ico] at ht ⊢; omega
        · intro t₁ ht₁ t₂ ht₂ heq; rw [mem_Ico] at ht₁ ht₂; omega
        · intro t' ht'; rw [mem_Ico] at ht'; exact ⟨t' + 1, by rw [mem_Ico]; omega, by omega⟩
        · intro t ht; rw [mem_Ico] at ht; rw [show t - 1 + 1 = t by omega]
      have hsplit4 : ∑ t ∈ Ico 1 (k + 1),
          (if 2 * ((p * s') % p ^ t) < p ^ t ∧ 2 * ((p * s') % p ^ t) < m % p ^ t then 1 else 0) =
          (if 2 * ((p * s') % p) < p ∧ 2 * ((p * s') % p) < m % p then 1 else 0) +
          ∑ t' ∈ Ico 1 k,
            (if 2 * ((p * s') % p ^ (t' + 1)) < p ^ (t' + 1) ∧
                2 * ((p * s') % p ^ (t' + 1)) < m % p ^ (t' + 1) then 1 else 0) := by
        have hIco : Ico 1 (k + 1) = insert 1 (Ico 2 (k + 1)) := by
          ext x; simp only [mem_Ico, mem_insert]; omega
        rw [hIco, Finset.sum_insert (by simp), pow_one]
        congr 1
        refine Finset.sum_bij (fun t _ => t - 1) ?_ ?_ ?_ ?_
        · intro t ht; rw [mem_Ico] at ht ⊢; omega
        · intro t₁ ht₁ t₂ ht₂ heq; rw [mem_Ico] at ht₁ ht₂; omega
        · intro t' ht'; rw [mem_Ico] at ht'; exact ⟨t' + 1, by rw [mem_Ico]; omega, by omega⟩
        · intro t ht; rw [mem_Ico] at ht; rw [show t - 1 + 1 = t by omega]
      have ht1_a : (if (2 * p * d) % p < w % p then 1 else 0) = 1 := by
        have h2p0 : (2 * p * d) % p = 0 := Nat.mod_eq_zero_of_dvd ⟨2 * d, by ring⟩
        have hwpos : 0 < w % p := by
          by_contra h0
          have hdvd : p ∣ w := Nat.dvd_of_mod_eq_zero (Nat.eq_zero_of_not_pos h0)
          apply hm_nd
          have hsum : p ∣ w + m := by simp only [w]; rw [Nat.sub_add_cancel hm_le]; exact dvd_mul_right p A
          exact (Nat.dvd_add_right hdvd).mp hsum
        simp [h2p0, hwpos]
      have ht1_b : (if 2 * ((p * s') % p) < p ∧ 2 * ((p * s') % p) < m % p then 1 else 0) = 1 := by
        have hps0 : (p * s') % p = 0 := Nat.mul_mod_right p s'
        have hmpos : 0 < m % p := by
          by_contra h0; exact hm_nd (Nat.dvd_of_mod_eq_zero (Nat.eq_zero_of_not_pos h0))
        simp [hps0, hp.pos, hmpos]
      have hpair_ge : 2 * (k - 1) ≤
          ∑ t' ∈ Ico 1 k,
            ((if A % p ^ t' < s' % p ^ t' then 1 else 0) +
             (if p ^ t' ≤ 2 * (s' % p ^ t') then 1 else 0) +
             (if (2 * p * d) % p ^ (t' + 1) < w % p ^ (t' + 1) then 1 else 0) +
             (if 2 * ((p * s') % p ^ (t' + 1)) < p ^ (t' + 1) ∧
                 2 * ((p * s') % p ^ (t' + 1)) < m % p ^ (t' + 1) then 1 else 0)) := by
        calc 2 * (k - 1) = ∑ _t' ∈ Ico 1 k, 2 := by simp [mul_comm]
          _ ≤ _ := by
              refine Finset.sum_le_sum fun t' ht' => ?_
              rw [mem_Ico] at ht'
              have hptA : p ^ t' ∣ A := dvd_trans (Nat.pow_dvd_pow p (by omega)) hAk
              have hAmod : A % p ^ t' = 0 := Nat.mod_eq_zero_of_dvd hptA
              have hpt1pA : p ^ (t' + 1) ∣ p * A := by
                rw [pow_succ, mul_comm (p ^ t') p]; exact Nat.mul_dvd_mul_left p hptA
              have hps_mod : (p * s') % p ^ (t' + 1) = p * (s' % p ^ t') := by
                rw [pow_succ, mul_comm (p ^ t') p, Nat.mul_mod_mul_left]
              have hpt_pos : 0 < p ^ t' := Nat.pow_pos hp.pos
              have hpt1_pos : 0 < p ^ (t' + 1) := Nat.pow_pos hp.pos
              have hm_pos : 0 < m % p ^ (t' + 1) := by
                by_contra h0
                have hdiv : p ^ (t' + 1) ∣ m := Nat.dvd_of_mod_eq_zero (Nat.eq_zero_of_not_pos h0)
                exact hm_nd (dvd_trans (dvd_pow_self p (by omega)) hdiv)
              have hw_pos : 0 < w % p ^ (t' + 1) := by
                rw [sub_mod_of_dvd hpt1_pos hpt1pA hm_le hm_pos]
                have := Nat.mod_lt m hpt1_pos; omega
              set sbar := s' % p ^ t'
              set mbar := m % p ^ (t' + 1)
              by_cases hs0 : sbar = 0
              · have hpt_s' : p ^ t' ∣ s' := Nat.dvd_of_mod_eq_zero hs0
                have hpt_d : p ^ t' ∣ d := Nat.dvd_sub hptA hpt_s'
                have h2pd0 : (2 * p * d) % p ^ (t' + 1) = 0 := by
                  apply Nat.mod_eq_zero_of_dvd
                  rw [pow_succ, mul_comm (p ^ t') p, show 2 * p * d = p * (2 * d) by ring]
                  exact Nat.mul_dvd_mul_left p (dvd_mul_of_dvd_right hpt_d 2)
                simp [h2pd0, hw_pos, hps_mod, hs0, hpt1_pos, hm_pos]
              · by_cases h2s : p ^ t' ≤ 2 * sbar
                · have hspos : 0 < sbar := by omega
                  simp [hAmod, hspos, h2s]; omega
                · have hspos : 0 < sbar := by omega
                  have h2ps_lt : 2 * (p * sbar) < p ^ (t' + 1) := by
                    rw [pow_succ, mul_comm (p ^ t') p, ← mul_assoc, mul_comm 2 p, mul_assoc]
                    exact Nat.mul_lt_mul_of_pos_left (by omega : 2 * sbar < p ^ t') hp.pos
                  by_cases hmb : 2 * (p * sbar) < mbar
                  · simp [hAmod, hspos, hps_mod, h2ps_lt, hmb]; omega
                  · have hne_m : mbar ≠ 2 * (p * sbar) := by
                      intro heq
                      apply hm_nd
                      have h1 : p ∣ mbar := by rw [heq]; exact ⟨2 * sbar, by ring⟩
                      have h2 : p ∣ p ^ (t' + 1) * (m / p ^ (t' + 1)) :=
                        dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _
                      have h3 := dvd_add h2 h1
                      rwa [Nat.div_add_mod] at h3
                    have hmb_lt : mbar < 2 * (p * sbar) := by omega
                    have hw_eq : w % p ^ (t' + 1) = p ^ (t' + 1) - mbar :=
                      sub_mod_of_dvd hpt1_pos hpt1pA hm_le hm_pos
                    have h2ps_mod : (2 * p * s') % p ^ (t' + 1) = 2 * (p * sbar) := by
                      have h1 : 2 * p * s' = p * (2 * s') := by ring
                      rw [h1, pow_succ, mul_comm (p ^ t') p, Nat.mul_mod_mul_left]
                      have h2 : (2 * s') % p ^ t' = 2 * sbar := by
                        rw [two_mul_mod_eq, Nat.mod_eq_of_lt (by omega)]
                      rw [h2]; ring
                    have h2pd_eq : (2 * p * d) % p ^ (t' + 1) = p ^ (t' + 1) - 2 * (p * sbar) := by
                      have hsub : 2 * p * d = 2 * (p * A) - 2 * p * s' := by simp only [d]; rw [Nat.mul_sub]; ring
                      have hle_2ps : 2 * p * s' ≤ 2 * (p * A) := by
                        rw [mul_assoc]
                        exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left p (by omega))
                      have hpos_2ps : 0 < (2 * p * s') % p ^ (t' + 1) := by
                        rw [h2ps_mod]
                        exact Nat.mul_pos (by decide) (Nat.mul_pos hp.pos hspos)
                      rw [hsub]
                      have h1 := sub_mod_of_dvd hpt1_pos (dvd_mul_of_dvd_right hpt1pA 2)
                        hle_2ps hpos_2ps
                      rwa [h2ps_mod] at h1
                    have hlt_w : (2 * p * d) % p ^ (t' + 1) < w % p ^ (t' + 1) := by
                      rw [h2pd_eq, hw_eq]; omega
                    simp [hAmod, hspos, hlt_w]; omega
      rw [h4, hsplit4]
      rw [hsplit3] at h3
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hpair_ge
      omega
    have hd_nat : p ^ (2 * k) ∣ A.choose s' * f (p * s') * (2 * p * d).choose w * T (p * s') m :=
      dvd_trans (Nat.pow_dvd_pow p hexp) hd_all
    exact_mod_cast hd_nat
  · have hz : (2 * p * d).choose w = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz]; simp

private lemma piece_3b_dvd {p n k s' j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hk : 0 < k) (hs'lt : s' < n * p ^ (k - 1)) (hjA : j ≤ n * p ^ (k - 1)) :
    (p : ℤ) ^ (2 * k) ∣
      (((n * p ^ (k - 1)).choose s' : ℤ) * (f (p * s') : ℤ) *
        (((2 * (p * (n * p ^ (k - 1)) - p * s')).choose (p * (n * p ^ (k - 1)) - p * j) : ℤ) -
          ((2 * (n * p ^ (k - 1) - s')).choose (n * p ^ (k - 1) - j) : ℤ)) *
        (T (p * s') (p * j) : ℤ)) := by
  set A := n * p ^ (k - 1)
  set d := A - s'
  set u := A - j
  have hAk : p ^ (k - 1) ∣ A := dvd_mul_left _ n
  have h2pd : 2 * (p * A - p * s') = p * (2 * d) := by
    have : p * A - p * s' = p * d := by simp only [d]; rw [Nat.mul_sub]
    rw [this]; ring
  have hpu : p * A - p * j = p * u := by simp only [u]; rw [Nat.mul_sub]
  rw [h2pd, hpu]
  by_cases hu0 : u = 0
  · simp [hu0]
  · by_cases hu2d : 2 * d ≤ u
    · by_cases heq : u = 2 * d
      · simp [heq]
      · have hlt : 2 * d < u := by omega
        have hplt : p * (2 * d) < p * u := Nat.mul_lt_mul_of_pos_left hlt hp.pos
        simp [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt hplt]
    · have hu1 : 1 ≤ u := by omega
      have hult : u < 2 * d := by omega
      have hkaz := choose_mul_p_sub_dvd (m := 2 * d) (b := u) hp hp5 hu1 hult
      have hA_ne : A.choose s' ≠ 0 := (Nat.choose_pos (by omega)).ne'
      have hf_ne : f (p * s') ≠ 0 := (Nat.choose_pos (by omega : p * s' ≤ 2 * (p * s'))).ne'
      have hAf_ne : A.choose s' * f (p * s') ≠ 0 := Nat.mul_ne_zero hA_ne hf_ne
      have hdAf : (p : ℤ) ^ vp p (A.choose s' * f (p * s')) ∣ ((A.choose s' : ℤ) * (f (p * s') : ℤ)) := by
        exact_mod_cast vp_dvd hp hAf_ne
      have hdT : (p : ℤ) ^ tauP p (k + 1) (p * s') (p * j) ∣ (T (p * s') (p * j) : ℤ) := by
        exact_mod_cast T_dvd_tauP (L := k + 1) hp
      have hmul := mul_dvd_mul (mul_dvd_mul hdAf hkaz) hdT
      rw [← pow_add, ← pow_add] at hmul
      refine dvd_trans (pow_dvd_pow (p : ℤ) ?_) hmul
      rw [vp_mul_eq hA_ne hf_ne]
      have h1 := vp_choose_ge_carry (p := p) (n := A) (a := s') (B0 := k) hp (by omega)
      have h2 := le_trans (vp_f_ge_carry (p := p) (m := s') (B0 := k) hp) (vp_f_mul_p_ge (m := s') hp hp5)
      have h3 := vp_ge_card_dvd (p := p) (X := u) (K := k) hp hu0
      have h4 := vp_ge_card_dvd (p := p) (X := 2 * d - u) (K := k) hp (by omega)
      have h5 := vp_ge_card_dvd (p := p) (X := 2 * d) (K := k) hp (by omega)
      have h6 := vp_choose_ge_carry (p := p) (n := 2 * d) (a := u) (B0 := k) hp (by omega)
      have h7 : ∑ t ∈ Ico 1 k,
          (if 2 * ((p * s') % p ^ (t + 1)) < p ^ (t + 1) ∧
              2 * ((p * s') % p ^ (t + 1)) < (p * j) % p ^ (t + 1) then 1 else 0) ≤
          tauP p (k + 1) (p * s') (p * j) := by
        unfold tauP
        have heq : ∑ t ∈ Ico 1 k,
            (if 2 * ((p * s') % p ^ (t + 1)) < p ^ (t + 1) ∧
                2 * ((p * s') % p ^ (t + 1)) < (p * j) % p ^ (t + 1) then 1 else 0) =
            ∑ t ∈ Ico 2 (k + 1),
              (if 2 * ((p * s') % p ^ t) < p ^ t ∧ 2 * ((p * s') % p ^ t) < (p * j) % p ^ t then 1 else 0) := by
          refine Finset.sum_bij (fun t _ => t + 1) ?_ ?_ ?_ ?_
          · intro t ht; rw [mem_Ico] at ht ⊢; omega
          · intro t₁ _ t₂ _ heq; omega
          · intro t ht; rw [mem_Ico] at ht; exact ⟨t - 1, by rw [mem_Ico]; omega, by omega⟩
          · intro _ _; rfl
        rw [heq, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
        exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Ico_subset_Ico_left (by omega)))
      have hpair_ge : 2 * (k - 1) ≤
          ∑ t ∈ Ico 1 k,
            ((if A % p ^ t < s' % p ^ t then 1 else 0) +
             (if p ^ t ≤ 2 * (s' % p ^ t) then 1 else 0) +
             (if p ^ t ∣ u then 1 else 0) +
             (if p ^ t ∣ 2 * d - u then 1 else 0) +
             (if p ^ t ∣ 2 * d then 1 else 0) +
             (if (2 * d) % p ^ t < u % p ^ t then 1 else 0) +
             (if 2 * ((p * s') % p ^ (t + 1)) < p ^ (t + 1) ∧
                 2 * ((p * s') % p ^ (t + 1)) < (p * j) % p ^ (t + 1) then 1 else 0)) := by
        calc 2 * (k - 1) = ∑ _t ∈ Ico 1 k, 2 := by simp [mul_comm]
          _ ≤ _ := by
              refine Finset.sum_le_sum fun t ht => ?_
              rw [mem_Ico] at ht
              have hptA : p ^ t ∣ A := dvd_trans (Nat.pow_dvd_pow p (by omega)) hAk
              have hAmod : A % p ^ t = 0 := Nat.mod_eq_zero_of_dvd hptA
              have hpt_pos : 0 < p ^ t := Nat.pow_pos hp.pos
              set sbar := s' % p ^ t
              set jbar := j % p ^ t
              by_cases hs0 : sbar = 0
              · have hpt_s' : p ^ t ∣ s' := Nat.dvd_of_mod_eq_zero hs0
                have hpt_2d : p ^ t ∣ 2 * d := dvd_mul_of_dvd_right (Nat.dvd_sub hptA hpt_s') 2
                have h2d0 : (2 * d) % p ^ t = 0 := Nat.mod_eq_zero_of_dvd hpt_2d
                by_cases hpu_dvd : p ^ t ∣ u
                · simp [hpt_2d, hpu_dvd]; omega
                · have hupos : 0 < u % p ^ t := by
                    by_contra h0; exact hpu_dvd (Nat.dvd_of_mod_eq_zero (Nat.eq_zero_of_not_pos h0))
                  simp [hpt_2d, h2d0, hupos]; omega
              · by_cases h2s : p ^ t ≤ 2 * sbar
                · have hspos : 0 < sbar := by omega
                  simp [hAmod, hspos, h2s]; omega
                · have hspos : 0 < sbar := by omega
                  by_cases hj0 : jbar = 0
                  · have hpt_j : p ^ t ∣ j := Nat.dvd_of_mod_eq_zero hj0
                    have hpt_u : p ^ t ∣ u := Nat.dvd_sub hptA hpt_j
                    simp [hAmod, hspos, hpt_u]; omega
                  · by_cases hj_lt : jbar < 2 * sbar
                    · have hjpos : 0 < jbar := Nat.pos_of_ne_zero hj0
                      have hu_eq : u % p ^ t = p ^ t - jbar := sub_mod_of_dvd hpt_pos hptA hjA hjpos
                      have h2s_mod : (2 * s') % p ^ t = 2 * sbar := by
                        rw [two_mul_mod_eq, Nat.mod_eq_of_lt (by omega)]
                      have h2d_eq : (2 * d) % p ^ t = p ^ t - 2 * sbar := by
                        have hsub : 2 * d = 2 * A - 2 * s' := by simp only [d]; rw [Nat.mul_sub]
                        rw [hsub]
                        have h := sub_mod_of_dvd hpt_pos (dvd_mul_of_dvd_right hptA 2)
                          (by omega : 2 * s' ≤ 2 * A) (by rw [h2s_mod]; omega)
                        rwa [h2s_mod] at h
                      have hlt_u : (2 * d) % p ^ t < u % p ^ t := by rw [h2d_eq, hu_eq]; omega
                      simp [hAmod, hspos, hlt_u]; omega
                    · by_cases hj_eq : jbar = 2 * sbar
                      · have hpt_2du : p ^ t ∣ 2 * d - u := by
                          have h2s_mod : (2 * s') % p ^ t = 2 * sbar := by
                            rw [two_mul_mod_eq, Nat.mod_eq_of_lt (by omega)]
                          have hmod0 : (2 * d - u) % p ^ t = 0 := by
                            have heq : 2 * d - u + 2 * s' = A + j := by omega
                            have h1 : (2 * d - u + 2 * s') % p ^ t = (A + j) % p ^ t := congrArg (· % p ^ t) heq
                            rw [Nat.add_mod (2 * d - u), Nat.add_mod A, hAmod, zero_add, Nat.mod_mod, h2s_mod] at h1
                            have hlt1 : (2 * d - u) % p ^ t < p ^ t := Nat.mod_lt _ hpt_pos
                            by_contra hne
                            by_cases hsum : (2 * d - u) % p ^ t + 2 * sbar < p ^ t
                            · rw [Nat.mod_eq_of_lt hsum] at h1; omega
                            · have hrem : ((2 * d - u) % p ^ t + 2 * sbar) % p ^ t =
                                  (2 * d - u) % p ^ t + 2 * sbar - p ^ t := by
                                have : (2 * d - u) % p ^ t + 2 * sbar =
                                    p ^ t + ((2 * d - u) % p ^ t + 2 * sbar - p ^ t) := by omega
                                conv_lhs => rw [this]
                                rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
                              rw [hrem] at h1; omega
                          exact Nat.dvd_of_mod_eq_zero hmod0
                        simp [hAmod, hspos, hpt_2du]; omega
                      · have hj_gt : 2 * sbar < jbar := by omega
                        have hps_mod : (p * s') % p ^ (t + 1) = p * sbar := by
                          rw [pow_succ, mul_comm (p ^ t) p, Nat.mul_mod_mul_left]
                        have hpj_mod : (p * j) % p ^ (t + 1) = p * jbar := by
                          rw [pow_succ, mul_comm (p ^ t) p, Nat.mul_mod_mul_left]
                        have hcond1 : 2 * (p * sbar) < p ^ (t + 1) := by
                          rw [pow_succ, mul_comm (p ^ t) p, ← mul_assoc, mul_comm 2 p, mul_assoc]
                          exact Nat.mul_lt_mul_of_pos_left (by omega : 2 * sbar < p ^ t) hp.pos
                        have hcond2 : 2 * (p * sbar) < p * jbar := by
                          rw [← mul_assoc, mul_comm 2 p, mul_assoc]
                          exact Nat.mul_lt_mul_of_pos_left hj_gt hp.pos
                        simp [hAmod, hspos, hps_mod, hpj_mod, hcond1, hcond2]; omega
      repeat rw [Finset.sum_add_distrib] at hpair_ge
      omega

private lemma piece_3c_dvd {p n k s' j : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hk : 0 < k) (hs'1 : 1 ≤ s') (hs'lt : s' < n * p ^ (k - 1))
    (hj2s : j ≤ 2 * s') (hjA : j ≤ n * p ^ (k - 1)) :
    (p : ℤ) ^ (2 * k) ∣
      (((n * p ^ (k - 1)).choose s' : ℤ) * (f (p * s') : ℤ) *
        ((2 * (n * p ^ (k - 1) - s')).choose (n * p ^ (k - 1) - j) : ℤ) *
        ((T (p * s') (p * j) : ℤ) - (T s' j : ℤ))) := by
  set A := n * p ^ (k - 1)
  set d := A - s'
  set u := A - j
  have hAk : p ^ (k - 1) ∣ A := dvd_mul_left _ n
  by_cases hu : u ≤ 2 * d
  · set e := min (vp p s') (k - 1)
    have hA_ne : A.choose s' ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hf_ne : f (p * s') ≠ 0 := (Nat.choose_pos (by omega : p * s' ≤ 2 * (p * s'))).ne'
    have hC_ne : (2 * d).choose u ≠ 0 := (Nat.choose_pos hu).ne'
    have hprod_ne : A.choose s' * f (p * s') * (2 * d).choose u ≠ 0 := by positivity
    have hd_pref : (p : ℤ) ^ vp p (A.choose s' * f (p * s') * (2 * d).choose u) ∣
        ((A.choose s' : ℤ) * (f (p * s') : ℤ) * ((2 * d).choose u : ℤ)) := by
      exact_mod_cast vp_dvd hp hprod_ne
    have hd_T := enhanced_trinom_supercong hp hp5 (k - 1) s' j hs'1 hj2s
    simp only [show min (vp p s') (k - 1) = e from rfl] at hd_T
    have hmul := mul_dvd_mul hd_pref hd_T
    rw [← pow_add] at hmul
    refine dvd_trans (pow_dvd_pow (p : ℤ) ?_) hmul
    rw [vp_mul_eq (Nat.mul_ne_zero hA_ne hf_ne) hC_ne, vp_mul_eq hA_ne hf_ne]
    have h1 := vp_choose_ge_carry (p := p) (n := A) (a := s') (B0 := k) hp (by omega)
    have h2 := le_trans (vp_f_ge_carry (p := p) (m := s') (B0 := k) hp) (vp_f_mul_p_ge (m := s') hp hp5)
    have h3 := vp_choose_ge_carry (p := p) (n := 2 * d) (a := u) (B0 := k) hp hu
    have hsub_Ico : Ico (e + 1) k ⊆ Ico 1 k := Finset.Ico_subset_Ico_left (by omega)
    have h1' := le_trans (Finset.sum_le_sum_of_subset hsub_Ico) h1
    have h2' := le_trans (Finset.sum_le_sum_of_subset hsub_Ico) h2
    have h3' := le_trans (Finset.sum_le_sum_of_subset hsub_Ico) h3
    have hmiss_sum : missK (k - 1) p s' j = ∑ t ∈ Ico (e + 1) k,
        if 2 * (s' % p ^ t) < p ^ t ∧ (j % p ^ t = 0 ∨ 2 * (s' % p ^ t) ≤ j % p ^ t) then 1 else 0 := by
      unfold missK
      rw [show min (vp p s') (k - 1) = e from rfl, show k - 1 + 1 = k by omega,
        ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    have hlevel : 2 * (k - 1 - e) ≤
        ∑ t ∈ Ico (e + 1) k,
          ((if A % p ^ t < s' % p ^ t then 1 else 0) +
           (if p ^ t ≤ 2 * (s' % p ^ t) then 1 else 0) +
           (if (2 * d) % p ^ t < u % p ^ t then 1 else 0) +
           (if 2 * (s' % p ^ t) < p ^ t ∧ (j % p ^ t = 0 ∨ 2 * (s' % p ^ t) ≤ j % p ^ t) then 1 else 0)) := by
      calc 2 * (k - 1 - e) = ∑ _t ∈ Ico (e + 1) k, 2 := by
            simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul]; omega
        _ ≤ _ := by
            refine Finset.sum_le_sum fun t ht => ?_
            rw [mem_Ico] at ht
            have hptA : p ^ t ∣ A := dvd_trans (Nat.pow_dvd_pow p (by omega)) hAk
            have hAmod : A % p ^ t = 0 := Nat.mod_eq_zero_of_dvd hptA
            have hpt_pos : 0 < p ^ t := Nat.pow_pos hp.pos
            have hspos : 0 < s' % p ^ t := by
              by_contra h0
              have hdvd : p ^ t ∣ s' := Nat.dvd_of_mod_eq_zero (Nat.eq_zero_of_not_pos h0)
              have hle := vp_le_of_dvd hp (by omega) hdvd
              omega
            set sbar := s' % p ^ t
            set jbar := j % p ^ t
            by_cases h2s : p ^ t ≤ 2 * sbar
            · simp [hAmod, hspos, h2s]; omega
            · have h2slt : 2 * sbar < p ^ t := by omega
              by_cases hmcond : jbar = 0 ∨ 2 * sbar ≤ jbar
              · simp [hAmod, hspos, h2slt, hmcond]; omega
              · have hjpos : 0 < jbar := Nat.pos_of_ne_zero (fun h => hmcond (Or.inl h))
                have hjlt : jbar < 2 * sbar := by omega
                have hu_eq : u % p ^ t = p ^ t - jbar := sub_mod_of_dvd hpt_pos hptA hjA hjpos
                have h2s_mod : (2 * s') % p ^ t = 2 * sbar := by
                  rw [two_mul_mod_eq, Nat.mod_eq_of_lt h2slt]
                have h2d_eq : (2 * d) % p ^ t = p ^ t - 2 * sbar := by
                  have hsub : 2 * d = 2 * A - 2 * s' := by simp only [d]; rw [Nat.mul_sub]
                  rw [hsub]
                  have h := sub_mod_of_dvd hpt_pos (dvd_mul_of_dvd_right hptA 2)
                    (by omega : 2 * s' ≤ 2 * A) (by rw [h2s_mod]; omega)
                  rwa [h2s_mod] at h
                have hlt_u : (2 * d) % p ^ t < u % p ^ t := by rw [h2d_eq, hu_eq]; omega
                simp [hAmod, hspos, hlt_u]; omega
    repeat rw [Finset.sum_add_distrib] at hlevel
    rw [← hmiss_sum] at hlevel
    omega
  · have hz : (2 * d).choose u = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz]; simp

private lemma piece_3_dvd {p n k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hk : 0 < k) :
    (p : ℤ) ^ (2 * k) ∣
      2 * ∑ s' ∈ range (n * p ^ (k - 1) + 1),
        (-1 : ℤ) ^ (n * p ^ (k - 1) - s') * ((n * p ^ (k - 1)).choose s' : ℤ) *
          (f (p * s') : ℤ) * (B (p * (n * p ^ (k - 1))) (p * s') - B (n * p ^ (k - 1)) s') := by
  set A := n * p ^ (k - 1)
  have hA1 : 1 ≤ A := Nat.mul_pos hn (Nat.pow_pos hp.pos)
  have hAk : p ^ (k - 1) ∣ A := dvd_mul_left _ n
  refine dvd_mul_of_dvd_right (Finset.dvd_sum fun s' hs' => ?_) 2
  have hs'A : s' ≤ A := by rw [mem_range] at hs'; omega
  have hre : (-1 : ℤ) ^ (A - s') * (A.choose s' : ℤ) * (f (p * s') : ℤ) *
      (B (p * A) (p * s') - B A s') =
      (-1 : ℤ) ^ (A - s') * ((A.choose s' : ℤ) * (f (p * s') : ℤ) *
        (B (p * A) (p * s') - B A s')) := by ring
  rw [hre]
  refine dvd_mul_of_dvd_right ?_ _
  by_cases hs'0 : s' = 0
  · subst hs'0
    simp only [f, mul_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
    have hB0 : ∀ L : ℕ, B L 0 = (f L : ℤ) := fun L => by
      rw [B_eq_binom L 0 (Nat.zero_le L)]; simp
    rw [hB0 (p * A), hB0 A]
    have hf := f_mul_p_sub_dvd (m := A) hp hp5 hA1
    have hvpA : k - 1 ≤ vp p A := vp_le_of_dvd hp (by omega) hAk
    exact dvd_trans (pow_dvd_pow (p : ℤ) (by omega)) hf
  · by_cases hs'eq : s' = A
    · subst hs'eq
      have hBA : ∀ L : ℕ, B L L = (T L L : ℤ) := fun L => by
        rw [B_eq_trinom L L]
        have hmem : L ∈ range (2 * L + 1) := mem_range.mpr (by omega)
        rw [Finset.sum_eq_single L]
        · simp
        · intro m _ hne
          split_ifs with hle
          · rw [Nat.sub_self, mul_zero, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
          · rfl
        · intro h; exact absurd hmem h
      rw [hBA (p * A), hBA A]
      have hbase := base_trinom_supercong (e := k - 1) (s' := A) (j := A) hp hp5 hA1 hAk
      rw [show k - 1 + 1 = k by omega] at hbase
      exact dvd_mul_of_dvd_right hbase _
    · have hs'1 : 1 ≤ s' := by omega
      have hs'lt : s' < A := by omega
      rw [B_eq_trinom (p * A) (p * s'), B_eq_trinom A s']
      rw [show 2 * (p * s') = p * (2 * s') by ring,
        sum_range_p_mul_split p (2 * s') hp.pos]
      have hsplit :
          (A.choose s' : ℤ) * (f (p * s') : ℤ) *
            (((∑ j ∈ range (2 * s' + 1),
                if p * j ≤ p * A then ((2 * (p * A - p * s')).choose (p * A - p * j) : ℤ) * (T (p * s') (p * j) : ℤ) else 0) +
              (∑ m ∈ (range (p * (2 * s') + 1)).filter (fun m => ¬ p ∣ m),
                if m ≤ p * A then ((2 * (p * A - p * s')).choose (p * A - m) : ℤ) * (T (p * s') m : ℤ) else 0)) -
             (∑ j ∈ range (2 * s' + 1),
                if j ≤ A then ((2 * (A - s')).choose (A - j) : ℤ) * (T s' j : ℤ) else 0)) =
          (∑ m ∈ (range (p * (2 * s') + 1)).filter (fun m => ¬ p ∣ m),
            if m ≤ p * A then
              (A.choose s' : ℤ) * (f (p * s') : ℤ) *
                ((2 * (p * A - p * s')).choose (p * A - m) : ℤ) * (T (p * s') m : ℤ) else 0) +
          (∑ j ∈ range (2 * s' + 1),
            if j ≤ A then
              (A.choose s' : ℤ) * (f (p * s') : ℤ) *
                (((2 * (p * A - p * s')).choose (p * A - p * j) : ℤ) - ((2 * (A - s')).choose (A - j) : ℤ)) *
                (T (p * s') (p * j) : ℤ) else 0) +
          (∑ j ∈ range (2 * s' + 1),
            if j ≤ A then
              (A.choose s' : ℤ) * (f (p * s') : ℤ) *
                ((2 * (A - s')).choose (A - j) : ℤ) * ((T (p * s') (p * j) : ℤ) - (T s' j : ℤ)) else 0) := by
        have hiff : ∀ j : ℕ, p * j ≤ p * A ↔ j ≤ A := fun j => Nat.mul_le_mul_left_iff hp.pos
        simp_rw [hiff]
        rw [mul_sub, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        have h1 : ∑ m ∈ (range (p * (2 * s') + 1)).filter (fun m => ¬ p ∣ m),
            (A.choose s' : ℤ) * (f (p * s') : ℤ) *
              (if m ≤ p * A then ((2 * (p * A - p * s')).choose (p * A - m) : ℤ) * (T (p * s') m : ℤ) else 0) =
            ∑ m ∈ (range (p * (2 * s') + 1)).filter (fun m => ¬ p ∣ m),
              if m ≤ p * A then
                (A.choose s' : ℤ) * (f (p * s') : ℤ) *
                  ((2 * (p * A - p * s')).choose (p * A - m) : ℤ) * (T (p * s') m : ℤ) else 0 := by
          refine Finset.sum_congr rfl fun m _ => ?_
          split_ifs <;> ring
        have h2 : (∑ j ∈ range (2 * s' + 1),
              (A.choose s' : ℤ) * (f (p * s') : ℤ) *
                (if j ≤ A then ((2 * (p * A - p * s')).choose (p * A - p * j) : ℤ) * (T (p * s') (p * j) : ℤ) else 0)) -
            (∑ j ∈ range (2 * s' + 1),
              (A.choose s' : ℤ) * (f (p * s') : ℤ) *
                (if j ≤ A then ((2 * (A - s')).choose (A - j) : ℤ) * (T s' j : ℤ) else 0)) =
            (∑ j ∈ range (2 * s' + 1),
              if j ≤ A then
                (A.choose s' : ℤ) * (f (p * s') : ℤ) *
                  (((2 * (p * A - p * s')).choose (p * A - p * j) : ℤ) - ((2 * (A - s')).choose (A - j) : ℤ)) *
                  (T (p * s') (p * j) : ℤ) else 0) +
            (∑ j ∈ range (2 * s' + 1),
              if j ≤ A then
                (A.choose s' : ℤ) * (f (p * s') : ℤ) *
                  ((2 * (A - s')).choose (A - j) : ℤ) * ((T (p * s') (p * j) : ℤ) - (T s' j : ℤ)) else 0) := by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> ring
        rw [h1]
        linarith
      rw [hsplit]
      refine dvd_add (dvd_add ?_ ?_) ?_
      · refine Finset.dvd_sum fun m hm => ?_
        rw [mem_filter] at hm
        split_ifs with hmpA
        · exact piece_3a_dvd hp hp5 hk hs'lt hm.2 hmpA
        · exact dvd_zero _
      · refine Finset.dvd_sum fun j _ => ?_
        split_ifs with hjA
        · exact piece_3b_dvd hp hp5 hk hs'lt hjA
        · exact dvd_zero _
      · refine Finset.dvd_sum fun j hj => ?_
        have hj2s : j ≤ 2 * s' := by rw [mem_range] at hj; omega
        split_ifs with hjA
        · exact piece_3c_dvd hp hp5 hk hs'1 hs'lt hj2s hjA
        · exact dvd_zero _

-- ============================================================================
-- Block 5: Main Theorem
-- ============================================================================

theorem main_proof (p n k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 0 < n) (hk : 0 < k) :
    OMA.S_oeis_a094061.a (n * p ^ k) ≡ OMA.S_oeis_a094061.a (n * p ^ (k - 1)) [MOD p ^ (2 * k)] := by
  rw [← Int.natCast_modEq_iff]
  set A := n * p ^ (k - 1)
  have hNpA : n * p ^ k = p * A := by
    simp only [A]
    calc n * p ^ k = n * (p ^ (k - 1) * p) := by rw [← pow_succ, Nat.sub_add_cancel hk]
      _ = p * (n * p ^ (k - 1)) := by ring
  rw [hNpA]
  symm
  rw [Int.modEq_iff_dvd, a_sub_decomp p A hp hp5]
  exact dvd_add (dvd_add (dvd_add (dvd_add
    (piece_NN_dvd hp hk) (piece_1a_dvd hp hp5 hn))
    (piece_1b_dvd hp hp5 hn hk)) (piece_2_dvd hp hp5 hk)) (piece_3_dvd hp hp5 hn hk)

end OeisA094061

theorem OMA.solution : type_of% @OMA.S_oeis_a094061.main :=
  OeisA094061.main_proof
