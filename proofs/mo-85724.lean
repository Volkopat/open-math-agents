import OMAStatements.S_mo_85724

namespace Mo85724

open Matrix Subgroup

-- Computable arithmetic checks (decided directly by the kernel!)
private def checkDivs63 : Bool :=
  (List.range 64).all fun n =>
    if 63 % n == 0 && n > 0 then [1, 3, 7, 9, 21, 63].contains n else true

private lemma checkDivs63_true : checkDivs63 = true := by decide

private def checkDivs63or65 : Bool :=
  (List.range 66).all fun n =>
    if (63 % n == 0 || 65 % n == 0) && n >= 3 then [3, 7, 9, 21, 63, 5, 13, 65].contains n else true

private lemma checkDivs63or65_true : checkDivs63or65 = true := by decide

private lemma checkTwoOrbits_spec :
    ∀ a1 ∈ [2, 4, 8, 16, 32, 64],
    ∀ n1 ∈ [1, 3, 7, 9, 21, 63],
    ∀ a2 ∈ [3, 9, 21, 63],
    (a1 - 1) % n1 = 0 →
    let den := n1 * a1 * (2 * a2)
    let num := (a1 - 1) * (2 * a2) + (a2 - 1) * (n1 * a1)
    num < den →
    let gap := den - num
    den % gap = 0 →
    let K := den / gap
    K % 6 = 0 → 262080 % K = 0 → K % a1 = 0 → K % (2 * a1) ≠ 0 →
    a1 * n1 < K → K % (a1 * n1) = 0 → K % (2 * a2) = 0 →
    (K = 6 ∧ a2 = 3) ∨ (K = 18 ∧ a2 = 9) ∨ (K = 42 ∧ a2 = 21) ∨ (K = 126 ∧ a2 = 63) := by
  decide

private def l7LeB (i j : Fin 7) : Bool :=
  i == j || i == 0 || j == 6 || (i == 1 && j == 3) || (i == 2 && (j == 3 || j == 4))

private lemma l7Le_iff_B (i j : Fin 7) : OMA.S_mo_85724.l7Le i j ↔ l7LeB i j = true := by
  simp [OMA.S_mo_85724.l7Le, l7LeB, or_assoc]

private def fL7Card : Fin 7 → ℕ
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 42
  | ⟨2, _⟩ => 18
  | ⟨3, _⟩ => 126
  | ⟨4, _⟩ => 504
  | ⟨5, _⟩ => 60
  | ⟨6, _⟩ => 262080

private lemma l7LeB_dvd : ∀ i j : Fin 7, l7LeB i j = true → fL7Card i ∣ fL7Card j := by decide

private lemma l7_remaining_cases :
    ∀ i j : Fin 7, i ≠ j → i ≠ 0 → j ≠ 6 → fL7Card i ∣ fL7Card j →
      (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
  decide

private def ok3 (a1 n1 a2 a3 n3 : ℕ) : Bool :=
  let den := n1 * a1 * (2 * a2) * (n3 * a3)
  let num := (a1 - 1) * (2 * a2) * (n3 * a3) + (a2 - 1) * (n1 * a1) * (n3 * a3) +
             (a3 - 1) * (n1 * a1) * (2 * a2)
  let gap := den - num
  let K := den / gap
  if (a1 - 1) % n1 == 0 && decide (num < den) && den % gap == 0 &&
     K % 6 == 0 && 262080 % K == 0 && K % a1 == 0 && K % (2 * a1) != 0 &&
     decide (a1 * n1 < K) && K % (a1 * n1) == 0 && K % (2 * a2) == 0 && K % (n3 * a3) == 0 then
    (K == 60 && a2 == 3 && a3 == 5) || (K == 504 && a2 == 9 && a3 == 7) || K == 262080
  else true

private lemma ok3_all :
    ([2, 4, 8, 16, 32, 64].all fun a1 =>
     [1, 3, 7, 9, 21, 63].all fun n1 =>
     [3, 9, 21, 63].all fun a2 =>
     [3, 7, 9, 21, 63, 5, 13, 65].all fun a3 =>
     [1, 2].all fun n3 => ok3 a1 n1 a2 a3 n3) = true := by decide

private lemma checkThreeOrbits_spec
    (a1 : ℕ) (ha1 : a1 ∈ [2, 4, 8, 16, 32, 64])
    (n1 : ℕ) (hn1 : n1 ∈ [1, 3, 7, 9, 21, 63])
    (a2 : ℕ) (ha2 : a2 ∈ [3, 9, 21, 63])
    (a3 : ℕ) (ha3 : a3 ∈ [3, 7, 9, 21, 63, 5, 13, 65])
    (n3 : ℕ) (hn3 : n3 ∈ [1, 2])
    (hm1 : (a1 - 1) % n1 = 0)
    (hnum : (a1 - 1) * (2 * a2) * (n3 * a3) + (a2 - 1) * (n1 * a1) * (n3 * a3) +
            (a3 - 1) * (n1 * a1) * (2 * a2) < n1 * a1 * (2 * a2) * (n3 * a3))
    (hdiv : n1 * a1 * (2 * a2) * (n3 * a3) %
            (n1 * a1 * (2 * a2) * (n3 * a3) -
             ((a1 - 1) * (2 * a2) * (n3 * a3) + (a2 - 1) * (n1 * a1) * (n3 * a3) +
              (a3 - 1) * (n1 * a1) * (2 * a2))) = 0) :
    let den := n1 * a1 * (2 * a2) * (n3 * a3)
    let num := (a1 - 1) * (2 * a2) * (n3 * a3) + (a2 - 1) * (n1 * a1) * (n3 * a3) +
               (a3 - 1) * (n1 * a1) * (2 * a2)
    let K := den / (den - num)
    K % 6 = 0 → 262080 % K = 0 → K % a1 = 0 → K % (2 * a1) ≠ 0 →
    a1 * n1 < K → K % (a1 * n1) = 0 → K % (2 * a2) = 0 → K % (n3 * a3) = 0 →
    (K = 60 ∧ a2 = 3 ∧ a3 = 5) ∨ (K = 504 ∧ a2 = 9 ∧ a3 = 7) ∨ K = 262080 := by
  intro den num K hK6 hKG ha1K h2a1K ha1n1lt ha1n1K ha2K ha3K
  have hall := ok3_all
  simp only [List.all_eq_true] at hall
  have hok : ok3 a1 n1 a2 a3 n3 = true := hall a1 ha1 n1 hn1 a2 ha2 a3 ha3 n3 hn3
  dsimp only [ok3] at hok
  have hcond : (((a1 - 1) % n1 == 0 && decide (num < den) && den % (den - num) == 0 &&
      K % 6 == 0 && 262080 % K == 0 && K % a1 == 0 && K % (2 * a1) != 0 &&
      decide (a1 * n1 < K) && K % (a1 * n1) == 0 && K % (2 * a2) == 0 && K % (n3 * a3) == 0)) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm1, hnum⟩, hdiv⟩, hK6⟩, hKG⟩, ha1K⟩, h2a1K⟩, ha1n1lt⟩, ha1n1K⟩, ha2K⟩, ha3K⟩
  change (if ((a1 - 1) % n1 == 0 && decide (num < den) && den % (den - num) == 0 &&
      K % 6 == 0 && 262080 % K == 0 && K % a1 == 0 && K % (2 * a1) != 0 &&
      decide (a1 * n1 < K) && K % (a1 * n1) == 0 && K % (2 * a2) == 0 && K % (n3 * a3) == 0) then
    (K == 60 && a2 == 3 && a3 == 5) || (K == 504 && a2 == 9 && a3 == 7) || K == 262080
    else true) = true at hok
  rw [hcond, if_pos rfl] at hok
  simpa [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, and_assoc, or_assoc] using hok

private lemma mem_divs_63 {n : ℕ} (h : n ∣ 63) : n ∈ [1, 3, 7, 9, 21, 63] := by
  have hle : n ≤ 63 := Nat.le_of_dvd (by norm_num) h
  have hpos : 0 < n := Nat.pos_of_dvd_of_pos h (by norm_num)
  have hmem : n ∈ List.range 64 := List.mem_range.mpr (by omega)
  have hchk := checkDivs63_true
  simp only [checkDivs63, List.all_eq_true] at hchk
  have hspec := hchk n hmem
  have hm : 63 % n = 0 := Nat.mod_eq_zero_of_dvd h
  simp only [hm, beq_self_eq_true, Bool.true_and, decide_eq_true hpos, ↓reduceIte,
    List.contains_eq_mem, decide_eq_true_eq] at hspec
  exact hspec

private lemma mem_divs_63_or_65 {n : ℕ} (h : (n ∣ 63 ∨ n ∣ 65) ∧ 3 ≤ n) :
    n ∈ [3, 7, 9, 21, 63, 5, 13, 65] := by
  have hle : n ≤ 65 := by
    rcases h.1 with h63 | h65
    · exact le_trans (Nat.le_of_dvd (by norm_num) h63) (by norm_num)
    · exact Nat.le_of_dvd (by norm_num) h65
  have hmem : n ∈ List.range 66 := List.mem_range.mpr (by omega)
  have hchk := checkDivs63or65_true
  simp only [checkDivs63or65, List.all_eq_true] at hchk
  have hspec := hchk n hmem
  have hor : (63 % n == 0 || 65 % n == 0) = true := by
    rcases h.1 with h63 | h65
    · simp [Nat.mod_eq_zero_of_dvd h63]
    · simp [Nat.mod_eq_zero_of_dvd h65]
  have hge : decide (n ≥ 3) = true := decide_eq_true h.2
  simp only [hor, hge, Bool.and_self, ↓reduceIte, List.contains_eq_mem, decide_eq_true_eq] at hspec
  exact hspec

open scoped Classical

noncomputable section

abbrev F64 := GaloisField 2 6
abbrev G := Matrix.SpecialLinearGroup (Fin 2) F64

abbrev normG (A : Subgroup G) : Subgroup G := Subgroup.normalizer (A : Set G)

lemma card_eq_sum_card_fiberwise' {α β : Type*} [Fintype α] [Fintype β] (f : α → β) :
    Fintype.card α = ∑ b : β, Fintype.card {a : α // f a = b} := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv f).symm

lemma card_eq_sum_natCard_fiberwise {α β : Type*} [Fintype α] [Fintype β] (f : α → β) :
    Fintype.card α = ∑ b : β, Nat.card {a : α // f a = b} := by
  rw [card_eq_sum_card_fiberwise' f]
  exact Finset.sum_congr rfl fun _ _ => Nat.card_eq_fintype_card.symm

/-! ### Section 1: Finite field `F64` arithmetic and multiplicative subgroups -/

lemma card_F64 : Nat.card F64 = 64 := by
  have h := GaloisField.card 2 6 (by norm_num)
  norm_num at h
  exact h

lemma fintype_card_F64 [Fintype F64] : Fintype.card F64 = 64 := by
  rw [← Nat.card_eq_fintype_card, card_F64]

lemma two_eq_zero_F64 : (2 : F64) = 0 := CharP.cast_eq_zero F64 2

lemma add_self_F64 (x : F64) : x + x = 0 := by
  linear_combination x * two_eq_zero_F64

lemma neg_eq_self_F64 (x : F64) : -x = x := by
  linear_combination -x * two_eq_zero_F64

lemma sub_eq_add_F64 (x y : F64) : x - y = x + y := by
  linear_combination -y * two_eq_zero_F64

lemma eq_of_add_eq_zero_F64 {x y : F64} (h : x + y = 0) : x = y := by
  linear_combination h - y * two_eq_zero_F64

lemma add_sq_F64 (x y : F64) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  linear_combination x * y * two_eq_zero_F64

lemma add_pow_four_F64 (x y : F64) : (x + y) ^ 4 = x ^ 4 + y ^ 4 := by
  calc (x + y) ^ 4 = ((x + y) ^ 2) ^ 2 := by ring
    _ = (x ^ 2 + y ^ 2) ^ 2 := by rw [add_sq_F64]
    _ = (x ^ 2) ^ 2 + (y ^ 2) ^ 2 := add_sq_F64 _ _
    _ = x ^ 4 + y ^ 4 := by ring

lemma add_pow_eight_F64 (x y : F64) : (x + y) ^ 8 = x ^ 8 + y ^ 8 := by
  calc (x + y) ^ 8 = ((x + y) ^ 4) ^ 2 := by ring
    _ = (x ^ 4 + y ^ 4) ^ 2 := by rw [add_pow_four_F64]
    _ = (x ^ 4) ^ 2 + (y ^ 4) ^ 2 := add_sq_F64 _ _
    _ = x ^ 8 + y ^ 8 := by ring

lemma pow_64_F64 (x : F64) : x ^ 64 = x := by
  let _ : Fintype F64 := Fintype.ofFinite F64
  have h := FiniteField.pow_card x
  rwa [fintype_card_F64] at h

lemma card_F64_units : Nat.card F64ˣ = 63 := by
  let _ : Fintype F64 := Fintype.ofFinite F64
  rw [Nat.card_eq_fintype_card, Fintype.card_units, fintype_card_F64]

lemma exists_gen_F64 : ∃ ζ : F64ˣ, orderOf ζ = 63 := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := F64ˣ)
  exact ⟨ζ, by rw [orderOf_eq_card_of_forall_mem_zpowers hζ, card_F64_units]⟩

def ζ : F64ˣ := exists_gen_F64.choose

lemma orderOf_ζ : orderOf ζ = 63 := exists_gen_F64.choose_spec

lemma pow_eq_one_iff_dvd_63 (k : ℕ) : ζ ^ k = 1 ↔ 63 ∣ k := by
  rw [orderOf_dvd_iff_pow_eq_one.symm, orderOf_ζ]

lemma units_eq_pow_ζ (u : F64ˣ) : ∃ k : Fin 63, u = ζ ^ k.val := by
  let f : Fin 63 → F64ˣ := fun k => ζ ^ k.val
  have hle_eq : ∀ a b : Fin 63, a.val ≤ b.val → f a = f b → a = b := by
    intro a b hle hab
    have hpow : ζ ^ (b.val - a.val) = 1 := by
      have : ζ ^ a.val * ζ ^ (b.val - a.val) = ζ ^ a.val * 1 := by
        rw [← pow_add, Nat.add_sub_of_le hle, mul_one]; exact hab.symm
      exact mul_left_cancel this
    have hdvd : 63 ∣ b.val - a.val := (pow_eq_one_iff_dvd_63 _).mp hpow
    have hlt : b.val - a.val < 63 := by omega
    have h0 : b.val - a.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    exact Fin.ext (by omega)
  have hinj : Function.Injective f := by
    intro a b hab
    rcases le_total a.val b.val with hle | hle
    · exact hle_eq a b hle hab
    · exact (hle_eq b a hle hab.symm).symm
  let _ : Fintype F64ˣ := Fintype.ofFinite F64ˣ
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hinj, by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, card_F64_units]⟩
  obtain ⟨k, hk⟩ := hbij.2 u
  exact ⟨k, hk.symm⟩

def unitSubgroup (d : ℕ) : Subgroup F64ˣ where
  carrier := {u : F64ˣ | u ^ d = 1}
  mul_mem' := fun {a b} ha hb => by
    show (a * b) ^ d = 1
    rw [mul_pow, show a ^ d = 1 from ha, show b ^ d = 1 from hb, mul_one]
  one_mem' := by show (1 : F64ˣ) ^ d = 1; exact one_pow d
  inv_mem' := fun {a} ha => by
    show a⁻¹ ^ d = 1
    rw [inv_pow, show a ^ d = 1 from ha, inv_one]

lemma card_unitSubgroup {d : ℕ} (hd : d ∣ 63) : Nat.card (unitSubgroup d) = d := by
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd (by norm_num)
  obtain ⟨q, hq⟩ := hd
  have hq_pos : 0 < q := by nlinarith
  let f : Fin d → unitSubgroup d := fun j =>
    ⟨ζ ^ (q * j.val), by
      show (ζ ^ (q * j.val)) ^ d = 1
      rw [← pow_mul, show q * j.val * d = 63 * j.val by nlinarith, pow_mul,
        (pow_eq_one_iff_dvd_63 63).mpr dvd_rfl, one_pow]⟩
  have hle_eq : ∀ a b : Fin d, a.val ≤ b.val → f a = f b → a = b := by
    intro a b hle hab
    have h1 : ζ ^ (q * a.val) = ζ ^ (q * b.val) := congrArg Subtype.val hab
    have hpow : ζ ^ (q * (b.val - a.val)) = 1 := by
      have : ζ ^ (q * a.val) * ζ ^ (q * (b.val - a.val)) = ζ ^ (q * a.val) * 1 := by
        rw [← pow_add, ← mul_add, Nat.add_sub_of_le hle, mul_one]; exact h1.symm
      exact mul_left_cancel this
    have hdvd : 63 ∣ q * (b.val - a.val) := (pow_eq_one_iff_dvd_63 _).mp hpow
    have hba_lt : b.val - a.val < d := by omega
    have hlt : q * (b.val - a.val) < 63 := by nlinarith
    have h0 : q * (b.val - a.val) = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    have : b.val - a.val = 0 := by nlinarith
    exact Fin.ext (by omega)
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      rcases le_total a.val b.val with hle | hle
      · exact hle_eq a b hle hab
      · exact (hle_eq b a hle hab.symm).symm
    · rintro ⟨u, hu⟩
      obtain ⟨k, rfl⟩ := units_eq_pow_ζ u
      have hu' : (ζ ^ k.val) ^ d = 1 := hu
      have hdvd : 63 ∣ k.val * d := (pow_eq_one_iff_dvd_63 _).mp (by rw [pow_mul]; exact hu')
      have hqdvd : q ∣ k.val := by
        obtain ⟨m, hm⟩ := hdvd
        exact ⟨m, by nlinarith⟩
      obtain ⟨j, hj⟩ := hqdvd
      have hjlt : j < d := by nlinarith [k.isLt]
      exact ⟨⟨j, hjlt⟩, Subtype.ext (by simp [f, hj])⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_eq_fintype_card, Fintype.card_fin]

def ω : F64ˣ := ζ ^ 21

lemma ω_pow_three : ω ^ 3 = 1 := by
  simp only [ω, ← pow_mul]
  exact (pow_eq_one_iff_dvd_63 63).mpr dvd_rfl

lemma ω_ne_one : ω ≠ 1 := by
  intro h
  have := (pow_eq_one_iff_dvd_63 21).mp h
  omega

lemma ω_sq_add_ω_add_one : (ω : F64) ^ 2 + (ω : F64) + 1 = 0 := by
  have h3val : (ω : F64) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ω_pow_three, Units.val_one]
  have h3 : ((ω : F64) - 1) * ((ω : F64) ^ 2 + (ω : F64) + 1) = 0 := by
    linear_combination h3val
  have hne : (ω : F64) - 1 ≠ 0 := by
    intro h
    apply ω_ne_one
    ext
    exact sub_eq_zero.mp h
  exact (mul_eq_zero.mp h3).resolve_left hne

lemma ω_add_ω_inv : (ω : F64) + ((ω⁻¹ : F64ˣ) : F64) = 1 := by
  have h1 : (ω⁻¹ : F64ˣ) = ω ^ 2 := by
    apply mul_left_cancel (a := ω)
    rw [mul_inv_cancel, ← pow_succ', ω_pow_three]
  rw [h1, Units.val_pow_eq_pow_val]
  linear_combination ω_sq_add_ω_add_one - two_eq_zero_F64

def η : F64ˣ := ζ ^ 7

lemma η_pow_nine : η ^ 9 = 1 := by
  simp only [η, ← pow_mul]
  exact (pow_eq_one_iff_dvd_63 63).mpr dvd_rfl

lemma η_add_η_inv_ne_zero : (η : F64) + ((η⁻¹ : F64ˣ) : F64) ≠ 0 := by
  intro h
  have h1 : (η : F64) = ((η⁻¹ : F64ˣ) : F64) := eq_of_add_eq_zero_F64 h
  have h2 : η * η = 1 := by
    apply Units.ext
    change (η : F64) * (η : F64) = 1
    calc (η : F64) * (η : F64) = ((η⁻¹ : F64ˣ) : F64) * (η : F64) := by rw [← h1]
      _ = 1 := Units.inv_mul η
  have h3 : ζ ^ 14 = 1 := by
    simpa [η, ← pow_add] using h2
  have := (pow_eq_one_iff_dvd_63 14).mp h3
  omega

lemma F4_card : Nat.card {x : F64 // x ^ 4 = x} = 4 := by
  let f : Option (unitSubgroup 3) → {x : F64 // x ^ 4 = x} := fun o =>
    match o with
    | none => ⟨0, by norm_num⟩
    | some u => ⟨(u.val : F64), by
        have h3u : u.val ^ 3 = 1 := u.prop
        have h3 : (u.val : F64) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3u, Units.val_one]
        calc (u.val : F64) ^ 4 = (u.val : F64) ^ 3 * (u.val : F64) := by ring
          _ = (u.val : F64) := by rw [h3, one_mul]⟩
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      cases a <;> cases b <;> simp only [f, Subtype.mk.injEq] at hab
      · rfl
      · exact absurd hab.symm (Units.ne_zero _)
      · exact absurd hab (Units.ne_zero _)
      · exact congrArg some (Subtype.ext (Units.ext hab))
    · rintro ⟨x, hx⟩
      by_cases h0 : x = 0
      · exact ⟨none, Subtype.ext h0.symm⟩
      · refine ⟨some ⟨Units.mk0 x h0, ?_⟩, Subtype.ext rfl⟩
        show (Units.mk0 x h0) ^ 3 = 1
        ext
        simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
        exact mul_right_cancel₀ h0 (by rw [← pow_succ, hx, one_mul])
  rw [← Nat.card_congr (Equiv.ofBijective f hbij)]
  let _ : Fintype (unitSubgroup 3) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card,
    card_unitSubgroup (by norm_num)]

lemma F8_card : Nat.card {x : F64 // x ^ 8 = x} = 8 := by
  let f : Option (unitSubgroup 7) → {x : F64 // x ^ 8 = x} := fun o =>
    match o with
    | none => ⟨0, by norm_num⟩
    | some u => ⟨(u.val : F64), by
        have h7u : u.val ^ 7 = 1 := u.prop
        have h7 : (u.val : F64) ^ 7 = 1 := by rw [← Units.val_pow_eq_pow_val, h7u, Units.val_one]
        calc (u.val : F64) ^ 8 = (u.val : F64) ^ 7 * (u.val : F64) := by ring
          _ = (u.val : F64) := by rw [h7, one_mul]⟩
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      cases a <;> cases b <;> simp only [f, Subtype.mk.injEq] at hab
      · rfl
      · exact absurd hab.symm (Units.ne_zero _)
      · exact absurd hab (Units.ne_zero _)
      · exact congrArg some (Subtype.ext (Units.ext hab))
    · rintro ⟨x, hx⟩
      by_cases h0 : x = 0
      · exact ⟨none, Subtype.ext h0.symm⟩
      · refine ⟨some ⟨Units.mk0 x h0, ?_⟩, Subtype.ext rfl⟩
        show (Units.mk0 x h0) ^ 7 = 1
        ext
        simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
        exact mul_right_cancel₀ h0 (by rw [← pow_succ, hx, one_mul])
  rw [← Nat.card_congr (Equiv.ofBijective f hbij)]
  let _ : Fintype (unitSubgroup 7) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card,
    card_unitSubgroup (by norm_num)]

/-! ### Section 2: `G = SL(2, F64)`, basic matrix identities, and the 7 subgroups -/

lemma det_eq_one_char2 (M : G) : M 0 0 * M 1 1 + M 0 1 * M 1 0 = 1 := by
  have h := M.prop
  rw [Matrix.det_fin_two, sub_eq_add_F64] at h
  exact h

lemma inv_entry_00 (M : G) : (M⁻¹ : G) 0 0 = M 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp

lemma inv_entry_01 (M : G) : (M⁻¹ : G) 0 1 = M 0 1 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp [neg_eq_self_F64]

lemma inv_entry_10 (M : G) : (M⁻¹ : G) 1 0 = M 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp [neg_eq_self_F64]

lemma inv_entry_11 (M : G) : (M⁻¹ : G) 1 1 = M 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp

def tr (M : G) : F64 := M 0 0 + M 1 1

lemma tr_one : tr 1 = 0 := by
  simp [tr, add_self_F64]

lemma tr_conj (X M : G) : tr (X * M * X⁻¹) = tr M := by
  have htr : ∀ A : G, tr A = Matrix.trace (A : Matrix (Fin 2) (Fin 2) F64) := fun A => by
    simp [tr, Matrix.trace, Fin.sum_univ_two]
  rw [htr, htr]
  have h1 : ((X * M * X⁻¹ : G) : Matrix (Fin 2) (Fin 2) F64) =
      (X : Matrix (Fin 2) (Fin 2) F64) * (M : Matrix (Fin 2) (Fin 2) F64) *
      ((X⁻¹ : G) : Matrix (Fin 2) (Fin 2) F64) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  have hinv : ((X⁻¹ : G) : Matrix (Fin 2) (Fin 2) F64) * (X : Matrix (Fin 2) (Fin 2) F64) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  rw [h1, Matrix.trace_mul_cycle, hinv, Matrix.one_mul]

lemma cayley_hamilton (M : G) :
    (M : Matrix (Fin 2) (Fin 2) F64) ^ 2 =
      tr M • (M : Matrix (Fin 2) (Fin 2) F64) + (1 : Matrix (Fin 2) (Fin 2) F64) := by
  have hdet := det_eq_one_char2 M
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, tr, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      ite_true, ite_false, show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide]
  · linear_combination hdet - (M 0 0 * M 1 1) * two_eq_zero_F64
  · linear_combination -M 0 1 * (M 0 0 + M 1 1) * two_eq_zero_F64 +
      M 0 1 * (M 0 0 + M 1 1) * two_eq_zero_F64
  · linear_combination -M 1 0 * (M 0 0 + M 1 1) * two_eq_zero_F64 +
      M 1 0 * (M 0 0 + M 1 1) * two_eq_zero_F64
  · linear_combination hdet - (M 0 0 * M 1 1) * two_eq_zero_F64

lemma eq_one_of_scalar {M : G} {r : F64}
    (h : (M : Matrix (Fin 2) (Fin 2) F64) = r • (1 : Matrix (Fin 2) (Fin 2) F64)) : M = 1 := by
  have h00 : M 0 0 = r := by simpa using congrFun (congrFun h 0) 0
  have h01 : M 0 1 = 0 := by simpa using congrFun (congrFun h 0) 1
  have h10 : M 1 0 = 0 := by simpa using congrFun (congrFun h 1) 0
  have h11 : M 1 1 = r := by simpa using congrFun (congrFun h 1) 1
  have hr2 : r ^ 2 = 1 := by
    have hd := det_eq_one_char2 M
    rw [h00, h01, h10, h11] at hd
    linear_combination hd
  have hr : r = 1 := by
    have : (r + 1) ^ 2 = 0 := by rw [add_sq_F64, hr2, one_pow, add_self_F64]
    exact eq_of_add_eq_zero_F64 (eq_zero_of_pow_eq_zero this)
  apply Subtype.ext
  rw [h, hr, one_smul]
  rfl

lemma linear_indep_one_M {M : G} (hM : M ≠ 1) {r s : F64}
    (h : r • (1 : Matrix (Fin 2) (Fin 2) F64) + s • (M : Matrix (Fin 2) (Fin 2) F64) = 0) :
    r = 0 ∧ s = 0 := by
  by_cases hs : s = 0
  · subst hs
    simp only [zero_smul, add_zero] at h
    have hr : r = 0 := by simpa using congrFun (congrFun h 0) 0
    exact ⟨hr, rfl⟩
  · exfalso
    apply hM
    apply eq_one_of_scalar (r := s⁻¹ * r)
    have hsm : s • (M : Matrix (Fin 2) (Fin 2) F64) = r • (1 : Matrix (Fin 2) (Fin 2) F64) := by
      ext i j
      have hij := congrFun (congrFun h i) j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hij ⊢
      exact (eq_of_add_eq_zero_F64 hij).symm
    calc (M : Matrix (Fin 2) (Fin 2) F64)
        = s⁻¹ • (s • (M : Matrix (Fin 2) (Fin 2) F64)) := by rw [inv_smul_smul₀ hs]
      _ = s⁻¹ • (r • (1 : Matrix (Fin 2) (Fin 2) F64)) := by rw [hsm]
      _ = (s⁻¹ * r) • (1 : Matrix (Fin 2) (Fin 2) F64) := by rw [smul_smul]

lemma sq_eq_one_iff_tr_eq_zero (M : G) : M * M = 1 ↔ tr M = 0 := by
  constructor
  · intro h
    by_cases hM : M = 1
    · rw [hM, tr_one]
    · have hch := cayley_hamilton M
      have hsq : (M : Matrix (Fin 2) (Fin 2) F64) ^ 2 = 1 := by
        rw [sq, ← Matrix.SpecialLinearGroup.coe_mul, h]; rfl
      have h0 : (0 : F64) • (1 : Matrix (Fin 2) (Fin 2) F64) +
          tr M • (M : Matrix (Fin 2) (Fin 2) F64) = 0 := by
        ext i j
        have hij := congrFun (congrFun (hsq.symm.trans hch) i) j
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul, zero_mul,
          zero_add] at hij ⊢
        linear_combination -hij
      exact (linear_indep_one_M hM h0).2
  · intro ht
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, ← sq, cayley_hamilton, ht, zero_smul, zero_add]
    rfl

lemma card_G : Nat.card G = 262080 := by
  let S1 := F64ˣ × F64
  let S2 := F64ˣ × F64 × F64
  let f : S1 ⊕ S2 → G := fun s =>
    match s with
    | Sum.inl (b, d) =>
      ⟨!![(0 : F64), (b : F64); (b⁻¹ : F64ˣ), d], by
        rw [Matrix.det_fin_two]; simp [neg_eq_self_F64]⟩
    | Sum.inr (a, b, c) =>
      ⟨!![(a : F64), b; c, (1 + b * c) * (a⁻¹ : F64ˣ)], by
        rw [Matrix.det_fin_two, sub_eq_add_F64]
        simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
        have ha : (a : F64) * (a⁻¹ : F64ˣ) = 1 := Units.mul_inv a
        linear_combination (1 + b * c) * ha + b * c * two_eq_zero_F64⟩
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      rcases x with ⟨b1, d1⟩ | ⟨a1, b1, c1⟩ <;> rcases y with ⟨b2, d2⟩ | ⟨a2, b2, c2⟩
      · have h01 : (b1 : F64) = (b2 : F64) := by simpa [f] using congrFun (congrFun (congrArg Subtype.val hxy) 0) 1
        have h11 : d1 = d2 := by simpa [f] using congrFun (congrFun (congrArg Subtype.val hxy) 1) 1
        exact congrArg Sum.inl (Prod.ext (Units.ext h01) h11)
      · have h00 : (0 : F64) = (a2 : F64) := by simpa [f] using congrFun (congrFun (congrArg Subtype.val hxy) 0) 0
        exact absurd h00.symm (Units.ne_zero _)
      · have h00 : (a1 : F64) = 0 := by simpa [f] using congrFun (congrFun (congrArg Subtype.val hxy) 0) 0
        exact absurd h00 (Units.ne_zero _)
      · have h00 : (a1 : F64) = (a2 : F64) := by simpa [f] using congrFun (congrFun (congrArg Subtype.val hxy) 0) 0
        have h01 : b1 = b2 := by simpa [f] using congrFun (congrFun (congrArg Subtype.val hxy) 0) 1
        have h10 : c1 = c2 := by simpa [f] using congrFun (congrFun (congrArg Subtype.val hxy) 1) 0
        exact congrArg Sum.inr (Prod.ext (Units.ext h00) (Prod.ext h01 h10))
    · intro M
      have hd := det_eq_one_char2 M
      by_cases ha : M 0 0 = 0
      · have hb : M 0 1 ≠ 0 := by
          intro hb0; rw [ha, hb0, zero_mul, zero_mul, add_zero] at hd; exact zero_ne_one hd
        refine ⟨Sum.inl (Units.mk0 (M 0 1) hb, M 1 1), ?_⟩
        apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [f, ha]
        rw [ha, zero_mul, zero_add] at hd
        exact mul_left_cancel₀ hb (by rw [hd, mul_inv_cancel₀ hb])
      · refine ⟨Sum.inr (Units.mk0 (M 0 0) ha, M 0 1, M 1 0), ?_⟩
        apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [f]
        apply mul_left_cancel₀ ha
        have hinv : M 0 0 * (M 0 0)⁻¹ = 1 := mul_inv_cancel₀ ha
        linear_combination (1 + M 0 1 * M 1 0) * hinv - hd + (M 0 1 * M 1 0) * two_eq_zero_F64
  rw [← Nat.card_congr (Equiv.ofBijective f hbij)]
  let _ : Fintype F64 := Fintype.ofFinite F64
  let _ : Fintype F64ˣ := Fintype.ofFinite F64ˣ
  rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_F64, card_F64_units]

/-! #### Monomial matrices and the 7 subgroups -/

def diagMat (u : F64ˣ) : G :=
  ⟨!![(u : F64), 0; 0, (u⁻¹ : F64ˣ)], by
    rw [Matrix.det_fin_two]; simp⟩

def antiMat (u : F64ˣ) : G :=
  ⟨!![0, (u : F64); (u⁻¹ : F64ˣ), 0], by
    rw [Matrix.det_fin_two]; simp [neg_eq_self_F64]⟩

lemma diagMat_one : diagMat 1 = 1 := by
  apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [diagMat]

lemma diagMat_mul (u v : F64ˣ) : diagMat u * diagMat v = diagMat (u * v) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

lemma diagMat_mul_antiMat (u v : F64ˣ) : diagMat u * antiMat v = antiMat (u * v) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagMat, antiMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

lemma antiMat_mul_diagMat (u v : F64ˣ) : antiMat u * diagMat v = antiMat (u * v⁻¹) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagMat, antiMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

lemma antiMat_mul_antiMat (u v : F64ˣ) : antiMat u * antiMat v = diagMat (u * v⁻¹) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagMat, antiMat, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

lemma diagMat_inv (u : F64ˣ) : (diagMat u)⁻¹ = diagMat u⁻¹ := by
  apply mul_left_cancel (a := diagMat u)
  rw [mul_inv_cancel, diagMat_mul, mul_inv_cancel, diagMat_one]

lemma antiMat_inv (u : F64ˣ) : (antiMat u)⁻¹ = antiMat u := by
  apply mul_left_cancel (a := antiMat u)
  rw [mul_inv_cancel, antiMat_mul_antiMat, mul_inv_cancel, diagMat_one]

lemma diagMat_ne_antiMat (u v : F64ˣ) : diagMat u ≠ antiMat v := by
  intro h
  have h00 := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  simp [diagMat, antiMat] at h00

lemma diagMat_inj : Function.Injective diagMat := by
  intro u v h
  have h00 := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  exact Units.ext (by simpa [diagMat] using h00)

lemma antiMat_inj : Function.Injective antiMat := by
  intro u v h
  have h01 := congrFun (congrFun (congrArg Subtype.val h) 0) 1
  exact Units.ext (by simpa [antiMat] using h01)

def monomialSubgroup (U : Subgroup F64ˣ) : Subgroup G where
  carrier := {M : G | ∃ u ∈ U, M = diagMat u ∨ M = antiMat u}
  one_mem' := ⟨1, U.one_mem, Or.inl diagMat_one.symm⟩
  mul_mem' := by
    rintro _ _ ⟨u, hu, rfl | rfl⟩ ⟨v, hv, rfl | rfl⟩
    · exact ⟨u * v, U.mul_mem hu hv, Or.inl (diagMat_mul u v)⟩
    · exact ⟨u * v, U.mul_mem hu hv, Or.inr (diagMat_mul_antiMat u v)⟩
    · exact ⟨u * v⁻¹, U.mul_mem hu (U.inv_mem hv), Or.inr (antiMat_mul_diagMat u v)⟩
    · exact ⟨u * v⁻¹, U.mul_mem hu (U.inv_mem hv), Or.inl (antiMat_mul_antiMat u v)⟩
  inv_mem' := by
    rintro _ ⟨u, hu, rfl | rfl⟩
    · exact ⟨u⁻¹, U.inv_mem hu, Or.inl (diagMat_inv u)⟩
    · exact ⟨u, hu, Or.inr (antiMat_inv u)⟩

lemma card_monomialSubgroup (U : Subgroup F64ˣ) :
    Nat.card (monomialSubgroup U) = 2 * Nat.card U := by
  let f : Bool × U → monomialSubgroup U := fun p =>
    match p with
    | (false, u) => ⟨diagMat u.val, u.val, u.prop, Or.inl rfl⟩
    | (true, u) => ⟨antiMat u.val, u.val, u.prop, Or.inr rfl⟩
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨b1, u1⟩ ⟨b2, u2⟩ h
      have hv : (f (b1, u1)).val = (f (b2, u2)).val := congrArg Subtype.val h
      cases b1 <;> cases b2 <;> simp only [f] at hv
      · exact Prod.ext rfl (Subtype.ext (diagMat_inj hv))
      · exact absurd hv (diagMat_ne_antiMat _ _)
      · exact absurd hv.symm (diagMat_ne_antiMat _ _)
      · exact Prod.ext rfl (Subtype.ext (antiMat_inj hv))
    · rintro ⟨M, u, hu, rfl | rfl⟩
      · exact ⟨(false, ⟨u, hu⟩), rfl⟩
      · exact ⟨(true, ⟨u, hu⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij)]
  let _ : Fintype U := Fintype.ofFinite U
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool, ← Nat.card_eq_fintype_card]

def H : Subgroup G := monomialSubgroup (unitSubgroup 3)
def D18 : Subgroup G := monomialSubgroup (unitSubgroup 9)
def D42 : Subgroup G := monomialSubgroup (unitSubgroup 21)
def D126 : Subgroup G := monomialSubgroup ⊤

lemma card_H : Nat.card H = 6 := by
  rw [H, card_monomialSubgroup, card_unitSubgroup (by norm_num)]

lemma card_D18 : Nat.card D18 = 18 := by
  rw [D18, card_monomialSubgroup, card_unitSubgroup (by norm_num)]

lemma card_D42 : Nat.card D42 = 42 := by
  rw [D42, card_monomialSubgroup, card_unitSubgroup (by norm_num)]

lemma card_D126 : Nat.card D126 = 126 := by
  rw [D126, card_monomialSubgroup]
  have htop : Nat.card (⊤ : Subgroup F64ˣ) = 63 := by
    rw [← card_F64_units]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [htop]

def SL2F4 : Subgroup G where
  carrier := {M : G | M 0 0 ^ 4 = M 0 0 ∧ M 0 1 ^ 4 = M 0 1 ∧
                      M 1 0 ^ 4 = M 1 0 ∧ M 1 1 ^ 4 = M 1 1}
  one_mem' := by simp
  mul_mem' := by
    intro A B hA hB
    rcases hA with ⟨a00, a01, a10, a11⟩
    rcases hB with ⟨b00, b01, b10, b11⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        add_pow_four_F64, mul_pow, a00, a01, a10, a11, b00, b01, b10, b11]
  inv_mem' := by
    intro A hA
    rcases hA with ⟨a00, a01, a10, a11⟩
    exact ⟨by rw [inv_entry_00]; exact a11, by rw [inv_entry_01]; exact a01,
           by rw [inv_entry_10]; exact a10, by rw [inv_entry_11]; exact a00⟩

lemma card_SL2F4 : Nat.card SL2F4 = 60 := by
  let F4 := {x : F64 // x ^ 4 = x}
  let S1 := unitSubgroup 3 × F4
  let S2 := unitSubgroup 3 × F4 × F4
  have pow4_of_u3 : ∀ u : unitSubgroup 3, (u.val : F64) ^ 4 = (u.val : F64) := fun u => by
    have h3u : u.val ^ 3 = 1 := u.prop
    have h3 : (u.val : F64) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3u, Units.val_one]
    calc (u.val : F64) ^ 4 = (u.val : F64) ^ 3 * (u.val : F64) := by ring
      _ = (u.val : F64) := by rw [h3, one_mul]
  have pow4_inv_of_u3 : ∀ u : unitSubgroup 3, ((u.val⁻¹ : F64ˣ) : F64) ^ 4 = (u.val⁻¹ : F64ˣ) :=
    fun u => pow4_of_u3 ⟨u.val⁻¹, (unitSubgroup 3).inv_mem u.prop⟩
  let f : S1 ⊕ S2 → SL2F4 := fun s =>
    match s with
    | Sum.inl (b, d) =>
      ⟨⟨!![(0 : F64), (b.val : F64); (b.val⁻¹ : F64ˣ), d.val], by
          rw [Matrix.det_fin_two]; simp [neg_eq_self_F64]⟩,
        ⟨by simp, by simpa using pow4_of_u3 b, by simpa using pow4_inv_of_u3 b, by simpa using d.prop⟩⟩
    | Sum.inr (a, b, c) =>
      ⟨⟨!![(a.val : F64), b.val; c.val, (1 + b.val * c.val) * (a.val⁻¹ : F64ˣ)], by
          rw [Matrix.det_fin_two, sub_eq_add_F64]
          simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
          have ha : (a.val : F64) * (a.val⁻¹ : F64ˣ) = 1 := Units.mul_inv a.val
          linear_combination (1 + b.val * c.val) * ha + b.val * c.val * two_eq_zero_F64⟩,
        ⟨by simpa using pow4_of_u3 a, by simpa using b.prop, by simpa using c.prop, by
          simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
            mul_pow, add_pow_four_F64, one_pow, b.prop, c.prop, pow4_inv_of_u3 a]⟩⟩
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hM : (f x).val = (f y).val := congrArg Subtype.val hxy
      rcases x with ⟨b1, d1⟩ | ⟨a1, b1, c1⟩ <;> rcases y with ⟨b2, d2⟩ | ⟨a2, b2, c2⟩
      · have h01 : (b1.val : F64) = (b2.val : F64) := by simpa [f] using congrFun (congrFun (congrArg Subtype.val hM) 0) 1
        have h11 : d1.val = d2.val := by simpa [f] using congrFun (congrFun (congrArg Subtype.val hM) 1) 1
        exact congrArg Sum.inl (Prod.ext (Subtype.ext (Units.ext h01)) (Subtype.ext h11))
      · have h00 : (0 : F64) = (a2.val : F64) := by simpa [f] using congrFun (congrFun (congrArg Subtype.val hM) 0) 0
        exact absurd h00.symm (Units.ne_zero _)
      · have h00 : (a1.val : F64) = 0 := by simpa [f] using congrFun (congrFun (congrArg Subtype.val hM) 0) 0
        exact absurd h00 (Units.ne_zero _)
      · have h00 : (a1.val : F64) = (a2.val : F64) := by simpa [f] using congrFun (congrFun (congrArg Subtype.val hM) 0) 0
        have h01 : b1.val = b2.val := by simpa [f] using congrFun (congrFun (congrArg Subtype.val hM) 0) 1
        have h10 : c1.val = c2.val := by simpa [f] using congrFun (congrFun (congrArg Subtype.val hM) 1) 0
        exact congrArg Sum.inr (Prod.ext (Subtype.ext (Units.ext h00)) (Prod.ext (Subtype.ext h01) (Subtype.ext h10)))
    · rintro ⟨M, h00, h01, h10, h11⟩
      have hd := det_eq_one_char2 M
      by_cases ha : M 0 0 = 0
      · have hb : M 0 1 ≠ 0 := by
          intro hb0; rw [ha, hb0, zero_mul, zero_mul, add_zero] at hd; exact zero_ne_one hd
        have hbu : Units.mk0 (M 0 1) hb ∈ unitSubgroup 3 := by
          show (Units.mk0 (M 0 1) hb) ^ 3 = 1
          ext; simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
          exact mul_right_cancel₀ hb (by rw [← pow_succ, h01, one_mul])
        refine ⟨Sum.inl (⟨Units.mk0 (M 0 1) hb, hbu⟩, ⟨M 1 1, h11⟩), ?_⟩
        apply Subtype.ext; apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [f, ha]
        rw [ha, zero_mul, zero_add] at hd
        exact mul_left_cancel₀ hb (by rw [hd, mul_inv_cancel₀ hb])
      · have hau : Units.mk0 (M 0 0) ha ∈ unitSubgroup 3 := by
          show (Units.mk0 (M 0 0) ha) ^ 3 = 1
          ext; simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
          exact mul_right_cancel₀ ha (by rw [← pow_succ, h00, one_mul])
        refine ⟨Sum.inr (⟨Units.mk0 (M 0 0) ha, hau⟩, ⟨M 0 1, h01⟩, ⟨M 1 0, h10⟩), ?_⟩
        apply Subtype.ext; apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [f]
        apply mul_left_cancel₀ ha
        have hinv : M 0 0 * (M 0 0)⁻¹ = 1 := mul_inv_cancel₀ ha
        linear_combination (1 + M 0 1 * M 1 0) * hinv - hd + (M 0 1 * M 1 0) * two_eq_zero_F64
  rw [← Nat.card_congr (Equiv.ofBijective f hbij)]
  let _ : Fintype (unitSubgroup 3) := Fintype.ofFinite _
  let _ : Fintype F4 := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    card_unitSubgroup (by norm_num), F4_card]

def SU2F8 : Subgroup G where
  carrier := {M : G | M 1 1 = M 0 0 ^ 8 ∧ M 1 0 = M 0 1 ^ 8}
  one_mem' := by simp
  mul_mem' := by
    rintro A B ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        ha1, ha2, hb1, hb2, add_pow_eight_F64, mul_pow, ← pow_mul]
      rw [show 8 * 8 = 64 by norm_num, pow_64_F64]; ring
    · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        ha1, ha2, hb1, hb2, add_pow_eight_F64, mul_pow, ← pow_mul]
      rw [show 8 * 8 = 64 by norm_num, pow_64_F64]; ring
  inv_mem' := by
    rintro A ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩
    · rw [inv_entry_11, inv_entry_00, ha1, ← pow_mul, pow_64_F64]
    · rw [inv_entry_10, inv_entry_01, ha2]

lemma card_norm9_fiber {y : F64} (hy0 : y ≠ 0) (hy8 : y ^ 8 = y) :
    Nat.card {x : F64 // x ^ 9 = y} = 9 := by
  have hyu : (Units.mk0 y hy0) ^ 7 = 1 := by
    ext; simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    exact mul_right_cancel₀ hy0 (by rw [← pow_succ, hy8, one_mul])
  obtain ⟨k, hk⟩ := units_eq_pow_ζ (Units.mk0 y hy0)
  have hdvd : 63 ∣ k.val * 7 := (pow_eq_one_iff_dvd_63 _).mp (by rw [pow_mul, ← hk, hyu])
  have h9dvd : 9 ∣ k.val := by obtain ⟨m, hm⟩ := hdvd; exact ⟨m, by omega⟩
  obtain ⟨j, hj⟩ := h9dvd
  let x0 : F64ˣ := ζ ^ j
  have hx0u : x0 ^ 9 = Units.mk0 y hy0 := by simp [x0, ← pow_mul, hk, hj, mul_comm]
  have hx0 : (x0 : F64) ^ 9 = y := by rw [← Units.val_pow_eq_pow_val, hx0u, Units.val_mk0]
  let f : unitSubgroup 9 → {x : F64 // x ^ 9 = y} := fun u =>
    ⟨(u.val : F64) * (x0 : F64), by
      have hu9 : u.val ^ 9 = 1 := u.prop
      have hu : (u.val : F64) ^ 9 = 1 := by rw [← Units.val_pow_eq_pow_val, hu9, Units.val_one]
      rw [mul_pow, hu, one_mul, hx0]⟩
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      have h1 : (a.val : F64) * (x0 : F64) = (b.val : F64) * (x0 : F64) := congrArg Subtype.val hab
      exact Subtype.ext (Units.ext (mul_right_cancel₀ (Units.ne_zero x0) h1))
    · rintro ⟨x, hx⟩
      have hxne : x ≠ 0 := by intro h0; rw [h0, zero_pow (by norm_num)] at hx; exact hy0 hx.symm
      let u := Units.mk0 x hxne * x0⁻¹
      have hu : u ∈ unitSubgroup 9 := by
        show u ^ 9 = 1
        ext; simp only [u, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mk0, Units.val_one,
          mul_pow, hx]
        have hinv9 : ((x0⁻¹ : F64ˣ) : F64) ^ 9 = y⁻¹ := by
          apply mul_left_cancel₀ hy0
          rw [mul_inv_cancel₀ hy0, ← hx0, ← mul_pow, Units.mul_inv, one_pow]
        rw [hinv9, mul_inv_cancel₀ hy0]
      exact ⟨⟨u, hu⟩, Subtype.ext (by simp [f, u])⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), card_unitSubgroup (by norm_num)]

lemma card_SU2F8 : Nat.card SU2F8 = 504 := by
  let S := {p : F64 × F64 // p.1 ^ 9 + p.2 ^ 9 = 1}
  have e1 : SU2F8 ≃ S :=
    { toFun := fun M => ⟨(M.val 0 0, M.val 0 1), by
        have hd := det_eq_one_char2 M.val
        rw [M.prop.1, M.prop.2] at hd
        simpa [pow_succ'] using hd⟩
      invFun := fun p =>
        ⟨⟨!![p.val.1, p.val.2; p.val.2 ^ 8, p.val.1 ^ 8], by
            rw [Matrix.det_fin_two, sub_eq_add_F64]
            simpa [pow_succ'] using p.prop⟩,
          ⟨rfl, rfl⟩⟩
      left_inv := fun M => by
        apply Subtype.ext; apply Subtype.ext; ext i j
        fin_cases i <;> fin_cases j <;> simp [M.prop.1, M.prop.2]
      right_inv := fun p => Subtype.ext rfl }
  rw [Nat.card_congr e1]
  let F8 := {y : F64 // y ^ 8 = y}
  let _ : Fintype F64 := Fintype.ofFinite F64
  let _ : Fintype F8 := Fintype.ofFinite F8
  let _ : Fintype S := Fintype.ofFinite S
  have hpow9_in_F8 : ∀ x : F64, (x ^ 9) ^ 8 = x ^ 9 := fun x => by
    calc (x ^ 9) ^ 8 = x ^ 64 * x ^ 8 := by ring
      _ = x * x ^ 8 := by rw [pow_64_F64]
      _ = x ^ 9 := by ring
  let proj : S → F8 := fun p => ⟨p.val.1 ^ 9, hpow9_in_F8 p.val.1⟩
  rw [Nat.card_eq_fintype_card, card_eq_sum_natCard_fiberwise proj]
  have hfiber : ∀ y : F8, Nat.card {p : S // proj p = y} =
      if y.val = 0 then 9 else if y.val = 1 then 9 else 81 := by
    intro y
    have h1y_F8 : (1 + y.val) ^ 8 = 1 + y.val := by
      rw [add_pow_eight_F64, one_pow, y.prop]
    have efib : {p : S // proj p = y} ≃ {a : F64 // a ^ 9 = y.val} × {b : F64 // b ^ 9 = 1 + y.val} :=
      { toFun := fun ⟨⟨⟨a, b⟩, hab⟩, hy⟩ =>
          have ha : a ^ 9 = y.val := congrArg Subtype.val hy
          ⟨⟨a, ha⟩, ⟨b, by linear_combination hab - ha - y.val * two_eq_zero_F64⟩⟩
        invFun := fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ =>
          ⟨⟨⟨a, b⟩, by linear_combination ha + hb + y.val * two_eq_zero_F64⟩, Subtype.ext ha⟩
        left_inv := fun ⟨⟨⟨_, _⟩, _⟩, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl }
    rw [Nat.card_congr efib, Nat.card_prod]
    by_cases hy0 : y.val = 0
    · simp only [hy0, ite_true, add_zero]
      have h0 : Nat.card {a : F64 // a ^ 9 = 0} = 1 := by
        have e0 : {a : F64 // a ^ 9 = 0} ≃ Unit :=
          { toFun := fun _ => (), invFun := fun _ => ⟨0, by norm_num⟩,
            left_inv := fun ⟨a, ha⟩ => Subtype.ext (eq_zero_of_pow_eq_zero ha).symm, right_inv := fun () => rfl }
        rw [Nat.card_congr e0]; simp
      rw [h0, card_norm9_fiber one_ne_zero (by norm_num)]
    · by_cases hy1 : y.val = 1
      · simp only [hy1, one_ne_zero, ite_false, ite_true, add_self_F64]
        have h0 : Nat.card {b : F64 // b ^ 9 = 0} = 1 := by
          have e0 : {b : F64 // b ^ 9 = 0} ≃ Unit :=
            { toFun := fun _ => (), invFun := fun _ => ⟨0, by norm_num⟩,
              left_inv := fun ⟨b, hb⟩ => Subtype.ext (eq_zero_of_pow_eq_zero hb).symm, right_inv := fun () => rfl }
          rw [Nat.card_congr e0]; simp
        rw [card_norm9_fiber one_ne_zero (by norm_num), h0]
      · simp only [hy0, hy1, ite_false]
        have h1yne : 1 + y.val ≠ 0 := fun h => hy1 (eq_of_add_eq_zero_F64 h).symm
        rw [card_norm9_fiber hy0 y.prop, card_norm9_fiber h1yne h1y_F8]
  trans (∑ y : F8, if y.val = 0 then 9 else if y.val = 1 then 9 else 81)
  · exact Finset.sum_congr rfl fun y _ => hfiber y
  let y0 : F8 := ⟨0, by norm_num⟩
  let y1 : F8 := ⟨1, by norm_num⟩
  have hy01 : y0 ≠ y1 := by intro h; exact zero_ne_one (congrArg Subtype.val h)
  have hcardF8 : (Finset.univ : Finset F8).card = 8 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, F8_card]
  have hsplit : (Finset.univ : Finset F8) = insert y0 (insert y1 ((Finset.univ.erase y0).erase y1)) := by
    ext y
    by_cases h0 : y = y0
    · simp [h0]
    · by_cases h1 : y = y1
      · simp [h1]
      · simp [h0, h1]
  rw [hsplit, Finset.sum_insert, Finset.sum_insert]
  · have hrest : ∑ y ∈ (Finset.univ.erase y0).erase y1,
        (if y.val = 0 then 9 else if y.val = 1 then 9 else 81) =
        ∑ _y ∈ (Finset.univ.erase y0).erase y1, 81 := by
      refine Finset.sum_congr rfl fun y hy => ?_
      have hne1 : y ≠ y1 := (Finset.mem_erase.mp hy).1
      have hne0 : y ≠ y0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
      have hv0 : y.val ≠ 0 := fun h => hne0 (Subtype.ext h)
      have hv1 : y.val ≠ 1 := fun h => hne1 (Subtype.ext h)
      simp [hv0, hv1]
    rw [hrest, Finset.sum_const, smul_eq_mul]
    have hcard_rest : ((Finset.univ.erase y0).erase y1).card = 6 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hy01.symm, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), hcardF8]
    rw [hcard_rest]
    simp [y0, y1]
  · simp
  · simp [hy01]

/-! ### Section 3: Centralizers, T.I. property, and Normalizer bounds -/

def C (M : G) : Subgroup G where
  carrier := {X : G | X * M = M * X}
  one_mem' := by simp
  mul_mem' := fun {A B} hA hB => by
    calc (A * B) * M = A * (B * M) := mul_assoc _ _ _
      _ = A * (M * B) := by rw [hB]
      _ = (A * M) * B := (mul_assoc _ _ _).symm
      _ = (M * A) * B := by rw [hA]
      _ = M * (A * B) := mul_assoc _ _ _
  inv_mem' := fun {A} hA => by
    calc A⁻¹ * M = A⁻¹ * (M * A) * A⁻¹ := by group
      _ = A⁻¹ * (A * M) * A⁻¹ := by rw [← hA]
      _ = M * A⁻¹ := by group

lemma mem_C_iff_linear {M X : G} (hM : M ≠ 1) :
    X ∈ C M ↔ ∃ r s : F64,
      (X : Matrix (Fin 2) (Fin 2) F64) =
        r • (1 : Matrix (Fin 2) (Fin 2) F64) + s • (M : Matrix (Fin 2) (Fin 2) F64) := by
  constructor
  · intro hX
    have hcomm : (X : Matrix (Fin 2) (Fin 2) F64) * M = M * X := by
      simpa [Matrix.SpecialLinearGroup.coe_mul] using congrArg Subtype.val hX
    have h00 : X 0 1 * M 1 0 = M 0 1 * X 1 0 := by
      have := congrFun (congrFun hcomm 0) 0
      simp only [Matrix.mul_apply, Fin.sum_univ_two] at this
      linear_combination this
    have h01 : X 0 0 * M 0 1 + X 0 1 * M 1 1 = M 0 0 * X 0 1 + M 0 1 * X 1 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hcomm 0) 1
    have h10 : X 1 0 * M 0 0 + X 1 1 * M 1 0 = M 1 0 * X 0 0 + M 1 1 * X 1 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hcomm 1) 0
    by_cases hb : M 0 1 ≠ 0
    · refine ⟨X 0 0 + X 0 1 * (M 0 1)⁻¹ * M 0 0, X 0 1 * (M 0 1)⁻¹, ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;>
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
          Fin.isValue, Fin.zero_eta, Fin.mk_one, ite_true, ite_false,
          show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide, mul_one, mul_zero,
          zero_add]
      · linear_combination -(X 0 1 * (M 0 1)⁻¹ * M 0 0) * two_eq_zero_F64
      · rw [mul_assoc, inv_mul_cancel₀ hb, mul_one]
      · apply mul_left_cancel₀ hb
        calc M 0 1 * X 1 0 = X 0 1 * M 1 0 := h00.symm
          _ = M 0 1 * (X 0 1 * (M 0 1)⁻¹ * M 1 0) := by
              rw [show M 0 1 * (X 0 1 * (M 0 1)⁻¹ * M 1 0) =
                  (M 0 1 * (M 0 1)⁻¹) * (X 0 1 * M 1 0) by ring, mul_inv_cancel₀ hb, one_mul]
      · apply mul_left_cancel₀ hb
        have hinv : M 0 1 * (M 0 1)⁻¹ = 1 := mul_inv_cancel₀ hb
        linear_combination -h01 - X 0 1 * (M 0 0 + M 1 1) * hinv -
          (X 0 1 * M 0 0) * two_eq_zero_F64
    · push Not at hb
      by_cases hc : M 1 0 ≠ 0
      · refine ⟨X 0 0 + X 1 0 * (M 1 0)⁻¹ * M 0 0, X 1 0 * (M 1 0)⁻¹, ?_⟩
        ext i j; fin_cases i <;> fin_cases j <;>
          simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
            Fin.isValue, Fin.zero_eta, Fin.mk_one, ite_true, ite_false,
            show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide, mul_one, mul_zero,
            zero_add]
        · linear_combination -(X 1 0 * (M 1 0)⁻¹ * M 0 0) * two_eq_zero_F64
        · rw [hb, mul_zero]
          rw [hb, zero_mul] at h00
          exact (mul_eq_zero.mp h00).resolve_right hc
        · rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
        · apply mul_left_cancel₀ hc
          have hinv : M 1 0 * (M 1 0)⁻¹ = 1 := mul_inv_cancel₀ hc
          linear_combination h10 - X 1 0 * (M 0 0 + M 1 1) * hinv -
            (X 1 0 * M 0 0) * two_eq_zero_F64
      · push Not at hc
        have ht : M 0 0 + M 1 1 ≠ 0 := by
          intro ht0
          apply hM
          have h11 : M 1 1 = M 0 0 := (eq_of_add_eq_zero_F64 ht0).symm
          apply eq_one_of_scalar (r := M 0 0)
          ext i j; fin_cases i <;> fin_cases j <;> simp [hb, hc, h11]
        have hx01 : X 0 1 = 0 := by
          rw [hb, mul_zero, zero_mul, zero_add, add_zero] at h01
          have : X 0 1 * (M 0 0 + M 1 1) = 0 := by
            linear_combination -h01 + X 0 1 * M 1 1 * two_eq_zero_F64
          exact (mul_eq_zero.mp this).resolve_right ht
        have hx10 : X 1 0 = 0 := by
          rw [hc, mul_zero, zero_mul, zero_add, add_zero] at h10
          have : X 1 0 * (M 0 0 + M 1 1) = 0 := by
            linear_combination h10 + M 1 1 * X 1 0 * two_eq_zero_F64
          exact (mul_eq_zero.mp this).resolve_right ht
        let s := (X 0 0 + X 1 1) * (M 0 0 + M 1 1)⁻¹
        refine ⟨X 0 0 + s * M 0 0, s, ?_⟩
        ext i j; fin_cases i <;> fin_cases j <;>
          simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
            Fin.isValue, Fin.zero_eta, Fin.mk_one, ite_true, ite_false,
            show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide, mul_one, mul_zero,
            add_zero, hb, hc, hx01, hx10]
        · linear_combination -(s * M 0 0) * two_eq_zero_F64
        · have hinv : s * (M 0 0 + M 1 1) = X 0 0 + X 1 1 := by
            simp only [s, mul_assoc, inv_mul_cancel₀ ht, mul_one]
          linear_combination -hinv - X 0 0 * two_eq_zero_F64
  · rintro ⟨r, s, hX⟩
    show X * M = M * X
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hX]
    simp [add_mul, mul_add]

lemma C_comm {M : G} (hM : M ≠ 1) {X Y : G} (hX : X ∈ C M) (hY : Y ∈ C M) : X * Y = Y * X := by
  obtain ⟨r1, s1, h1⟩ := (mem_C_iff_linear hM).mp hX
  obtain ⟨r2, s2, h2⟩ := (mem_C_iff_linear hM).mp hY
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h1, h2]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add, smul_smul]
  rw [mul_comm r1 r2, mul_comm s1 s2, mul_comm r1 s2, mul_comm s1 r2]
  abel

lemma C_eq_of_mem {M N : G} (hM : M ≠ 1) (hN : N ≠ 1) (hNM : N ∈ C M) : C N = C M := by
  ext X
  constructor
  · intro hX
    have hMN : M ∈ C N := hNM.symm
    exact C_comm hN hX hMN
  · intro hX
    exact C_comm hM hX hNM

lemma det_linear_F64 (M : G) (r s : F64) :
    Matrix.det (r • (1 : Matrix (Fin 2) (Fin 2) F64) + s • (M : Matrix (Fin 2) (Fin 2) F64)) =
      r ^ 2 + tr M * r * s + s ^ 2 := by
  rw [Matrix.det_fin_two, sub_eq_add_F64]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Fin.isValue, ite_true, ite_false, show (0 : Fin 2) ≠ 1 by decide,
    show (1 : Fin 2) ≠ 0 by decide, mul_one, mul_zero, zero_add, tr]
  have hd := det_eq_one_char2 M
  linear_combination s ^ 2 * hd

def C_equiv_quad {M : G} (hM : M ≠ 1) :
    C M ≃ {p : F64 × F64 // p.1 ^ 2 + tr M * p.1 * p.2 + p.2 ^ 2 = 1} := by
  let invF : {p : F64 × F64 // p.1 ^ 2 + tr M * p.1 * p.2 + p.2 ^ 2 = 1} → C M := fun p =>
    ⟨⟨p.val.1 • (1 : Matrix (Fin 2) (Fin 2) F64) + p.val.2 • (M : Matrix (Fin 2) (Fin 2) F64), by
        rw [det_linear_F64]; exact p.prop⟩,
      (mem_C_iff_linear hM).mpr ⟨p.val.1, p.val.2, rfl⟩⟩
  have hbij : Function.Bijective invF := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨r1, s1⟩, hp1⟩ ⟨⟨r2, s2⟩, hp2⟩ h
      have hmat : (r1 + r2) • (1 : Matrix (Fin 2) (Fin 2) F64) +
          (s1 + s2) • (M : Matrix (Fin 2) (Fin 2) F64) = 0 := by
        have h' : r1 • (1 : Matrix (Fin 2) (Fin 2) F64) + s1 • (M : Matrix (Fin 2) (Fin 2) F64) =
                  r2 • (1 : Matrix (Fin 2) (Fin 2) F64) + s2 • (M : Matrix (Fin 2) (Fin 2) F64) :=
          congrArg (fun x => (x.val : Matrix (Fin 2) (Fin 2) F64)) h
        ext i j
        have hij := congrFun (congrFun h' i) j
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hij ⊢
        linear_combination hij + (r2 * (1 : Matrix (Fin 2) (Fin 2) F64) i j +
          s2 * (M : Matrix (Fin 2) (Fin 2) F64) i j) * two_eq_zero_F64
      obtain ⟨hr, hs⟩ := linear_indep_one_M hM hmat
      exact Subtype.ext (Prod.ext (eq_of_add_eq_zero_F64 hr) (eq_of_add_eq_zero_F64 hs))
    · rintro ⟨X, hX⟩
      obtain ⟨r, s, hrs⟩ := (mem_C_iff_linear hM).mp hX
      have hq : r ^ 2 + tr M * r * s + s ^ 2 = 1 := by
        rw [← det_linear_F64 M r s, ← hrs]; exact X.prop
      exact ⟨⟨(r, s), hq⟩, Subtype.ext (Subtype.ext hrs.symm)⟩
  exact (Equiv.ofBijective invF hbij).symm

lemma card_C_unipotent {M : G} (hM : M ≠ 1) (ht : tr M = 0) : Nat.card (C M) = 64 := by
  rw [Nat.card_congr (C_equiv_quad hM)]
  let f : F64 → {p : F64 × F64 // p.1 ^ 2 + tr M * p.1 * p.2 + p.2 ^ 2 = 1} := fun s =>
    ⟨(1 + s, s), by
      rw [ht, zero_mul, zero_mul, add_zero, add_sq_F64, one_pow, add_assoc, add_self_F64, add_zero]⟩
  have hbij : Function.Bijective f := by
    refine ⟨fun s1 s2 h => by simpa [f] using congrArg (fun x => x.val.2) h, ?_⟩
    rintro ⟨⟨r, s⟩, hq⟩
    rw [ht, zero_mul, zero_mul, add_zero] at hq
    have hsq : (r + s + 1) ^ 2 = 0 := by
      rw [add_sq_F64, add_sq_F64, one_pow, hq, add_self_F64]
    have h0 := eq_zero_of_pow_eq_zero hsq
    have hr : r = 1 + s := eq_of_add_eq_zero_F64 (by linear_combination h0)
    exact ⟨s, Subtype.ext (Prod.ext hr.symm rfl)⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), card_F64]

lemma card_C_split {M : G} (hM : M ≠ 1) (ht : tr M ≠ 0)
    (hsplit : ∃ u : F64, u ^ 2 + tr M * u + 1 = 0) : Nat.card (C M) = 63 := by
  obtain ⟨u, hu⟩ := hsplit
  have hu0 : u ≠ 0 := by intro h0; rw [h0] at hu; norm_num at hu
  have huinv : u + u⁻¹ = tr M := by
    apply mul_left_cancel₀ hu0
    have hinv : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
    linear_combination hu + hinv - u * tr M * two_eq_zero_F64
  have hudiff : u + u⁻¹ ≠ 0 := by rw [huinv]; exact ht
  rw [Nat.card_congr (C_equiv_quad hM)]
  let f : {p : F64 × F64 // p.1 ^ 2 + tr M * p.1 * p.2 + p.2 ^ 2 = 1} → F64ˣ := fun p =>
    Units.mk0 (p.val.1 + u * p.val.2) (by
      intro h0
      have hprod : (p.val.1 + u * p.val.2) * (p.val.1 + u⁻¹ * p.val.2) = 1 := by
        calc (p.val.1 + u * p.val.2) * (p.val.1 + u⁻¹ * p.val.2)
            = p.val.1 ^ 2 + (u + u⁻¹) * p.val.1 * p.val.2 + (u * u⁻¹) * p.val.2 ^ 2 := by ring
          _ = p.val.1 ^ 2 + tr M * p.val.1 * p.val.2 + p.val.2 ^ 2 := by
              rw [huinv, mul_inv_cancel₀ hu0, one_mul]
          _ = 1 := p.prop
      rw [h0, zero_mul] at hprod
      exact zero_ne_one hprod)
  have hbij : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨r1, s1⟩, hp1⟩ ⟨⟨r2, s2⟩, hp2⟩ h
      have hv : r1 + u * s1 = r2 + u * s2 := congrArg Units.val h
      have hprod : ∀ r s, r ^ 2 + tr M * r * s + s ^ 2 = 1 →
          (r + u * s) * (r + u⁻¹ * s) = 1 := fun r s hq => by
        calc (r + u * s) * (r + u⁻¹ * s)
            = r ^ 2 + (u + u⁻¹) * r * s + (u * u⁻¹) * s ^ 2 := by ring
          _ = r ^ 2 + tr M * r * s + s ^ 2 := by rw [huinv, mul_inv_cancel₀ hu0, one_mul]
          _ = 1 := hq
      have hne : r1 + u * s1 ≠ 0 := Units.ne_zero (f ⟨(r1, s1), hp1⟩)
      have hw : r1 + u⁻¹ * s1 = r2 + u⁻¹ * s2 := by
        apply mul_left_cancel₀ hne
        rw [hprod r1 s1 hp1, hv, hprod r2 s2 hp2]
      have hs : (u + u⁻¹) * (s1 + s2) = 0 := by
        linear_combination hv - hw + (u * s2 + u⁻¹ * s1) * two_eq_zero_F64
      have hs0 : s1 + s2 = 0 := (mul_eq_zero.mp hs).resolve_left hudiff
      have hs' : s1 = s2 := eq_of_add_eq_zero_F64 hs0
      subst hs'
      have hr' : r1 = r2 := by linear_combination hv
      exact Subtype.ext (Prod.ext hr' rfl)
    · intro v
      let s := ((v : F64) + ((v⁻¹ : F64ˣ) : F64)) * (tr M)⁻¹
      let r := (v : F64) + u * s
      have hrs1 : r + u * s = (v : F64) := by
        simp only [r, add_assoc, add_self_F64, add_zero]
      have hrs2 : r + u⁻¹ * s = ((v⁻¹ : F64ˣ) : F64) := by
        have h1 : (u + u⁻¹) * s = (v : F64) + ((v⁻¹ : F64ˣ) : F64) := by
          simp only [s, huinv, mul_comm (tr M), mul_assoc, inv_mul_cancel₀ ht, mul_one]
        simp only [r]
        linear_combination h1 + (v : F64) * two_eq_zero_F64
      refine ⟨⟨(r, s), ?_⟩, Units.ext hrs1⟩
      calc r ^ 2 + tr M * r * s + s ^ 2
          = r ^ 2 + (u + u⁻¹) * r * s + (u * u⁻¹) * s ^ 2 := by
              rw [huinv, mul_inv_cancel₀ hu0, one_mul]
        _ = (r + u * s) * (r + u⁻¹ * s) := by ring
        _ = (v : F64) * ((v⁻¹ : F64ˣ) : F64) := by rw [hrs1, hrs2]
        _ = 1 := Units.mul_inv v
  rw [Nat.card_congr (Equiv.ofBijective f hbij), card_F64_units]

lemma card_C_nonsplit {M : G} (hM : M ≠ 1)
    (hirr : ∀ u : F64, u ^ 2 + tr M * u + 1 ≠ 0) : Nat.card (C M) = 65 := by
  rw [Nat.card_congr (C_equiv_quad hM)]
  let Q : F64 × F64 → F64 := fun p => p.1 ^ 2 + tr M * p.1 * p.2 + p.2 ^ 2
  have hQne : ∀ p : F64 × F64, p ≠ (0, 0) → Q p ≠ 0 := by
    rintro ⟨r, s⟩ hp hq
    by_cases hs : s = 0
    · simp only [Q, hs, mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] at hq
      exact hp (Prod.ext (eq_zero_of_pow_eq_zero hq) hs)
    · apply hirr (r * s⁻¹)
      have : (r * s⁻¹) ^ 2 + tr M * (r * s⁻¹) + 1 = Q (r, s) * (s⁻¹) ^ 2 := by
        simp only [Q]; field_simp [hs]
      rw [this, hq, zero_mul]
  have hsqrt_sq : ∀ x : F64, (x ^ 32) ^ 2 = x := fun x => by
    rw [← pow_mul, show 32 * 2 = 64 by norm_num, pow_64_F64]
  have hsqrt_ne : ∀ {x : F64}, x ≠ 0 → x ^ 32 ≠ 0 := fun hx => pow_ne_zero 32 hx
  let P0 := {p : F64 × F64 // p ≠ (0, 0)}
  let S := {p : F64 × F64 // Q p = 1}
  let e : P0 ≃ S × F64ˣ :=
    { toFun := fun ⟨p, hp⟩ =>
        let l := Units.mk0 ((Q p) ^ 32) (hsqrt_ne (hQne p hp))
        (⟨((l⁻¹ : F64ˣ) * p.1, (l⁻¹ : F64ˣ) * p.2), by
            show Q ((l⁻¹ : F64ˣ) * p.1, (l⁻¹ : F64ˣ) * p.2) = 1
            have hl2 : ((l : F64) ^ 2) = Q p := hsqrt_sq (Q p)
            have hlinv2 : ((l⁻¹ : F64ˣ) : F64) ^ 2 * Q p = 1 := by
              rw [← hl2, ← mul_pow, Units.inv_mul, one_pow]
            calc ((l⁻¹ : F64ˣ) * p.1) ^ 2 + tr M * ((l⁻¹ : F64ˣ) * p.1) * ((l⁻¹ : F64ˣ) * p.2) +
                    ((l⁻¹ : F64ˣ) * p.2) ^ 2
                = ((l⁻¹ : F64ˣ) : F64) ^ 2 * Q p := by simp only [Q]; ring
              _ = 1 := hlinv2⟩, l)
      invFun := fun ⟨⟨p, hp⟩, l⟩ =>
        ⟨((l : F64) * p.1, (l : F64) * p.2), by
          intro h0
          have hp1 : p.1 = 0 := (mul_eq_zero.mp (congrArg Prod.fst h0)).resolve_left (Units.ne_zero l)
          have hp2 : p.2 = 0 := (mul_eq_zero.mp (congrArg Prod.snd h0)).resolve_left (Units.ne_zero l)
          simp [Q, hp1, hp2] at hp⟩
      left_inv := fun ⟨⟨r, s⟩, hp⟩ => by
        have hqne : Q (r, s) ^ 32 ≠ 0 := hsqrt_ne (hQne (r, s) hp)
        apply Subtype.ext; apply Prod.ext <;> simp [← mul_assoc, mul_inv_cancel₀ hqne]
      right_inv := fun ⟨⟨⟨r, s⟩, hp⟩, l⟩ => by
        have hQl : Q ((l : F64) * r, (l : F64) * s) = (l : F64) ^ 2 := by
          calc ((l : F64) * r) ^ 2 + tr M * ((l : F64) * r) * ((l : F64) * s) + ((l : F64) * s) ^ 2
              = (l : F64) ^ 2 * Q (r, s) := by simp only [Q]; ring
            _ = (l : F64) ^ 2 := by rw [hp, mul_one]
        have hl32 : ((Q ((l : F64) * r, (l : F64) * s)) ^ 32) = (l : F64) := by
          rw [hQl, ← pow_mul, show 2 * 32 = 64 by norm_num, pow_64_F64]
        apply Prod.ext
        · apply Subtype.ext; apply Prod.ext <;> simp [hl32]
        · exact Units.ext hl32 }
  have hcardP0 : Nat.card P0 = 4095 := by
    let _ : Fintype F64 := Fintype.ofFinite F64
    let _ : Fintype P0 := Fintype.ofFinite P0
    have h1 : Fintype.card P0 + 1 = Fintype.card (F64 × F64) := by
      have eopt : Option P0 ≃ F64 × F64 :=
        { toFun := fun o => match o with | none => (0, 0) | some x => x.val
          invFun := fun p => if h : p = (0, 0) then none else some ⟨p, h⟩
          left_inv := fun o => by
            cases o with
            | none => simp
            | some x => simp [x.prop]
          right_inv := fun p => by by_cases h : p = (0, 0) <;> simp [h] }
      rw [← Fintype.card_congr eopt, Fintype.card_option]
    rw [Nat.card_eq_fintype_card]
    have h2 : Fintype.card (F64 × F64) = 4096 := by
      rw [Fintype.card_prod, fintype_card_F64]
    omega
  have hprod : Nat.card P0 = Nat.card S * 63 := by
    rw [Nat.card_congr e]
    let _ : Fintype S := Fintype.ofFinite S
    let _ : Fintype F64ˣ := Fintype.ofFinite F64ˣ
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, ← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card, card_F64_units]
  change Nat.card S = 65
  omega

lemma card_C_cases {M : G} (hM : M ≠ 1) :
    (tr M = 0 ∧ Nat.card (C M) = 64) ∨
    (tr M ≠ 0 ∧ (Nat.card (C M) = 63 ∨ Nat.card (C M) = 65)) := by
  by_cases ht : tr M = 0
  · exact Or.inl ⟨ht, card_C_unipotent hM ht⟩
  · by_cases hs : ∃ u : F64, u ^ 2 + tr M * u + 1 = 0
    · exact Or.inr ⟨ht, Or.inl (card_C_split hM ht hs)⟩
    · push Not at hs
      exact Or.inr ⟨ht, Or.inr (card_C_nonsplit hM hs)⟩

lemma tr_eq_zero_of_mem_C_unipotent {M X : G} (hM : M ≠ 1) (ht : tr M = 0) (hX : X ∈ C M) :
    tr X = 0 := by
  obtain ⟨r, s, hX⟩ := (mem_C_iff_linear hM).mp hX
  have h00 : X 0 0 = r + s * M 0 0 := by simpa using congrFun (congrFun hX 0) 0
  have h11 : X 1 1 = r + s * M 1 1 := by simpa using congrFun (congrFun hX 1) 1
  simp only [tr, h00, h11]
  have htrM : M 0 0 + M 1 1 = 0 := ht
  linear_combination s * htrM + r * two_eq_zero_F64

lemma conj_C (X M : G) :
    (C M).map (MulAut.conj X).toMonoidHom = C (X * M * X⁻¹) := by
  ext Y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨Z, hZ, rfl⟩
    show X * Z * X⁻¹ * (X * M * X⁻¹) = X * M * X⁻¹ * (X * Z * X⁻¹)
    have hZ' : Z * M = M * Z := hZ
    calc X * Z * X⁻¹ * (X * M * X⁻¹) = X * (Z * M) * X⁻¹ := by group
      _ = X * (M * Z) * X⁻¹ := by rw [hZ']
      _ = X * M * X⁻¹ * (X * Z * X⁻¹) := by group
  · intro hY
    refine ⟨X⁻¹ * Y * X, ?_, by group⟩
    show X⁻¹ * Y * X * M = M * (X⁻¹ * Y * X)
    have hY' : Y * (X * M * X⁻¹) = X * M * X⁻¹ * Y := hY
    calc X⁻¹ * Y * X * M = X⁻¹ * (Y * (X * M * X⁻¹)) * X := by group
      _ = X⁻¹ * (X * M * X⁻¹ * Y) * X := by rw [hY']
      _ = M * (X⁻¹ * Y * X) := by group

lemma mem_normalizer_C_of_mem_normalizer_inf {K : Subgroup G} {M X : G}
    (hM : M ≠ 1) (hMK : M ∈ K) (hX : X ∈ normG (K ⊓ C M)) :
    X ∈ normG (C M) := by
  have hconjM : X * M * X⁻¹ ∈ K ⊓ C M :=
    (Subgroup.mem_normalizer_iff.mp hX M).mp ⟨hMK, rfl⟩
  have hne : X * M * X⁻¹ ≠ 1 := by
    intro h0; apply hM
    calc M = X⁻¹ * (X * M * X⁻¹) * X := by group
      _ = X⁻¹ * 1 * X := by rw [h0]
      _ = 1 := by group
  have hCeq : C (X * M * X⁻¹) = C M := C_eq_of_mem hM hne hconjM.2
  rw [Subgroup.mem_normalizer_iff]
  intro Y
  have h1 : X * Y * X⁻¹ ∈ C (X * M * X⁻¹) ↔ Y ∈ C M := by
    rw [← conj_C]
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact ⟨fun ⟨Z, hZ, hZY⟩ => by
      have : Z = Y := by
        calc Z = X⁻¹ * (X * Z * X⁻¹) * X := by group
          _ = X⁻¹ * (X * Y * X⁻¹) * X := by rw [hZY]
          _ = Y := by group
      rwa [← this], fun hY => ⟨Y, hY, rfl⟩⟩
  rw [hCeq] at h1
  exact h1.symm

lemma conj_mem_pair_of_tr_ne_zero {M X : G} (hM : M ≠ 1) (ht : tr M ≠ 0)
    (hX : X ∈ normG (C M)) : X * M * X⁻¹ = M ∨ X * M * X⁻¹ = M⁻¹ := by
  have hmem : X * M * X⁻¹ ∈ C M := (Subgroup.mem_normalizer_iff.mp hX M).mp rfl
  obtain ⟨r, s, hrs⟩ := (mem_C_iff_linear hM).mp hmem
  have htr : tr (X * M * X⁻¹) = s * tr M := by
    have h00 : (X * M * X⁻¹) 0 0 = r + s * M 0 0 := by simpa using congrFun (congrFun hrs 0) 0
    have h11 : (X * M * X⁻¹) 1 1 = r + s * M 1 1 := by simpa using congrFun (congrFun hrs 1) 1
    simp only [tr, h00, h11]
    linear_combination r * two_eq_zero_F64
  rw [tr_conj] at htr
  have hs : s = 1 := mul_right_cancel₀ ht (by rw [← htr, one_mul])
  have hdet : r ^ 2 + tr M * r * s + s ^ 2 = 1 := by
    rw [← det_linear_F64 M r s, ← hrs]; exact (X * M * X⁻¹).prop
  rw [hs, mul_one, one_pow] at hdet
  have hr0 : r * (r + tr M) = 0 := by linear_combination hdet
  rcases mul_eq_zero.mp hr0 with rfl | hrt
  · left
    apply Subtype.ext; rw [hrs, hs, zero_smul, one_smul, zero_add]
  · right
    have hr : r = tr M := eq_of_add_eq_zero_F64 hrt
    have hMinv : ((M⁻¹ : G) : Matrix (Fin 2) (Fin 2) F64) =
        tr M • (1 : Matrix (Fin 2) (Fin 2) F64) + (M : Matrix (Fin 2) (Fin 2) F64) := by
      ext i j; fin_cases i <;> fin_cases j
      · change ((M⁻¹ : G) : Matrix (Fin 2) (Fin 2) F64) 0 0 =
          (tr M • (1 : Matrix (Fin 2) (Fin 2) F64) + (M : Matrix (Fin 2) (Fin 2) F64)) 0 0
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
          ite_true, mul_one, tr, inv_entry_00]
        linear_combination -M 0 0 * two_eq_zero_F64
      · simp [inv_entry_01]
      · simp [inv_entry_10]
      · change ((M⁻¹ : G) : Matrix (Fin 2) (Fin 2) F64) 1 1 =
          (tr M • (1 : Matrix (Fin 2) (Fin 2) F64) + (M : Matrix (Fin 2) (Fin 2) F64)) 1 1
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
          ite_true, mul_one, tr, inv_entry_11]
        linear_combination -M 1 1 * two_eq_zero_F64
    apply Subtype.ext; rw [hrs, hr, hs, one_smul, hMinv]

lemma normalizer_inf_card_le_two_mul {K : Subgroup G} {M : G}
    (hM : M ≠ 1) (hMK : M ∈ K) (ht : tr M ≠ 0) :
    Nat.card (normG (K ⊓ C M) ⊓ K : Subgroup G) = Nat.card (K ⊓ C M : Subgroup G) ∨
    Nat.card (normG (K ⊓ C M) ⊓ K : Subgroup G) = 2 * Nat.card (K ⊓ C M : Subgroup G) := by
  let A : Subgroup G := K ⊓ C M
  let N : Subgroup G := normG A ⊓ K
  change Nat.card N = Nat.card A ∨ Nat.card N = 2 * Nat.card A
  have hAN : A ≤ N := fun x hx => ⟨Subgroup.le_normalizer hx, hx.1⟩
  have hdvd : Nat.card A ∣ Nat.card N := Subgroup.card_dvd_of_le hAN
  have hle2 : Nat.card N ≤ 2 * Nat.card A := by
    by_cases hex : ∃ Y : N, (Y : G) * M * (Y : G)⁻¹ = M⁻¹ ∧ (Y : G) * M * (Y : G)⁻¹ ≠ M
    · obtain ⟨Y, hY1, _⟩ := hex
      let f : N → Bool × A := fun X =>
        if h : (X : G) * M * (X : G)⁻¹ = M then
          (false, ⟨X.val, X.prop.2, by
            show (X : G) * M = M * (X : G)
            calc (X : G) * M = (X : G) * M * (X : G)⁻¹ * (X : G) := by group
              _ = M * (X : G) := by rw [h]⟩)
        else
          (true, ⟨(Y⁻¹ * X : N).val, (Y⁻¹ * X).prop.2, by
            have hXnorm := mem_normalizer_C_of_mem_normalizer_inf hM hMK X.prop.1
            have hXinv : (X : G) * M * (X : G)⁻¹ = M⁻¹ :=
              (conj_mem_pair_of_tr_ne_zero hM ht hXnorm).resolve_left h
            show ((Y : G)⁻¹ * (X : G)) * M = M * ((Y : G)⁻¹ * (X : G))
            have h1 : (X : G) * M = M⁻¹ * (X : G) := by
              calc (X : G) * M = (X : G) * M * (X : G)⁻¹ * (X : G) := by group
                _ = M⁻¹ * (X : G) := by rw [hXinv]
            have h2 : (Y : G) * M = M⁻¹ * (Y : G) := by
              calc (Y : G) * M = (Y : G) * M * (Y : G)⁻¹ * (Y : G) := by group
                _ = M⁻¹ * (Y : G) := by rw [hY1]
            have h3 : (Y : G)⁻¹ * M⁻¹ = M * (Y : G)⁻¹ := by
              calc (Y : G)⁻¹ * M⁻¹ = (Y : G)⁻¹ * (M⁻¹ * (Y : G)) * (Y : G)⁻¹ := by group
                _ = (Y : G)⁻¹ * ((Y : G) * M) * (Y : G)⁻¹ := by rw [← h2]
                _ = M * (Y : G)⁻¹ := by group
            calc (Y : G)⁻¹ * (X : G) * M = (Y : G)⁻¹ * ((X : G) * M) := by group
              _ = (Y : G)⁻¹ * (M⁻¹ * (X : G)) := by rw [h1]
              _ = ((Y : G)⁻¹ * M⁻¹) * (X : G) := by group
              _ = M * (Y : G)⁻¹ * (X : G) := by rw [h3]
              _ = M * ((Y : G)⁻¹ * (X : G)) := by group⟩)
      have hinj : Function.Injective f := by
        intro X1 X2 h
        by_cases h1 : (X1 : G) * M * (X1 : G)⁻¹ = M <;> by_cases h2 : (X2 : G) * M * (X2 : G)⁻¹ = M
        · simp only [f, h1, h2, dite_true, Prod.mk.injEq, true_and] at h
          exact Subtype.ext (Subtype.mk.inj h)
        · simp [f, h1, h2] at h
        · simp [f, h1, h2] at h
        · simp only [f, h1, h2, dite_false, Prod.mk.injEq, true_and] at h
          have hv : (Y : G)⁻¹ * (X1 : G) = (Y : G)⁻¹ * (X2 : G) := Subtype.mk.inj h
          exact Subtype.ext (mul_left_cancel hv)
      let _ : Fintype N := Fintype.ofFinite N
      let _ : Fintype A := Fintype.ofFinite A
      calc Nat.card N = Fintype.card N := Nat.card_eq_fintype_card
        _ ≤ Fintype.card (Bool × A) := Fintype.card_le_of_injective f hinj
        _ = 2 * Nat.card A := by rw [Fintype.card_prod, Fintype.card_bool, ← Nat.card_eq_fintype_card]
    · push Not at hex
      have hNA : N ≤ A := by
        intro X hX
        have hXnorm := mem_normalizer_C_of_mem_normalizer_inf hM hMK hX.1
        have hcomm : X * M * X⁻¹ = M := by
          rcases conj_mem_pair_of_tr_ne_zero hM ht hXnorm with h | h
          · exact h
          · exact hex ⟨X, hX⟩ h
        exact ⟨hX.2, by
          show X * M = M * X
          calc X * M = X * M * X⁻¹ * X := by group
            _ = M * X := by rw [hcomm]⟩
      have hEq : N = A := le_antisymm hNA hAN
      rw [hEq]; omega
  obtain ⟨q, hq⟩ := hdvd
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hqle : q ≤ 2 := by nlinarith
  have hqpos : 0 < q := by
    have : 0 < Nat.card N := Nat.card_pos
    nlinarith
  interval_cases q
  · left; omega
  · right; omega

lemma normalizer_inf_unipotent_dvd {K : Subgroup G} {M : G}
    (hM : M ≠ 1) (hMK : M ∈ K) (ht : tr M = 0) :
    let A := K ⊓ C M
    let N := normG A ⊓ K
    (Nat.card N / Nat.card A) ∣ (Nat.card A - 1) ∧ (Nat.card N / Nat.card A) ∣ 63 := by
  intro A N
  have hAN : A ≤ N := fun x hx => ⟨Subgroup.le_normalizer hx, hx.1⟩
  have hAdvdN : Nat.card A ∣ Nat.card N := Subgroup.card_dvd_of_le hAN
  have hdvd_subset : ∀ (S : Finset G),
      (∀ x ∈ S, x ∈ C M ∧ x ≠ 1) →
      (∀ (g : N), ∀ x ∈ S, (g : G) * x * (g : G)⁻¹ ∈ S) →
      (Nat.card N / Nat.card A) ∣ S.card := by
    intro S hSC hScl
    let _ : MulAction N S :=
      { smul := fun g x => ⟨(g : G) * x.val * (g : G)⁻¹, hScl g x.val x.prop⟩
        one_smul := fun x => Subtype.ext (by show (1 : G) * x.val * (1 : G)⁻¹ = x.val; group)
        mul_smul := fun g1 g2 x => Subtype.ext (by
          show ((g1 : G) * (g2 : G)) * x.val * ((g1 : G) * (g2 : G))⁻¹ =
               (g1 : G) * ((g2 : G) * x.val * (g2 : G)⁻¹) * (g1 : G)⁻¹
          group) }
    have hstab : ∀ x : S, Nat.card (MulAction.stabilizer N x) = Nat.card A := by
      intro x
      have hxC : x.val ∈ C M := (hSC x.val x.prop).1
      have hxne : x.val ≠ 1 := (hSC x.val x.prop).2
      have hCx : C x.val = C M := C_eq_of_mem hM hxne hxC
      have e : MulAction.stabilizer N x ≃ A :=
        { toFun := fun ⟨g, hg⟩ => ⟨g.val, g.prop.2, by
            rw [← hCx]
            have hgx : (g : G) * x.val * (g : G)⁻¹ = x.val := congrArg Subtype.val hg
            show (g : G) * x.val = x.val * (g : G)
            calc (g : G) * x.val = (g : G) * x.val * (g : G)⁻¹ * (g : G) := by group
              _ = x.val * (g : G) := by rw [hgx]⟩
          invFun := fun a => ⟨⟨a.val, hAN a.prop⟩, Subtype.ext (by
            have ha : a.val ∈ C x.val := by rw [hCx]; exact a.prop.2
            show a.val * x.val * a.val⁻¹ = x.val
            have ha' : a.val * x.val = x.val * a.val := ha
            calc a.val * x.val * a.val⁻¹ = x.val * a.val * a.val⁻¹ := by rw [ha']
              _ = x.val := by group)⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact Nat.card_congr e
    let _ : Fintype N := Fintype.ofFinite N
    let _ : Fintype S := Fintype.ofFinite S
    let q := Nat.card N / Nat.card A
    have horb : ∀ x : S, Nat.card (MulAction.orbit N x) = q := by
      intro x
      have hmul := MulAction.card_orbit_mul_card_stabilizer_eq_card_group N x
      rw [← Nat.card_eq_fintype_card (α := MulAction.orbit N x),
        ← Nat.card_eq_fintype_card (α := MulAction.stabilizer N x), hstab x,
        ← Nat.card_eq_fintype_card (α := N)] at hmul
      have hApos : 0 < Nat.card A := Nat.card_pos
      have hqmul : q * Nat.card A = Nat.card N := Nat.div_mul_cancel hAdvdN
      exact Nat.eq_of_mul_eq_mul_right hApos (hmul.trans hqmul.symm)
    let _ : Fintype (Quotient (MulAction.orbitRel N S)) := Fintype.ofFinite _
    have hcardS : Fintype.card S =
        ∑ o : Quotient (MulAction.orbitRel N S),
          Nat.card {x : S // Quotient.mk (MulAction.orbitRel N S) x = o} :=
      card_eq_sum_natCard_fiberwise (Quotient.mk (MulAction.orbitRel N S))
    have hfib : ∀ o : Quotient (MulAction.orbitRel N S),
        Nat.card {x : S // Quotient.mk (MulAction.orbitRel N S) x = o} = q := by
      intro o
      induction o using Quotient.ind with
      | _ x =>
        have ef : {y : S // Quotient.mk (MulAction.orbitRel N S) y = Quotient.mk _ x} ≃
            MulAction.orbit N x :=
          { toFun := fun ⟨y, hy⟩ => ⟨y, Quotient.exact hy⟩
            invFun := fun ⟨y, hy⟩ => ⟨y, Quotient.sound hy⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [Nat.card_congr ef, horb x]
    rw [← Fintype.card_coe, hcardS, Finset.sum_congr rfl (fun o _ => hfib o),
      Finset.sum_const, smul_eq_mul]
    exact dvd_mul_left q _
  let _ : Fintype G := Fintype.ofFinite G
  have h1 := hdvd_subset (Finset.univ.filter (fun x : G => x ∈ A ∧ x ≠ 1))
    (fun x hx => ⟨(Finset.mem_filter.mp hx).2.1.2, (Finset.mem_filter.mp hx).2.2⟩)
    (fun g x hx => by
      have hx' := (Finset.mem_filter.mp hx).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp g.prop.1 x).mp hx'.1
      · intro h0; apply hx'.2
        calc x = (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) := by group
          _ = 1 := by rw [h0]; group)
  have h2 := hdvd_subset (Finset.univ.filter (fun x : G => x ∈ C M ∧ x ≠ 1))
    (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun g x hx => by
      have hx' := (Finset.mem_filter.mp hx).2
      have hgnorm := mem_normalizer_C_of_mem_normalizer_inf hM hMK g.prop.1
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp hgnorm x).mp hx'.1
      · intro h0; apply hx'.2
        calc x = (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) := by group
          _ = 1 := by rw [h0]; group)
  have hcard_filter : ∀ (P : Subgroup G),
      (Finset.univ.filter (fun x : G => x ∈ P ∧ x ≠ 1)).card = Nat.card P - 1 := by
    intro P
    have eP : {x : G // x ∈ P ∧ x ≠ 1} ≃ {x : P // x ≠ 1} :=
      { toFun := fun ⟨x, hx1, hx2⟩ => ⟨⟨x, hx1⟩, fun h => hx2 (congrArg Subtype.val h)⟩
        invFun := fun ⟨⟨x, hx⟩, hne⟩ => ⟨x, hx, fun h => hne (Subtype.ext h)⟩
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    let _ : Fintype P := Fintype.ofFinite P
    rw [← Fintype.card_subtype, Fintype.card_congr eP]
    have hopt : Option {x : P // x ≠ 1} ≃ P :=
      { toFun := fun o => match o with | none => 1 | some x => x.val
        invFun := fun x => if h : x = 1 then none else some ⟨x, h⟩
        left_inv := fun o => by cases o with | none => simp | some x => simp [x.prop]
        right_inv := fun x => by by_cases h : x = 1 <;> simp [h] }
    have hc := Fintype.card_congr hopt
    rw [Fintype.card_option, ← Nat.card_eq_fintype_card (α := P)] at hc
    omega
  rw [hcard_filter A] at h1
  rw [hcard_filter (C M), card_C_unipotent hM ht] at h2
  exact ⟨h1, h2⟩

def C3 : G := diagMat ω
def τ : G := antiMat 1

lemma C3_ne_one : C3 ≠ 1 := by
  intro h
  exact ω_ne_one (diagMat_inj (h.trans diagMat_one.symm))

lemma tr_C3 : tr C3 = 1 := by
  change (ω : F64) + ((ω⁻¹ : F64ˣ) : F64) = 1
  exact ω_add_ω_inv

lemma C3_mem_H : C3 ∈ H := ⟨ω, ω_pow_three, Or.inl rfl⟩
lemma τ_mem_H : τ ∈ H := ⟨1, one_pow 3, Or.inr rfl⟩
lemma τ_ne_one : τ ≠ 1 := by
  intro h; exact diagMat_ne_antiMat 1 1 (diagMat_one.trans h.symm)
lemma tr_τ : tr τ = 0 := by simp [tr, τ, antiMat]

lemma C_C3_eq_diag : ∀ X : G, X ∈ C C3 ↔ ∃ u : F64ˣ, X = diagMat u := by
  intro X
  constructor
  · intro hX
    have hcomm : (X : Matrix (Fin 2) (Fin 2) F64) * C3 = C3 * X := by
      simpa [Matrix.SpecialLinearGroup.coe_mul] using congrArg Subtype.val hX
    have h01 : X 0 1 * ((ω⁻¹ : F64ˣ) : F64) = (ω : F64) * X 0 1 := by
      simpa [C3, diagMat, Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hcomm 0) 1
    have h10 : X 1 0 * (ω : F64) = ((ω⁻¹ : F64ˣ) : F64) * X 1 0 := by
      simpa [C3, diagMat, Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hcomm 1) 0
    have hne : (ω : F64) + ((ω⁻¹ : F64ˣ) : F64) ≠ 0 := by rw [ω_add_ω_inv]; exact one_ne_zero
    have hx01 : X 0 1 = 0 := by
      have : X 0 1 * ((ω : F64) + ((ω⁻¹ : F64ˣ) : F64)) = 0 := by
        linear_combination h01 + (ω : F64) * X 0 1 * two_eq_zero_F64
      exact (mul_eq_zero.mp this).resolve_right hne
    have hx10 : X 1 0 = 0 := by
      have : X 1 0 * ((ω : F64) + ((ω⁻¹ : F64ˣ) : F64)) = 0 := by
        linear_combination h10 + ((ω⁻¹ : F64ˣ) : F64) * X 1 0 * two_eq_zero_F64
      exact (mul_eq_zero.mp this).resolve_right hne
    have hd := det_eq_one_char2 X
    rw [hx01, hx10, mul_zero, add_zero] at hd
    have ha : X 0 0 ≠ 0 := by intro h0; rw [h0, zero_mul] at hd; exact zero_ne_one hd
    refine ⟨Units.mk0 (X 0 0) ha, ?_⟩
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [diagMat, hx01, hx10]
    exact mul_left_cancel₀ ha (by rw [hd, mul_inv_cancel₀ ha])
  · rintro ⟨u, rfl⟩
    show diagMat u * diagMat ω = diagMat ω * diagMat u
    rw [diagMat_mul, diagMat_mul, mul_comm]

lemma normalizer_C_C3_eq_D126 : normG (C C3) = D126 := by
  ext X
  constructor
  · intro hX
    rcases conj_mem_pair_of_tr_ne_zero C3_ne_one (by rw [tr_C3]; exact one_ne_zero) hX with h | h
    · have hcomm : X ∈ C C3 := by
        show X * C3 = C3 * X
        calc X * C3 = X * C3 * X⁻¹ * X := by group
          _ = C3 * X := by rw [h]
      obtain ⟨u, rfl⟩ := (C_C3_eq_diag X).mp hcomm
      exact ⟨u, trivial, Or.inl rfl⟩
    · have hτX : τ * X ∈ C C3 := by
        show (τ * X) * C3 = C3 * (τ * X)
        have hXC3 : X * C3 = C3⁻¹ * X := by
          calc X * C3 = X * C3 * X⁻¹ * X := by group
            _ = C3⁻¹ * X := by rw [h]
        have hτC3' : τ * C3⁻¹ = C3 * τ := by
          simp only [τ, C3, diagMat_inv, antiMat_mul_diagMat, diagMat_mul_antiMat, inv_inv,
            one_mul, mul_one]
        calc τ * X * C3 = τ * (X * C3) := mul_assoc _ _ _
          _ = τ * (C3⁻¹ * X) := by rw [hXC3]
          _ = (τ * C3⁻¹) * X := (mul_assoc _ _ _).symm
          _ = C3 * (τ * X) := by rw [hτC3', mul_assoc]
      obtain ⟨u, hu⟩ := (C_C3_eq_diag (τ * X)).mp hτX
      have hXeq : X = antiMat u⁻¹ := by
        have h1 : τ * (τ * X) = τ * diagMat u := congrArg (τ * ·) hu
        have hτ2 : τ * τ = 1 := by simp [τ, antiMat_mul_antiMat, diagMat_one]
        rw [← mul_assoc, hτ2, one_mul] at h1
        rw [h1]; simp [τ, antiMat_mul_diagMat]
      exact ⟨u⁻¹, trivial, Or.inr hXeq⟩
  · rintro ⟨u, _, rfl | rfl⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro Y
      rw [C_C3_eq_diag, C_C3_eq_diag]
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨v, by rw [diagMat_inv, diagMat_mul, diagMat_mul, mul_comm u v, mul_assoc, mul_inv_cancel, mul_one]⟩
      · rintro ⟨v, hv⟩
        refine ⟨v, ?_⟩
        calc Y = (diagMat u)⁻¹ * (diagMat u * Y * (diagMat u)⁻¹) * diagMat u := by group
          _ = diagMat u⁻¹ * diagMat v * diagMat u := by rw [hv, diagMat_inv]
          _ = diagMat v := by rw [diagMat_mul, diagMat_mul, mul_comm u⁻¹ v, mul_assoc, inv_mul_cancel, mul_one]
    · rw [Subgroup.mem_normalizer_iff]
      intro Y
      rw [C_C3_eq_diag, C_C3_eq_diag]
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨v⁻¹, by rw [antiMat_inv, antiMat_mul_diagMat, antiMat_mul_antiMat, mul_comm u v⁻¹, mul_assoc, mul_inv_cancel, mul_one]⟩
      · rintro ⟨v, hv⟩
        refine ⟨v⁻¹, ?_⟩
        calc Y = (antiMat u)⁻¹ * (antiMat u * Y * (antiMat u)⁻¹) * antiMat u := by group
          _ = antiMat u * diagMat v * antiMat u := by rw [hv, antiMat_inv]
          _ = diagMat v⁻¹ := by rw [antiMat_mul_diagMat, antiMat_mul_antiMat, mul_comm u v⁻¹, mul_assoc, mul_inv_cancel, mul_one]

/-! ### Section 4: Sylow-2 uniqueness and Suzuki's T.I. partition equation -/

lemma C_unipotent_is_sylow2 {M : G} (hM : M ≠ 1) (ht : tr M = 0) :
    IsPGroup 2 (C M) ∧ ∀ Q : Sylow 2 G, C M ≤ Q → (Q : Subgroup G) = C M := by
  have hcard : Nat.card (C M) = 2 ^ 6 := by rw [card_C_unipotent hM ht]; norm_num
  have hp : IsPGroup 2 (C M) := IsPGroup.of_card hcard
  refine ⟨hp, fun Q hle => ?_⟩
  have hQcard : Nat.card (Q : Subgroup G) = 64 := by
    rw [Sylow.card_eq_multiplicity, card_G]
    have : (262080 : ℕ).factorization 2 = 6 := by
      have hfact : 262080 = 2 ^ 6 * 4095 := by norm_num
      rw [hfact, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
      have hodd : ¬ 2 ∣ 4095 := by norm_num
      rw [Nat.factorization_eq_zero_of_not_dvd hodd]
    rw [this]; norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hQcard, card_C_unipotent hM ht])).symm

lemma unipotent_inf_is_sylow2 {K : Subgroup G} {M : G}
    (hM : M ≠ 1) (hMK : M ∈ K) (ht : tr M = 0) :
    ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = K ⊓ C M := by
  let A := K ⊓ C M
  have hAcard : Nat.card A ∣ 64 := by
    rw [← card_C_unipotent hM ht]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hAp : IsPGroup 2 (A.subgroupOf K) := by
    have hcard_eq : Nat.card (A.subgroupOf K) = Nat.card A := by
      have e : A.subgroupOf K ≃ A :=
        { toFun := fun x => ⟨x.val.val, x.prop⟩
          invFun := fun x => ⟨⟨x.val, x.prop.1⟩, x.prop⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      exact Nat.card_congr e
    obtain ⟨k, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hcard_eq ▸ hAcard : Nat.card (A.subgroupOf K) ∣ 2 ^ 6)
    exact IsPGroup.of_card hk.2
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  refine ⟨P, ?_⟩
  apply le_antisymm
  · have hPmap_p : IsPGroup 2 ((P : Subgroup K).map K.subtype) := P.isPGroup'.map K.subtype
    obtain ⟨Q, hPQ⟩ := hPmap_p.exists_le_sylow
    obtain ⟨Q0, hCMQ0⟩ := (C_unipotent_is_sylow2 hM ht).1.exists_le_sylow
    have hQ0eq : (Q0 : Subgroup G) = C M := (C_unipotent_is_sylow2 hM ht).2 Q0 hCMQ0
    have htrans : ∃ g : G, g • Q0 = Q := by
      have := Sylow.orbit_eq_top Q0
      have hmem : Q ∈ MulAction.orbit G Q0 := by rw [this]; trivial
      exact hmem
    obtain ⟨g, hg⟩ := htrans
    have hQeq : (Q : Subgroup G) = C (g * M * g⁻¹) := by
      rw [← hg, Sylow.coe_subgroup_smul, ← conj_C, ← hQ0eq]
      rfl
    have hMinQ : M ∈ (Q : Subgroup G) := by
      apply hPQ
      refine ⟨⟨M, hMK⟩, hAP ⟨hMK, rfl⟩, rfl⟩
    rw [hQeq] at hMinQ
    have hgMne : g * M * g⁻¹ ≠ 1 := by
      intro h0; apply hM
      calc M = g⁻¹ * (g * M * g⁻¹) * g := by group
        _ = 1 := by rw [h0]; group
    have hCeq : C (g * M * g⁻¹) = C M := (C_eq_of_mem hgMne hM hMinQ).symm
    intro x hx
    have hxK : x ∈ K := by rcases hx with ⟨y, _, rfl⟩; exact y.prop
    have hxC : x ∈ C M := by rw [← hCeq, ← hQeq]; exact hPQ hx
    exact ⟨hxK, hxC⟩
  · intro x hx
    exact ⟨⟨x, hx.1⟩, hAP hx, rfl⟩

lemma unipotent_conj_in_K {K : Subgroup G} {M1 M2 : G}
    (hM1 : M1 ≠ 1) (hM1K : M1 ∈ K) (ht1 : tr M1 = 0)
    (hM2 : M2 ≠ 1) (hM2K : M2 ∈ K) (ht2 : tr M2 = 0) :
    ∃ k : K, (K ⊓ C M1).map (MulAut.conj (k : G)).toMonoidHom = K ⊓ C M2 := by
  obtain ⟨P1, hP1⟩ := unipotent_inf_is_sylow2 hM1 hM1K ht1
  obtain ⟨P2, hP2⟩ := unipotent_inf_is_sylow2 hM2 hM2K ht2
  have hmem : P2 ∈ MulAction.orbit K P1 := by rw [Sylow.orbit_eq_top P1]; trivial
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  rw [← hP1, ← hP2, ← hk, Sylow.coe_subgroup_smul]
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype,
    Subgroup.pointwise_smul_def]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨k * z * k⁻¹, ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, ⟨z, hz, rfl⟩, rfl⟩

lemma arith_two_orbits {K a1 n1 a2 : ℕ}
    (hK6 : 6 ∣ K) (hKG : K ∣ 262080)
    (ha1 : a1 = 2 ∨ a1 = 4 ∨ a1 = 8 ∨ a1 = 16 ∨ a1 = 32 ∨ a1 = 64)
    (ha1K : a1 ∣ K) (h2a1K : ¬ (2 * a1 ∣ K))
    (hn1 : n1 ∣ 63) (hn1a1 : n1 ∣ a1 - 1) (ha1n1lt : a1 * n1 < K) (ha1n1K : a1 * n1 ∣ K)
    (ha2 : a2 = 3 ∨ a2 = 9 ∨ a2 = 21 ∨ a2 = 63) (ha2K : 2 * a2 ∣ K)
    (heq : (K - 1 : ℚ) / K = (a1 - 1 : ℚ) / (n1 * a1) + (a2 - 1 : ℚ) / (2 * a2)) :
    (K = 6 ∧ a2 = 3) ∨ (K = 18 ∧ a2 = 9) ∨ (K = 42 ∧ a2 = 21) ∨ (K = 126 ∧ a2 = 63) := by
  have hn1_mem : n1 ∈ [1, 3, 7, 9, 21, 63] := mem_divs_63 hn1
  have ha1_mem : a1 ∈ [2, 4, 8, 16, 32, 64] := by rcases ha1 with rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  have ha2_mem : a2 ∈ [3, 9, 21, 63] := by rcases ha2 with rfl|rfl|rfl|rfl <;> simp
  have hKpos : 0 < K := Nat.pos_of_dvd_of_pos hKG (by norm_num)
  have ha1pos : 0 < a1 := by rcases ha1 with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have hn1pos : 0 < n1 := Nat.pos_of_dvd_of_pos hn1 (by norm_num)
  have ha2pos : 0 < a2 := by rcases ha2 with rfl|rfl|rfl|rfl <;> omega
  let den := n1 * a1 * (2 * a2)
  let num := (a1 - 1) * (2 * a2) + (a2 - 1) * (n1 * a1)
  have hden_pos : 0 < den := by positivity
  have hnat : (K - 1) * den = K * num := by
    have hq : ((K - 1 : ℕ) : ℚ) * (den : ℚ) = (K : ℚ) * (num : ℚ) := by
      have hK0 : (K : ℚ) ≠ 0 := by positivity
      have h10 : (n1 : ℚ) * (a1 : ℚ) ≠ 0 := by positivity
      have h20 : (2 : ℚ) * (a2 : ℚ) ≠ 0 := by positivity
      have hsubK : ((K - 1 : ℕ) : ℚ) = (K : ℚ) - 1 := Nat.cast_sub (by omega)
      have hsub1 : ((a1 - 1 : ℕ) : ℚ) = (a1 : ℚ) - 1 := Nat.cast_sub (by omega)
      have hsub2 : ((a2 - 1 : ℕ) : ℚ) = (a2 : ℚ) - 1 := Nat.cast_sub (by omega)
      simp only [den, num, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, hsubK, hsub1, hsub2]
      field_simp at heq
      linarith
    exact_mod_cast hq
  have hnum_lt : num < den := by
    have hlt : K * num < K * den := by
      rw [← hnat]; exact Nat.mul_lt_mul_of_pos_right (by omega) hden_pos
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hgap_pos : 0 < den - num := by omega
  have hKgap : K * (den - num) = den := by
    have : K * den - den = K * num := by
      rw [Nat.sub_mul, one_mul] at hnat; exact hnat
    zify [show num ≤ den by omega, show den ≤ K * den by nlinarith] at this ⊢
    linarith
  have hdiv : den % (den - num) = 0 := Nat.mod_eq_zero_of_dvd ⟨K, by linarith⟩
  have hKeq : K = den / (den - num) := by
    calc K = K * (den - num) / (den - num) := (Nat.mul_div_cancel K hgap_pos).symm
      _ = den / (den - num) := by rw [hKgap]
  rw [hKeq]
  exact checkTwoOrbits_spec a1 ha1_mem n1 hn1_mem a2 ha2_mem
    (Nat.mod_eq_zero_of_dvd hn1a1) hnum_lt hdiv
    (by rw [← hKeq]; exact Nat.mod_eq_zero_of_dvd hK6)
    (by rw [← hKeq]; exact Nat.mod_eq_zero_of_dvd hKG)
    (by rw [← hKeq]; exact Nat.mod_eq_zero_of_dvd ha1K)
    (by rw [← hKeq]; exact fun h => h2a1K (Nat.dvd_of_mod_eq_zero h))
    (by rw [← hKeq]; exact ha1n1lt)
    (by rw [← hKeq]; exact Nat.mod_eq_zero_of_dvd ha1n1K)
    (by rw [← hKeq]; exact Nat.mod_eq_zero_of_dvd ha2K)

lemma arith_three_orbits {K a1 n1 a2 a3 n3 : ℕ}
    (hK6 : 6 ∣ K) (hKG : K ∣ 262080)
    (ha1 : a1 = 2 ∨ a1 = 4 ∨ a1 = 8 ∨ a1 = 16 ∨ a1 = 32 ∨ a1 = 64)
    (ha1K : a1 ∣ K) (h2a1K : ¬ (2 * a1 ∣ K))
    (hn1 : n1 ∣ 63) (hn1a1 : n1 ∣ a1 - 1) (ha1n1lt : a1 * n1 < K) (ha1n1K : a1 * n1 ∣ K)
    (ha2 : a2 = 3 ∨ a2 = 9 ∨ a2 = 21 ∨ a2 = 63) (ha2K : 2 * a2 ∣ K)
    (ha3 : (a3 ∣ 63 ∨ a3 ∣ 65) ∧ 3 ≤ a3) (hn3 : n3 = 1 ∨ n3 = 2) (ha3K : n3 * a3 ∣ K)
    (heq : (K - 1 : ℚ) / K = (a1 - 1 : ℚ) / (n1 * a1) + (a2 - 1 : ℚ) / (2 * a2) +
           (a3 - 1 : ℚ) / (n3 * a3)) :
    (K = 60 ∧ a2 = 3 ∧ a3 = 5) ∨ (K = 504 ∧ a2 = 9 ∧ a3 = 7) ∨ K = 262080 := by
  have hn1_mem : n1 ∈ [1, 3, 7, 9, 21, 63] := mem_divs_63 hn1
  have ha1_mem : a1 ∈ [2, 4, 8, 16, 32, 64] := by rcases ha1 with rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  have ha2_mem : a2 ∈ [3, 9, 21, 63] := by rcases ha2 with rfl|rfl|rfl|rfl <;> simp
  have ha3_mem : a3 ∈ [3, 7, 9, 21, 63, 5, 13, 65] := mem_divs_63_or_65 ha3
  have hn3_mem : n3 ∈ [1, 2] := by rcases hn3 with rfl|rfl <;> simp
  have hKpos : 0 < K := Nat.pos_of_dvd_of_pos hKG (by norm_num)
  have ha1pos : 0 < a1 := by rcases ha1 with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  have hn1pos : 0 < n1 := Nat.pos_of_dvd_of_pos hn1 (by norm_num)
  have ha2pos : 0 < a2 := by rcases ha2 with rfl|rfl|rfl|rfl <;> omega
  have ha3pos : 0 < a3 := by omega
  have hn3pos : 0 < n3 := by omega
  let den := n1 * a1 * (2 * a2) * (n3 * a3)
  let num := (a1 - 1) * (2 * a2) * (n3 * a3) + (a2 - 1) * (n1 * a1) * (n3 * a3) +
             (a3 - 1) * (n1 * a1) * (2 * a2)
  have hden_pos : 0 < den := by positivity
  have hnat : (K - 1) * den = K * num := by
    have hq : ((K - 1 : ℕ) : ℚ) * (den : ℚ) = (K : ℚ) * (num : ℚ) := by
      have hK0 : (K : ℚ) ≠ 0 := by positivity
      have h10 : (n1 : ℚ) * (a1 : ℚ) ≠ 0 := by positivity
      have h20 : (2 : ℚ) * (a2 : ℚ) ≠ 0 := by positivity
      have h30 : (n3 : ℚ) * (a3 : ℚ) ≠ 0 := by positivity
      have hsubK : ((K - 1 : ℕ) : ℚ) = (K : ℚ) - 1 := Nat.cast_sub (by omega)
      have hsub1 : ((a1 - 1 : ℕ) : ℚ) = (a1 : ℚ) - 1 := Nat.cast_sub (by omega)
      have hsub2 : ((a2 - 1 : ℕ) : ℚ) = (a2 : ℚ) - 1 := Nat.cast_sub (by omega)
      have hsub3 : ((a3 - 1 : ℕ) : ℚ) = (a3 : ℚ) - 1 := Nat.cast_sub (by omega)
      simp only [den, num, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, hsubK, hsub1, hsub2, hsub3]
      field_simp at heq
      linarith
    exact_mod_cast hq
  have hnum_lt : num < den := by
    have hlt : K * num < K * den := by
      rw [← hnat]; exact Nat.mul_lt_mul_of_pos_right (by omega) hden_pos
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hgap_pos : 0 < den - num := by omega
  have hKgap : K * (den - num) = den := by
    have : K * den - den = K * num := by
      rw [Nat.sub_mul, one_mul] at hnat; exact hnat
    zify [show num ≤ den by omega, show den ≤ K * den by nlinarith] at this ⊢
    linarith
  have hdiv : den % (den - num) = 0 := Nat.mod_eq_zero_of_dvd ⟨K, by linarith⟩
  have hKeq : K = den / (den - num) := by
    calc K = K * (den - num) / (den - num) := (Nat.mul_div_cancel K hgap_pos).symm
      _ = den / (den - num) := by rw [hKgap]
  rw [hKeq]
  exact checkThreeOrbits_spec a1 ha1_mem n1 hn1_mem a2 ha2_mem a3 ha3_mem n3 hn3_mem
    (Nat.mod_eq_zero_of_dvd hn1a1) hnum_lt hdiv
    (by rw [← hKeq]; exact Nat.mod_eq_zero_of_dvd hK6)
    (by rw [← hKeq]; exact Nat.mod_eq_zero_of_dvd hKG)
    (by rw [← hKeq]; exact Nat.mod_eq_zero_of_dvd ha1K)
    (by rw [← hKeq]; exact fun h => h2a1K (Nat.dvd_of_mod_eq_zero h))
    (by rw [← hKeq]; exact ha1n1lt)
    (by rw [← hKeq]; exact Nat.mod_eq_zero_of_dvd ha1n1K)
    (by rw [← hKeq]; exact Nat.mod_eq_zero_of_dvd ha2K)
    (by rw [← hKeq]; exact Nat.mod_eq_zero_of_dvd ha3K)

/-! ### Section 5: Trace polynomials and identification of all 7 overgroups of `H` -/

lemma pow_step_matrix (M : G) (k : ℕ) (p q : F64)
    (hk : (M : Matrix (Fin 2) (Fin 2) F64) ^ k = p • (M : Matrix (Fin 2) (Fin 2) F64) + q • 1) :
    (M : Matrix (Fin 2) (Fin 2) F64) ^ (k + 1) =
      (p * tr M + q) • (M : Matrix (Fin 2) (Fin 2) F64) + p • 1 := by
  have h2 := cayley_hamilton M
  calc (M : Matrix (Fin 2) (Fin 2) F64) ^ (k + 1)
      = (M : Matrix (Fin 2) (Fin 2) F64) ^ k * M := pow_succ _ k
    _ = (p • (M : Matrix (Fin 2) (Fin 2) F64) + q • 1) * M := by rw [hk]
    _ = p • ((M : Matrix (Fin 2) (Fin 2) F64) ^ 2) + q • M := by
        rw [add_mul, smul_mul_assoc, smul_mul_assoc, sq, one_mul]
    _ = p • (tr M • (M : Matrix (Fin 2) (Fin 2) F64) + 1) + q • M := by rw [h2]
    _ = (p * tr M + q) • (M : Matrix (Fin 2) (Fin 2) F64) + p • 1 := by
        rw [smul_add, smul_smul, add_smul]; abel

lemma pow_three_matrix (M : G) :
    (M : Matrix (Fin 2) (Fin 2) F64) ^ 3 =
      ((tr M) ^ 2 + 1) • (M : Matrix (Fin 2) (Fin 2) F64) +
      (tr M) • (1 : Matrix (Fin 2) (Fin 2) F64) := by
  have h3 := pow_step_matrix M 2 (tr M) 1 (by simpa using cayley_hamilton M)
  rw [h3]; congr 2; ring

lemma pow_five_matrix (M : G) :
    (M : Matrix (Fin 2) (Fin 2) F64) ^ 5 =
      ((tr M) ^ 4 + (tr M) ^ 2 + 1) • (M : Matrix (Fin 2) (Fin 2) F64) +
      ((tr M) ^ 3) • (1 : Matrix (Fin 2) (Fin 2) F64) := by
  have h4 := pow_step_matrix M 3 _ _ (pow_three_matrix M)
  have h4' : (M : Matrix (Fin 2) (Fin 2) F64) ^ 4 =
      ((tr M) ^ 3) • (M : Matrix (Fin 2) (Fin 2) F64) +
      ((tr M) ^ 2 + 1) • (1 : Matrix (Fin 2) (Fin 2) F64) := by
    rw [h4]; congr 2; linear_combination tr M * two_eq_zero_F64
  have h5 := pow_step_matrix M 4 _ _ h4'
  rw [h5]; congr 2; ring

lemma pow_seven_and_nine_matrix (M : G) :
    (M : Matrix (Fin 2) (Fin 2) F64) ^ 7 =
      ((tr M) ^ 6 + (tr M) ^ 4 + 1) • (M : Matrix (Fin 2) (Fin 2) F64) +
      ((tr M) ^ 5 + tr M) • (1 : Matrix (Fin 2) (Fin 2) F64) ∧
    (M : Matrix (Fin 2) (Fin 2) F64) ^ 9 =
      ((tr M) ^ 8 + (tr M) ^ 6 + (tr M) ^ 4 + 1) • (M : Matrix (Fin 2) (Fin 2) F64) +
      ((tr M) ^ 7) • (1 : Matrix (Fin 2) (Fin 2) F64) := by
  have h6 := pow_step_matrix M 5 _ _ (pow_five_matrix M)
  have h6' : (M : Matrix (Fin 2) (Fin 2) F64) ^ 6 =
      ((tr M) ^ 5 + tr M) • (M : Matrix (Fin 2) (Fin 2) F64) +
      ((tr M) ^ 4 + (tr M) ^ 2 + 1) • 1 := by
    rw [h6]; congr 2; linear_combination (tr M) ^ 3 * two_eq_zero_F64
  have h7 := pow_step_matrix M 6 _ _ h6'
  have h7' : (M : Matrix (Fin 2) (Fin 2) F64) ^ 7 =
      ((tr M) ^ 6 + (tr M) ^ 4 + 1) • (M : Matrix (Fin 2) (Fin 2) F64) +
      ((tr M) ^ 5 + tr M) • 1 := by
    rw [h7]; congr 2; linear_combination (tr M) ^ 2 * two_eq_zero_F64
  have h8 := pow_step_matrix M 7 _ _ h7'
  have h8' : (M : Matrix (Fin 2) (Fin 2) F64) ^ 8 =
      ((tr M) ^ 7) • (M : Matrix (Fin 2) (Fin 2) F64) +
      ((tr M) ^ 6 + (tr M) ^ 4 + 1) • 1 := by
    rw [h8]; congr 2; linear_combination ((tr M) ^ 5 + tr M) * two_eq_zero_F64
  have h9 := pow_step_matrix M 8 _ _ h8'
  have h9' : (M : Matrix (Fin 2) (Fin 2) F64) ^ 9 =
      ((tr M) ^ 8 + (tr M) ^ 6 + (tr M) ^ 4 + 1) • (M : Matrix (Fin 2) (Fin 2) F64) +
      ((tr M) ^ 7) • 1 := by
    rw [h9]; congr 2; ring
  exact ⟨h7', h9'⟩

lemma coe_pow_G (M : G) (n : ℕ) :
    ((M ^ n : G) : Matrix (Fin 2) (Fin 2) F64) = (M : Matrix (Fin 2) (Fin 2) F64) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]

lemma tr_pow_four_of_pow_eq_one {M : G} (h : M ^ 2 = 1 ∨ M ^ 3 = 1 ∨ M ^ 5 = 1) :
    (tr M) ^ 4 = tr M := by
  by_cases hM : M = 1
  · rw [hM, tr_one]; norm_num
  rcases h with h2 | h3 | h5
  · have ht : tr M = 0 := (sq_eq_one_iff_tr_eq_zero M).mp (by simpa [sq] using h2)
    rw [ht]; norm_num
  · have hm : (M : Matrix (Fin 2) (Fin 2) F64) ^ 3 = 1 := by
      rw [← coe_pow_G, h3]; rfl
    have h0 : (tr M + 1) • (1 : Matrix (Fin 2) (Fin 2) F64) +
        ((tr M) ^ 2 + 1) • (M : Matrix (Fin 2) (Fin 2) F64) = 0 := by
      ext i j
      have hij := congrFun (congrFun (hm.symm.trans (pow_three_matrix M)) i) j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hij ⊢
      linear_combination -hij + (1 : Matrix (Fin 2) (Fin 2) F64) i j * two_eq_zero_F64
    have ht1 : tr M + 1 = 0 := (linear_indep_one_M hM h0).1
    have ht : tr M = 1 := eq_of_add_eq_zero_F64 ht1
    rw [ht]; norm_num
  · have hm : (M : Matrix (Fin 2) (Fin 2) F64) ^ 5 = 1 := by
      rw [← coe_pow_G, h5]; rfl
    have h0 : ((tr M) ^ 3 + 1) • (1 : Matrix (Fin 2) (Fin 2) F64) +
        ((tr M) ^ 4 + (tr M) ^ 2 + 1) • (M : Matrix (Fin 2) (Fin 2) F64) = 0 := by
      ext i j
      have hij := congrFun (congrFun (hm.symm.trans (pow_five_matrix M)) i) j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hij ⊢
      linear_combination -hij + (1 : Matrix (Fin 2) (Fin 2) F64) i j * two_eq_zero_F64
    have ht3 : (tr M) ^ 3 + 1 = 0 := (linear_indep_one_M hM h0).1
    have ht3' : (tr M) ^ 3 = 1 := eq_of_add_eq_zero_F64 ht3
    calc (tr M) ^ 4 = (tr M) ^ 3 * tr M := by ring
      _ = tr M := by rw [ht3', one_mul]

lemma poly8_of_poly6_F64 (t : F64) (hp : t ^ 6 + t ^ 4 + 1 = 0) : t ^ 8 = t := by
  have hsq : (t ^ 3 + t ^ 2 + 1) ^ 2 = 0 := by
    rw [add_sq_F64, add_sq_F64, one_pow]
    have h1 : (t ^ 3) ^ 2 = t ^ 6 := by ring
    have h2 : (t ^ 2) ^ 2 = t ^ 4 := by ring
    rw [h1, h2]; exact hp
  have hg : t ^ 3 + t ^ 2 + 1 = 0 := eq_zero_of_pow_eq_zero hsq
  have h8 : t ^ 8 + t = 0 := by
    have hid : t ^ 8 + t = (t ^ 5 + t ^ 4 + t ^ 3 + t) * (t ^ 3 + t ^ 2 + 1) -
        (2 : F64) * (t ^ 7 + t ^ 6 + t ^ 5 + t ^ 4 + t ^ 3) := by ring
    rw [hid, hg, two_eq_zero_F64]; ring
  exact eq_of_add_eq_zero_F64 h8

lemma tr_pow_eight_of_pow_eq_one {M : G} (h : M ^ 2 = 1 ∨ M ^ 7 = 1 ∨ M ^ 9 = 1) :
    (tr M) ^ 8 = tr M := by
  by_cases hM : M = 1
  · rw [hM, tr_one]; norm_num
  rcases h with h2 | h7 | h9
  · have ht : tr M = 0 := (sq_eq_one_iff_tr_eq_zero M).mp (by simpa [sq] using h2)
    rw [ht]; norm_num
  · have hm : (M : Matrix (Fin 2) (Fin 2) F64) ^ 7 = 1 := by
      rw [← coe_pow_G, h7]; rfl
    have h0 : ((tr M) ^ 5 + tr M + 1) • (1 : Matrix (Fin 2) (Fin 2) F64) +
        ((tr M) ^ 6 + (tr M) ^ 4 + 1) • (M : Matrix (Fin 2) (Fin 2) F64) = 0 := by
      ext i j
      have hij := congrFun (congrFun (hm.symm.trans (pow_seven_and_nine_matrix M).1) i) j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hij ⊢
      linear_combination -hij + (1 : Matrix (Fin 2) (Fin 2) F64) i j * two_eq_zero_F64
    have hp7 : (tr M) ^ 6 + (tr M) ^ 4 + 1 = 0 := (linear_indep_one_M hM h0).2
    exact poly8_of_poly6_F64 (tr M) hp7
  · have hm : (M : Matrix (Fin 2) (Fin 2) F64) ^ 9 = 1 := by
      rw [← coe_pow_G, h9]; rfl
    have h0 : ((tr M) ^ 7 + 1) • (1 : Matrix (Fin 2) (Fin 2) F64) +
        ((tr M) ^ 8 + (tr M) ^ 6 + (tr M) ^ 4 + 1) • (M : Matrix (Fin 2) (Fin 2) F64) = 0 := by
      ext i j
      have hij := congrFun (congrFun (hm.symm.trans (pow_seven_and_nine_matrix M).2) i) j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hij ⊢
      linear_combination -hij + (1 : Matrix (Fin 2) (Fin 2) F64) i j * two_eq_zero_F64
    have ht7 : (tr M) ^ 7 + 1 = 0 := (linear_indep_one_M hM h0).1
    have ht7' : (tr M) ^ 7 = 1 := eq_of_add_eq_zero_F64 ht7
    calc (tr M) ^ 8 = (tr M) ^ 7 * tr M := by ring
      _ = tr M := by rw [ht7', one_mul]

lemma tr_diagMat_mul (u : F64ˣ) (M : G) :
    tr (diagMat u * M) = (u : F64) * M 0 0 + ((u⁻¹ : F64ˣ) : F64) * M 1 1 := by
  simp only [tr, Matrix.SpecialLinearGroup.coe_mul]
  simp [diagMat, Matrix.mul_apply, Fin.sum_univ_two]

lemma τ_mul_00 (M : G) : (τ * M) 0 0 = M 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [τ, antiMat, Matrix.mul_apply, Fin.sum_univ_two]

lemma τ_mul_11 (M : G) : (τ * M) 1 1 = M 0 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  simp [τ, antiMat, Matrix.mul_apply, Fin.sum_univ_two]

lemma le_SL2F4_of_tr_pow_four {K : Subgroup G} (hHK : H ≤ K)
    (htr : ∀ M ∈ K, (tr M) ^ 4 = tr M) : K ≤ SL2F4 := by
  have hdiag : ∀ M ∈ K, M 0 0 ^ 4 = M 0 0 ∧ M 1 1 ^ 4 = M 1 1 := by
    intro M hMK
    have h1 := htr M hMK
    have h2 := htr (C3 * M) (K.mul_mem (hHK C3_mem_H) hMK)
    have htr1 : tr M = M 0 0 + M 1 1 := rfl
    have htr2 : tr (C3 * M) = (ω : F64) * M 0 0 + ((ω⁻¹ : F64ˣ) : F64) * M 1 1 := tr_diagMat_mul ω M
    rw [htr1, add_pow_four_F64] at h1
    rw [htr2, add_pow_four_F64, mul_pow, mul_pow] at h2
    have hω4 : (ω : F64) ^ 4 = (ω : F64) := by
      have h3 : (ω : F64) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ω_pow_three, Units.val_one]
      calc (ω : F64) ^ 4 = (ω : F64) ^ 3 * (ω : F64) := by ring
        _ = (ω : F64) := by rw [h3, one_mul]
    have hωi4 : ((ω⁻¹ : F64ˣ) : F64) ^ 4 = ((ω⁻¹ : F64ˣ) : F64) := by
      have h3u : (ω⁻¹ : F64ˣ) ^ 3 = 1 := by rw [inv_pow, ω_pow_three, inv_one]
      have h3 : ((ω⁻¹ : F64ˣ) : F64) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3u, Units.val_one]
      calc ((ω⁻¹ : F64ˣ) : F64) ^ 4 = ((ω⁻¹ : F64ˣ) : F64) ^ 3 * ((ω⁻¹ : F64ˣ) : F64) := by ring
        _ = ((ω⁻¹ : F64ˣ) : F64) := by rw [h3, one_mul]
    rw [hω4, hωi4] at h2
    have ha_eq_d : M 0 0 ^ 4 + M 0 0 = M 1 1 ^ 4 + M 1 1 := by
      linear_combination h1 + (M 0 0 - M 1 1 ^ 4) * two_eq_zero_F64
    have hsum : (ω : F64) * (M 0 0 ^ 4 + M 0 0) + ((ω⁻¹ : F64ˣ) : F64) * (M 1 1 ^ 4 + M 1 1) = 0 := by
      linear_combination h2 + ((ω : F64) * M 0 0 + ((ω⁻¹ : F64ˣ) : F64) * M 1 1) * two_eq_zero_F64
    rw [← ha_eq_d, ← add_mul, ω_add_ω_inv, one_mul] at hsum
    have h00 : M 0 0 ^ 4 = M 0 0 := eq_of_add_eq_zero_F64 hsum
    have h11 : M 1 1 ^ 4 = M 1 1 := eq_of_add_eq_zero_F64 (by rw [← ha_eq_d, hsum])
    exact ⟨h00, h11⟩
  intro M hMK
  obtain ⟨h00, h11⟩ := hdiag M hMK
  obtain ⟨h10, h01⟩ := hdiag (τ * M) (K.mul_mem (hHK τ_mem_H) hMK)
  rw [τ_mul_00] at h10
  rw [τ_mul_11] at h01
  exact ⟨h00, h01, h10, h11⟩

lemma le_SU2F8_of_tr_pow_eight {K : Subgroup G} (hHK : H ≤ K) (hη : diagMat η ∈ K)
    (htr : ∀ M ∈ K, (tr M) ^ 8 = tr M) : K ≤ SU2F8 := by
  have hdiag : ∀ M ∈ K, M 1 1 = M 0 0 ^ 8 := by
    intro M hMK
    have h1 := htr M hMK
    have h2 := htr (diagMat η * M) (K.mul_mem hη hMK)
    have htr1 : tr M = M 0 0 + M 1 1 := rfl
    have htr2 : tr (diagMat η * M) = (η : F64) * M 0 0 + ((η⁻¹ : F64ˣ) : F64) * M 1 1 := tr_diagMat_mul η M
    rw [htr1, add_pow_eight_F64] at h1
    rw [htr2, add_pow_eight_F64, mul_pow, mul_pow] at h2
    have hη8 : (η : F64) ^ 8 = ((η⁻¹ : F64ˣ) : F64) := by
      have : η ^ 8 = η⁻¹ := by
        apply mul_left_cancel (a := η)
        rw [mul_inv_cancel, ← pow_succ', η_pow_nine]
      rw [← Units.val_pow_eq_pow_val, this]
    have hηi8 : ((η⁻¹ : F64ˣ) : F64) ^ 8 = (η : F64) := by
      have : (η⁻¹) ^ 8 = η := by
        apply mul_left_cancel (a := η⁻¹)
        rw [inv_mul_cancel, ← pow_succ', inv_pow, η_pow_nine, inv_one]
      rw [← Units.val_pow_eq_pow_val, this]
    rw [hη8, hηi8] at h2
    have heq : M 0 0 + M 1 1 ^ 8 = M 1 1 + M 0 0 ^ 8 := by
      linear_combination -h1 + (M 1 1 ^ 8 - M 1 1) * two_eq_zero_F64
    have hsum : (η : F64) * (M 0 0 + M 1 1 ^ 8) + ((η⁻¹ : F64ˣ) : F64) * (M 1 1 + M 0 0 ^ 8) = 0 := by
      linear_combination h2 + ((η : F64) * M 0 0 + ((η⁻¹ : F64ˣ) : F64) * M 1 1) * two_eq_zero_F64
    rw [heq, ← add_mul] at hsum
    have h0 := (mul_eq_zero.mp hsum).resolve_left η_add_η_inv_ne_zero
    exact eq_of_add_eq_zero_F64 h0
  intro M hMK
  have h11 := hdiag M hMK
  have h10 := hdiag (τ * M) (K.mul_mem (hHK τ_mem_H) hMK)
  rw [τ_mul_00, τ_mul_11] at h10
  refine ⟨h11, ?_⟩
  calc M 1 0 = M 1 0 ^ 64 := (pow_64_F64 _).symm
    _ = (M 1 0 ^ 8) ^ 8 := by ring
    _ = M 0 1 ^ 8 := by rw [← h10]

lemma eq_monomial_of_le_D126 {K : Subgroup G} (hHK : H ≤ K) (hKD : K ≤ D126)
    {d : ℕ} (hd : d ∣ 63) (hcard : Nat.card K = 2 * d) :
    K = monomialSubgroup (unitSubgroup d) := by
  have hle : K ≤ monomialSubgroup (unitSubgroup d) := by
    intro M hMK
    have hU : ∀ u : F64ˣ, diagMat u ∈ K → u ∈ unitSubgroup d := by
      intro u huK
      show u ^ d = 1
      let D : Subgroup G := K ⊓ C C3
      have hDcard : Nat.card D = d := by
        let f : Bool × D → K := fun p =>
          match p with
          | (false, x) => ⟨x.val, x.prop.1⟩
          | (true, x) => ⟨τ * x.val, K.mul_mem (hHK τ_mem_H) x.prop.1⟩
        have hbij : Function.Bijective f := by
          refine ⟨?_, ?_⟩
          · rintro ⟨b1, x1⟩ ⟨b2, x2⟩ h
            have hv : (f (b1, x1)).val = (f (b2, x2)).val := congrArg Subtype.val h
            cases b1 <;> cases b2 <;> simp only [f] at hv
            · exact Prod.ext rfl (Subtype.ext hv)
            · exfalso
              obtain ⟨u1, hu1⟩ := (C_C3_eq_diag x1.val).mp x1.prop.2
              obtain ⟨u2, hu2⟩ := (C_C3_eq_diag x2.val).mp x2.prop.2
              rw [hu1, hu2, τ, antiMat_mul_diagMat] at hv
              exact diagMat_ne_antiMat _ _ hv
            · exfalso
              obtain ⟨u1, hu1⟩ := (C_C3_eq_diag x1.val).mp x1.prop.2
              obtain ⟨u2, hu2⟩ := (C_C3_eq_diag x2.val).mp x2.prop.2
              rw [hu1, hu2, τ, antiMat_mul_diagMat] at hv
              exact diagMat_ne_antiMat _ _ hv.symm
            · exact Prod.ext rfl (Subtype.ext (mul_left_cancel hv))
          · rintro ⟨X, hXK⟩
            rcases hKD hXK with ⟨v, _, rfl | rfl⟩
            · exact ⟨(false, ⟨diagMat v, hXK, (C_C3_eq_diag _).mpr ⟨v, rfl⟩⟩), rfl⟩
            · have hτX : τ * antiMat v = diagMat v⁻¹ := by
                simp [τ, antiMat_mul_antiMat]
              have hmem : diagMat v⁻¹ ∈ D := by
                refine ⟨?_, (C_C3_eq_diag _).mpr ⟨v⁻¹, rfl⟩⟩
                rw [← hτX]; exact K.mul_mem (hHK τ_mem_H) hXK
              refine ⟨(true, ⟨diagMat v⁻¹, hmem⟩), Subtype.ext ?_⟩
              simp [f, τ, antiMat_mul_diagMat]
        have hc := Nat.card_congr (Equiv.ofBijective f hbij)
        let _ : Fintype D := Fintype.ofFinite D
        rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_bool,
          ← Nat.card_eq_fintype_card] at hc
        omega
      let _ : Fintype D := Fintype.ofFinite D
      have huD : diagMat u ∈ D := ⟨huK, (C_C3_eq_diag _).mpr ⟨u, rfl⟩⟩
      have hpow : (⟨diagMat u, huD⟩ : D) ^ Fintype.card D = 1 := pow_card_eq_one
      rw [← Nat.card_eq_fintype_card, hDcard] at hpow
      have hpowG : (diagMat u) ^ d = 1 := congrArg Subtype.val hpow
      have hdm : ∀ n : ℕ, (diagMat u) ^ n = diagMat (u ^ n) := by
        intro n; induction n with
        | zero => simp [diagMat_one]
        | succ n ih => rw [pow_succ, pow_succ, ih, diagMat_mul]
      rw [hdm] at hpowG
      exact diagMat_inj (hpowG.trans diagMat_one.symm)
    rcases hKD hMK with ⟨u, _, rfl | rfl⟩
    · exact ⟨u, hU u hMK, Or.inl rfl⟩
    · have hτM : τ * antiMat u = diagMat u⁻¹ := by simp [τ, antiMat_mul_antiMat]
      have huinv : u⁻¹ ∈ unitSubgroup d := hU u⁻¹ (by rw [← hτM]; exact K.mul_mem (hHK τ_mem_H) hMK)
      have hu : u ∈ unitSubgroup d := by
        have := (unitSubgroup d).inv_mem huinv; simpa using this
      exact ⟨u, hu, Or.inr rfl⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_monomialSubgroup, card_unitSubgroup hd, hcard]

set_option maxHeartbeats 800000 in
lemma classify_overgroup (K : Subgroup G) (hHK : H ≤ K) :
    K = H ∨ K = D42 ∨ K = D18 ∨ K = D126 ∨ K = SU2F8 ∨ K = SL2F4 ∨ K = ⊤ := by
  let _ : Fintype G := Fintype.ofFinite G
  let _ : Fintype K := Fintype.ofFinite K
  let conjK : K → Subgroup G → Subgroup G :=
    fun k A => A.map (MulAut.conj (k : G)).toMonoidHom
  have hconj_one : ∀ A : Subgroup G, conjK 1 A = A := fun A => by
    ext x; simp [conjK]
  have hconj_mul : ∀ (k1 k2 : K) (A : Subgroup G), conjK (k1 * k2) A = conjK k1 (conjK k2 A) := by
    intro k1 k2 A; ext x
    simp only [conjK, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_mul]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(k2 : G) * y * (k2 : G)⁻¹, ⟨y, hy, rfl⟩, ?_⟩
      group
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by group⟩
  have hconj_inf : ∀ (k : K) (M : G), conjK k (K ⊓ C M) = K ⊓ C ((k : G) * M * (k : G)⁻¹) := by
    intro k M; ext x
    simp only [conjK, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.mem_inf, ← conj_C]
    constructor
    · rintro ⟨y, ⟨hyK, hyC⟩, rfl⟩
      exact ⟨K.mul_mem (K.mul_mem k.prop hyK) (K.inv_mem k.prop), ⟨y, hyC, rfl⟩⟩
    · rintro ⟨hxK, ⟨y, hyC, rfl⟩⟩
      refine ⟨y, ⟨?_, hyC⟩, rfl⟩
      have : y = (k : G)⁻¹ * ((k : G) * y * (k : G)⁻¹) * (k : G) := by group
      rw [this]; exact K.mul_mem (K.mul_mem (K.inv_mem k.prop) hxK) k.prop
  let K_ne1 : Finset G := Finset.univ.filter (fun M : G => M ∈ K ∧ M ≠ 1)
  let TI : Finset (Subgroup G) := K_ne1.image (fun M => K ⊓ C M)
  have hTI_cl : ∀ (k : K), ∀ A ∈ TI, conjK k A ∈ TI := by
    intro k A hA
    rcases Finset.mem_image.mp hA with ⟨M, hM, rfl⟩
    have hM' := (Finset.mem_filter.mp hM).2
    rw [hconj_inf]
    refine Finset.mem_image.mpr ⟨(k : G) * M * (k : G)⁻¹, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      K.mul_mem (K.mul_mem k.prop hM'.1) (K.inv_mem k.prop), ?_⟩, rfl⟩
    intro h0; apply hM'.2
    calc M = (k : G)⁻¹ * ((k : G) * M * (k : G)⁻¹) * (k : G) := by group
      _ = 1 := by rw [h0]; group
  let _ : MulAction K TI :=
    { smul := fun k A => ⟨conjK k A.val, hTI_cl k A.val A.prop⟩
      one_smul := fun A => Subtype.ext (hconj_one A.val)
      mul_smul := fun k1 k2 A => Subtype.ext (hconj_mul k1 k2 A.val) }
  have hpart : K_ne1.card = ∑ A ∈ TI, (Nat.card A - 1) := by
    have hbi : K_ne1 = TI.biUnion (fun A => Finset.univ.filter (fun M : G => M ∈ A ∧ M ≠ 1)) := by
      ext M
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, K_ne1]
      constructor
      · intro ⟨hMK, hMne⟩
        exact ⟨K ⊓ C M, Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMK, hMne⟩, rfl⟩,
          ⟨hMK, rfl⟩, hMne⟩
      · rintro ⟨A, hA, hMA, hMne⟩
        rcases Finset.mem_image.mp hA with ⟨N, _, rfl⟩
        exact ⟨hMA.1, hMne⟩
    have hdisj : (TI : Set (Subgroup G)).PairwiseDisjoint
        (fun A => Finset.univ.filter (fun M : G => M ∈ A ∧ M ≠ 1)) := by
      intro A1 hA1 A2 hA2 hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro M h1 h2
      rcases Finset.mem_image.mp hA1 with ⟨N1, hN1, rfl⟩
      rcases Finset.mem_image.mp hA2 with ⟨N2, hN2, rfl⟩
      have hN1' := (Finset.mem_filter.mp hN1).2
      have hN2' := (Finset.mem_filter.mp hN2).2
      have hM1 := (Finset.mem_filter.mp h1).2
      have hM2 := (Finset.mem_filter.mp h2).2
      have hC1 : C M = C N1 := C_eq_of_mem hN1'.2 hM1.2 hM1.1.2
      have hC2 : C M = C N2 := C_eq_of_mem hN2'.2 hM2.2 hM2.1.2
      exact hne (by rw [← hC1, hC2])
    rw [hbi, Finset.card_biUnion hdisj]
    refine Finset.sum_congr rfl fun A _ => ?_
    have eA : {x : G // x ∈ A ∧ x ≠ 1} ≃ {x : A // x ≠ 1} :=
      { toFun := fun ⟨x, hx1, hx2⟩ => ⟨⟨x, hx1⟩, fun h => hx2 (congrArg Subtype.val h)⟩
        invFun := fun ⟨⟨x, hx⟩, hne⟩ => ⟨x, hx, fun h => hne (Subtype.ext h)⟩
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    let _ : Fintype A := Fintype.ofFinite A
    rw [← Fintype.card_subtype, Fintype.card_congr eA]
    have hopt : Option {x : A // x ≠ 1} ≃ A :=
      { toFun := fun o => match o with | none => 1 | some x => x.val
        invFun := fun x => if h : x = 1 then none else some ⟨x, h⟩
        left_inv := fun o => by cases o with | none => simp | some x => simp [x.prop]
        right_inv := fun x => by by_cases h : x = 1 <;> simp [h] }
    have hc := Fintype.card_congr hopt
    rw [Fintype.card_option, ← Nat.card_eq_fintype_card (α := A)] at hc
    omega
  have hKne1_card : K_ne1.card = Nat.card K - 1 := by
    have eK : {x : G // x ∈ K ∧ x ≠ 1} ≃ {x : K // x ≠ 1} :=
      { toFun := fun ⟨x, hx1, hx2⟩ => ⟨⟨x, hx1⟩, fun h => hx2 (congrArg Subtype.val h)⟩
        invFun := fun ⟨⟨x, hx⟩, hne⟩ => ⟨x, hx, fun h => hne (Subtype.ext h)⟩
        left_inv := fun ⟨_, _, _⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    rw [← Fintype.card_subtype, Fintype.card_congr eK]
    have hopt : Option {x : K // x ≠ 1} ≃ K :=
      { toFun := fun o => match o with | none => 1 | some x => x.val
        invFun := fun x => if h : x = 1 then none else some ⟨x, h⟩
        left_inv := fun o => by cases o with | none => simp | some x => simp [x.prop]
        right_inv := fun x => by by_cases h : x = 1 <;> simp [h] }
    have hc := Fintype.card_congr hopt
    rw [Fintype.card_option, ← Nat.card_eq_fintype_card (α := K)] at hc
    omega
  let Orb := Quotient (MulAction.orbitRel K TI)
  let _ : Fintype Orb := Fintype.ofFinite Orb
  have hstab_eq : ∀ A : TI, Nat.card (MulAction.stabilizer K A) = Nat.card (normG A.val ⊓ K : Subgroup G) := by
    intro A
    have e : MulAction.stabilizer K A ≃ (normG A.val ⊓ K : Subgroup G) :=
      { toFun := fun ⟨k, hk⟩ => ⟨k.val, by
          have hk' : conjK k A.val = A.val := congrArg Subtype.val hk
          show (k : G) ∈ normG A.val
          rw [Subgroup.mem_normalizer_iff]
          intro h
          have : (k : G) * h * (k : G)⁻¹ ∈ conjK k A.val ↔ h ∈ A.val := by
            simp only [conjK, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
            exact ⟨fun ⟨y, hy, heq⟩ => by
              have : y = h := by
                calc y = (k : G)⁻¹ * ((k : G) * y * (k : G)⁻¹) * (k : G) := by group
                  _ = (k : G)⁻¹ * ((k : G) * h * (k : G)⁻¹) * (k : G) := by rw [heq]
                  _ = h := by group
              rwa [← this], fun hh => ⟨h, hh, rfl⟩⟩
          rw [hk'] at this; exact this.symm, k.prop⟩
        invFun := fun ⟨g, hg1, hg2⟩ => ⟨⟨g, hg2⟩, Subtype.ext (by
          change conjK ⟨g, hg2⟩ A.val = A.val
          ext x
          simp only [conjK, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          constructor
          · rintro ⟨y, hy, rfl⟩; exact (Subgroup.mem_normalizer_iff.mp hg1 y).mp hy
          · intro hx
            refine ⟨g⁻¹ * x * g, ?_, by group⟩
            have hconj : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
            exact (Subgroup.mem_normalizer_iff.mp hg1 (g⁻¹ * x * g)).mpr (by rwa [hconj]))⟩
        left_inv := fun ⟨_, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl }
    exact Nat.card_congr e
  let nIdx (A : TI) : ℕ := Nat.card (normG A.val ⊓ K : Subgroup G) / Nat.card A.val
  have hAdvdN : ∀ A : TI, Nat.card A.val ∣ Nat.card (normG A.val ⊓ K : Subgroup G) := fun A => by
    apply Subgroup.card_dvd_of_le
    intro x hx
    rcases Finset.mem_image.mp A.prop with ⟨M, _, hMA⟩
    exact ⟨Subgroup.le_normalizer hx, by rw [← hMA] at hx; exact hx.1⟩
  have hterm_orb : ∀ (A : TI),
      (∑ B ∈ Finset.univ.filter (fun B : TI => Quotient.mk (MulAction.orbitRel K TI) B = Quotient.mk _ A),
        ((Nat.card B.val - 1 : ℕ) : ℚ)) / (Nat.card K : ℚ) =
      ((Nat.card A.val - 1 : ℕ) : ℚ) / ((nIdx A : ℚ) * (Nat.card A.val : ℚ)) := by
    intro A
    have hcard_eq : ∀ B : TI, Quotient.mk (MulAction.orbitRel K TI) B = Quotient.mk _ A →
        Nat.card B.val = Nat.card A.val := by
      intro B hBA
      obtain ⟨k, hk⟩ := Quotient.exact hBA
      have hk' : conjK k A.val = B.val := congrArg Subtype.val hk
      rw [← hk']
      exact Nat.card_congr (MulAut.conj (k : G) |>.subgroupMap A.val).symm.toEquiv
    have hsum_eq : (∑ B ∈ Finset.univ.filter (fun B : TI => Quotient.mk (MulAction.orbitRel K TI) B = Quotient.mk _ A),
        ((Nat.card B.val - 1 : ℕ) : ℚ)) =
        ((Finset.univ.filter (fun B : TI => Quotient.mk (MulAction.orbitRel K TI) B = Quotient.mk _ A)).card : ℚ) *
        ((Nat.card A.val - 1 : ℕ) : ℚ) := by
      rw [Finset.sum_congr rfl (fun B hB => by rw [hcard_eq B (Finset.mem_filter.mp hB).2]),
        Finset.sum_const, nsmul_eq_mul]
    have hfib_card : (Finset.univ.filter (fun B : TI => Quotient.mk (MulAction.orbitRel K TI) B = Quotient.mk _ A)).card =
        Fintype.card (MulAction.orbit K A) := by
      rw [← Fintype.card_subtype]
      exact Fintype.card_congr
        { toFun := fun ⟨B, hB⟩ => ⟨B, Quotient.exact hB⟩
          invFun := fun ⟨B, hB⟩ => ⟨B, Quotient.sound hB⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    have horb_stab := MulAction.card_orbit_mul_card_stabilizer_eq_card_group K A
    rw [← Nat.card_eq_fintype_card (α := MulAction.stabilizer K A), hstab_eq A,
      ← Nat.card_eq_fintype_card (α := K)] at horb_stab
    have hNmul : nIdx A * Nat.card A.val = Nat.card (normG A.val ⊓ K : Subgroup G) :=
      Nat.div_mul_cancel (hAdvdN A)
    have hKeq : (Nat.card K : ℚ) =
        (Fintype.card (MulAction.orbit K A) : ℚ) * ((nIdx A : ℚ) * (Nat.card A.val : ℚ)) := by
      exact_mod_cast (by rw [← horb_stab, ← hNmul] : Nat.card K = Fintype.card (MulAction.orbit K A) * (nIdx A * Nat.card A.val))
    have hApos : (0 : ℚ) < Nat.card A.val := Nat.cast_pos.mpr Nat.card_pos
    have hNpos : (0 : ℚ) < Nat.card (normG A.val ⊓ K : Subgroup G) := Nat.cast_pos.mpr Nat.card_pos
    have hnpos : (0 : ℚ) < nIdx A := by
      have : 0 < nIdx A := by
        have hNpos' : 0 < Nat.card (normG A.val ⊓ K : Subgroup G) := Nat.card_pos
        by_contra h0; push Not at h0
        have h0' : nIdx A = 0 := by omega
        rw [h0', zero_mul] at hNmul
        omega
      exact Nat.cast_pos.mpr this
    have horbpos : (0 : ℚ) < Fintype.card (MulAction.orbit K A) := by
      have : Nonempty (MulAction.orbit K A) := ⟨⟨A, MulAction.mem_orbit_self A⟩⟩
      exact Nat.cast_pos.mpr Fintype.card_pos
    rw [hsum_eq, hfib_card, hKeq]
    field_simp
  let rep : Orb → TI := fun o => Quotient.out o
  have hrep_mk : ∀ o : Orb, Quotient.mk (MulAction.orbitRel K TI) (rep o) = o :=
    fun o => Quotient.out_eq o
  have hKeq_sum : ((Nat.card K - 1 : ℕ) : ℚ) / (Nat.card K : ℚ) =
      ∑ o : Orb, ((Nat.card (rep o).val - 1 : ℕ) : ℚ) / ((nIdx (rep o) : ℚ) * (Nat.card (rep o).val : ℚ)) := by
    have hsum1 : ((Nat.card K - 1 : ℕ) : ℚ) = ∑ A : TI, ((Nat.card A.val - 1 : ℕ) : ℚ) := by
      have h1 : Nat.card K - 1 = ∑ A ∈ TI, (Nat.card A - 1) := hKne1_card.symm.trans hpart
      have h2 : (∑ A ∈ TI, (Nat.card A - 1)) = ∑ A : TI, (Nat.card A.val - 1) :=
        (Finset.sum_coe_sort TI (fun A => Nat.card A - 1)).symm
      exact_mod_cast h1.trans h2
    rw [hsum1, Finset.sum_div]
    rw [← Finset.sum_fiberwise_of_maps_to (g := Quotient.mk (MulAction.orbitRel K TI))
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [← Finset.sum_div]
    have hfilt : Finset.univ.filter (fun x : TI => Quotient.mk (MulAction.orbitRel K TI) x = o) =
        Finset.univ.filter (fun x : TI => Quotient.mk (MulAction.orbitRel K TI) x = Quotient.mk _ (rep o)) := by
      rw [hrep_mk o]
    rw [hfilt, hterm_orb (rep o)]
  let A1 : TI := ⟨K ⊓ C τ, Finset.mem_image.mpr ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHK τ_mem_H, τ_ne_one⟩, rfl⟩⟩
  let A2 : TI := ⟨K ⊓ C C3, Finset.mem_image.mpr ⟨C3, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hHK C3_mem_H, C3_ne_one⟩, rfl⟩⟩
  let O1 : Orb := Quotient.mk (MulAction.orbitRel K TI) A1
  let O2 : Orb := Quotient.mk (MulAction.orbitRel K TI) A2
  have hrep_term : ∀ (o : Orb) (A : TI), Quotient.mk (MulAction.orbitRel K TI) A = o →
      ((Nat.card (rep o).val - 1 : ℕ) : ℚ) / ((nIdx (rep o) : ℚ) * (Nat.card (rep o).val : ℚ)) =
      ((Nat.card A.val - 1 : ℕ) : ℚ) / ((nIdx A : ℚ) * (Nat.card A.val : ℚ)) := by
    intro o A hA
    rw [← hterm_orb A, ← hterm_orb (rep o), hA, hrep_mk o]
  have hA1_even : 2 ∣ Nat.card A1.val := by
    have hτA1 : τ ∈ A1.val := ⟨hHK τ_mem_H, rfl⟩
    have hord : orderOf (⟨τ, hτA1⟩ : A1.val) = 2 := by
      have hsq : (⟨τ, hτA1⟩ : A1.val) ^ 2 = 1 := Subtype.ext (by
        rw [sq]; exact (sq_eq_one_iff_tr_eq_zero τ).mpr tr_τ)
      have hne : (⟨τ, hτA1⟩ : A1.val) ≠ 1 := fun h => τ_ne_one (congrArg Subtype.val h)
      exact orderOf_eq_prime hsq hne
    have hdvd := orderOf_dvd_natCard (⟨τ, hτA1⟩ : A1.val)
    rwa [hord] at hdvd
  have hA1_dvd64 : Nat.card A1.val ∣ 64 := by
    rw [← card_C_unipotent τ_ne_one tr_τ]; exact Subgroup.card_dvd_of_le inf_le_right
  have ha1_cases : Nat.card A1.val = 2 ∨ Nat.card A1.val = 4 ∨ Nat.card A1.val = 8 ∨
      Nat.card A1.val = 16 ∨ Nat.card A1.val = 32 ∨ Nat.card A1.val = 64 := by
    obtain ⟨e, he1, he2⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show Nat.card A1.val ∣ 2 ^ 6 from hA1_dvd64)
    have he_pos : 1 ≤ e := by
      by_contra h0; push Not at h0; interval_cases e; rw [pow_zero] at he2; rw [he2] at hA1_even; omega
    interval_cases e <;> (rw [he2]; norm_num)
  have hA1_sylow : Nat.card A1.val ∣ Nat.card K ∧ ¬ (2 * Nat.card A1.val ∣ Nat.card K) := by
    obtain ⟨P, hP⟩ := unipotent_inf_is_sylow2 τ_ne_one (hHK τ_mem_H) tr_τ
    have hcardP : Nat.card (P : Subgroup K) = Nat.card A1.val := by
      change Nat.card (P : Subgroup K) = Nat.card (K ⊓ C τ : Subgroup G)
      rw [← hP]
      exact (Nat.card_congr (Equiv.ofBijective
        (fun x : (P : Subgroup K) => (⟨x.val.val, ⟨x.val, x.prop, rfl⟩⟩ : ((P : Subgroup K).map K.subtype)))
        ⟨fun a b h => Subtype.ext (Subtype.ext (Subtype.mk.inj h)),
         fun ⟨_, y, hy, rfl⟩ => ⟨⟨y, hy⟩, rfl⟩⟩))
    rw [← hcardP]
    refine ⟨Subgroup.card_subgroup_dvd_card _, ?_⟩
    rw [Sylow.card_eq_multiplicity]
    intro hdvd
    have hKpos : Nat.card K ≠ 0 := Nat.card_pos.ne'
    have hle : (Nat.card K).factorization 2 + 1 ≤ (Nat.card K).factorization 2 := by
      have : 2 ^ ((Nat.card K).factorization 2 + 1) ∣ Nat.card K := by
        simpa [pow_succ'] using hdvd
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hKpos).mp this
    omega
  have hn1_props : nIdx A1 ∣ 63 ∧ nIdx A1 ∣ Nat.card A1.val - 1 := by
    have h := normalizer_inf_unipotent_dvd τ_ne_one (hHK τ_mem_H) tr_τ
    exact ⟨h.2, h.1⟩
  have hA1n1_dvd : Nat.card A1.val * nIdx A1 ∣ Nat.card K := by
    have hmul : Nat.card A1.val * nIdx A1 = Nat.card (normG A1.val ⊓ K : Subgroup G) := by
      rw [mul_comm]; exact Nat.div_mul_cancel (hAdvdN A1)
    rw [hmul]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hA1n1_lt : Nat.card A1.val * nIdx A1 < Nat.card K := by
    have hle : Nat.card A1.val * nIdx A1 ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos hA1n1_dvd
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hmul : Nat.card A1.val * nIdx A1 = Nat.card (normG A1.val ⊓ K : Subgroup G) := by
      rw [mul_comm]; exact Nat.div_mul_cancel (hAdvdN A1)
    rw [hmul] at heq
    have hNK : (normG A1.val ⊓ K : Subgroup G) = K :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq heq.symm)
    have hC3norm : C3 ∈ normG A1.val := by
      have : C3 ∈ (normG A1.val ⊓ K : Subgroup G) := by rw [hNK]; exact hHK C3_mem_H
      exact this.1
    have hcomm : C3 * τ * C3⁻¹ ∈ C τ :=
      ((Subgroup.mem_normalizer_iff.mp hC3norm τ).mp ⟨hHK τ_mem_H, rfl⟩).2
    have hcalc : C3 * τ * C3⁻¹ = antiMat (ω * ω) := by
      simp [C3, τ, diagMat_inv, diagMat_mul_antiMat, antiMat_mul_diagMat]
    rw [hcalc] at hcomm
    have hcomm' : antiMat (ω * ω) * antiMat 1 = antiMat 1 * antiMat (ω * ω) := hcomm
    rw [antiMat_mul_antiMat, antiMat_mul_antiMat, inv_one, mul_one, one_mul] at hcomm'
    have hω4 : ω * ω = (ω * ω)⁻¹ := diagMat_inj hcomm'
    have hωsq : ω ^ 4 = 1 := by
      have : (ω * ω) * (ω * ω) = 1 := by
        calc (ω * ω) * (ω * ω) = (ω * ω)⁻¹ * (ω * ω) := by rw [← hω4]
          _ = 1 := inv_mul_cancel _
      simpa [pow_succ, mul_assoc] using this
    have : ω = 1 := by
      have := ω_pow_three
      calc ω = ω ^ 3 * ω := by rw [this, one_mul]
        _ = ω ^ 4 := by rw [← pow_succ]
        _ = 1 := hωsq
    exact ω_ne_one this
  have hA2_dvd63 : Nat.card A2.val ∣ 63 := by
    have hsplit : ∃ u : F64, u ^ 2 + tr C3 * u + 1 = 0 := ⟨(ω : F64), by rw [tr_C3, one_mul]; exact ω_sq_add_ω_add_one⟩
    rw [← card_C_split C3_ne_one (by rw [tr_C3]; exact one_ne_zero) hsplit]
    exact Subgroup.card_dvd_of_le inf_le_right
  have h3_dvd_A2 : 3 ∣ Nat.card A2.val := by
    have hC3A2 : C3 ∈ A2.val := ⟨hHK C3_mem_H, rfl⟩
    have hord : orderOf (⟨C3, hC3A2⟩ : A2.val) = 3 := by
      have h3 : (⟨C3, hC3A2⟩ : A2.val) ^ 3 = 1 := Subtype.ext (by
        have hdm : ∀ n : ℕ, (diagMat ω) ^ n = diagMat (ω ^ n) := by
          intro n; induction n with
          | zero => simp [diagMat_one]
          | succ n ih => rw [pow_succ, pow_succ, ih, diagMat_mul]
        change (diagMat ω) ^ 3 = 1; rw [hdm, ω_pow_three, diagMat_one])
      have hne : (⟨C3, hC3A2⟩ : A2.val) ≠ 1 := fun h => C3_ne_one (congrArg Subtype.val h)
      exact orderOf_eq_prime h3 hne
    rw [← hord]; exact orderOf_dvd_natCard _
  have ha2_cases : Nat.card A2.val = 3 ∨ Nat.card A2.val = 9 ∨
      Nat.card A2.val = 21 ∨ Nat.card A2.val = 63 := by
    have hmem := mem_divs_63 hA2_dvd63
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with h|h|h|h|h|h <;> omega
  have hn2_eq : nIdx A2 = 2 := by
    rcases normalizer_inf_card_le_two_mul C3_ne_one (hHK C3_mem_H) (by rw [tr_C3]; exact one_ne_zero) with h1 | h2
    · exfalso
      have hτN : τ ∈ (normG A2.val ⊓ K : Subgroup G) := by
        refine ⟨?_, hHK τ_mem_H⟩
        show τ ∈ normG A2.val
        rw [Subgroup.mem_normalizer_iff]
        intro X
        have hτnorm : τ ∈ normG (C C3) := by
          rw [normalizer_C_C3_eq_D126]; exact ⟨1, trivial, Or.inr rfl⟩
        have hτK : τ ∈ K := hHK τ_mem_H
        constructor
        · intro ⟨hXK, hXC⟩
          exact ⟨K.mul_mem (K.mul_mem hτK hXK) (K.inv_mem hτK),
            (Subgroup.mem_normalizer_iff.mp hτnorm X).mp hXC⟩
        · intro ⟨hXK, hXC⟩
          refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hτnorm X).mpr hXC⟩
          have : X = τ⁻¹ * (τ * X * τ⁻¹) * τ := by group
          rw [this]; exact K.mul_mem (K.mul_mem (K.inv_mem hτK) hXK) hτK
      have hA2_le_N : A2.val ≤ (normG A2.val ⊓ K : Subgroup G) :=
        fun x hx => ⟨Subgroup.le_normalizer hx, hx.1⟩
      have hEq : (normG A2.val ⊓ K : Subgroup G) = A2.val :=
        (Subgroup.eq_of_le_of_card_ge hA2_le_N (le_of_eq h1)).symm
      have hτA2 : τ ∈ A2.val := hEq ▸ hτN
      obtain ⟨u, hu⟩ := (C_C3_eq_diag τ).mp hτA2.2
      exact diagMat_ne_antiMat u 1 hu.symm
    · show Nat.card (normG A2.val ⊓ K : Subgroup G) / Nat.card A2.val = 2
      rw [h2, Nat.mul_div_cancel _ Nat.card_pos]
  have h2a2_dvd : 2 * Nat.card A2.val ∣ Nat.card K := by
    have hmul : 2 * Nat.card A2.val = Nat.card (normG A2.val ⊓ K : Subgroup G) := by
      calc 2 * Nat.card A2.val = nIdx A2 * Nat.card A2.val := by rw [hn2_eq]
        _ = Nat.card (normG A2.val ⊓ K : Subgroup G) := Nat.div_mul_cancel (hAdvdN A2)
    rw [hmul]; exact Subgroup.card_dvd_of_le inf_le_right
  have hO12 : O1 ≠ O2 := by
    intro h
    obtain ⟨k, hk⟩ := Quotient.exact h
    have hk' : conjK k A2.val = A1.val := congrArg Subtype.val hk
    have hcard_eq : Nat.card A2.val = Nat.card A1.val := by
      rw [← hk']; exact Nat.card_congr (MulAut.conj (k : G) |>.subgroupMap A2.val).toEquiv
    rw [← hcard_eq] at hA1_even
    have := Nat.dvd_trans hA1_even hA2_dvd63
    omega
  have hnonunip : ∀ o : Orb, o ≠ O1 →
      (Nat.card (rep o).val ∣ 63 ∨ Nat.card (rep o).val ∣ 65) ∧
      3 ≤ Nat.card (rep o).val ∧
      (nIdx (rep o) = 1 ∨ nIdx (rep o) = 2) ∧
      nIdx (rep o) * Nat.card (rep o).val ∣ Nat.card K ∧
      (1 : ℚ) / 3 ≤ ((Nat.card (rep o).val - 1 : ℕ) : ℚ) /
        ((nIdx (rep o) : ℚ) * (Nat.card (rep o).val : ℚ)) := by
    intro o ho1
    rcases Finset.mem_image.mp (rep o).prop with ⟨M, hM, hMA⟩
    have hM' := (Finset.mem_filter.mp hM).2
    have htr_ne : tr M ≠ 0 := by
      intro ht0
      apply ho1
      obtain ⟨k, hk⟩ := unipotent_conj_in_K τ_ne_one (hHK τ_mem_H) tr_τ hM'.2 hM'.1 ht0
      have hmk : Quotient.mk (MulAction.orbitRel K TI) (rep o) = O1 := by
        apply Quotient.sound
        exact ⟨k, Subtype.ext (hk.trans hMA)⟩
      rw [hrep_mk] at hmk; exact hmk
    have hdvd_63_65 : Nat.card (rep o).val ∣ 63 ∨ Nat.card (rep o).val ∣ 65 := by
      have hle : (rep o).val ≤ C M := by rw [← hMA]; exact inf_le_right
      have hd := Subgroup.card_dvd_of_le hle
      rcases card_C_cases hM'.2 with ⟨ht0, _⟩ | ⟨_, h63 | h65⟩
      · exact absurd ht0 htr_ne
      · left; rwa [h63] at hd
      · right; rwa [h65] at hd
    have ha_ge3 : 3 ≤ Nat.card (rep o).val := by
      have hne1 : Nat.card (rep o).val ≠ 1 := by
        intro h1
        have hMmem : M ∈ (rep o).val := by rw [← hMA]; exact ⟨hM'.1, rfl⟩
        have hsub : Subsingleton (rep o).val := (Nat.card_eq_one_iff_unique.mp h1).1
        have : (⟨M, hMmem⟩ : (rep o).val) = 1 := Subsingleton.elim _ _
        exact hM'.2 (congrArg Subtype.val this)
      have hodd : ¬ 2 ∣ Nat.card (rep o).val := by
        intro h2
        rcases hdvd_63_65 with h63 | h65
        · have := Nat.dvd_trans h2 h63; omega
        · have := Nat.dvd_trans h2 h65; omega
      have hpos : 0 < Nat.card (rep o).val := Nat.card_pos
      omega
    have hn_12 : nIdx (rep o) = 1 ∨ nIdx (rep o) = 2 := by
      have hnorm := normalizer_inf_card_le_two_mul hM'.2 hM'.1 htr_ne
      rw [hMA] at hnorm
      rcases hnorm with h1 | h2
      · left; show Nat.card (normG (rep o).val ⊓ K : Subgroup G) / Nat.card (rep o).val = 1
        rw [h1, Nat.div_self Nat.card_pos]
      · right; show Nat.card (normG (rep o).val ⊓ K : Subgroup G) / Nat.card (rep o).val = 2
        rw [h2, Nat.mul_div_cancel _ Nat.card_pos]
    have hna_dvd : nIdx (rep o) * Nat.card (rep o).val ∣ Nat.card K := by
      rw [Nat.div_mul_cancel (hAdvdN (rep o))]
      exact Subgroup.card_dvd_of_le inf_le_right
    have hterm_ge : (1 : ℚ) / 3 ≤ ((Nat.card (rep o).val - 1 : ℕ) : ℚ) /
        ((nIdx (rep o) : ℚ) * (Nat.card (rep o).val : ℚ)) := by
      have haq : (3 : ℚ) ≤ Nat.card (rep o).val := by exact_mod_cast ha_ge3
      have hsub : ((Nat.card (rep o).val - 1 : ℕ) : ℚ) = (Nat.card (rep o).val : ℚ) - 1 :=
        Nat.cast_sub (by omega)
      rw [hsub]
      rcases hn_12 with hn1 | hn2
      · rw [hn1]; push_cast
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]
        linarith
      · rw [hn2]; push_cast
        rw [div_le_div_iff₀ (by norm_num) (by linarith)]
        linarith
    exact ⟨hdvd_63_65, ha_ge3, hn_12, hna_dvd, hterm_ge⟩
  let rest : Finset Orb := (Finset.univ.erase O1).erase O2
  have hterm_O1_pos : (0 : ℚ) < ((Nat.card (rep O1).val - 1 : ℕ) : ℚ) /
      ((nIdx (rep O1) : ℚ) * (Nat.card (rep O1).val : ℚ)) := by
    rw [hrep_term O1 A1 rfl]
    have ha1_ge2 : 2 ≤ Nat.card A1.val := by rcases ha1_cases with h|h|h|h|h|h <;> omega
    have hnum_pos : (0 : ℚ) < ((Nat.card A1.val - 1 : ℕ) : ℚ) := Nat.cast_pos.mpr (by omega)
    have hn1_pos : (0 : ℚ) < nIdx A1 := Nat.cast_pos.mpr (Nat.pos_of_dvd_of_pos hn1_props.1 (by norm_num))
    have ha1_pos : (0 : ℚ) < Nat.card A1.val := Nat.cast_pos.mpr Nat.card_pos
    positivity
  have hsum_split : ((Nat.card K - 1 : ℕ) : ℚ) / (Nat.card K : ℚ) =
      ((Nat.card A1.val - 1 : ℕ) : ℚ) / ((nIdx A1 : ℚ) * (Nat.card A1.val : ℚ)) +
      ((Nat.card A2.val - 1 : ℕ) : ℚ) / ((2 : ℚ) * (Nat.card A2.val : ℚ)) +
      ∑ o ∈ rest, ((Nat.card (rep o).val - 1 : ℕ) : ℚ) /
        ((nIdx (rep o) : ℚ) * (Nat.card (rep o).val : ℚ)) := by
    have huniv : (Finset.univ : Finset Orb) = insert O1 (insert O2 rest) := by
      ext o
      by_cases h1 : o = O1
      · simp [rest, h1]
      · by_cases h2 : o = O2 <;> simp [rest, h1, h2]
    rw [hKeq_sum, huniv, Finset.sum_insert, Finset.sum_insert]
    · rw [hrep_term O1 A1 rfl, hrep_term O2 A2 rfl, hn2_eq]; push_cast; ring
    · simp [rest]
    · simp [rest, hO12]
  have hrest_card_lt : rest.card < 2 := by
    by_contra hge
    push Not at hge
    have hsum_rest : (rest.card : ℚ) * ((1 : ℚ) / 3) ≤
        ∑ o ∈ rest, ((Nat.card (rep o).val - 1 : ℕ) : ℚ) /
          ((nIdx (rep o) : ℚ) * (Nat.card (rep o).val : ℚ)) := by
      have hle := Finset.sum_le_sum (s := rest) (f := fun _ => ((1 : ℚ) / 3))
        (g := fun o => ((Nat.card (rep o).val - 1 : ℕ) : ℚ) /
          ((nIdx (rep o) : ℚ) * (Nat.card (rep o).val : ℚ)))
        (fun o ho => (hnonunip o (Finset.mem_erase.mp (Finset.mem_erase.mp ho).2).1).2.2.2.2)
      simpa [Finset.sum_const, nsmul_eq_mul] using hle
    have hO2_ge : (1 : ℚ) / 3 ≤ ((Nat.card A2.val - 1 : ℕ) : ℚ) / ((2 : ℚ) * (Nat.card A2.val : ℚ)) := by
      have := (hnonunip O2 hO12.symm).2.2.2.2
      rw [hrep_term O2 A2 rfl, hn2_eq] at this
      exact_mod_cast this
    have hO1_pos' : (0 : ℚ) < ((Nat.card A1.val - 1 : ℕ) : ℚ) / ((nIdx A1 : ℚ) * (Nat.card A1.val : ℚ)) := by
      rwa [← hrep_term O1 A1 rfl]
    have hlt1 : ((Nat.card K - 1 : ℕ) : ℚ) / (Nat.card K : ℚ) < 1 := by
      have hKpos : (0 : ℚ) < Nat.card K := Nat.cast_pos.mpr Nat.card_pos
      have hsub : ((Nat.card K - 1 : ℕ) : ℚ) = (Nat.card K : ℚ) - 1 := Nat.cast_sub Nat.card_pos
      rw [hsub, div_lt_one hKpos]; linarith
    have hrc : (2 : ℚ) ≤ rest.card := by exact_mod_cast hge
    linarith
  have hK6 : 6 ∣ Nat.card K := by
    have hd := Subgroup.card_dvd_of_le hHK
    rwa [card_H] at hd
  have hKG : Nat.card K ∣ 262080 := by
    have hd := Subgroup.card_subgroup_dvd_card K
    rwa [card_G] at hd
  have hsubK : ((Nat.card K - 1 : ℕ) : ℚ) = (Nat.card K : ℚ) - 1 := Nat.cast_sub Nat.card_pos
  have hsub1 : ((Nat.card A1.val - 1 : ℕ) : ℚ) = (Nat.card A1.val : ℚ) - 1 := Nat.cast_sub Nat.card_pos
  have hsub2 : ((Nat.card A2.val - 1 : ℕ) : ℚ) = (Nat.card A2.val : ℚ) - 1 := Nat.cast_sub Nat.card_pos
  have hK_le_D126_of_eq : Nat.card K = 2 * Nat.card A2.val → K ≤ D126 := by
    intro hK2a2
    have hNcard : Nat.card (normG A2.val ⊓ K : Subgroup G) = Nat.card K := by
      have hmul : nIdx A2 * Nat.card A2.val = Nat.card (normG A2.val ⊓ K : Subgroup G) :=
        Nat.div_mul_cancel (hAdvdN A2)
      rw [hn2_eq] at hmul; omega
    have hNK : (normG A2.val ⊓ K : Subgroup G) = K :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq hNcard.symm)
    intro X hXK
    rw [← normalizer_C_C3_eq_D126]
    have hXN : X ∈ (normG A2.val ⊓ K : Subgroup G) := by rwa [hNK]
    exact mem_normalizer_C_of_mem_normalizer_inf C3_ne_one (hHK C3_mem_H) hXN.1
  interval_cases hrc : rest.card
  · have hrest_empty : rest = ∅ := Finset.card_eq_zero.mp hrc
    rw [hrest_empty, Finset.sum_empty, add_zero, hsubK, hsub1, hsub2] at hsum_split
    have hres := arith_two_orbits hK6 hKG ha1_cases hA1_sylow.1 hA1_sylow.2 hn1_props.1
      hn1_props.2 hA1n1_lt hA1n1_dvd ha2_cases h2a2_dvd hsum_split
    rcases hres with ⟨hK, ha2⟩ | ⟨hK, ha2⟩ | ⟨hK, ha2⟩ | ⟨hK, ha2⟩
    · left; exact eq_monomial_of_le_D126 hHK (hK_le_D126_of_eq (by omega)) (by norm_num) (by omega)
    · right; right; left; exact eq_monomial_of_le_D126 hHK (hK_le_D126_of_eq (by omega)) (by norm_num) (by omega)
    · right; left; exact eq_monomial_of_le_D126 hHK (hK_le_D126_of_eq (by omega)) (by norm_num) (by omega)
    · right; right; right; left
      exact Subgroup.eq_of_le_of_card_ge (hK_le_D126_of_eq (by omega)) (by rw [card_D126, hK])
  · obtain ⟨O3, hrest_eq⟩ := Finset.card_eq_one.mp hrc
    have hO3_mem : O3 ∈ rest := by rw [hrest_eq]; exact Finset.mem_singleton_self O3
    have hO3_ne2 : O3 ≠ O2 := (Finset.mem_erase.mp hO3_mem).1
    have hO3_ne1 : O3 ≠ O1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hO3_mem).2).1
    obtain ⟨ha3_dvd, ha3_ge3, hn3_12, hna3_dvd, _⟩ := hnonunip O3 hO3_ne1
    have hsub3 : ((Nat.card (rep O3).val - 1 : ℕ) : ℚ) = (Nat.card (rep O3).val : ℚ) - 1 :=
      Nat.cast_sub Nat.card_pos
    rw [hrest_eq, Finset.sum_singleton, hsubK, hsub1, hsub2, hsub3] at hsum_split
    have hres := arith_three_orbits hK6 hKG ha1_cases hA1_sylow.1 hA1_sylow.2 hn1_props.1
      hn1_props.2 hA1n1_lt hA1n1_dvd ha2_cases h2a2_dvd ⟨ha3_dvd, ha3_ge3⟩ hn3_12 hna3_dvd hsum_split
    have hmem_three : ∀ M ∈ K, M = 1 ∨ M ^ 2 = 1 ∨ M ^ Nat.card A2.val = 1 ∨ M ^ Nat.card (rep O3).val = 1 := by
      intro M hMK
      by_cases hM1 : M = 1
      · exact Or.inl hM1
      right
      let AM : TI := ⟨K ⊓ C M, Finset.mem_image.mpr ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMK, hM1⟩, rfl⟩⟩
      let oM : Orb := Quotient.mk (MulAction.orbitRel K TI) AM
      have hoM_cases : oM = O1 ∨ oM = O2 ∨ oM = O3 := by
        by_cases h1 : oM = O1
        · exact Or.inl h1
        by_cases h2 : oM = O2
        · exact Or.inr (Or.inl h2)
        have hmem : oM ∈ rest := Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, Finset.mem_univ oM⟩⟩
        rw [hrest_eq, Finset.mem_singleton] at hmem
        exact Or.inr (Or.inr hmem)
      rcases hoM_cases with h1 | h2 | h3
      · left
        obtain ⟨k, hk⟩ := Quotient.exact h1
        have hk' : conjK k A1.val = AM.val := congrArg Subtype.val hk
        have hM_in : M ∈ conjK k A1.val := by rw [hk']; exact ⟨hMK, rfl⟩
        rcases Subgroup.mem_map.mp hM_in with ⟨y, hy, rfl⟩
        have hty : tr y = 0 := tr_eq_zero_of_mem_C_unipotent τ_ne_one tr_τ hy.2
        have htM : tr ((MulAut.conj (k : G)).toMonoidHom y) = 0 := by
          rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, tr_conj, hty]
        rw [sq]; exact (sq_eq_one_iff_tr_eq_zero _).mpr htM
      · right; left
        obtain ⟨k, hk⟩ := Quotient.exact h2
        have hk' : conjK k A2.val = AM.val := congrArg Subtype.val hk
        have hcard_AM : Nat.card AM.val = Nat.card A2.val := by
          rw [← hk']; exact Nat.card_congr (MulAut.conj (k : G) |>.subgroupMap A2.val).symm.toEquiv
        let _ : Fintype AM.val := Fintype.ofFinite _
        have hpow : (⟨M, ⟨hMK, rfl⟩⟩ : AM.val) ^ Fintype.card AM.val = 1 := pow_card_eq_one
        rw [← Nat.card_eq_fintype_card, hcard_AM] at hpow
        simpa using congrArg Subtype.val hpow
      · right; right
        have h3' : Quotient.mk (MulAction.orbitRel K TI) AM = Quotient.mk _ (rep O3) := by
          rw [hrep_mk O3]; exact h3
        obtain ⟨k, hk⟩ := Quotient.exact h3'
        have hk' : conjK k (rep O3).val = AM.val := congrArg Subtype.val hk
        have hcard_AM : Nat.card AM.val = Nat.card (rep O3).val := by
          rw [← hk']; exact Nat.card_congr (MulAut.conj (k : G) |>.subgroupMap (rep O3).val).symm.toEquiv
        let _ : Fintype AM.val := Fintype.ofFinite _
        have hpow : (⟨M, ⟨hMK, rfl⟩⟩ : AM.val) ^ Fintype.card AM.val = 1 := pow_card_eq_one
        rw [← Nat.card_eq_fintype_card, hcard_AM] at hpow
        simpa using congrArg Subtype.val hpow
    rcases hres with ⟨hK, ha2, ha3⟩ | ⟨hK, ha2, ha3⟩ | hK
    · right; right; right; right; right; left
      have htr4 : ∀ M ∈ K, (tr M) ^ 4 = tr M := by
        intro M hMK
        rcases hmem_three M hMK with rfl | h2 | h3 | h5
        · rw [tr_one]; norm_num
        · exact tr_pow_four_of_pow_eq_one (Or.inl h2)
        · rw [ha2] at h3; exact tr_pow_four_of_pow_eq_one (Or.inr (Or.inl h3))
        · rw [ha3] at h5; exact tr_pow_four_of_pow_eq_one (Or.inr (Or.inr h5))
      exact Subgroup.eq_of_le_of_card_ge (le_SL2F4_of_tr_pow_four hHK htr4) (by rw [card_SL2F4, hK])
    · right; right; right; right; left
      have hηK : diagMat η ∈ K := by
        let D9 : Subgroup G :=
          { carrier := {X : G | ∃ u ∈ unitSubgroup 9, X = diagMat u}
            one_mem' := ⟨1, one_pow 9, diagMat_one.symm⟩
            mul_mem' := by rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩; exact ⟨u * v, (unitSubgroup 9).mul_mem hu hv, diagMat_mul u v⟩
            inv_mem' := by rintro _ ⟨u, hu, rfl⟩; exact ⟨u⁻¹, (unitSubgroup 9).inv_mem hu, diagMat_inv u⟩ }
        have hcardD9 : Nat.card D9 = 9 := by
          let f : unitSubgroup 9 → D9 := fun u => ⟨diagMat u.val, u.val, u.prop, rfl⟩
          have hbij : Function.Bijective f :=
            ⟨fun a b h => Subtype.ext (diagMat_inj (Subtype.mk.inj h)),
             fun ⟨_, u, hu, rfl⟩ => ⟨⟨u, hu⟩, rfl⟩⟩
          rw [← Nat.card_congr (Equiv.ofBijective f hbij), card_unitSubgroup (by norm_num)]
        have hA2_le_D9 : A2.val ≤ D9 := by
          intro X hXA2
          obtain ⟨u, rfl⟩ := (C_C3_eq_diag X).mp hXA2.2
          let _ : Fintype A2.val := Fintype.ofFinite _
          have hpow : (⟨diagMat u, hXA2⟩ : A2.val) ^ Fintype.card A2.val = 1 := pow_card_eq_one
          rw [← Nat.card_eq_fintype_card, ha2] at hpow
          have hpowG : (diagMat u) ^ 9 = 1 := by simpa using congrArg Subtype.val hpow
          have hdm : ∀ n : ℕ, (diagMat u) ^ n = diagMat (u ^ n) := by
            intro n; induction n with
            | zero => simp [diagMat_one]
            | succ n ih => rw [pow_succ, pow_succ, ih, diagMat_mul]
          rw [hdm] at hpowG
          exact ⟨u, diagMat_inj (hpowG.trans diagMat_one.symm), rfl⟩
        have hA2_eq_D9 : A2.val = D9 := Subgroup.eq_of_le_of_card_ge hA2_le_D9 (by rw [hcardD9, ha2])
        have hηD9 : diagMat η ∈ D9 := ⟨η, η_pow_nine, rfl⟩
        rw [← hA2_eq_D9] at hηD9
        exact hηD9.1
      have htr8 : ∀ M ∈ K, (tr M) ^ 8 = tr M := by
        intro M hMK
        rcases hmem_three M hMK with rfl | h2 | h9 | h7
        · rw [tr_one]; norm_num
        · exact tr_pow_eight_of_pow_eq_one (Or.inl h2)
        · rw [ha2] at h9; exact tr_pow_eight_of_pow_eq_one (Or.inr (Or.inr h9))
        · rw [ha3] at h7; exact tr_pow_eight_of_pow_eq_one (Or.inr (Or.inl h7))
      exact Subgroup.eq_of_le_of_card_ge (le_SU2F8_of_tr_pow_eight hHK hηK htr8) (by rw [card_SU2F8, hK])
    · right; right; right; right; right; right
      exact Subgroup.eq_of_le_of_card_ge le_top (by
        rw [Nat.card_congr Subgroup.topEquiv.toEquiv, card_G, hK])

/-! ### Section 6: Verification of the `L_7` interval isomorphism -/

lemma mono_le_mono {U V : Subgroup F64ˣ} (h : U ≤ V) :
    monomialSubgroup U ≤ monomialSubgroup V := by
  rintro M ⟨u, hu, hM⟩; exact ⟨u, h hu, hM⟩

lemma unitSubgroup_le_of_dvd {d1 d2 : ℕ} (h : d1 ∣ d2) :
    unitSubgroup d1 ≤ unitSubgroup d2 := by
  intro u hu
  obtain ⟨k, rfl⟩ := h
  show u ^ (d1 * k) = 1
  rw [pow_mul, show u ^ d1 = 1 from hu, one_pow]

lemma H_le_D42 : H ≤ D42 := mono_le_mono (unitSubgroup_le_of_dvd (by norm_num))
lemma H_le_D18 : H ≤ D18 := mono_le_mono (unitSubgroup_le_of_dvd (by norm_num))
lemma H_le_D126 : H ≤ D126 := mono_le_mono le_top
lemma D42_le_D126 : D42 ≤ D126 := mono_le_mono le_top
lemma D18_le_D126 : D18 ≤ D126 := mono_le_mono le_top

lemma D18_le_SU2F8 : D18 ≤ SU2F8 := by
  rintro M ⟨u, hu, rfl | rfl⟩
  · have hu8 : (u : F64) ^ 8 = ((u⁻¹ : F64ˣ) : F64) := by
      have : u ^ 8 = u⁻¹ := by
        apply mul_left_cancel (a := u); rw [mul_inv_cancel, ← pow_succ']; exact hu
      rw [← Units.val_pow_eq_pow_val, this]
    exact ⟨by simp [diagMat, hu8], by simp [diagMat]⟩
  · have hu8 : (u : F64) ^ 8 = ((u⁻¹ : F64ˣ) : F64) := by
      have : u ^ 8 = u⁻¹ := by
        apply mul_left_cancel (a := u); rw [mul_inv_cancel, ← pow_succ']; exact hu
      rw [← Units.val_pow_eq_pow_val, this]
    exact ⟨by simp [antiMat], by simp [antiMat, hu8]⟩

lemma H_le_SU2F8 : H ≤ SU2F8 := le_trans H_le_D18 D18_le_SU2F8

lemma H_le_SL2F4 : H ≤ SL2F4 := by
  rintro M ⟨u, hu, rfl | rfl⟩
  · have h3u : u ^ 3 = 1 := hu
    have hu4 : (u : F64) ^ 4 = (u : F64) := by
      have h3 : (u : F64) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3u, Units.val_one]
      calc (u : F64) ^ 4 = (u : F64) ^ 3 * (u : F64) := by ring
        _ = (u : F64) := by rw [h3, one_mul]
    have hui4 : ((u⁻¹ : F64ˣ) : F64) ^ 4 = ((u⁻¹ : F64ˣ) : F64) := by
      have h3i : (u⁻¹ : F64ˣ) ^ 3 = 1 := by rw [inv_pow, h3u, inv_one]
      have h3 : ((u⁻¹ : F64ˣ) : F64) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3i, Units.val_one]
      calc ((u⁻¹ : F64ˣ) : F64) ^ 4 = ((u⁻¹ : F64ˣ) : F64) ^ 3 * ((u⁻¹ : F64ˣ) : F64) := by ring
        _ = ((u⁻¹ : F64ˣ) : F64) := by rw [h3, one_mul]
    exact ⟨by simpa [diagMat] using hu4, by simp [diagMat], by simp [diagMat], by simpa [diagMat] using hui4⟩
  · have h3u : u ^ 3 = 1 := hu
    have hu4 : (u : F64) ^ 4 = (u : F64) := by
      have h3 : (u : F64) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3u, Units.val_one]
      calc (u : F64) ^ 4 = (u : F64) ^ 3 * (u : F64) := by ring
        _ = (u : F64) := by rw [h3, one_mul]
    have hui4 : ((u⁻¹ : F64ˣ) : F64) ^ 4 = ((u⁻¹ : F64ˣ) : F64) := by
      have h3i : (u⁻¹ : F64ˣ) ^ 3 = 1 := by rw [inv_pow, h3u, inv_one]
      have h3 : ((u⁻¹ : F64ˣ) : F64) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, h3i, Units.val_one]
      calc ((u⁻¹ : F64ˣ) : F64) ^ 4 = ((u⁻¹ : F64ˣ) : F64) ^ 3 * ((u⁻¹ : F64ˣ) : F64) := by ring
        _ = ((u⁻¹ : F64ˣ) : F64) := by rw [h3, one_mul]
    exact ⟨by simp [antiMat], by simpa [antiMat] using hu4, by simpa [antiMat] using hui4, by simp [antiMat]⟩

lemma not_D42_le_SU2F8 : ¬ (D42 ≤ SU2F8) := by
  intro h
  have hmem : diagMat (ζ ^ 3) ∈ D42 :=
    ⟨ζ ^ 3, by show (ζ ^ 3) ^ 21 = 1; rw [← pow_mul]; exact (pow_eq_one_iff_dvd_63 63).mpr dvd_rfl, Or.inl rfl⟩
  have hsu := h hmem
  have h11 : (((ζ ^ 3)⁻¹ : F64ˣ) : F64) = ((ζ ^ 3 : F64ˣ) : F64) ^ 8 := hsu.1
  have hu : (ζ ^ 3)⁻¹ = (ζ ^ 3) ^ 8 := Units.ext (by rw [h11, ← Units.val_pow_eq_pow_val])
  have h27 : ζ ^ 27 = 1 := by
    have hmul : (ζ ^ 3) * (ζ ^ 3) ^ 8 = 1 := by rw [← hu, mul_inv_cancel]
    rw [← pow_mul, ← pow_add] at hmul
    exact hmul
  have := (pow_eq_one_iff_dvd_63 27).mp h27
  omega

lemma not_D126_le_SU2F8 : ¬ (D126 ≤ SU2F8) :=
  fun h => not_D42_le_SU2F8 (le_trans D42_le_D126 h)

def fL7 : Fin 7 → Set.Ici H
  | ⟨0, _⟩ => ⟨H, show H ≤ H from le_rfl⟩
  | ⟨1, _⟩ => ⟨D42, H_le_D42⟩
  | ⟨2, _⟩ => ⟨D18, H_le_D18⟩
  | ⟨3, _⟩ => ⟨D126, H_le_D126⟩
  | ⟨4, _⟩ => ⟨SU2F8, H_le_SU2F8⟩
  | ⟨5, _⟩ => ⟨SL2F4, H_le_SL2F4⟩
  | ⟨6, _⟩ => ⟨⊤, show H ≤ ⊤ from le_top⟩

lemma card_fL7 (i : Fin 7) : Nat.card (fL7 i).val = fL7Card i := by
  fin_cases i
  · exact card_H
  · exact card_D42
  · exact card_D18
  · exact card_D126
  · exact card_SU2F8
  · exact card_SL2F4
  · change Nat.card (⊤ : Subgroup G) = 262080
    rw [← card_G]; exact Nat.card_congr Subgroup.topEquiv.toEquiv

lemma fL7_order_iff (i j : Fin 7) :
    OMA.S_mo_85724.l7Le i j ↔ fL7 i ≤ fL7 j := by
  rw [l7Le_iff_B]
  by_cases hij : i = j
  · subst hij; exact iff_of_true (by rw [← l7Le_iff_B]; exact Or.inl rfl) le_rfl
  by_cases hi0 : i = 0
  · subst hi0; exact iff_of_true (by rw [← l7Le_iff_B]; exact Or.inr (Or.inl rfl)) (fL7 j).prop
  by_cases hj6 : j = 6
  · subst hj6; exact iff_of_true (by rw [← l7Le_iff_B]; exact Or.inr (Or.inr (Or.inl rfl))) le_top
  by_cases hdvd : fL7Card i ∣ fL7Card j
  · rcases l7_remaining_cases i j hij hi0 hj6 hdvd with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact iff_of_true rfl D42_le_D126
    · exact iff_of_true rfl D18_le_D126
    · exact iff_of_true rfl D18_le_SU2F8
    · exact iff_of_false Bool.false_ne_true not_D42_le_SU2F8
    · exact iff_of_false Bool.false_ne_true not_D126_le_SU2F8
  · refine iff_of_false (fun h => hdvd (l7LeB_dvd i j h)) (fun hle => hdvd ?_)
    have h1 := Subgroup.card_dvd_of_le hle
    rwa [card_fL7 i, card_fL7 j] at h1

lemma fL7_bijective : Function.Bijective fL7 := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hle1 : OMA.S_mo_85724.l7Le i j := (fL7_order_iff i j).mpr (le_of_eq hij)
    have hle2 : OMA.S_mo_85724.l7Le j i := (fL7_order_iff j i).mpr (le_of_eq hij.symm)
    fin_cases i <;> fin_cases j <;> simp_all [OMA.S_mo_85724.l7Le]
  · rintro ⟨K, hHK⟩
    rcases classify_overgroup K hHK with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, Subtype.ext rfl⟩
    · exact ⟨1, Subtype.ext rfl⟩
    · exact ⟨2, Subtype.ext rfl⟩
    · exact ⟨3, Subtype.ext rfl⟩
    · exact ⟨4, Subtype.ext rfl⟩
    · exact ⟨5, Subtype.ext rfl⟩
    · exact ⟨6, Subtype.ext rfl⟩

end

end Mo85724

theorem OMA.solution : type_of% @OMA.S_mo_85724.main := by
  refine ⟨Mo85724.G, inferInstance, inferInstance, Mo85724.H,
    Equiv.ofBijective Mo85724.fL7 Mo85724.fL7_bijective, ?_⟩
  intro i j
  exact Mo85724.fL7_order_iff i j
