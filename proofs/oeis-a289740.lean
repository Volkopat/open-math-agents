import OMAStatements.S_oeis_a289740
import Mathlib

-- Problem: A289740: Prime powers P for which the number of modulo P residues among sums of three sixth powers is less than P.
-- Upstream: statements/oeis-a289740.lean (declaration OMA.S_oeis_a289740.main)
-- Credit: @nnkostov

namespace A289740Proof

open scoped BigOperators

/-! ### Part 1: p = 31 is prime and has a missing residue (15 mod 31) -/

private lemma thirtyone_prime : Nat.Prime 31 := by decide

private lemma sixth_mod_31_mem (x : Fin 31) :
    x.val ^ 6 % 31 = 0 ∨ x.val ^ 6 % 31 = 1 ∨ x.val ^ 6 % 31 = 2 ∨
    x.val ^ 6 % 31 = 4 ∨ x.val ^ 6 % 31 = 8 ∨ x.val ^ 6 % 31 = 16 := by
  revert x
  decide

private lemma sum_three_sixth_ne_15 :
    ∀ u ∈ ([0, 1, 2, 4, 8, 16] : List ℕ),
    ∀ v ∈ ([0, 1, 2, 4, 8, 16] : List ℕ),
    ∀ w ∈ ([0, 1, 2, 4, 8, 16] : List ℕ),
    (u + v + w) % 31 ≠ 15 := by
  decide

private lemma thirtyone_has_missing : OMA.S_oeis_a289740.HasMissingResidue 31 := by
  refine ⟨15, ?_⟩
  rintro ⟨a, b, c, h⟩
  have hmem (x : ZMod 31) : (x ^ 6).val ∈ ([0, 1, 2, 4, 8, 16] : List ℕ) := by
    have hx := sixth_mod_31_mem ⟨x.val, x.val_lt⟩
    have hv : (x ^ 6).val = x.val ^ 6 % 31 := by
      have hxcast : x ^ 6 = ((x.val ^ 6 : ℕ) : ZMod 31) := by
        rw [Nat.cast_pow, ZMod.natCast_zmod_val]
      rw [hxcast, ZMod.val_natCast]
    rw [hv]
    rcases hx with h | h | h | h | h | h <;> simp [h]
  have hsum : ((a ^ 6).val + (b ^ 6).val + (c ^ 6).val) % 31 = 15 := by
    have hv := congr_arg ZMod.val h
    have h15 : (15 : ZMod 31).val = 15 := by decide
    rw [ZMod.val_add, ZMod.val_add, Nat.mod_add_mod, h15] at hv
    exact hv
  exact sum_three_sixth_ne_15 _ (hmem a) _ (hmem b) _ (hmem c) hsum

/-! ### Part 2: Primes p > 31 with p % 6 ≠ 1 (i.e. p % 6 = 5) -/

private lemma exists_sq_add_sq_zmod (p : ℕ) [Fact p.Prime] (r : ZMod p) :
    ∃ a b : ZMod p, a ^ 2 + b ^ 2 = r := by
  classical
  let S : Finset (ZMod p) := Finset.univ.image (fun x : ZMod p => x ^ 2)
  let T : Finset (ZMod p) := S.image (fun y : ZMod p => r - y)
  have hTcard : T.card = S.card := by
    refine Finset.card_image_of_injective S ?_
    intro x y hxy
    exact sub_right_inj.mp hxy
  have h2S : Fintype.card (ZMod p) < 2 * S.card := by
    have hcard_univ : Fintype.card (ZMod p) = ∑ s ∈ S, (Finset.univ.filter fun x : ZMod p => x ^ 2 = s).card := by
      rw [← Finset.card_univ]
      exact Finset.card_eq_sum_card_image (fun x : ZMod p => x ^ 2) Finset.univ
    have h0mem : (0 : ZMod p) ∈ S := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by ring⟩
    have h0card : (Finset.univ.filter fun x : ZMod p => x ^ 2 = (0 : ZMod p)).card = 1 := by
      have heq : (Finset.univ.filter fun x : ZMod p => x ^ 2 = (0 : ZMod p)) = {0} := by
        ext x
        simp
      rw [heq, Finset.card_singleton]
    have hle2 : ∀ s ∈ S, (Finset.univ.filter fun x : ZMod p => x ^ 2 = s).card ≤ 2 := by
      intro s hs
      obtain ⟨x0, -, rfl⟩ := Finset.mem_image.mp hs
      have hsub : (Finset.univ.filter fun x : ZMod p => x ^ 2 = x0 ^ 2) ⊆ {x0, -x0} := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        have hsq : x = x0 ∨ x = -x0 := sq_eq_sq_iff_eq_or_eq_neg.mp hx
        rcases hsq with rfl | rfl <;> simp
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
    have hsum_le : ∑ s ∈ S, (Finset.univ.filter fun x : ZMod p => x ^ 2 = s).card ≤ 1 + 2 * (S.card - 1) := by
      rw [← Finset.add_sum_erase _ _ h0mem, h0card]
      have hrest : ∑ s ∈ S.erase 0, (Finset.univ.filter fun x : ZMod p => x ^ 2 = s).card ≤
          ∑ _s ∈ S.erase 0, (2 : ℕ) :=
        Finset.sum_le_sum fun s hs => hle2 s (Finset.mem_of_mem_erase hs)
      rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem h0mem, mul_comm] at hrest
      omega
    have hSpos : 1 ≤ S.card := Finset.one_le_card.mpr ⟨0, h0mem⟩
    omega
  have hnotdisj : ¬ Disjoint S T := by
    intro hdisj
    have hunion := Finset.card_union_of_disjoint hdisj
    have hle : (S ∪ T).card ≤ Fintype.card (ZMod p) := Finset.card_le_univ _
    omega
  rw [Finset.not_disjoint_iff] at hnotdisj
  obtain ⟨s, hsS, hsT⟩ := hnotdisj
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hsS
  obtain ⟨y, hyS, hy⟩ := Finset.mem_image.mp hsT
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hyS
  exact ⟨a, b, by linear_combination -hy⟩

private lemma no_missing_of_mod6_ne_one (p : ℕ) [hp : Fact p.Prime] (h31 : 31 < p) (h6 : p % 6 ≠ 1) :
    ¬ OMA.S_oeis_a289740.HasMissingResidue p := by
  have hp5 : p % 6 = 5 := by
    have h2 : p % 2 = 1 := by
      have hodd := hp.out.eq_two_or_odd.resolve_left (by omega)
      exact hodd
    have h3 : p % 3 ≠ 0 := by
      intro hdiv
      have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hdiv
      have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp.out).mp hd
      omega
    omega
  have hsq_is_sixth : ∀ x : ZMod p, ∃ y : ZMod p, y ^ 6 = x ^ 2 := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    · refine ⟨x ^ (4 * (p / 6) + 3), ?_⟩
      have hexp : 3 * (4 * (p / 6) + 3) = 2 * (p - 1) + 1 := by omega
      have hflt : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
      calc
        (x ^ (4 * (p / 6) + 3)) ^ 6
            = (x ^ (3 * (4 * (p / 6) + 3))) ^ 2 := by rw [← pow_mul, ← pow_mul]; ring_nf
        _ = (x ^ (2 * (p - 1) + 1)) ^ 2 := by rw [hexp]
        _ = ((x ^ (p - 1)) ^ 2 * x) ^ 2 := by rw [pow_add, pow_one, pow_mul']
        _ = x ^ 2 := by rw [hflt, one_pow, one_mul]
  rintro ⟨r, hr⟩
  obtain ⟨a, b, hab⟩ := exists_sq_add_sq_zmod p r
  obtain ⟨a', ha'⟩ := hsq_is_sixth a
  obtain ⟨b', hb'⟩ := hsq_is_sixth b
  refine hr ⟨a', b', 0, ?_⟩
  simp [ha', hb', hab]

/-! ### Part 3: The 50 primes 31 < p ≤ 625 with p % 6 = 1 via coset witnesses -/

private structure PrimeWitness where
  p : ℕ
  g : ℕ
  a1 : ℕ
  b1 : ℕ
  c1 : ℕ
  a2 : ℕ
  b2 : ℕ
  c2 : ℕ
  a3 : ℕ
  b3 : ℕ
  c3 : ℕ
  a4 : ℕ
  b4 : ℕ
  c4 : ℕ
  a5 : ℕ
  b5 : ℕ
  c5 : ℕ

private def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc, m => acc % m
  | fuel + 1, a, e, acc, m =>
    if e % 2 = 0 then powModAux fuel ((a * a) % m) (e / 2) acc m
    else powModAux fuel ((a * a) % m) (e / 2) ((acc * a) % m) m

private lemma powModAux_cast : ∀ fuel a e acc m : ℕ, e < 2 ^ fuel →
    (powModAux fuel a e acc m : ZMod m) = (acc : ZMod m) * (a : ZMod m) ^ e
  | 0, a, e, acc, m, he => by
    have he0 : e = 0 := by omega
    subst he0
    simp [powModAux]
  | fuel + 1, a, e, acc, m, he => by
    unfold powModAux
    have hhalf : e / 2 < 2 ^ fuel := by
      have : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by ring
      omega
    split_ifs with hpar
    · rw [powModAux_cast fuel ((a * a) % m) (e / 2) acc m hhalf]
      have heeq : e = 2 * (e / 2) := by omega
      rw [ZMod.natCast_mod]
      push_cast
      conv_rhs => rw [heeq, pow_mul, sq]
    · rw [powModAux_cast fuel ((a * a) % m) (e / 2) ((acc * a) % m) m hhalf]
      have heeq : e = 2 * (e / 2) + 1 := by omega
      rw [ZMod.natCast_mod, ZMod.natCast_mod]
      push_cast
      conv_rhs => rw [heeq, pow_add, pow_one, pow_mul, sq]
      ring

private def pow6Mod (a p : ℕ) : ℕ :=
  let a2 := (a * a) % p
  let a3 := (a2 * a) % p
  (a3 * a3) % p

private lemma pow6Mod_cast (a p : ℕ) : (pow6Mod a p : ZMod p) = (a : ZMod p) ^ 6 := by
  unfold pow6Mod
  simp only [ZMod.natCast_mod, Nat.cast_mul]
  ring

private def checkTriple (a b c gj p : ℕ) : Bool :=
  (pow6Mod a p + pow6Mod b p + pow6Mod c p) % p == gj % p

private lemma checkTriple_eq {a b c gj p : ℕ} (h : checkTriple a b c gj p = true) :
    (a : ZMod p) ^ 6 + (b : ZMod p) ^ 6 + (c : ZMod p) ^ 6 = (gj : ZMod p) := by
  unfold checkTriple at h
  have hmod : (pow6Mod a p + pow6Mod b p + pow6Mod c p) % p = gj % p := by
    simpa [beq_iff_eq] using h
  have hcast : ((pow6Mod a p + pow6Mod b p + pow6Mod c p : ℕ) : ZMod p) = (gj : ZMod p) := by
    rw [← ZMod.natCast_mod, hmod, ZMod.natCast_mod]
  simpa [pow6Mod_cast, Nat.cast_add] using hcast

private def checkWitness (w : PrimeWitness) : Bool :=
  let p := w.p
  let g := w.g
  let q := (p - 1) / 6
  let g1 := g % p
  let g2 := (g1 * g1) % p
  let g3 := (g2 * g1) % p
  let g4 := (g3 * g1) % p
  let g5 := (g4 * g1) % p
  (31 < p) && (p ≤ 625) && (p % 6 == 1) && (g1 != 0) &&
  (powModAux 10 g (2 * q) 1 p != 1) &&
  (powModAux 10 g (3 * q) 1 p != 1) &&
  checkTriple w.a1 w.b1 w.c1 g1 p &&
  checkTriple w.a2 w.b2 w.c2 g2 p &&
  checkTriple w.a3 w.b3 w.c3 g3 p &&
  checkTriple w.a4 w.b4 w.c4 g4 p &&
  checkTriple w.a5 w.b5 w.c5 g5 p

private lemma no_missing_of_checkWitness (w : PrimeWitness) [hp : Fact w.p.Prime]
    (hw : checkWitness w = true) : ¬ OMA.S_oeis_a289740.HasMissingResidue w.p := by
  have hp31 : 31 < w.p := by
    unfold checkWitness at hw
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at hw
    exact hw.1.1.1.1.1.1.1.1.1.1
  have hp625 : w.p ≤ 625 := by
    unfold checkWitness at hw
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at hw
    exact hw.1.1.1.1.1.1.1.1.1.2
  have hp6 : w.p % 6 = 1 := by
    unfold checkWitness at hw
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at hw
    exact hw.1.1.1.1.1.1.1.1.2
  have hg_mod_ne : w.g % w.p ≠ 0 := by
    unfold checkWitness at hw
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at hw
    exact hw.1.1.1.1.1.1.1.2
  have hg2_ne : powModAux 10 w.g (2 * ((w.p - 1) / 6)) 1 w.p ≠ 1 := by
    unfold checkWitness at hw
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at hw
    exact hw.1.1.1.1.1.1.2
  have hg3_ne : powModAux 10 w.g (3 * ((w.p - 1) / 6)) 1 w.p ≠ 1 := by
    unfold checkWitness at hw
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at hw
    exact hw.1.1.1.1.1.2
  have ht1 : checkTriple w.a1 w.b1 w.c1 (w.g % w.p) w.p = true := by
    unfold checkWitness at hw
    simp only [Bool.and_eq_true] at hw
    exact hw.1.1.1.1.2
  have ht2 : checkTriple w.a2 w.b2 w.c2 ((w.g % w.p * (w.g % w.p)) % w.p) w.p = true := by
    unfold checkWitness at hw
    simp only [Bool.and_eq_true] at hw
    exact hw.1.1.1.2
  have ht3 : checkTriple w.a3 w.b3 w.c3 (((w.g % w.p * (w.g % w.p)) % w.p * (w.g % w.p)) % w.p) w.p = true := by
    unfold checkWitness at hw
    simp only [Bool.and_eq_true] at hw
    exact hw.1.1.2
  have ht4 : checkTriple w.a4 w.b4 w.c4 ((((w.g % w.p * (w.g % w.p)) % w.p * (w.g % w.p)) % w.p * (w.g % w.p)) % w.p) w.p = true := by
    unfold checkWitness at hw
    simp only [Bool.and_eq_true] at hw
    exact hw.1.2
  have ht5 : checkTriple w.a5 w.b5 w.c5 (((((w.g % w.p * (w.g % w.p)) % w.p * (w.g % w.p)) % w.p * (w.g % w.p)) % w.p * (w.g % w.p)) % w.p) w.p = true := by
    unfold checkWitness at hw
    simp only [Bool.and_eq_true] at hw
    exact hw.2
  have hq : 6 * ((w.p - 1) / 6) = w.p - 1 := by omega
  set q := (w.p - 1) / 6
  have hg0 : (w.g : ZMod w.p) ≠ 0 := by
    intro h0
    have hval := congr_arg ZMod.val h0
    rw [ZMod.val_natCast, ZMod.val_zero] at hval
    exact hg_mod_ne hval
  have h1z : (1 : ℕ) % w.p = 1 := Nat.mod_eq_of_lt (by omega)
  have hlt1 : ∀ n : ℕ, n < w.p → n ≠ 1 → (n : ZMod w.p) ≠ 1 := by
    intro n hlt hne hcast
    have hv := congr_arg ZMod.val hcast
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ZMod.val_one] at hv
    exact hne hv
  have hpowMod_lt : ∀ fuel a e acc, powModAux fuel a e acc w.p < w.p := by
    intro fuel
    induction fuel with
    | zero => intro a e acc; exact Nat.mod_lt _ (by omega)
    | succ fuel ih =>
      intro a e acc
      unfold powModAux
      split_ifs <;> exact ih _ _ _
  have hgz2 : (w.g : ZMod w.p) ^ (2 * q) ≠ 1 := by
    have hcast := powModAux_cast 10 w.g (2 * q) 1 w.p (by omega)
    rw [Nat.cast_one, one_mul] at hcast
    rw [← hcast]
    exact hlt1 _ (hpowMod_lt 10 _ _ _) hg2_ne
  have hgz3 : (w.g : ZMod w.p) ^ (3 * q) ≠ 1 := by
    have hcast := powModAux_cast 10 w.g (3 * q) 1 w.p (by omega)
    rw [Nat.cast_one, one_mul] at hcast
    rw [← hcast]
    exact hlt1 _ (hpowMod_lt 10 _ _ _) hg3_ne
  have hrep1 : (w.a1 : ZMod w.p) ^ 6 + (w.b1 : ZMod w.p) ^ 6 + (w.c1 : ZMod w.p) ^ 6 = (w.g : ZMod w.p) ^ 1 := by
    have h := checkTriple_eq ht1
    simpa [ZMod.natCast_mod] using h
  have hrep2 : (w.a2 : ZMod w.p) ^ 6 + (w.b2 : ZMod w.p) ^ 6 + (w.c2 : ZMod w.p) ^ 6 = (w.g : ZMod w.p) ^ 2 := by
    have h := checkTriple_eq ht2
    simp only [ZMod.natCast_mod, Nat.cast_mul] at h
    simpa [sq] using h
  have hrep3 : (w.a3 : ZMod w.p) ^ 6 + (w.b3 : ZMod w.p) ^ 6 + (w.c3 : ZMod w.p) ^ 6 = (w.g : ZMod w.p) ^ 3 := by
    have h := checkTriple_eq ht3
    simp only [ZMod.natCast_mod, Nat.cast_mul] at h
    convert h using 1
    ring
  have hrep4 : (w.a4 : ZMod w.p) ^ 6 + (w.b4 : ZMod w.p) ^ 6 + (w.c4 : ZMod w.p) ^ 6 = (w.g : ZMod w.p) ^ 4 := by
    have h := checkTriple_eq ht4
    simp only [ZMod.natCast_mod, Nat.cast_mul] at h
    convert h using 1
    ring
  have hrep5 : (w.a5 : ZMod w.p) ^ 6 + (w.b5 : ZMod w.p) ^ 6 + (w.c5 : ZMod w.p) ^ 6 = (w.g : ZMod w.p) ^ 5 := by
    have h := checkTriple_eq ht5
    simp only [ZMod.natCast_mod, Nat.cast_mul] at h
    convert h using 1
    ring
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := (ZMod w.p)ˣ)
  have hord : orderOf ζ = w.p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_eq_fintype_card, ZMod.card_units w.p]
  let u : (ZMod w.p)ˣ := Units.mk0 (w.g : ZMod w.p) hg0
  have hu_mem : u ∈ Subgroup.zpowers ζ := hζ u
  obtain ⟨a, ha⟩ := hu_mem
  have ha_mod3 : ¬ ((3 : ℤ) ∣ a) := by
    rintro ⟨k, rfl⟩
    have hpow : u ^ (2 * q) = 1 := by
      rw [← ha, ← zpow_natCast, ← zpow_mul]
      have heq : 3 * k * (2 * q : ℕ) = (w.p - 1 : ℕ) * k := by
        rw [← hq]
        push_cast
        ring
      rw [heq, zpow_mul, zpow_natCast, ← hord, pow_orderOf_eq_one, one_zpow]
    exact hgz2 (by simpa [u] using congr_arg Units.val hpow)
  have ha_mod2 : ¬ ((2 : ℤ) ∣ a) := by
    rintro ⟨k, rfl⟩
    have hpow : u ^ (3 * q) = 1 := by
      rw [← ha, ← zpow_natCast, ← zpow_mul]
      have heq : 2 * k * (3 * q : ℕ) = (w.p - 1 : ℕ) * k := by
        rw [← hq]
        push_cast
        ring
      rw [heq, zpow_mul, zpow_natCast, ← hord, pow_orderOf_eq_one, one_zpow]
    exact hgz3 (by simpa [u] using congr_arg Units.val hpow)
  rintro ⟨r, hr⟩
  by_cases hr0 : r = 0
  · exact hr ⟨0, 0, 0, by simp [hr0]⟩
  · let v : (ZMod w.p)ˣ := Units.mk0 r hr0
    obtain ⟨b, hb⟩ := hζ v
    have hexists_j : ∃ j : ℕ, j < 6 ∧ (6 : ℤ) ∣ (b - (j : ℤ) * a) := by
      have ha6 : a % 6 = 1 ∨ a % 6 = 5 := by omega
      have hb_eq : b = 6 * (b / 6) + b % 6 := by omega
      rcases ha6 with h1 | h5
      · have ha_eq : a = 6 * (a / 6) + 1 := by omega
        refine ⟨(b % 6).toNat, by omega, b / 6 - (b % 6) * (a / 6), ?_⟩
        have hj : ((b % 6).toNat : ℤ) = b % 6 := Int.toNat_of_nonneg (by omega)
        rw [hj]
        linear_combination hb_eq - (b % 6) * ha_eq
      · have ha_eq : a = 6 * (a / 6) + 5 := by omega
        by_cases hb0 : b % 6 = 0
        · refine ⟨0, by omega, b / 6, ?_⟩
          omega
        · refine ⟨(6 - b % 6).toNat, by omega, b / 6 - (6 - b % 6) * (a / 6) + b % 6 - 5, ?_⟩
          have hj : ((6 - b % 6).toNat : ℤ) = 6 - b % 6 := Int.toNat_of_nonneg (by omega)
          rw [hj]
          linear_combination hb_eq - (6 - b % 6) * ha_eq
    obtain ⟨j, hj6, m, hm⟩ := hexists_j
    let c : ZMod w.p := ((ζ ^ m : (ZMod w.p)ˣ) : ZMod w.p)
    have hrc : r = c ^ 6 * (w.g : ZMod w.p) ^ j := by
      have hv_eq : v = (ζ ^ m) ^ 6 * u ^ j := by
        rw [← hb, ← ha, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
        congr 1
        push_cast
        linarith
      simpa [v, u, c] using congr_arg Units.val hv_eq
    interval_cases j
    · exact hr ⟨c, 0, 0, by simp [hrc]⟩
    · refine hr ⟨c * w.a1, c * w.b1, c * w.c1, ?_⟩
      calc
        (c * w.a1) ^ 6 + (c * w.b1) ^ 6 + (c * w.c1) ^ 6
            = c ^ 6 * ((w.a1 : ZMod w.p) ^ 6 + (w.b1 : ZMod w.p) ^ 6 + (w.c1 : ZMod w.p) ^ 6) := by ring
        _ = c ^ 6 * (w.g : ZMod w.p) ^ 1 := by rw [hrep1]
        _ = r := hrc.symm
    · refine hr ⟨c * w.a2, c * w.b2, c * w.c2, ?_⟩
      calc
        (c * w.a2) ^ 6 + (c * w.b2) ^ 6 + (c * w.c2) ^ 6
            = c ^ 6 * ((w.a2 : ZMod w.p) ^ 6 + (w.b2 : ZMod w.p) ^ 6 + (w.c2 : ZMod w.p) ^ 6) := by ring
        _ = c ^ 6 * (w.g : ZMod w.p) ^ 2 := by rw [hrep2]
        _ = r := hrc.symm
    · refine hr ⟨c * w.a3, c * w.b3, c * w.c3, ?_⟩
      calc
        (c * w.a3) ^ 6 + (c * w.b3) ^ 6 + (c * w.c3) ^ 6
            = c ^ 6 * ((w.a3 : ZMod w.p) ^ 6 + (w.b3 : ZMod w.p) ^ 6 + (w.c3 : ZMod w.p) ^ 6) := by ring
        _ = c ^ 6 * (w.g : ZMod w.p) ^ 3 := by rw [hrep3]
        _ = r := hrc.symm
    · refine hr ⟨c * w.a4, c * w.b4, c * w.c4, ?_⟩
      calc
        (c * w.a4) ^ 6 + (c * w.b4) ^ 6 + (c * w.c4) ^ 6
            = c ^ 6 * ((w.a4 : ZMod w.p) ^ 6 + (w.b4 : ZMod w.p) ^ 6 + (w.c4 : ZMod w.p) ^ 6) := by ring
        _ = c ^ 6 * (w.g : ZMod w.p) ^ 4 := by rw [hrep4]
        _ = r := hrc.symm
    · refine hr ⟨c * w.a5, c * w.b5, c * w.c5, ?_⟩
      calc
        (c * w.a5) ^ 6 + (c * w.b5) ^ 6 + (c * w.c5) ^ 6
            = c ^ 6 * ((w.a5 : ZMod w.p) ^ 6 + (w.b5 : ZMod w.p) ^ 6 + (w.c5 : ZMod w.p) ^ 6) := by ring
        _ = c ^ 6 * (w.g : ZMod w.p) ^ 5 := by rw [hrep5]
        _ = r := hrc.symm

private def witnesses : List PrimeWitness := [
  ⟨37, 2, 0, 1, 1, 3, 3, 3, 9, 6, 6, 0, 3, 2, 9, 5, 5⟩,
  ⟨43, 3, 0, 4, 10, 0, 4, 3, 0, 4, 5, 1, 5, 2, 1, 4, 5⟩,
  ⟨61, 2, 0, 1, 1, 0, 1, 2, 0, 4, 11, 4, 8, 7, 0, 7, 6⟩,
  ⟨67, 2, 0, 1, 1, 0, 4, 12, 1, 17, 3, 0, 1, 17, 0, 8, 3⟩,
  ⟨73, 5, 0, 4, 11, 0, 1, 14, 0, 5, 13, 0, 13, 12, 1, 6, 13⟩,
  ⟨79, 3, 0, 3, 2, 0, 1, 9, 1, 9, 3, 0, 1, 1, 0, 3, 4⟩,
  ⟨97, 5, 0, 10, 9, 0, 12, 13, 0, 1, 10, 0, 26, 26, 0, 4, 6⟩,
  ⟨103, 5, 0, 3, 6, 0, 2, 2, 0, 3, 12, 0, 17, 10, 0, 1, 17⟩,
  ⟨109, 6, 1, 1, 6, 0, 4, 18, 0, 30, 2, 0, 6, 11, 0, 5, 8⟩,
  ⟨127, 3, 0, 1, 10, 0, 1, 16, 0, 10, 29, 0, 16, 9, 0, 8, 18⟩,
  ⟨139, 2, 0, 1, 1, 0, 25, 6, 1, 1, 11, 0, 7, 28, 0, 7, 34⟩,
  ⟨151, 6, 0, 20, 6, 0, 2, 39, 0, 1, 2, 0, 7, 17, 0, 10, 6⟩,
  ⟨157, 5, 0, 1, 21, 0, 16, 43, 0, 4, 8, 0, 1, 9, 0, 1, 32⟩,
  ⟨163, 2, 0, 1, 1, 0, 4, 24, 0, 4, 12, 0, 4, 10, 0, 8, 18⟩,
  ⟨181, 2, 0, 1, 1, 0, 3, 7, 0, 8, 17, 0, 2, 17, 0, 3, 12⟩,
  ⟨193, 5, 0, 19, 42, 0, 1, 17, 0, 1, 22, 0, 56, 4, 0, 11, 29⟩,
  ⟨199, 3, 0, 25, 35, 0, 1, 20, 0, 5, 16, 0, 42, 11, 0, 8, 29⟩,
  ⟨211, 2, 0, 1, 1, 0, 2, 39, 0, 10, 50, 0, 11, 5, 0, 19, 23⟩,
  ⟨223, 3, 0, 1, 25, 0, 1, 15, 25, 15, 19, 0, 5, 30, 0, 24, 59⟩,
  ⟨229, 6, 0, 11, 16, 0, 5, 31, 0, 52, 31, 0, 30, 21, 0, 1, 16⟩,
  ⟨241, 7, 0, 1, 3, 0, 1, 26, 0, 7, 13, 0, 56, 36, 0, 1, 8⟩,
  ⟨271, 6, 0, 24, 35, 0, 1, 7, 0, 4, 42, 0, 11, 5, 0, 1, 3⟩,
  ⟨277, 5, 0, 1, 56, 0, 56, 42, 0, 53, 13, 0, 39, 28, 0, 56, 61⟩,
  ⟨283, 3, 0, 48, 6, 0, 48, 9, 0, 47, 27, 0, 49, 40, 0, 20, 16⟩,
  ⟨307, 5, 0, 1, 15, 0, 1, 9, 0, 9, 10, 0, 39, 6, 0, 1, 14⟩,
  ⟨313, 10, 0, 23, 5, 0, 13, 2, 0, 43, 13, 0, 6, 10, 0, 1, 84⟩,
  ⟨331, 2, 0, 1, 1, 0, 50, 28, 0, 37, 58, 0, 5, 14, 0, 45, 79⟩,
  ⟨337, 10, 0, 24, 22, 0, 7, 2, 0, 15, 25, 0, 1, 40, 0, 57, 44⟩,
  ⟨349, 2, 0, 1, 1, 0, 3, 104, 0, 8, 15, 0, 101, 24, 0, 1, 3⟩,
  ⟨367, 6, 0, 73, 29, 0, 59, 82, 0, 36, 7, 0, 59, 18, 0, 12, 29⟩,
  ⟨373, 2, 0, 1, 1, 0, 61, 10, 0, 1, 43, 0, 61, 69, 0, 1, 6⟩,
  ⟨379, 2, 0, 1, 1, 0, 71, 3, 0, 34, 3, 0, 2, 114, 0, 33, 32⟩,
  ⟨397, 5, 0, 1, 53, 0, 87, 25, 0, 1, 8, 0, 74, 39, 0, 76, 21⟩,
  ⟨409, 7, 0, 1, 4, 0, 1, 21, 0, 59, 56, 0, 6, 103, 0, 79, 6⟩,
  ⟨421, 2, 0, 1, 1, 0, 5, 38, 0, 1, 37, 0, 15, 95, 0, 51, 29⟩,
  ⟨433, 5, 0, 1, 33, 0, 51, 19, 0, 86, 23, 0, 2, 40, 0, 73, 43⟩,
  ⟨439, 15, 0, 1, 124, 0, 1, 81, 0, 124, 45, 0, 124, 70, 0, 1, 119⟩,
  ⟨457, 13, 0, 21, 50, 0, 1, 84, 0, 66, 70, 0, 91, 7, 0, 80, 47⟩,
  ⟨463, 3, 0, 95, 19, 0, 1, 96, 0, 13, 119, 0, 95, 78, 0, 1, 75⟩,
  ⟨487, 3, 0, 91, 34, 0, 1, 91, 0, 91, 106, 0, 9, 38, 0, 1, 3⟩,
  ⟨499, 7, 0, 1, 9, 0, 44, 13, 0, 9, 16, 0, 23, 29, 0, 28, 38⟩,
  ⟨523, 2, 0, 1, 1, 0, 10, 40, 0, 33, 64, 0, 10, 56, 0, 75, 91⟩,
  ⟨541, 2, 0, 1, 1, 0, 36, 51, 0, 1, 13, 0, 1, 34, 0, 53, 26⟩,
  ⟨547, 2, 0, 1, 1, 0, 116, 32, 0, 116, 39, 0, 44, 58, 0, 116, 169⟩,
  ⟨571, 2, 0, 1, 1, 0, 128, 108, 0, 7, 133, 0, 7, 28, 0, 1, 128⟩,
  ⟨577, 5, 0, 34, 66, 0, 1, 9, 0, 4, 15, 0, 9, 9, 0, 9, 32⟩,
  ⟨601, 7, 0, 81, 5, 0, 54, 66, 0, 61, 113, 0, 1, 131, 0, 67, 111⟩,
  ⟨607, 3, 0, 68, 39, 0, 1, 71, 0, 1, 82, 0, 134, 60, 0, 1, 99⟩,
  ⟨613, 2, 0, 1, 1, 0, 1, 173, 0, 108, 35, 0, 16, 29, 0, 106, 137⟩,
  ⟨619, 2, 0, 1, 1, 0, 18, 114, 0, 58, 114, 0, 19, 153, 0, 1, 18⟩
]

private def sieveCond (p : ℕ) : Bool :=
  (31 < p) && (p % 6 == 1) && ([5, 7, 11, 13, 17, 19, 23].all fun d => p % d != 0)

private lemma witnesses_ok : witnesses.all checkWitness = true := by
  decide

private lemma sieve_covered :
    (List.range 105).all
      (fun k => let p := 6 * k + 1; !sieveCond p || witnesses.any (fun w => w.p == p)) = true := by
  decide

private lemma no_missing_of_small_mod6_one (p : ℕ) [hp : Fact p.Prime]
    (h31 : 31 < p) (h625 : p ≤ 625) (h6 : p % 6 = 1) :
    ¬ OMA.S_oeis_a289740.HasMissingResidue p := by
  have hsieve : sieveCond p = true := by
    unfold sieveCond
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, bne_iff_ne]
    refine ⟨⟨h31, h6⟩, ?_⟩
    intro d hd hdiv
    have hdp : d ∣ p := Nat.dvd_of_mod_eq_zero hdiv
    have hd1 : d ≠ 1 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      omega
    have hdlt : d < p := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      omega
    rcases hp.out.eq_one_or_self_of_dvd d hdp with h1 | hself
    · exact hd1 h1
    · omega
  have hk_mem : p / 6 ∈ List.range 105 := List.mem_range.mpr (by omega)
  have hp_eq : 6 * (p / 6) + 1 = p := by omega
  have hcov := List.all_eq_true.mp sieve_covered (p / 6) hk_mem
  dsimp only at hcov
  rw [hp_eq, hsieve] at hcov
  simp only [Bool.not_true, Bool.false_or, List.any_eq_true, beq_iff_eq] at hcov
  obtain ⟨w, hw_mem, hwp⟩ := hcov
  have hwcheck : checkWitness w = true := List.all_eq_true.mp witnesses_ok w hw_mem
  subst hwp
  exact no_missing_of_checkWitness w hwcheck

/-! ### Part 4: Primes p > 625 with p % 6 = 1 via Gauss sums -/

private lemma geom_sum_sixth_root {z : ℂ} (hz6 : z ^ 6 = 1) :
    ∑ j ∈ Finset.range 6, z ^ j = if z = 1 then 6 else 0 := by
  split_ifs with h
  · simp [h]
  · have hmul : (z - 1) * ∑ j ∈ Finset.range 6, z ^ j = 0 := by
      have hg := mul_geom_sum z 6
      rw [hz6, sub_self] at hg
      exact hg
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr h)

private lemma norm_exp_two_pi_I_div (n : ℕ) :
    ‖Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))‖ = 1 := by
  have heq : 2 * Real.pi * Complex.I / (n : ℂ) = ((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [heq, Complex.norm_exp_ofReal_mul_I]

private lemma sum_zmod_erase_zero {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommMonoid M]
    (f : ZMod p → M) :
    ∑ x ∈ Finset.univ.erase (0 : ZMod p), f x = ∑ u : (ZMod p)ˣ, f (u : ZMod p) := by
  classical
  symm
  refine Finset.sum_bij (fun u _ => (u : ZMod p)) ?_ ?_ ?_ ?_
  · intro u _; exact Finset.mem_erase.mpr ⟨Units.ne_zero u, Finset.mem_univ _⟩
  · intro u1 _ u2 _ h; exact Units.ext h
  · intro x hx
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
    exact ⟨Units.mk0 x hx0, Finset.mem_univ _, rfl⟩
  · intro u _; rfl

private lemma sum_sixth_zmod_mul {p : ℕ} [NeZero (p - 1)] (hp6 : p % 6 = 1) (h31 : 31 < p)
    (f : ZMod (p - 1) → ℂ) :
    ∑ m : ZMod (p - 1), f (6 * m) =
      ∑ k : ZMod (p - 1), (if 6 ∣ k.val then (6 : ℂ) else 0) * f k := by
  set q := (p - 1) / 6
  have h6q : 6 * q = p - 1 := by omega
  have hq_pos : 0 < q := by omega
  let eFin : Fin 6 × Fin q ≃ ZMod (p - 1) :=
    { toFun := fun ab => ((ab.1.val * q + ab.2.val : ℕ) : ZMod (p - 1))
      invFun := fun m =>
        (⟨m.val / q, by
          have hlt := m.val_lt
          by_contra h
          push Not at h
          have h1 : 6 * q ≤ m.val / q * q := Nat.mul_le_mul_right q h
          have h2 : m.val / q * q ≤ m.val := Nat.div_mul_le_self m.val q
          omega⟩,
         ⟨m.val % q, Nat.mod_lt _ hq_pos⟩)
      left_inv := fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => by
        have hlt : a * q + b < p - 1 := by nlinarith
        have hv : (((a * q + b : ℕ) : ZMod (p - 1)).val) = a * q + b := by
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
        ext
        · simp only [hv]
          rw [Nat.mul_comm a q, Nat.mul_add_div hq_pos, Nat.div_eq_of_lt hb, add_zero]
        · simp only [hv]
          rw [Nat.mul_comm a q, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
      right_inv := fun m => by
        have hdiv : m.val / q * q + m.val % q = m.val := by
          rw [mul_comm]
          exact Nat.div_add_mod m.val q
        simp [hdiv] }
  have hlhs : ∑ m : ZMod (p - 1), f (6 * m) = 6 * ∑ b : Fin q, f ((6 * b.val : ℕ) : ZMod (p - 1)) := by
    rw [← Fintype.sum_equiv eFin (fun ab => f (6 * eFin ab)) (fun m => f (6 * m)) (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    have hterm : ∀ (a : Fin 6) (b : Fin q), 6 * eFin (a, b) = ((6 * b.val : ℕ) : ZMod (p - 1)) := by
      intro a b
      show (6 : ZMod (p - 1)) * ((a.val * q + b.val : ℕ) : ZMod (p - 1)) = ((6 * b.val : ℕ) : ZMod (p - 1))
      have hnat : 6 * (a.val * q + b.val) = a.val * (p - 1) + 6 * b.val := by
        rw [← h6q]
        ring
      have hcast : (6 : ZMod (p - 1)) * ((a.val * q + b.val : ℕ) : ZMod (p - 1)) =
          ((a.val * (p - 1) + 6 * b.val : ℕ) : ZMod (p - 1)) := by
        rw [← hnat]
        push_cast
        rfl
      rw [hcast]
      simp
    simp_rw [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
  have hrhs : ∑ k : ZMod (p - 1), (if 6 ∣ k.val then (6 : ℂ) else 0) * f k =
      6 * ∑ b : Fin q, f ((6 * b.val : ℕ) : ZMod (p - 1)) := by
    let eFin2 : Fin q × Fin 6 ≃ ZMod (p - 1) :=
      { toFun := fun br => ((6 * br.1.val + br.2.val : ℕ) : ZMod (p - 1))
        invFun := fun k => (⟨k.val / 6, by have := k.val_lt; omega⟩, ⟨k.val % 6, Nat.mod_lt _ (by omega)⟩)
        left_inv := fun ⟨⟨b, hb⟩, ⟨r, hr⟩⟩ => by
          have hlt : 6 * b + r < p - 1 := by omega
          have hv : (((6 * b + r : ℕ) : ZMod (p - 1)).val) = 6 * b + r := by
            rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
          ext
          · simp only [hv]; omega
          · simp only [hv]; omega
        right_inv := fun k => by
          have hdiv : 6 * (k.val / 6) + k.val % 6 = k.val := Nat.div_add_mod k.val 6
          simp [hdiv] }
    rw [← Fintype.sum_equiv eFin2 (fun br => (if 6 ∣ (eFin2 br).val then (6 : ℂ) else 0) * f (eFin2 br))
        (fun k => (if 6 ∣ k.val then (6 : ℂ) else 0) * f k) (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_eq_single (0 : Fin 6)]
    · have hlt : 6 * b.val < p - 1 := by omega
      have hv : (eFin2 (b, 0)).val = 6 * b.val := by
        show ((6 * b.val + 0 : ℕ) : ZMod (p - 1)).val = 6 * b.val
        rw [add_zero, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
      have hdvd : 6 ∣ (eFin2 (b, 0)).val := by rw [hv]; exact dvd_mul_right 6 b.val
      rw [if_pos hdvd]
      simp [eFin2]
    · intro r _ hr0
      have hlt : 6 * b.val + r.val < p - 1 := by have := r.isLt; omega
      have hv : (eFin2 (b, r)).val = 6 * b.val + r.val := by
        show ((6 * b.val + r.val : ℕ) : ZMod (p - 1)).val = 6 * b.val + r.val
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
      have hndvd : ¬ 6 ∣ (eFin2 (b, r)).val := by
        rw [hv]
        have hrpos : 0 < r.val := Nat.pos_of_ne_zero (fun h => hr0 (Fin.ext h))
        have hrlt : r.val < 6 := r.isLt
        omega
      rw [if_neg hndvd, zero_mul]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  rw [hlhs, hrhs]

private lemma exists_units_iso_and_char (p : ℕ) [hp : Fact p.Prime] [NeZero (p - 1)]
    (h31 : 31 < p) (hp6 : p % 6 = 1) :
    let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (6 : ℂ))
    ∃ (e : Multiplicative (ZMod (p - 1)) ≃* (ZMod p)ˣ) (χ : MulChar (ZMod p) ℂ),
      (∀ (j : ℕ) (k : ZMod (p - 1)),
        (χ ^ j) ((e (Multiplicative.ofAdd k) : (ZMod p)ˣ) : ZMod p) = ω ^ (j * k.val)) ∧
      (∀ j ∈ Finset.Ico 1 6, χ ^ j ≠ 1) := by
  intro ω
  have hω_prim : IsPrimitiveRoot ω 6 := Complex.isPrimitiveRoot_exp 6 (by norm_num)
  have hω_ne : ω ≠ 0 := hω_prim.ne_zero (by norm_num)
  let ωu : ℂˣ := Units.mk0 ω hω_ne
  have hωu6 : ωu ^ 6 = 1 := Units.ext hω_prim.pow_eq_one
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hcard_u : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  have hgpow : g ^ (p - 1) = 1 := by
    rw [← hcard_u]
    exact pow_card_eq_one
  let φ : Multiplicative (ZMod (p - 1)) →* (ZMod p)ˣ :=
    { toFun := fun k => g ^ (Multiplicative.toAdd k).val
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [toAdd_mul, ZMod.val_add]
        rw [← pow_eq_pow_mod _ hgpow, pow_add] }
  have hφ_surj : Function.Surjective φ := by
    intro u
    obtain ⟨k, hk⟩ := hg u
    have hm_pos : (0 : ℤ) < ((p - 1 : ℕ) : ℤ) := by omega
    have hnonneg : 0 ≤ k % ((p - 1 : ℕ) : ℤ) := Int.emod_nonneg k (ne_of_gt hm_pos)
    have hpow : g ^ ((k % ((p - 1 : ℕ) : ℤ)).toNat) = u := by
      have hdiv := Int.emod_add_mul_ediv k ((p - 1 : ℕ) : ℤ)
      rw [← hk]
      conv_rhs => rw [← hdiv]
      dsimp only
      rw [zpow_add, zpow_mul, zpow_natCast, hgpow, one_zpow, mul_one]
      rw [← zpow_natCast, Int.toNat_of_nonneg hnonneg]
    refine ⟨Multiplicative.ofAdd (((k % ((p - 1 : ℕ) : ℤ)).toNat : ℕ) : ZMod (p - 1)), ?_⟩
    show g ^ (((k % ((p - 1 : ℕ) : ℤ)).toNat : ZMod (p - 1)).val) = u
    have hlt : (k % ((p - 1 : ℕ) : ℤ)).toNat < p - 1 := by
      have := Int.emod_lt_of_pos k hm_pos
      omega
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
    exact hpow
  have hφ_bij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_surjective_and_card]
    refine ⟨hφ_surj, ?_⟩
    rw [Fintype.card_multiplicative, ZMod.card, hcard_u]
  let e : Multiplicative (ZMod (p - 1)) ≃* (ZMod p)ˣ := MulEquiv.ofBijective φ hφ_bij
  let f6 : Multiplicative (ZMod (p - 1)) →* ℂˣ :=
    { toFun := fun k => ωu ^ (Multiplicative.toAdd k).val
      map_one' := by simp
      map_mul' := fun x y => by
        simp only [toAdd_mul, ZMod.val_add]
        have h6dvd : 6 ∣ p - 1 := ⟨(p - 1) / 6, by omega⟩
        rw [pow_eq_pow_mod _ hωu6, Nat.mod_mod_of_dvd _ h6dvd, ← pow_eq_pow_mod _ hωu6, pow_add] }
  let χu : (ZMod p)ˣ →* ℂˣ := f6.comp e.symm.toMonoidHom
  let χ : MulChar (ZMod p) ℂ :=
    { toFun := fun x => if hx : x = 0 then 0 else ((χu (Units.mk0 x hx) : ℂˣ) : ℂ)
      map_one' := by simp
      map_mul' := fun x y => by
        by_cases hx : x = 0
        · simp [hx]
        · by_cases hy : y = 0
          · simp [hy]
          · have hxy : x * y ≠ 0 := mul_ne_zero hx hy
            simp only [hx, hy, hxy, ↓reduceDIte]
            have hu : Units.mk0 (x * y) hxy = Units.mk0 x hx * Units.mk0 y hy := by
              ext; rfl
            rw [hu, map_mul, Units.val_mul]
      map_nonunit' := fun a ha => by
        have ha0 : a = 0 := by
          by_contra h
          exact ha (Ne.isUnit h)
        simp [ha0] }
  have hχ_pow_unit : ∀ (j : ℕ) (k : ZMod (p - 1)),
      (χ ^ j) ((e (Multiplicative.ofAdd k) : (ZMod p)ˣ) : ZMod p) = ω ^ (j * k.val) := by
    intro j k
    have hne : ((e (Multiplicative.ofAdd k) : (ZMod p)ˣ) : ZMod p) ≠ 0 := Units.ne_zero _
    have h1 : χ ((e (Multiplicative.ofAdd k) : (ZMod p)ˣ) : ZMod p) = ω ^ k.val := by
      simp only [χ, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, hne, ↓reduceDIte]
      have hmk : Units.mk0 ((e (Multiplicative.ofAdd k) : (ZMod p)ˣ) : ZMod p) hne =
          e (Multiplicative.ofAdd k) := by ext; rfl
      rw [hmk]
      simp [χu, f6, ωu]
    cases j with
    | zero =>
      simp [MulChar.one_apply_coe]
    | succ j =>
      rw [MulChar.pow_apply' _ (Nat.succ_ne_zero j), h1, ← pow_mul, mul_comm]
  have hχ_ne_one : ∀ j ∈ Finset.Ico 1 6, χ ^ j ≠ 1 := by
    intro j hj heq
    rw [Finset.mem_Ico] at hj
    have hval := congr_arg
      (fun c : MulChar (ZMod p) ℂ => c ((e (Multiplicative.ofAdd (1 : ZMod (p - 1))) : (ZMod p)ˣ) : ZMod p)) heq
    rw [hχ_pow_unit] at hval
    have h1val : (1 : ZMod (p - 1)).val = 1 := by
      have : Fact (1 < p - 1) := ⟨by omega⟩
      exact ZMod.val_one (p - 1)
    have hne : ((e (Multiplicative.ofAdd (1 : ZMod (p - 1))) : (ZMod p)ˣ) : ZMod p) ≠ 0 := Units.ne_zero _
    rw [h1val, mul_one, MulChar.one_apply (Ne.isUnit hne)] at hval
    exact hω_prim.pow_ne_one_of_pos_of_lt (by omega) hj.2 hval
  exact ⟨e, χ, hχ_pow_unit, hχ_ne_one⟩

private lemma sixth_power_sum_eq_gauss (p : ℕ) [Fact p.Prime] [NeZero (p - 1)]
    (h31 : 31 < p) (hp6 : p % 6 = 1)
    (ψ : AddChar (ZMod p) ℂ) (hψ_prim : ψ.IsPrimitive)
    (e : Multiplicative (ZMod (p - 1)) ≃* (ZMod p)ˣ) (χ : MulChar (ZMod p) ℂ)
    (hχ_pow : ∀ (j : ℕ) (k : ZMod (p - 1)),
      (χ ^ j) ((e (Multiplicative.ofAdd k) : (ZMod p)ˣ) : ZMod p) =
        (Complex.exp (2 * Real.pi * Complex.I / (6 : ℂ))) ^ (j * k.val))
    (t : ZMod p) (ht : t ≠ 0) :
    ∑ x : ZMod p, ψ (t * x ^ 6) = ∑ j ∈ Finset.Ico 1 6, gaussSum (χ ^ j) (ψ.mulShift t) := by
  classical
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (6 : ℂ))
  have hω_prim : IsPrimitiveRoot ω 6 := Complex.isPrimitiveRoot_exp 6 (by norm_num)
  have hsum6 : ∑ j ∈ Finset.range 6, gaussSum (χ ^ j) (ψ.mulShift t) =
      (∑ x : ZMod p, ψ (t * x ^ 6)) - 1 := by
    have hswap : ∑ j ∈ Finset.range 6, gaussSum (χ ^ j) (ψ.mulShift t) =
        ∑ y : ZMod p, (∑ j ∈ Finset.range 6, (χ ^ j) y) * ψ (t * y) := by
      simp_rw [gaussSum, AddChar.mulShift_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [hswap]
    have hsplit_y : ∑ y : ZMod p, (∑ j ∈ Finset.range 6, (χ ^ j) y) * ψ (t * y) =
        ∑ u : (ZMod p)ˣ, (∑ j ∈ Finset.range 6, (χ ^ j) (u : ZMod p)) * ψ (t * (u : ZMod p)) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
      have hz : (∑ j ∈ Finset.range 6, (χ ^ j) (0 : ZMod p)) = 0 :=
        Finset.sum_eq_zero fun j _ => MulChar.map_zero (χ ^ j)
      rw [hz, zero_mul, zero_add]
      exact sum_zmod_erase_zero (fun y => (∑ j ∈ Finset.range 6, (χ ^ j) y) * ψ (t * y))
    rw [hsplit_y]
    let e' : ZMod (p - 1) ≃ (ZMod p)ˣ := Multiplicative.ofAdd.trans e.toEquiv
    have he_y : ∑ u : (ZMod p)ˣ, (∑ j ∈ Finset.range 6, (χ ^ j) (u : ZMod p)) * ψ (t * (u : ZMod p)) =
        ∑ k : ZMod (p - 1), (if 6 ∣ k.val then (6 : ℂ) else 0) * ψ (t * (e (Multiplicative.ofAdd k) : ZMod p)) := by
      rw [← Fintype.sum_equiv e'
          (fun k => (∑ j ∈ Finset.range 6, (χ ^ j) (e (Multiplicative.ofAdd k) : ZMod p)) * ψ (t * (e (Multiplicative.ofAdd k) : ZMod p)))
          (fun u => (∑ j ∈ Finset.range 6, (χ ^ j) (u : ZMod p)) * ψ (t * (u : ZMod p)))
          (fun _ => rfl)]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      have hpow6 : (ω ^ k.val) ^ 6 = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hω_prim.pow_eq_one, one_pow]
      have hgeom : ∑ j ∈ Finset.range 6, (χ ^ j) (e (Multiplicative.ofAdd k) : ZMod p) =
          ∑ j ∈ Finset.range 6, (ω ^ k.val) ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hχ_pow j k, ← pow_mul, mul_comm j k.val]
      rw [hgeom, geom_sum_sixth_root hpow6]
      have hiff : ω ^ k.val = 1 ↔ 6 ∣ k.val := hω_prim.pow_eq_one_iff_dvd k.val
      simp [hiff]
    rw [he_y, ← sum_sixth_zmod_mul hp6 h31 (fun k => ψ (t * (e (Multiplicative.ofAdd k) : ZMod p)))]
    have hsplit_x : (∑ x : ZMod p, ψ (t * x ^ 6)) - 1 = ∑ u : (ZMod p)ˣ, ψ (t * (u : ZMod p) ^ 6) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
      have h0 : ψ (t * (0 : ZMod p) ^ 6) = 1 := by simp
      rw [h0, add_sub_cancel_left]
      exact sum_zmod_erase_zero (fun x => ψ (t * x ^ 6))
    rw [hsplit_x]
    rw [← Fintype.sum_equiv e'
        (fun m => ψ (t * (e (Multiplicative.ofAdd m) : ZMod p) ^ 6))
        (fun u => ψ (t * (u : ZMod p) ^ 6))
        (fun _ => rfl)]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h6m : (e (Multiplicative.ofAdd m) : (ZMod p)ˣ) ^ 6 = e (Multiplicative.ofAdd (6 * m)) := by
      rw [← map_pow]
      congr 1
      have : (Multiplicative.ofAdd m) ^ 6 = Multiplicative.ofAdd (6 • m) := (ofAdd_nsmul 6 m).symm
      rw [this, nsmul_eq_mul, Nat.cast_ofNat]
    rw [← Units.val_pow_eq_pow_val, h6m]
  have hsplit_j : ∑ j ∈ Finset.range 6, gaussSum (χ ^ j) (ψ.mulShift t) =
      gaussSum (1 : MulChar (ZMod p) ℂ) (ψ.mulShift t) +
        ∑ j ∈ Finset.Ico 1 6, gaussSum (χ ^ j) (ψ.mulShift t) := by
    have hrange : Finset.range 6 = insert 0 (Finset.Ico 1 6) := by decide
    rw [hrange, Finset.sum_insert (by decide), pow_zero]
  have htriv : gaussSum (1 : MulChar (ZMod p) ℂ) (ψ.mulShift t) = -1 :=
    gaussSum_one_left (hψ_prim ht)
  rw [hsplit_j, htriv] at hsum6
  linear_combination -hsum6

private lemma card_sixth_pairs (p : ℕ) [Fact p.Prime] [NeZero (p - 1)]
    (h31 : 31 < p) (hp6 : p % 6 = 1)
    (e : Multiplicative (ZMod (p - 1)) ≃* (ZMod p)ˣ) :
    ∑ x : ZMod p, ∑ y : ZMod p, (if x ^ 6 = y ^ 6 then (1 : ℂ) else 0) =
      (6 * (p : ℂ) - 5) := by
  classical
  have hunit_sols : ∀ x : (ZMod p)ˣ,
      ∑ y : (ZMod p)ˣ, (if (x : ZMod p) ^ 6 = (y : ZMod p) ^ 6 then (1 : ℂ) else 0) = 6 := by
    intro x
    have hbij : ∑ y : (ZMod p)ˣ, (if (x : ZMod p) ^ 6 = (y : ZMod p) ^ 6 then (1 : ℂ) else 0) =
        ∑ w : (ZMod p)ˣ, (if (w : ZMod p) ^ 6 = 1 then (1 : ℂ) else 0) := by
      refine Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ fun y => ?_
      have hiff : (x : ZMod p) ^ 6 = (y : ZMod p) ^ 6 ↔ ((x⁻¹ * y : (ZMod p)ˣ) : ZMod p) ^ 6 = 1 := by
        rw [Units.val_mul, mul_pow]
        constructor
        · intro h
          rw [← h, ← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow]
        · intro h
          have := congr_arg (fun z => (x : ZMod p) ^ 6 * z) h
          simp only [mul_one, ← mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel,
            one_mul] at this
          exact this.symm
      rw [if_congr hiff rfl rfl]
      rfl
    rw [hbij]
    let e' : ZMod (p - 1) ≃ (ZMod p)ˣ := Multiplicative.ofAdd.trans e.toEquiv
    rw [← Fintype.sum_equiv e'
        (fun m => if (e (Multiplicative.ofAdd m) : ZMod p) ^ 6 = 1 then (1 : ℂ) else 0)
        (fun w => if (w : ZMod p) ^ 6 = 1 then (1 : ℂ) else 0)
        (fun _ => rfl)]
    have hiff : ∀ m : ZMod (p - 1), ((e (Multiplicative.ofAdd m) : ZMod p) ^ 6 = 1) ↔ (6 * m = 0) := by
      intro m
      have h6m : (e (Multiplicative.ofAdd m) : (ZMod p)ˣ) ^ 6 = e (Multiplicative.ofAdd (6 * m)) := by
        rw [← map_pow]
        congr 1
        have : (Multiplicative.ofAdd m) ^ 6 = Multiplicative.ofAdd (6 • m) := (ofAdd_nsmul 6 m).symm
        rw [this, nsmul_eq_mul, Nat.cast_ofNat]
      rw [← Units.val_pow_eq_pow_val, h6m, Units.val_eq_one]
      constructor
      · intro h
        have he1 : e (Multiplicative.ofAdd (6 * m)) = e (Multiplicative.ofAdd 0) := by
          simpa using h
        exact Multiplicative.ofAdd.injective (e.injective he1)
      · intro h
        rw [h]
        simp
    simp_rw [hiff]
    have hstep := sum_sixth_zmod_mul hp6 h31 (fun k => if k = 0 then (1 : ℂ) else 0)
    rw [hstep, Finset.sum_eq_single (0 : ZMod (p - 1))]
    · simp
    · intro k _ hk; simp [hk]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
  have hx0 : ∑ y : ZMod p, (if (0 : ZMod p) ^ 6 = y ^ 6 then (1 : ℂ) else 0) = 1 := by
    rw [Finset.sum_eq_single (0 : ZMod p)]
    · simp
    · intro y _ hy
      have : y ^ 6 ≠ 0 := pow_ne_zero 6 hy
      simp [this.symm]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  rw [hx0]
  have hrest : ∑ x ∈ Finset.univ.erase (0 : ZMod p),
      ∑ y : ZMod p, (if x ^ 6 = y ^ 6 then (1 : ℂ) else 0) = 6 * ((p : ℂ) - 1) := by
    have hterm : ∀ x ∈ Finset.univ.erase (0 : ZMod p),
        ∑ y : ZMod p, (if x ^ 6 = y ^ 6 then (1 : ℂ) else 0) = 6 := by
      intro x hx
      have hxne : x ≠ 0 := (Finset.mem_erase.mp hx).1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))]
      have hy0 : (if x ^ 6 = (0 : ZMod p) ^ 6 then (1 : ℂ) else 0) = 0 := by
        have : x ^ 6 ≠ 0 := pow_ne_zero 6 hxne
        simp [this]
      rw [hy0, zero_add]
      rw [sum_zmod_erase_zero (fun y => if x ^ 6 = y ^ 6 then (1 : ℂ) else 0)]
      exact hunit_sols (Units.mk0 x hxne)
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
    ring
  rw [hrest]
  ring

private lemma no_missing_of_large_mod6_one (p : ℕ) [hp : Fact p.Prime]
    (h625 : 625 < p) (h6 : p % 6 = 1) :
    ¬ OMA.S_oeis_a289740.HasMissingResidue p := by
  classical
  have h31 : 31 < p := by omega
  have : NeZero (p - 1) := ⟨by omega⟩
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (p : ℂ))
  have hζ_prim : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hp.out.ne_zero
  let ψ : AddChar (ZMod p) ℂ := AddChar.zmodChar p hζ_prim.pow_eq_one
  have hψ_prim : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root p hζ_prim
  have hψ_norm : ∀ x : ZMod p, ‖ψ x‖ = 1 := by
    intro x
    show ‖ζ ^ x.val‖ = 1
    rw [norm_pow, norm_exp_two_pi_I_div, one_pow]
  obtain ⟨e, χ, hχ_pow, hχ_ne_one⟩ := exists_units_iso_and_char p h31 h6
  let S : ZMod p → ℂ := fun t => ∑ x : ZMod p, ψ (t * x ^ 6)
  have hS_bound : ∀ t : ZMod p, t ≠ 0 → ‖S t‖ ≤ 5 * Real.sqrt (p : ℝ) := by
    intro t ht
    show ‖∑ x : ZMod p, ψ (t * x ^ 6)‖ ≤ 5 * Real.sqrt (p : ℝ)
    rw [sixth_power_sum_eq_gauss p h31 h6 ψ hψ_prim e χ hχ_pow t ht]
    have hprim_t : (ψ.mulShift t).IsPrimitive := AddChar.IsPrimitive.of_ne_one (hψ_prim ht)
    have hterm : ∀ j ∈ Finset.Ico 1 6, ‖gaussSum (χ ^ j) (ψ.mulShift t)‖ = Real.sqrt (p : ℝ) := by
      intro j hj
      have hne1 : χ ^ j ≠ 1 := hχ_ne_one j hj
      have hmul := gaussSum_mul_gaussSum_eq_card hne1 hprim_t
      rw [← star_gaussSum_eq, ZMod.card] at hmul
      have hnorm_sq : ((‖gaussSum (χ ^ j) (ψ.mulShift t)‖ ^ 2 : ℝ) : ℂ) = (p : ℂ) := by
        rw [Complex.ofReal_pow, ← Complex.mul_conj']
        simpa [Complex.star_def] using hmul
      have hreal : ‖gaussSum (χ ^ j) (ψ.mulShift t)‖ ^ 2 = (p : ℝ) := by
        exact_mod_cast hnorm_sq
      rw [← hreal, Real.sqrt_sq (norm_nonneg _)]
    calc
      ‖∑ j ∈ Finset.Ico 1 6, gaussSum (χ ^ j) (ψ.mulShift t)‖
          ≤ ∑ j ∈ Finset.Ico 1 6, ‖gaussSum (χ ^ j) (ψ.mulShift t)‖ := norm_sum_le _ _
      _ = ∑ _j ∈ Finset.Ico 1 6, Real.sqrt (p : ℝ) := Finset.sum_congr rfl hterm
      _ = 5 * Real.sqrt (p : ℝ) := by
        rw [Finset.sum_const, show (Finset.Ico 1 6).card = 5 by decide, nsmul_eq_mul, Nat.cast_ofNat]
  have hparseval : ∑ t ∈ Finset.univ.erase (0 : ZMod p), ‖S t‖ ^ 2 = 5 * (p : ℝ) * ((p : ℝ) - 1) := by
    have htotal : ∑ t : ZMod p, S t * star (S t) = (p : ℂ) * (6 * (p : ℂ) - 5) := by
      have hstar : ∀ t : ZMod p, star (S t) = ∑ y : ZMod p, ψ (-(t * y ^ 6)) := by
        intro t
        simp only [S, map_sum, ← starRingEnd_apply]
        refine Finset.sum_congr rfl fun y _ => (AddChar.map_neg_eq_conj ψ _).symm
      calc
        ∑ t : ZMod p, S t * star (S t)
            = ∑ t : ZMod p, ∑ x : ZMod p, ∑ y : ZMod p, ψ (t * (x ^ 6 - y ^ 6)) := by
              refine Finset.sum_congr rfl fun t _ => ?_
              rw [hstar t]
              dsimp only [S]
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [← AddChar.map_add_eq_mul]
              congr 1
              ring
        _ = ∑ x : ZMod p, ∑ y : ZMod p, ∑ t : ZMod p, ψ (t * (x ^ 6 - y ^ 6)) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
        _ = ∑ x : ZMod p, ∑ y : ZMod p, (if x ^ 6 = y ^ 6 then (p : ℂ) else 0) := by
              refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
              rw [AddChar.sum_mulShift _ hψ_prim, ZMod.card]
              simp [sub_eq_zero]
        _ = (p : ℂ) * ∑ x : ZMod p, ∑ y : ZMod p, (if x ^ 6 = y ^ 6 then (1 : ℂ) else 0) := by
              simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
        _ = (p : ℂ) * (6 * (p : ℂ) - 5) := by rw [card_sixth_pairs p h31 h6 e]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))] at htotal
    have hS0 : S 0 = (p : ℂ) := by simp [S, ZMod.card]
    have h0term : S 0 * star (S 0) = (p : ℂ) ^ 2 := by rw [hS0]; simp [sq]
    rw [h0term] at htotal
    have hterm_norm : ∀ t : ZMod p, S t * star (S t) = ((‖S t‖ ^ 2 : ℝ) : ℂ) := by
      intro t
      rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
    simp_rw [hterm_norm] at htotal
    have herase_c : ((∑ t ∈ Finset.univ.erase (0 : ZMod p), ‖S t‖ ^ 2 : ℝ) : ℂ) =
        ((5 * (p : ℝ) * ((p : ℝ) - 1) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      have hrhs : ((5 * (p : ℝ) * ((p : ℝ) - 1) : ℝ) : ℂ) =
          (p : ℂ) * (6 * (p : ℂ) - 5) - (p : ℂ) ^ 2 := by
        push_cast
        ring
      rw [hrhs]
      linear_combination htotal
    exact Complex.ofReal_injective herase_c
  rintro ⟨r, hr⟩
  have hzero : ∑ t : ZMod p, ψ (-(t * r)) * (S t) ^ 3 = 0 := by
    have hexpand : ∑ t : ZMod p, ψ (-(t * r)) * (S t) ^ 3 =
        ∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p,
          ∑ t : ZMod p, ψ (t * (a ^ 6 + b ^ 6 + c ^ 6 - r)) := by
      have hcub : ∀ t : ZMod p, ψ (-(t * r)) * (S t) ^ 3 =
          ∑ a : ZMod p, ∑ b : ZMod p, ∑ c : ZMod p, ψ (t * (a ^ 6 + b ^ 6 + c ^ 6 - r)) := by
        intro t
        have hpow3 : (S t) ^ 3 = S t * S t * S t := by ring
        rw [hpow3]
        simp only [S, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 1
        ring
      simp_rw [hcub]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_comm
    rw [hexpand]
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => ?_
    rw [AddChar.sum_mulShift _ hψ_prim]
    have hne : a ^ 6 + b ^ 6 + c ^ 6 - r ≠ 0 := fun h => hr ⟨a, b, c, sub_eq_zero.mp h⟩
    simp [hne]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p))] at hzero
  have hS0 : S 0 = (p : ℂ) := by simp [S, ZMod.card]
  have h0val : ψ (-((0 : ZMod p) * r)) * (S 0) ^ 3 = (p : ℂ) ^ 3 := by simp [hS0]
  rw [h0val] at hzero
  have heq_neg : ((p : ℂ) ^ 3) = - ∑ t ∈ Finset.univ.erase (0 : ZMod p), ψ (-(t * r)) * (S t) ^ 3 := by
    linear_combination hzero
  have hnorm_le : (p : ℝ) ^ 3 ≤ 25 * Real.sqrt (p : ℝ) * (p : ℝ) * ((p : ℝ) - 1) := by
    have h1 : (p : ℝ) ^ 3 = ‖(p : ℂ) ^ 3‖ := by rw [norm_pow, Complex.norm_natCast]
    rw [h1, heq_neg, norm_neg]
    calc
      ‖∑ t ∈ Finset.univ.erase (0 : ZMod p), ψ (-(t * r)) * (S t) ^ 3‖
          ≤ ∑ t ∈ Finset.univ.erase (0 : ZMod p), ‖ψ (-(t * r)) * (S t) ^ 3‖ := norm_sum_le _ _
      _ = ∑ t ∈ Finset.univ.erase (0 : ZMod p), ‖S t‖ * ‖S t‖ ^ 2 := by
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [norm_mul, hψ_norm, one_mul, norm_pow]
            ring
      _ ≤ ∑ t ∈ Finset.univ.erase (0 : ZMod p), (5 * Real.sqrt (p : ℝ)) * ‖S t‖ ^ 2 := by
            refine Finset.sum_le_sum fun t ht => ?_
            have ht0 : t ≠ 0 := (Finset.mem_erase.mp ht).1
            exact mul_le_mul_of_nonneg_right (hS_bound t ht0) (sq_nonneg _)
      _ = (5 * Real.sqrt (p : ℝ)) * ∑ t ∈ Finset.univ.erase (0 : ZMod p), ‖S t‖ ^ 2 := by
            rw [← Finset.mul_sum]
      _ = 25 * Real.sqrt (p : ℝ) * (p : ℝ) * ((p : ℝ) - 1) := by
            rw [hparseval]
            ring
  have hp_real : (625 : ℝ) < (p : ℝ) := by exact_mod_cast h625
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  have hsqrt_sq : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) := Real.sq_sqrt (by positivity)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hle_p3 : (p : ℝ) ^ 3 ≤ 25 * Real.sqrt (p : ℝ) * (p : ℝ) ^ 2 := by
    have h1 : 25 * Real.sqrt (p : ℝ) * (p : ℝ) * ((p : ℝ) - 1) ≤
        25 * Real.sqrt (p : ℝ) * (p : ℝ) * (p : ℝ) := by
      have hfac : 0 ≤ 25 * Real.sqrt (p : ℝ) * (p : ℝ) := by positivity
      nlinarith
    nlinarith
  have hp_le_25sqrt : (p : ℝ) ≤ 25 * Real.sqrt (p : ℝ) := by
    have hmul : (p : ℝ) * (p : ℝ) ^ 2 ≤ (25 * Real.sqrt (p : ℝ)) * (p : ℝ) ^ 2 := by
      linarith
    exact le_of_mul_le_mul_right hmul (sq_pos_of_pos hp_pos)
  have hp_le_625 : (p : ℝ) ≤ 625 := by
    nlinarith
  linarith

end A289740Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a289740.main := by
  refine ⟨⟨A289740Proof.thirtyone_prime, A289740Proof.thirtyone_has_missing⟩, ?_⟩
  rintro p ⟨hp, hmiss⟩
  by_contra hgt
  push Not at hgt
  have : Fact p.Prime := ⟨hp⟩
  by_cases h6 : p % 6 = 1
  · by_cases h625 : p ≤ 625
    · exact A289740Proof.no_missing_of_small_mod6_one p hgt h625 h6 hmiss
    · exact A289740Proof.no_missing_of_large_mod6_one p (by omega) h6 hmiss
  · exact A289740Proof.no_missing_of_mod6_ne_one p hgt h6 hmiss
