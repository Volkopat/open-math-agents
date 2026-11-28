import OMAStatements.S_oeis_a246541

-- Problem: A246541, number of distinct squares of reduced residues mod the primorial.
-- Credit: @bnb9001

namespace OMA_A246541_Proof

open Finset OMA.S_oeis_a246541

/-- The squares in a finite group. -/
def sqs (G : Type*) [Group G] [Fintype G] [DecidableEq G] : Finset G :=
  (univ : Finset G).image (fun g => g ^ 2)

lemma card_sqs_equiv {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H] (e : G ≃* H) : (sqs G).card = (sqs H).card := by
  have : sqs H = (sqs G).map e.toEquiv.toEmbedding := by
    ext h
    simp only [sqs, mem_image, mem_univ, true_and, mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(e.symm y) ^ 2, ⟨_, rfl⟩, by simp [map_pow]⟩
    · rintro ⟨g, ⟨x, rfl⟩, rfl⟩
      exact ⟨e x, by simp [map_pow]⟩
  rw [this, card_map]

lemma card_sqs_prod {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    [DecidableEq G] [DecidableEq H] : (sqs (G × H)).card = (sqs G).card * (sqs H).card := by
  have : sqs (G × H) = sqs G ×ˢ sqs H := by
    ext ⟨g, h⟩
    simp only [sqs, mem_image, mem_univ, true_and, mem_product]
    constructor
    · rintro ⟨⟨x, y⟩, hxy⟩
      simp only [Prod.pow_mk, Prod.mk.injEq] at hxy
      exact ⟨⟨x, hxy.1⟩, ⟨y, hxy.2⟩⟩
    · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      exact ⟨(x, y), by simp [hx, hy]⟩
  rw [this, card_product]

lemma card_sqs_of_card_one (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (h : Fintype.card G = 1) : (sqs G).card = 1 := by
  apply le_antisymm
  · calc (sqs G).card ≤ (univ : Finset G).card := card_image_le
      _ = 1 := by rw [card_univ, h]
  · exact card_pos.2 (Finset.image_nonempty.2 univ_nonempty)

lemma two_mul_card_sqs_odd (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    2 * (sqs (ZMod p)ˣ).card = p - 1 := by
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by exact_mod_cast h
    rw [ZMod.natCast_eq_natCast_iff'] at this
    have hp3 := hp.out.two_le
    rcases Nat.lt_or_ge 2 p with hlt | hle
    · rw [Nat.mod_eq_of_lt hlt] at this; simp at this
    · omega
  have hfib : ∀ b ∈ sqs (ZMod p)ˣ, (univ.filter (fun g : (ZMod p)ˣ => g ^ 2 = b)).card = 2 := by
    intro b hb
    obtain ⟨a, -, rfl⟩ := mem_image.1 hb
    have hne : a ≠ -a := by
      intro h
      have h' : (a : ZMod p) = -(a : ZMod p) := by rw [← Units.val_neg, ← h]
      have : (2 : ZMod p) * (a : ZMod p) = 0 := by linear_combination h'
      rcases mul_eq_zero.1 this with h0 | h0
      · exact h2 h0
      · exact a.ne_zero h0
    have hset : univ.filter (fun g : (ZMod p)ˣ => g ^ 2 = a ^ 2) = {a, -a} := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · intro h
        have h' : (x : ZMod p) ^ 2 = (a : ZMod p) ^ 2 := by
          rw [← Units.val_pow_eq_pow_val, h, Units.val_pow_eq_pow_val]
        rcases sq_eq_sq_iff_eq_or_eq_neg.1 h' with h1 | h1
        · left; exact Units.ext h1
        · right; exact Units.ext (by rw [h1, Units.val_neg])
      · rintro (rfl | rfl)
        · rfl
        · exact neg_sq a
    rw [hset, card_pair hne]
  have hsum := card_eq_sum_card_image (fun g : (ZMod p)ˣ => g ^ 2) (univ : Finset (ZMod p)ˣ)
  rw [card_univ, hcard] at hsum
  rw [hsum, show image (fun g : (ZMod p)ˣ => g ^ 2) univ = sqs (ZMod p)ˣ from rfl,
    Finset.sum_congr rfl hfib, sum_const, smul_eq_mul, mul_comm]

lemma card_sqs_two : (sqs (ZMod 2)ˣ).card = 1 :=
  card_sqs_of_card_one _ (by rw [ZMod.card_units 2])

lemma coprime_firstPrimesProd (k : ℕ) : Nat.Coprime (firstPrimesProd k) (Nat.nth Nat.Prime k) := by
  unfold firstPrimesProd
  apply Nat.Coprime.prod_left
  intro i hi
  have hik : i < k := mem_range.1 hi
  exact (Nat.coprime_primes (Nat.prime_nth_prime i) (Nat.prime_nth_prime k)).2
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime hik).ne

lemma Q_pos (k : ℕ) : 0 < firstPrimesProd k := by
  unfold firstPrimesProd
  exact prod_pos fun i _ => (Nat.prime_nth_prime i).pos

instance (k : ℕ) : NeZero (firstPrimesProd k) := ⟨(Q_pos k).ne'⟩

/-- `t i` is `2` for `i = 0` (the prime 2) and `prime_i - 1` otherwise. -/
noncomputable def t (i : ℕ) : ℕ := if i = 0 then 2 else Nat.nth Nat.Prime i - 1

lemma key (k : ℕ) : 2 ^ k * (sqs (ZMod (firstPrimesProd k))ˣ).card = ∏ i ∈ range k, t i := by
  induction k with
  | zero =>
    simp only [pow_zero, one_mul, prod_range_zero]
    have : firstPrimesProd 0 = 1 := by simp [firstPrimesProd]
    exact card_sqs_of_card_one _ (by rw [ZMod.card_units_eq_totient, this]; rfl)
  | succ k ih =>
    have hQ : firstPrimesProd (k + 1) = firstPrimesProd k * Nat.nth Nat.Prime k := by simp [firstPrimesProd, prod_range_succ]
    haveI : NeZero (Nat.nth Nat.Prime k) := ⟨(Nat.prime_nth_prime k).ne_zero⟩
    have e : (ZMod (firstPrimesProd (k + 1)))ˣ ≃* (ZMod (firstPrimesProd k))ˣ × (ZMod (Nat.nth Nat.Prime k))ˣ := by
      rw [hQ]
      exact (Units.mapEquiv (ZMod.chineseRemainder (coprime_firstPrimesProd k)).toMulEquiv).trans MulEquiv.prodUnits
    rw [card_sqs_equiv e, card_sqs_prod, prod_range_succ, ← ih]
    haveI : Fact (Nat.nth Nat.Prime k).Prime := ⟨Nat.prime_nth_prime k⟩
    have hk : 2 * (sqs (ZMod (Nat.nth Nat.Prime k))ˣ).card = t k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have hc : (sqs (ZMod (Nat.nth Nat.Prime 0))ˣ).card = 1 :=
          card_sqs_of_card_one _ (by rw [ZMod.card_units, Nat.nth_prime_zero_eq_two])
        rw [hc]
        simp [t]
      · have hp2 : Nat.nth Nat.Prime k ≠ 2 := by
          intro h
          have := Nat.nth_strictMono Nat.infinite_setOfPred_prime hk0
          rw [h, Nat.nth_prime_zero_eq_two] at this
          omega
        simp only [t, if_neg hk0.ne']
        exact two_mul_card_sqs_odd _ hp2
    rw [← hk, pow_succ]
    ring

lemma translate (P : ℕ) [NeZero P] :
    (((range P).filter (fun x => Nat.Coprime x P)).image (fun x => x ^ 2 % P)).card =
      (sqs (ZMod P)ˣ).card := by
  have himg : ((range P).filter (fun x => Nat.Coprime x P)).image (fun x => x ^ 2 % P) =
      (sqs (ZMod P)ˣ).image (fun u => ((u : (ZMod P)ˣ) : ZMod P).val) := by
    ext y
    simp only [sqs, mem_image, mem_filter, mem_range, mem_univ, true_and]
    constructor
    · rintro ⟨x, ⟨hxP, hc⟩, rfl⟩
      refine ⟨(ZMod.unitOfCoprime x hc) ^ 2, ⟨_, rfl⟩, ?_⟩
      rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ZMod.val_natCast]
    · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
      refine ⟨(u : ZMod P).val, ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime u⟩, ?_⟩
      rw [Units.val_pow_eq_pow_val, ← ZMod.val_natCast, Nat.cast_pow, ZMod.natCast_zmod_val]
  rw [himg, card_image_of_injective]
  intro u v h
  exact Units.ext (ZMod.val_injective P h)

end OMA_A246541_Proof

open Finset OMA_A246541_Proof OMA.S_oeis_a246541 in
theorem OMA.solution : type_of% @OMA.S_oeis_a246541.main := by
  intro n _
  have hk := key (n + 1)
  rw [prod_range_succ'] at hk
  have ht0 : t 0 = 2 := by simp [t]
  have hshift : ∏ i ∈ range n, t (i + 1) = ∏ j ∈ Icc 1 n, (Nat.nth Nat.Prime j - 1) := by
    rw [show Icc 1 n = Ico 1 (n + 1) by rfl, prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    refine prod_congr rfl fun i _ => ?_
    simp [t, add_comm]
  rw [ht0, hshift] at hk
  unfold a
  rw [translate]
  have hk' : 2 ^ n * (sqs (ZMod (firstPrimesProd (n + 1)))ˣ).card = ∏ j ∈ Icc 1 n, (Nat.nth Nat.Prime j - 1) := by
    rw [pow_succ] at hk
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by norm_num)
    rw [← hk]; ring
  rw [← hk', Nat.mul_div_cancel_left _ (by positivity)]
