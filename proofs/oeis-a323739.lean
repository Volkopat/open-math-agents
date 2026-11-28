import OMAStatements.S_oeis_a323739

-- Problem: A323739, squares of large primes mod 4*primorial(n): Dirichlet plus a CRT count of square units.
-- Credit: @bnb9001

namespace OMA_A323739_Proof

open Finset OMA.S_oeis_a323739

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


lemma card_sqs_eight : (sqs (ZMod 8)ˣ).card = 1 := by
  have h : sqs (ZMod 8)ˣ = {1} := by
    ext u
    simp only [sqs, mem_image, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨x, rfl⟩
      revert x; decide
    · rintro rfl; exact ⟨1, by simp⟩
  rw [h, card_singleton]

lemma card_sqs_of_eq_eight {N : ℕ} [NeZero N] (h : N = 8) : (sqs (ZMod N)ˣ).card = 1 := by
  subst h; convert card_sqs_eight

lemma nth_prime_gt_two {k : ℕ} (hk : 0 < k) : 2 < Nat.nth Nat.Prime k := by
  have := Nat.nth_strictMono Nat.infinite_setOfPred_prime hk
  rwa [Nat.nth_prime_zero_eq_two] at this

lemma cop_four_mul {k p : ℕ} (hp : p.Prime) (hkp : Nat.nth Nat.Prime (k + 1) ≤ p) :
    Nat.Coprime p (4 * firstPrimesProd (k + 1)) := by
  have hp2 : p ≠ 2 := by
    have := nth_prime_gt_two (show 0 < k + 1 by omega); omega
  apply Nat.Coprime.mul_right
  · rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  · unfold firstPrimesProd
    apply Nat.Coprime.prod_right
    intro i hi
    have hik : i < k + 1 := mem_range.1 hi
    have hlt : Nat.nth Nat.Prime i < Nat.nth Nat.Prime (k + 1) :=
      Nat.nth_strictMono Nat.infinite_setOfPred_prime hik
    exact (Nat.coprime_primes hp (Nat.prime_nth_prime i)).2 (by omega)

lemma M_pos (k : ℕ) : 0 < 4 * firstPrimesProd k := by
  have := Q_pos k; omega

instance instNZ4 (k : ℕ) : NeZero (4 * firstPrimesProd k) := ⟨(M_pos k).ne'⟩

lemma keyM (k : ℕ) :
    2 ^ k * (sqs (ZMod (4 * firstPrimesProd (k + 1)))ˣ).card =
      ∏ i ∈ range k, (Nat.nth Nat.Prime (i + 1) - 1) := by
  induction k with
  | zero =>
    have : 4 * firstPrimesProd 1 = 8 := by
      simp [firstPrimesProd, Nat.nth_prime_zero_eq_two]
    rw [card_sqs_of_eq_eight this]; simp
  | succ k ih =>
    have hQ : 4 * firstPrimesProd (k + 2) = 4 * firstPrimesProd (k + 1) * Nat.nth Nat.Prime (k + 1) := by
      simp [firstPrimesProd, prod_range_succ, mul_assoc]
    haveI : NeZero (Nat.nth Nat.Prime (k + 1)) := ⟨(Nat.prime_nth_prime (k + 1)).ne_zero⟩
    have hcop : Nat.Coprime (4 * firstPrimesProd (k + 1)) (Nat.nth Nat.Prime (k + 1)) :=
      (cop_four_mul (Nat.prime_nth_prime (k + 1)) le_rfl).symm
    have e : (ZMod (4 * firstPrimesProd (k + 2)))ˣ ≃*
        (ZMod (4 * firstPrimesProd (k + 1)))ˣ × (ZMod (Nat.nth Nat.Prime (k + 1)))ˣ := by
      rw [hQ]
      exact (Units.mapEquiv (ZMod.chineseRemainder hcop).toMulEquiv).trans MulEquiv.prodUnits
    rw [card_sqs_equiv e, card_sqs_prod, prod_range_succ, ← ih]
    haveI : Fact (Nat.nth Nat.Prime (k + 1)).Prime := ⟨Nat.prime_nth_prime (k + 1)⟩
    have hp2 : Nat.nth Nat.Prime (k + 1) ≠ 2 := by
      have := nth_prime_gt_two (show 0 < k + 1 by omega); omega
    have hk := two_mul_card_sqs_odd (Nat.nth Nat.Prime (k + 1)) hp2
    rw [← hk, pow_succ]
    ring

lemma set_eq (k : ℕ) :
    {r : ℕ | ∃ p : ℕ, p.Prime ∧ Nat.nth Nat.Prime (k + 1) ≤ p ∧
        r = p ^ 2 % (4 * firstPrimesProd (k + 1))} =
      ↑((sqs (ZMod (4 * firstPrimesProd (k + 1)))ˣ).image
        (fun u : (ZMod (4 * firstPrimesProd (k + 1)))ˣ =>
          (u : ZMod (4 * firstPrimesProd (k + 1))).val)) := by
  ext r
  simp only [Set.mem_ofPred_eq, coe_image, Set.mem_image, mem_coe, sqs, mem_image, mem_univ,
    true_and]
  constructor
  · rintro ⟨p, hp, hle, rfl⟩
    have hc := cop_four_mul hp hle
    refine ⟨(ZMod.unitOfCoprime p hc) ^ 2, ⟨_, rfl⟩, ?_⟩
    rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ZMod.val_natCast]
  · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
    obtain ⟨p, hpgt, hp, hpu⟩ :=
      Nat.forall_exists_prime_gt_and_eq_mod u.isUnit (Nat.nth Nat.Prime (k + 1))
    refine ⟨p, hp, hpgt.le, ?_⟩
    rw [Units.val_pow_eq_pow_val, ← hpu, ← Nat.cast_pow, ZMod.val_natCast]

lemma a_zero : a 0 = 2 := by
  unfold a
  have h : {r : ℕ | ∃ p : ℕ, p.Prime ∧ Nat.nth Nat.Prime 0 ≤ p ∧
      r = p ^ 2 % (4 * firstPrimesProd 0)} = {0, 1} := by
    have h4 : 4 * firstPrimesProd 0 = 4 := by simp [firstPrimesProd]
    rw [h4, Nat.nth_prime_zero_eq_two]
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨p, hp, -, rfl⟩
      rcases hp.eq_two_or_odd' with rfl | ⟨t, rfl⟩
      · left; norm_num
      · right; ring_nf; omega
    · rintro (rfl | rfl)
      · exact ⟨2, Nat.prime_two, le_rfl, by norm_num⟩
      · exact ⟨3, Nat.prime_three, by norm_num, by norm_num⟩
  rw [h, Set.ncard_pair (by norm_num)]

end OMA_A323739_Proof

open Finset OMA.S_oeis_a323739 OMA_A323739_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a323739.main := by
  intro n
  rcases n with _ | k
  · simp [a_zero]
  · unfold a
    rw [set_eq k, Set.ncard_coe_finset, card_image_of_injective _ (fun u v h =>
      Units.ext (ZMod.val_injective _ h))]
    rw [prod_range_succ', Nat.nth_prime_zero_eq_two, ← keyM k, pow_succ]
    ring
