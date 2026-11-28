import FormalConjectures.Wikipedia.Emirp

-- Credit: @Pixelstorm44
namespace OMA.R_Emirp_infinitude_question_R1

/-- Lower sieve estimate on arbitrarily large decimal blocks. Count integers whose
reversal is a smaller prime and whose least prime factor exceeds the cube root
of the block's upper endpoint. -/
def H1 : Prop :=
  ∀ K : ℕ, ∃ k ≥ K,
    let X := 10 ^ (k + 1)
    X / (5 * (k + 1)^2) <
      ((Finset.Ico (10^k) X).filter fun m =>
        (Emirp.reverse10 m).Prime ∧ Emirp.reverse10 m < m ∧ X < m.minFac^3).card

/-- Upper bilinear estimate on sufficiently large blocks. Count prime factor
pairs in increasing (nonstrict) order, including squares exactly once. -/
def H2 : Prop :=
  ∃ K : ℕ, ∀ k ≥ K,
    let X := 10 ^ (k + 1)
    (((Finset.range X) ×ˢ (Finset.range X)).filter fun w : ℕ × ℕ =>
      let m := w.1 * w.2
      w.1.Prime ∧ w.2.Prime ∧ w.1 ≤ w.2 ∧ X < w.1^3 ∧
        10^k ≤ m ∧ m < X ∧ (Emirp.reverse10 m).Prime ∧ Emirp.reverse10 m < m).card
      ≤ X / (5 * (k + 1)^2)

/-- A composite survivor of the cube-root sieve is a product of two primes.
Choosing its least prime factor fixes their order. -/
private theorem factor_survivor {m X : ℕ} (hm : 2 ≤ m) (hlt : m < X)
    (hrough : X < m.minFac^3) (hc : ¬ m.Prime) :
    ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ a ≤ b ∧ X < a^3 ∧ a*b = m := by
  let a := m.minFac
  let b := m / a
  have ha : a.Prime := Nat.minFac_prime (by omega)
  have hab : a * b = m := Nat.mul_div_cancel' (Nat.minFac_dvd m)
  have hle : a ≤ b := Nat.minFac_le_div (by omega) hc
  have hb : 2 ≤ b := ha.two_le.trans hle
  refine ⟨a, b, ha, ?_, hle, hrough, hab⟩
  by_contra h
  have hd : b.minFac ∣ m := hab ▸ dvd_mul_of_dvd_right (Nat.minFac_dvd b) a
  have had : a ≤ b.minFac :=
    Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega : b ≠ 1)).two_le hd
  have hs : a^2 ≤ b :=
    (Nat.pow_le_pow_left had 2).trans (Nat.minFac_sq_le_self (by omega) h)
  have : a^3 ≤ m := calc
    a^3 = a * a^2 := by ring
    _ ≤ a * b := Nat.mul_le_mul_left a hs
    _ = m := hab
  exact (lt_trans hlt hrough).not_ge this

theorem main : H1 → H2 → type_of% @Emirp.infinitude_question := by
  rintro lower ⟨K, upper⟩
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨k, hk, hs⟩ := lower (max N K)
  have ht := upper k (le_trans (le_max_right N K) hk)
  let X := 10 ^ (k + 1)
  let S := (Finset.Ico (10^k) X).filter fun m =>
    (Emirp.reverse10 m).Prime ∧ Emirp.reverse10 m < m ∧ X < m.minFac^3
  let T := ((Finset.range X) ×ˢ (Finset.range X)).filter fun w : ℕ × ℕ =>
    let m := w.1 * w.2
    w.1.Prime ∧ w.2.Prime ∧ w.1 ≤ w.2 ∧ X < w.1^3 ∧
      10^k ≤ m ∧ m < X ∧ (Emirp.reverse10 m).Prime ∧ Emirp.reverse10 m < m
  have hgap : T.card < S.card := lt_of_le_of_lt ht hs
  obtain ⟨m, hm, hp⟩ : ∃ m ∈ S, Nat.Prime m := by
    by_contra! none
    have hsub : S ⊆ T.image (fun w => w.1 * w.2) := by
      intro m hm
      obtain ⟨hi, hr, hlt, hf⟩ := Finset.mem_filter.mp hm
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hi
      obtain ⟨a, b, ha, hb, hab, hcube, heq⟩ :=
        factor_survivor (hr.two_le.trans hlt.le) hhi hf (none m hm)
      have hb_lt : b < X := lt_of_le_of_lt
        (Nat.le_of_dvd (by omega) (heq ▸ dvd_mul_left b a)) hhi
      apply Finset.mem_image.mpr
      refine ⟨(a,b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (hab.trans_lt hb_lt), Finset.mem_range.mpr hb_lt⟩, ?_⟩, heq⟩
      exact ⟨ha, hb, hab, hcube, heq ▸ hlo, heq ▸ hhi, heq ▸ hr, heq ▸ hlt⟩
    exact hgap.not_ge ((Finset.card_le_card hsub).trans Finset.card_image_le)
  obtain ⟨hi, hr, hlt, _⟩ := Finset.mem_filter.mp hm
  refine ⟨m, ⟨hp, hr, hlt.ne⟩, ?_⟩
  exact lt_of_le_of_lt ((le_max_left N K).trans hk)
    ((k.lt_pow_self (by decide : 1 < 10)).trans_le (Finset.mem_Ico.mp hi).1)

end OMA.R_Emirp_infinitude_question_R1
