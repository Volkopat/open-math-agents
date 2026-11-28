import FormalConjectures.GreensOpenProblems.«62»

/-!
# A cube-root sieve reduction for Green's problem 62

The ordered rough pairs of a fixed product class are closed under swapping factors.
The two estimates below leave a positive surplus after discarding all pairs with a
semiprime coordinate. Every remaining coordinate must be prime.
-/
-- Credit: @Pixelstorm44

namespace OMA.R_Green62_green_62_R1

open Filter

/-- A surviving composite is a semiprime, including the prime-square case. -/
theorem twoFactors_of_composite {p a : ℕ} (hap : a < p) (ha2 : 2 ≤ a)
    (hcube : p < a.minFac ^ 3) (hc : ¬a.Prime) :
    (a / a.minFac).Prime := by
  let q := a.minFac
  let b := a / q
  have hq : q.Prime := Nat.minFac_prime (by omega)
  have hqb : q ≤ b := Nat.minFac_le_div (by omega) hc
  have hb2 : 2 ≤ b := hq.two_le.trans hqb
  have heq : b * q = a := Nat.div_mul_cancel (Nat.minFac_dvd a)
  have hd : b ∣ a := ⟨q, heq.symm⟩
  change b.Prime
  by_contra hn
  have hsmall : q ≤ b.minFac := Nat.minFac_le_of_dvd
    (Nat.minFac_prime (by omega : b ≠ 1)).two_le ((Nat.minFac_dvd b).trans hd)
  have hsq : q ^ 2 ≤ b :=
    (Nat.pow_le_pow_left hsmall 2).trans (Nat.minFac_sq_le_self (by omega) hn)
  have hle : q ^ 3 ≤ a := by
    rw [pow_succ, ← heq]
    exact Nat.mul_le_mul_right q hsq
  change p < q ^ 3 at hcube
  omega

/-- Uniform lower sieve estimate, compared with the mean fiber size. -/
def H1 : Prop :=
  ∀ᶠ p : ℕ in atTop, p.Prime → ∀ x : ℕ, 1 ≤ x ∧ x < p →
    let rough := (Finset.range p).filter fun a => 2 ≤ a ∧ p < a.minFac ^ 3
    let pairs := (rough ×ˢ rough).filter fun t => (x : ZMod p) = (t.1 : ZMod p) * t.2
    9 * rough.card ^ 2 < 10 * ((p - 1) * pairs.card)

/-- Upper estimate for the semiprime-by-rough contribution in one orientation. -/
def H2 : Prop :=
  ∀ᶠ p : ℕ in atTop, p.Prime → ∀ x : ℕ, 1 ≤ x ∧ x < p →
    let rough := (Finset.range p).filter fun a => 2 ≤ a ∧ p < a.minFac ^ 3
    let pairs := (rough ×ˢ rough).filter fun t => (x : ZMod p) = (t.1 : ZMod p) * t.2
    let correction := pairs.filter fun t => (t.1 / t.1.minFac).Prime
    20 * ((p - 1) * correction.card) ≤ 9 * rough.card ^ 2

theorem main : H1 → H2 → type_of% @Green62.green_62 := by
  intro lower upper
  filter_upwards [lower, upper] with p hl hu
  intro hp A x hx
  let rough := (Finset.range p).filter fun a => 2 ≤ a ∧ p < a.minFac ^ 3
  let pairs := (rough ×ˢ rough).filter fun t => (x : ZMod p) = (t.1 : ZMod p) * t.2
  let correction := pairs.filter fun t => (t.1 / t.1.minFac).Prime
  have mem_pairs {a b : ℕ} : (a, b) ∈ pairs ↔ a ∈ rough ∧ b ∈ rough ∧
      (x : ZMod p) = (a : ZMod p) * b := by
    simp [pairs, and_assoc]
  have composite {a : ℕ} (ha : a ∈ rough) (hc : ¬a.Prime) : (a / a.minFac).Prime := by
    obtain ⟨hlt, htwo, hcube⟩ : a < p ∧ 2 ≤ a ∧ p < a.minFac ^ 3 := by
      simpa [rough] using ha
    exact twoFactors_of_composite hlt htwo hcube hc
  have hgap : 2 * correction.card < pairs.card := by
    have hh : 20 * ((p - 1) * correction.card) < 10 * ((p - 1) * pairs.card) :=
      lt_of_le_of_lt (hu hp x hx) (hl hp x hx)
    by_contra! h
    have hm := Nat.mul_le_mul_left (10 * (p - 1)) h
    nlinarith
  classical
  by_contra hnone
  have cover : pairs ⊆ correction ∪ correction.image Prod.swap := by
    rintro ⟨a, b⟩ hab
    obtain ⟨ha, hb, he⟩ := mem_pairs.mp hab
    by_cases hpa : a.Prime
    · have hnb : ¬b.Prime := by
        intro hpb
        apply hnone
        exact ⟨a, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, hpa⟩,
          b, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hb).1, hpb⟩, he⟩
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(b,a), Finset.mem_filter.mpr ⟨?_, composite hb hnb⟩, rfl⟩
      exact mem_pairs.mpr ⟨hb, ha, by simpa [mul_comm] using he⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨hab, composite ha hpa⟩)
  have hc := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have hi : (correction.image Prod.swap).card ≤ correction.card :=
    Finset.card_image_le
  omega

end OMA.R_Green62_green_62_R1
