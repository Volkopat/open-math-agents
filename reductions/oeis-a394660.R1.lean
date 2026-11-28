import OMAStatements.S_oeis_a394660

-- Credit: @Pixelstorm44
namespace OMA.R_oeis_a394660_R1

/-- Cube-root sieve for p ≡ 1 modulo three. Count ordered semiprime
factor pairs in the band u ≤ v < u² and compare with all sifted shifts. -/
def H1 : Prop := by
  classical
  exact ∀ p : ℕ, p.Prime → 3 ≤ p → ¬ (∃ q k : ℕ, q.Prime ∧ q < p ∧ (p - q = 2 ^ k ∨ p - q = 3 ^ k)) → p % 3 = 1 →
    let sifted := (Finset.Ico 2 p).filter fun n =>
      (∃ a b : ℕ, p - n = 6 * (2 ^ a * 3 ^ b)) ∧ n < n.minFac ^ 3
    let products := ((Finset.Icc 2 p.sqrt) ×ˢ (Finset.range p)).filter fun z =>
      z.1.Prime ∧ z.2.Prime ∧ z.1 ≤ z.2 ∧ z.2 < z.1 ^ 2 ∧ z.1 * z.2 < p ∧
      (∃ a b : ℕ, p - z.1 * z.2 = 6 * (2 ^ a * 3 ^ b)) ∧ z.1 % 3 = z.2 % 3
    products.card < sifted.card

/-- Cube-root sieve for p ≡ 2 modulo three. Count ordered semiprime
factor pairs in the band u ≤ v < u² and compare with all sifted shifts. -/
def H2 : Prop := by
  classical
  exact ∀ p : ℕ, p.Prime → 3 ≤ p → ¬ (∃ q k : ℕ, q.Prime ∧ q < p ∧ (p - q = 2 ^ k ∨ p - q = 3 ^ k)) → p % 3 = 2 →
    let sifted := (Finset.Ico 2 p).filter fun n =>
      (∃ a b : ℕ, p - n = 6 * (2 ^ a * 3 ^ b)) ∧ n < n.minFac ^ 3
    let products := ((Finset.Icc 2 p.sqrt) ×ˢ (Finset.range p)).filter fun z =>
      z.1.Prime ∧ z.2.Prime ∧ z.1 ≤ z.2 ∧ z.2 < z.1 ^ 2 ∧ z.1 * z.2 < p ∧
      (∃ a b : ℕ, p - z.1 * z.2 = 6 * (2 ^ a * 3 ^ b)) ∧ z.1 % 3 ≠ z.2 % 3
    products.card < sifted.card

private theorem factor_band {n : ℕ} (hn : 2 ≤ n) (hc : ¬ n.Prime)
    (hrough : n < n.minFac ^ 3) :
    ∃ u v : ℕ, u.Prime ∧ v.Prime ∧ u ≤ v ∧ v < u ^ 2 ∧ n = u * v := by
  let u := n.minFac
  have hu : u.Prime := Nat.minFac_prime (by omega)
  obtain ⟨v, hv⟩ := Nat.minFac_dvd n
  change n = u * v at hv
  have hv2 : 2 ≤ v := by
    by_contra! h
    interval_cases v <;> simp_all
  have huv := Nat.minFac_le_of_dvd hv2 (show v ∣ n from ⟨u, by simpa [mul_comm] using hv⟩)
  change u ≤ v at huv
  have hband : v < u ^ 2 := by
    apply (Nat.mul_lt_mul_left hu.pos).mp
    simpa [hv.symm, ← pow_succ', u] using hrough
  have hvp : v.Prime := by
    by_contra h
    have hsq := Nat.minFac_sq_le_self (by omega : 0 < v) h
    have hd : v.minFac ∣ n := (Nat.minFac_dvd v).trans ⟨u, by simpa [mul_comm] using hv⟩
    have hl : u ≤ v.minFac := Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega : v ≠ 1)).two_le hd
    nlinarith [Nat.pow_le_pow_left hl 2]
  exact ⟨u, v, hu, hvp, huv, hband, hv⟩

private theorem residue_pattern {u v : ℕ} (hne : u * v % 3 ≠ 0) :
    (u % 3 = v % 3) ↔ u * v % 3 = 1 := by
  rw [Nat.mul_mod] at hne ⊢
  have hu := Nat.mod_lt u (by decide : 0 < 3)
  have hv := Nat.mod_lt v (by decide : 0 < 3)
  generalize u % 3 = x at *
  generalize v % 3 = y at *
  interval_cases x <;> interval_cases y <;> norm_num at *

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a394660.main := by
  classical
  intro h1 h2 p hp hp3
  by_cases axis : (∃ q k : ℕ, q.Prime ∧ q < p ∧ (p - q = 2 ^ k ∨ p - q = 3 ^ k))
  · obtain ⟨q,k,hq,hlt,h | h⟩ := axis
    · exact ⟨q,hq,hlt,k,0,by simpa using h⟩
    · exact ⟨q,hq,hlt,0,k,by simpa using h⟩
  have hp0 : p % 3 ≠ 0 := by
    intro h
    have he := (Nat.dvd_prime_two_le hp (by decide : 2 ≤ 3)).mp (Nat.dvd_of_mod_eq_zero h)
    subst p
    exact axis ⟨2,0,Nat.prime_two,by decide,Or.inl (by decide)⟩
  let sifted := (Finset.Ico 2 p).filter fun n =>
      (∃ a b : ℕ, p - n = 6 * (2 ^ a * 3 ^ b)) ∧ n < n.minFac ^ 3
  let products := ((Finset.Icc 2 p.sqrt) ×ˢ (Finset.range p)).filter fun z =>
      z.1.Prime ∧ z.2.Prime ∧ z.1 ≤ z.2 ∧ z.2 < z.1 ^ 2 ∧ z.1 * z.2 < p ∧
      (∃ a b : ℕ, p - z.1 * z.2 = 6 * (2 ^ a * 3 ^ b)) ∧ (z.1 % 3 = z.2 % 3 ↔ p % 3 = 1)
  have hcount : products.card < sifted.card := by
    have hm := Nat.mod_lt p (by decide : 0 < 3)
    by_cases h : p % 3 = 1
    · simpa [products,sifted,h] using h1 p hp hp3 axis h
    · simpa [products,sifted,h] using h2 p hp hp3 axis (by omega)
  by_contra hnone
  have cover : sifted ⊆ products.image (fun z => z.1 * z.2) := by
    intro n hn
    obtain ⟨hi,⟨a,b,hgap⟩,hr⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn2,hnp⟩ := Finset.mem_Ico.mp hi
    have hdiff : p - n = 2 ^ (a+1) * 3 ^ (b+1) := by rw [hgap]; ring
    have hcomp : ¬ n.Prime := fun h => hnone ⟨n,h,hnp,a+1,b+1,hdiff⟩
    obtain ⟨u,v,hu,hv,huv,hband,he⟩ := factor_band hn2 hcomp hr
    have hmod : u * v % 3 = p % 3 := by omega
    have hpat := residue_pattern (hne := (hmod.trans_ne hp0))
    have hbool : u % 3 = v % 3 ↔ p % 3 = 1 := by simpa only [hmod] using hpat
    have hs : u ≤ p.sqrt := (Nat.le_sqrt).mpr (by nlinarith [Nat.mul_le_mul_left u huv])
    have hvp : v < p := by nlinarith [Nat.le_mul_of_pos_left v hu.pos]
    refine Finset.mem_image.mpr ⟨(u,v), ?_, he.symm⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hu.two_le,hs⟩, Finset.mem_range.mpr hvp⟩,
      hu,hv,huv,hband,he ▸ hnp,⟨a,b,he ▸ hgap⟩,hbool⟩
  exact (Nat.not_lt_of_ge ((Finset.card_le_card cover).trans Finset.card_image_le)) hcount

end OMA.R_oeis_a394660_R1
