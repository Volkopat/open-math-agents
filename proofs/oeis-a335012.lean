import OMAStatements.S_oeis_a335012
import Mathlib

namespace RepunitRemainders

def R (b j : ℕ) : ℕ := ∑ i ∈ Finset.range j, b^i

def residues (b n : ℕ) : Finset (ZMod n) :=
  (Finset.range n).image fun j => (R b (j+1) : ZMod n)

end RepunitRemainders

namespace RepunitRemainders

private theorem geom_identity (j : ℕ) : 9 * R 10 j + 1 = 10^j := by
  induction j with
  | zero => simp [R]
  | succ j ih =>
    rw [show R 10 (j+1) = R 10 j + 10^j by simp [R, Finset.sum_range_succ], pow_succ]
    omega

theorem order_dvd_phi {n : ℕ} (hc : n.Coprime 10) :
    orderOf (10 : ZMod n) ∣ n.totient := by
  apply orderOf_dvd_of_pow_eq_one
  simpa using (ZMod.natCast_eq_natCast_iff (10^n.totient) 1 n).mpr (Nat.ModEq.pow_totient hc.symm)

theorem card_eq_order {n : ℕ} (hn : 0 < n) (hc : n.Coprime 10) (h3 : ¬3∣n) :
    (residues 10 n).card = orderOf (10 : ZMod n) := by
  let x : ZMod n := 10
  have hunit : IsUnit x := (ZMod.isUnit_iff_coprime 10 n).mpr hc.symm
  have h9 : IsUnit (9 : ZMod n) :=
    (ZMod.isUnit_iff_coprime 9 n).mpr ((Nat.prime_three.coprime_iff_not_dvd.mpr h3).pow_left 2)
  let g (v : ZMod n) := 9*v+1
  have hg : Function.Injective g := fun _ _ h => h9.mul_right_inj.mp (add_right_cancel h)
  have hmul : Function.Injective (fun v : ZMod n => v*x) := fun _ _ h => hunit.mul_left_inj.mp h
  have hmap : (residues 10 n).image g = ((Finset.range n).image (x^·)).image (·*x) := by
    simp only [residues, Finset.image_image]
    apply Finset.image_congr
    intro j _
    change 9*(R 10 (j+1) : ZMod n)+1 = x^j*x
    rw [← pow_succ]
    dsimp [x]
    simpa using congrArg (fun v : ℕ => (v : ZMod n)) (geom_identity (j+1))
  have hphi := Nat.totient_pos.mpr hn
  have hdvd : orderOf x ∣ n.totient := order_dvd_phi hc
  have hpos := Nat.pos_of_dvd_of_pos hdvd hphi
  have hle := (Nat.le_of_dvd hphi hdvd).trans (Nat.totient_le n)
  have heq : (Finset.range n).image (x^·) = (Finset.range (orderOf x)).image (x^·) := by
    apply Finset.Subset.antisymm
    · intro v hv
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨j % orderOf x, Finset.mem_range.mpr (Nat.mod_lt _ hpos),
        pow_mod_orderOf x j⟩
    · exact Finset.image_mono _ (Finset.range_mono hle)
  have hinj : Set.InjOn (x^·) (↑(Finset.range (orderOf x)) : Set ℕ) := by
    intro a ha b hb h
    exact pow_injOn_Iio_orderOf (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) h
  calc
    (residues 10 n).card = ((residues 10 n).image g).card :=
      (Finset.card_image_of_injective _ hg).symm
    _ = ((Finset.range n).image (x^·)).card := by rw [hmap, Finset.card_image_of_injective _ hmul]
    _ = orderOf x := by rw [heq, Finset.card_image_of_injOn hinj, Finset.card_range]

end RepunitRemainders

namespace RepunitRemainders

private theorem orbit_succ (b a : ℕ) : R b (a+1) = R b a + b^a := by
  simp [R, Finset.sum_range_succ]

private theorem orbit_add (b a d : ℕ) : R b (a+d) = R b a + b^a * R b d := by
  induction d with
  | zero => simp [R]
  | succ d hd =>
    rw [Nat.add_succ, orbit_succ, hd, orbit_succ, pow_add]
    ring

private theorem orbit_mod_three (d : ℕ) : (R 10 d : ZMod 3) = d := by
  have h10 : (10 : ZMod 3) = 1 := by decide +kernel
  simp [R, Nat.cast_sum, Nat.cast_pow, h10]

/-- Invertibility of 10 converts a collision of repunits to a period. If exactly one
residue were missing, the period would have to be n−1, whereas 3 divides every period. -/
theorem three_dvd_excludes {n : ℕ} (hn : 0<n) (h3 : 3∣n) (hc : n.Coprime 10) :
    (residues 10 n).card ≠ n-1 := by
  intro hcard
  let f (j : ℕ) : ZMod n := (R 10 (j+1) : ZMod n)
  have hlt : ((Finset.range n).image f).card < (Finset.range n).card := by
    change (residues 10 n).card < _
    rw [hcard, Finset.card_range]
    omega
  obtain ⟨i, hi, j, hj, hne, he⟩ := Finset.exists_ne_map_eq_of_card_image_lt hlt
  have hx : ∃ a b : ℕ, a < b ∧ b < n ∧ f a = f b := by
    rcases lt_or_gt_of_ne hne with h|h
    · exact ⟨i, j, h, Finset.mem_range.mp hj, he⟩
    · exact ⟨j, i, h, Finset.mem_range.mp hi, he.symm⟩
  obtain ⟨a, b, hab, hbn, heq⟩ := hx
  let d := b-a
  have hd : 0 < d := by dsimp [d]; omega
  have hindex : a+1+d = b+1 := by dsimp [d]; omega
  have hsum := congrArg (fun v : ℕ => (v : ZMod n)) (orbit_add 10 (a+1) d)
  rw [hindex] at hsum
  push_cast at hsum
  change (R 10 (a+1) : ZMod n) = (R 10 (b+1) : ZMod n) at heq
  have hzprod : (10:ZMod n)^(a+1) * (R 10 d : ZMod n) = 0 := by
    apply add_left_cancel (a := (R 10 (a+1) : ZMod n))
    simpa only [add_zero] using hsum.symm.trans heq.symm
  have hunit : IsUnit (10 : ZMod n) := (ZMod.isUnit_iff_coprime 10 n).mpr hc.symm
  have hz : (R 10 d : ZMod n) = 0 :=
    (hunit.pow (a+1)).mul_right_inj.mp (by simpa only [mul_zero] using hzprod)
  have hper : Function.Periodic f d := by
    intro t
    change (R 10 (t+d+1) : ZMod n) = (R 10 (t+1) : ZMod n)
    rw [show t+d+1 = (t+1)+d by omega, orbit_add]
    push_cast
    simp [hz]
  have hsub : residues 10 n ⊆ (Finset.range d).image f := by
    intro x h
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨t%d, Finset.mem_range.mpr (Nat.mod_lt _ hd), hper.map_mod_nat t⟩
  have hle := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [hcard, Finset.card_range] at hle
  have hdiv := (ZMod.natCast_eq_zero_iff (R 10 d) n).mp hz
  have hzero := (ZMod.natCast_eq_zero_iff (R 10 d) 3).mpr (h3.trans hdiv)
  rw [orbit_mod_three] at hzero
  have hd3 := (ZMod.natCast_eq_zero_iff d 3).mp hzero
  dsimp [d] at hle hd3
  omega

end RepunitRemainders

namespace RepunitRemainders

private theorem nonunit_reduction {p : ℕ} (h : p ∣ 10) (j : ℕ) :
    (R 10 (j+1) : ZMod p) = 1 := by
  have hzero : ((10 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff 10 p).mpr h
  induction j with
  | zero => simp [R]
  | succ j ih =>
    have he : R 10 (j+1+1) = R 10 (j+1) + 10^(j+1) := by
      simp only [R, Finset.sum_range_succ]
    rw [he, Nat.cast_add, Nat.cast_pow, ih, hzero, zero_pow (by omega), add_zero]

/-- Every repunit reduces to 1 modulo any common prime factor of the modulus
and the base. For n > 2 this omits the distinct residues 0 and 2 modulo n. -/
theorem noncoprime_excludes {n : ℕ} (hn : 2 < n) (hc : ¬ n.Coprime 10) :
    (residues 10 n).card ≠ n-1 := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨p, hp, hpn, hp10⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  let : Fact p.Prime := ⟨hp⟩
  have hmap (x : ZMod n) (hx : x ∈ residues 10 n) : ZMod.castHom hpn (ZMod p) x = 1 := by
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    simpa only [map_natCast] using nonunit_reduction hp10 j
  have htwo : (2 : ZMod p) ≠ 1 := by
    intro e
    apply (one_ne_zero : (1 : ZMod p) ≠ 0)
    linear_combination e
  have distinct : (2 : ZMod n) ≠ 0 := by
    intro e
    have := (ZMod.natCast_eq_zero_iff 2 n).mp e
    have := Nat.le_of_dvd (by decide : 0<2) this
    omega
  have keep : (2 : ZMod n) ∈ Finset.univ.erase (0 : ZMod n) := by simp [distinct]
  have sub : residues 10 n ⊆ (Finset.univ.erase (0 : ZMod n)).erase 2 := by
    intro x hx
    have hx' := hmap x hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
    · rintro rfl
      exact htwo (by simpa only [map_ofNat] using hx')
    · rintro rfl
      exact zero_ne_one (by simpa only [map_zero] using hx')
  have hcard := Finset.card_le_card sub
  rw [Finset.card_erase_of_mem keep, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card] at hcard
  omega

end RepunitRemainders

namespace RepunitRemainders

/-- The sole exceptional index is two. -/
theorem classification {n : ℕ} (hn : 0 < n) :
    ((residues 10 n).card = n-1 ↔
      n = 2 ∨ (n.Prime ∧ n.Coprime 10 ∧ orderOf (10 : ZMod n) = n-1)) := by
  constructor
  · intro h
    by_cases h2 : n = 2
    · exact Or.inl h2
    right
    by_cases h1 : n = 1
    · subst n
      exact False.elim ((by decide +kernel : (residues 10 1).card ≠ 1-1) h)
    have hlarge : 2 < n := by omega
    have hc : n.Coprime 10 := by
      by_contra hc
      exact noncoprime_excludes hlarge hc h
    have h3 : ¬3∣n := fun hd => three_dvd_excludes hn hd hc h
    rw [card_eq_order hn hc h3] at h
    have hle := Nat.le_of_dvd (Nat.totient_pos.mpr hn) (order_dvd_phi hc)
    have hlt := Nat.totient_lt n (by omega)
    exact ⟨(Nat.totient_eq_iff_prime hn).mp (by omega),hc,h⟩
  · rintro (rfl | ⟨hp,hc,ho⟩)
    · decide +kernel
    · have h3 : ¬3∣n := by
        intro hd
        rcases (Nat.dvd_prime hp).mp hd with he|he
        · omega
        · subst n
          have hone : (10 : ZMod 3) = 1 := by decide +kernel
          rw [hone, orderOf_one] at ho
          omega
      exact (card_eq_order hn hc h3).trans ho

end RepunitRemainders

theorem OMA.solution : type_of% @OMA.S_oeis_a335012.main := by
  intro n hn
  exact RepunitRemainders.classification hn
