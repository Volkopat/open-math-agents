import OMAReductions.R_Erdos7_erdos_7_R1
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! A finite search for the seed of the odd covering construction, with fresh
prime 3. The nonemptiness input is the case of Hough--Nielsen's theorem with
all moduli coprime to 6, https://arxiv.org/abs/1703.02133. -/

namespace OMA.R_Erdos7_erdos_7_R1_H1_R1

private def moduli (M : ℕ) : Finset ℕ := M.divisors.erase 1

private def residue {M : ℕ} (a : ∀ d : moduli M, Fin d.val) (d : ℕ) : ℤ :=
  if hd : d ∈ moduli M then ((a ⟨d, hd⟩).val : ℤ) else 0

private def holes (M : ℕ) (r : ℕ → ℤ) : Finset (Fin M) :=
  Finset.univ.filter fun x => ∀ d ∈ moduli M, ¬ (d : ℤ) ∣ (x.val : ℤ) - r d

private theorem divisor_of_mem {M d : ℕ} (hd : d ∈ moduli M) : d ∣ M :=
  (Nat.mem_divisors.mp (Finset.mem_erase.mp hd).2).1

private theorem representative {M : ℕ} (hM : 0 < M) (z : ℤ) :
    ∃ x : Fin M, (M : ℤ) ∣ z - (x.val : ℤ) := by
  have hMZ : (0 : ℤ) < M := by exact_mod_cast hM
  have hr0 : 0 ≤ z % (M : ℤ) := Int.emod_nonneg _ hMZ.ne'
  have hrM : z % (M : ℤ) < M := Int.emod_lt_of_pos z hMZ
  let x : Fin M := ⟨(z % (M : ℤ)).toNat, by omega⟩
  refine ⟨x, z / (M : ℤ), ?_⟩
  change z - ((z % (M : ℤ)).toNat : ℤ) = (M : ℤ) * (z / (M : ℤ))
  rw [Int.toNat_of_nonneg hr0]
  have hm := Int.emod_add_mul_ediv z (M : ℤ)
  omega

private theorem lift_cover {M : ℕ} {r : ℕ → ℤ} {z : ℤ} {x : Fin M}
    (hz : (M : ℤ) ∣ z - (x.val : ℤ)) {d : ℕ} (hd : d ∈ moduli M)
    (hx : (d : ℤ) ∣ (x.val : ℤ) - r d) : (d : ℤ) ∣ z - r d := by
  have hDM : (d : ℤ) ∣ (M : ℤ) := by exact_mod_cast divisor_of_mem hd
  have hsum := dvd_add (hDM.trans hz) hx
  rwa [sub_add_sub_cancel] at hsum

/-- A finite residue assignment outside 2 and 3 with fewer holes than its number of moduli. -/
def H1 : Prop := ∃ (M : ℕ) (a : ∀ d : moduli M, Fin d.val),
  Odd M ∧ ¬ 3 ∣ M ∧ (holes M (residue a)).card < (moduli M).card

/-- Hough--Nielsen, Theorem 1, for distinct positive moduli greater than one and coprime to six. -/
def H2 : Prop := ∀ (D : Finset ℕ) (r : ℕ → ℤ),
  (∀ d ∈ D, 1 < d ∧ Odd d ∧ ¬ 3 ∣ d) →
  ∃ z : ℤ, ∀ d ∈ D, ¬ (d : ℤ) ∣ z - r d

theorem main : H1 → H2 → OMA.R_Erdos7_erdos_7_R1.H1 := by
  classical
  intro hFinite hHN
  obtain ⟨M, a, hOdd, hThree, hCard⟩ := hFinite
  let r := residue a
  let U := holes M r
  let e : Fin U.card ≃o U := U.orderIsoOfFin rfl
  let u (i : Fin U.card) : ℕ := ((e i).val : Fin M).val
  have hProper : ∃ z : ℤ, ∀ d ∈ moduli M, ¬ (d : ℤ) ∣ z - r d := by
    apply hHN (moduli M) r
    intro d hd
    have hdiv := divisor_of_mem hd
    have hdpos := Nat.pos_of_dvd_of_pos hdiv hOdd.pos
    have hne : d ≠ 1 := (Finset.mem_erase.mp hd).1
    exact ⟨by omega, hOdd.of_dvd_nat hdiv, fun h => hThree (h.trans hdiv)⟩
  have hcop : Nat.Coprime 3 M := (show Nat.Prime 3 by decide).coprime_iff_not_dvd.mpr hThree
  have hb : (3 - 2) * U.card < (M.divisors.erase 1).card := by
    simpa [U, r, moduli] using hCard
  refine ⟨M, 3, U.card, u, r, by decide, by decide, hOdd, hcop, hb, hProper, ?_⟩
  intro z
  obtain ⟨x, hx⟩ := representative hOdd.pos z
  by_cases h : x ∈ U
  · right
    refine ⟨e.symm ⟨x, h⟩, ?_⟩
    simpa only [u, OrderIso.apply_symm_apply] using hx
  · left
    have hm : ¬ (∀ d ∈ moduli M, ¬ (d : ℤ) ∣ (x.val : ℤ) - r d) := by
      intro hh
      exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
    push Not at hm
    obtain ⟨d, hd, hxd⟩ := hm
    exact ⟨d, hd, lift_cover hx hd hxd⟩

end OMA.R_Erdos7_erdos_7_R1_H1_R1
