import OMAStatements.S_oeis_a364153
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

namespace OMA.P_oeis_a364153

open OMA.S_oeis_a364153

/-- Erdős–Turán Sidon sequence `P_p(k) = 2*p*k + (k^2 mod p)`. -/
private def etSeq (p k : ℕ) : ℕ :=
  2 * p * k + k ^ 2 % p

private lemma etSeq_strictMono_step (p : ℕ) (hp : 1 ≤ p) (k : ℕ) :
    etSeq p k < etSeq p (k + 1) ∧ etSeq p (k + 1) - etSeq p k ≤ 3 * p - 1 := by
  unfold etSeq
  have h1 : k ^ 2 % p < p := Nat.mod_lt _ (by omega)
  have h2 : (k + 1) ^ 2 % p < p := Nat.mod_lt _ (by omega)
  have hmul : 2 * p * (k + 1) = 2 * p * k + 2 * p := by ring
  omega

private lemma etSeq_mono (p : ℕ) (hp : 1 ≤ p) {i j : ℕ} (hij : i ≤ j) :
    etSeq p i ≤ etSeq p j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ m _ ih =>
    have hstep := (etSeq_strictMono_step p hp m).1
    omega

private lemma sum_Icc_etSeq_diff (p : ℕ) (hp : 1 ≤ p) {i j : ℕ} (hij : i ≤ j) :
    ∑ k ∈ Finset.Icc i j, (etSeq p (k + 1) - etSeq p k) = etSeq p (j + 1) - etSeq p i := by
  induction j, hij using Nat.le_induction with
  | base =>
    simp
  | succ m hm ih =>
    have hIcc : Finset.Icc i (m + 1) = insert (m + 1) (Finset.Icc i m) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : m + 1 ∉ Finset.Icc i m := by
      simp only [Finset.mem_Icc]
      omega
    rw [hIcc, Finset.sum_insert hnotmem, ih]
    have h1 : etSeq p i ≤ etSeq p (m + 1) := etSeq_mono p hp (by omega)
    have h2 : etSeq p (m + 1) ≤ etSeq p (m + 1 + 1) := le_of_lt (etSeq_strictMono_step p hp (m + 1)).1
    omega

/-- Sidon property of the Erdős–Turán sequence for an odd prime `p`:
if `a, b, c, d < p` and `etSeq p a + etSeq p b = etSeq p c + etSeq p d`, then `a = c ∨ a = d`. -/
private lemma etSeq_sidon {p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    {a b c d : ℕ} (ha : a < p) (_hb : b < p) (hc : c < p) (hd : d < p)
    (heq : etSeq p a + etSeq p b = etSeq p c + etSeq p d) :
    a = c ∨ a = d := by
  unfold etSeq at heq
  have hp_pos : 0 < p := hp.pos
  have hra : a ^ 2 % p < p := Nat.mod_lt _ hp_pos
  have hrb : b ^ 2 % p < p := Nat.mod_lt _ hp_pos
  have hrc : c ^ 2 % p < p := Nat.mod_lt _ hp_pos
  have hrd : d ^ 2 % p < p := Nat.mod_lt _ hp_pos
  have hlin : 2 * p * (a + b) + (a ^ 2 % p + b ^ 2 % p) =
      2 * p * (c + d) + (c ^ 2 % p + d ^ 2 % p) := by linarith
  have hsum_nat : a + b = c + d := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmul : 2 * p * (a + b + 1) ≤ 2 * p * (c + d) := Nat.mul_le_mul_left (2 * p) hlt
      rw [mul_add, mul_one] at hmul
      omega
    · have hmul : 2 * p * (c + d + 1) ≤ 2 * p * (a + b) := Nat.mul_le_mul_left (2 * p) hgt
      rw [mul_add, mul_one] at hmul
      omega
  have hrem_nat : a ^ 2 % p + b ^ 2 % p = c ^ 2 % p + d ^ 2 % p := by
    nlinarith
  have : Fact p.Prime := ⟨hp⟩
  have hsumZ : (a : ZMod p) + (b : ZMod p) = (c : ZMod p) + (d : ZMod p) := by
    have := congrArg (Nat.cast : ℕ → ZMod p) hsum_nat
    simpa [Nat.cast_add] using this
  have hsqZ : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = (c : ZMod p) ^ 2 + (d : ZMod p) ^ 2 := by
    have h1 := congrArg (Nat.cast : ℕ → ZMod p) hrem_nat
    simp only [Nat.cast_add, ZMod.natCast_mod, Nat.cast_pow] at h1
    exact h1
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h0)
    have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hdvd
    omega
  have h2prod : (2 : ZMod p) * ((a : ZMod p) * (b : ZMod p) - (c : ZMod p) * (d : ZMod p)) = 0 := by
    calc (2 : ZMod p) * ((a : ZMod p) * (b : ZMod p) - (c : ZMod p) * (d : ZMod p))
        = ((a : ZMod p) + (b : ZMod p)) ^ 2 - ((a : ZMod p) ^ 2 + (b : ZMod p) ^ 2) -
            (((c : ZMod p) + (d : ZMod p)) ^ 2 - ((c : ZMod p) ^ 2 + (d : ZMod p) ^ 2)) := by ring
      _ = 0 := by rw [hsumZ, hsqZ]; ring
  have hprodZ : (a : ZMod p) * (b : ZMod p) = (c : ZMod p) * (d : ZMod p) := by
    have := (mul_eq_zero.mp h2prod).resolve_left h2ne
    exact sub_eq_zero.mp this
  have hfacZ : ((a : ZMod p) - (c : ZMod p)) * ((a : ZMod p) - (d : ZMod p)) = 0 := by
    calc ((a : ZMod p) - (c : ZMod p)) * ((a : ZMod p) - (d : ZMod p))
        = (a : ZMod p) ^ 2 - ((c : ZMod p) + (d : ZMod p)) * (a : ZMod p) +
            (c : ZMod p) * (d : ZMod p) := by ring
      _ = (a : ZMod p) ^ 2 - ((a : ZMod p) + (b : ZMod p)) * (a : ZMod p) +
            (a : ZMod p) * (b : ZMod p) := by rw [← hsumZ, ← hprodZ]
      _ = 0 := by ring
  rcases mul_eq_zero.mp hfacZ with hac | had
  · left
    have hZ : (a : ZMod p) = (c : ZMod p) := sub_eq_zero.mp hac
    have hv := congrArg ZMod.val hZ
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] using hv
  · right
    have hZ : (a : ZMod p) = (d : ZMod p) := sub_eq_zero.mp had
    have hv := congrArg ZMod.val hZ
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hd] using hv

private theorem prove_main : type_of% @OMA.S_oeis_a364153.main := by
  refine ⟨7, 6, fun n hn => ?_⟩
  obtain ⟨p, hp_prime, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul (n + 1) (by omega)
  have hp2 : 2 < p := by omega
  have hp1 : 1 ≤ p := by omega
  have hmem : 3 * p - 1 ∈ {m : ℕ | 1 ≤ m ∧ HasUniqueSegmentSums n m} := by
    refine ⟨by omega, fun k => etSeq p (k + 1) - etSeq p k, ?_, ?_⟩
    · intro k _
      have hstep := etSeq_strictMono_step p hp1 k
      exact ⟨Nat.sub_pos_of_lt hstep.1, hstep.2⟩
    · intro i₁ j₁ i₂ j₂ h1 hj1 h2 hj2 hsum
      rw [sum_Icc_etSeq_diff p hp1 h1, sum_Icc_etSeq_diff p hp1 h2] at hsum
      have hle1 : etSeq p i₁ ≤ etSeq p (j₁ + 1) := etSeq_mono p hp1 (by omega)
      have hle2 : etSeq p i₂ ≤ etSeq p (j₂ + 1) := etSeq_mono p hp1 (by omega)
      have hadd : etSeq p (j₁ + 1) + etSeq p i₂ = etSeq p (j₂ + 1) + etSeq p i₁ := by omega
      have hsid := etSeq_sidon hp_prime hp2 (by omega) (by omega) (by omega) (by omega) hadd
      rcases hsid with hj_eq | hbad
      · have hj : j₁ = j₂ := by omega
        subst hj
        have hstep_eq : etSeq p i₂ = etSeq p i₁ := by omega
        have hi : i₁ = i₂ := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have h1' := etSeq_mono p hp1 (show i₁ + 1 ≤ i₂ by omega)
            have h2' := (etSeq_strictMono_step p hp1 i₁).1
            omega
          · have h1' := etSeq_mono p hp1 (show i₂ + 1 ≤ i₁ by omega)
            have h2' := (etSeq_strictMono_step p hp1 i₂).1
            omega
        exact ⟨hi, rfl⟩
      · omega
  have hle_inf : a n ≤ 3 * p - 1 := Nat.sInf_le hmem
  omega

end OMA.P_oeis_a364153

theorem OMA.solution : type_of% @OMA.S_oeis_a364153.main :=
  OMA.P_oeis_a364153.prove_main
