import OMAStatements.S_oeis_a046385
import Mathlib

namespace OMA.S_oeis_a046385

private def powModAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, m => 1 % m
  | fuel + 1, b, e, m =>
    if e = 0 then 1 % m
    else
      let half := powModAux fuel b (e / 2) m
      let sq := (half * half) % m
      if e % 2 = 0 then sq else (sq * (b % m)) % m

private lemma powModAux_eq : ∀ fuel b e m : ℕ, e < 2 ^ fuel → powModAux fuel b e m = b ^ e % m
  | 0, b, e, m, h => by
    have he : e = 0 := by omega
    subst he; simp [powModAux]
  | fuel + 1, b, e, m, h => by
    simp only [powModAux]
    split_ifs with he hpar
    · subst he; simp
    · have hlt : e / 2 < 2 ^ fuel := by
        rw [pow_succ'] at h; omega
      rw [powModAux_eq fuel b (e / 2) m hlt]
      have he2 : e = e / 2 + e / 2 := by omega
      conv_rhs => rw [he2, pow_add]
      rw [← Nat.mul_mod]
    · have hlt : e / 2 < 2 ^ fuel := by
        rw [pow_succ'] at h; omega
      rw [powModAux_eq fuel b (e / 2) m hlt]
      have he2 : e = (e / 2 + e / 2) + 1 := by omega
      conv_rhs => rw [he2, pow_succ, pow_add]
      rw [Nat.mul_mod ((b ^ (e / 2) % m * (b ^ (e / 2) % m)) % m),
        Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod (b ^ (e / 2)),
        Nat.mul_mod (b ^ (e / 2) * b ^ (e / 2) % m), Nat.mod_mod, ← Nat.mul_mod, Nat.mul_mod_mod]

private lemma pocklington_prime {p g F fuel : ℕ} (hp2 : 2 ≤ p) (hpfuel : p < 2 ^ fuel)
    (hF : F ∣ p - 1) (hF2 : p < F * F)
    (hfermat : powModAux fuel g (p - 1) p = 1)
    (factors : List (ℕ × ℕ))
    (hprod : (factors.map fun qe => qe.1 ^ qe.2).prod = F)
    (hprimes : ∀ qe ∈ factors, qe.1.Prime)
    (hpair : factors.Pairwise fun a b => Nat.Coprime a.1 b.1)
    (hgcd : ∀ qe ∈ factors, 1 ≤ powModAux fuel g ((p - 1) / qe.1) p ∧
      Nat.gcd (powModAux fuel g ((p - 1) / qe.1) p - 1) p = 1) :
    p.Prime := by
  by_contra hnot
  set r := p.minFac
  have hrp : r.Prime := Nat.minFac_prime (by omega)
  have hrdvd : r ∣ p := Nat.minFac_dvd p
  have hrsq : r * r ≤ p := by
    have := Nat.minFac_sq_le_self (by omega) hnot
    simpa [sq] using this
  have : Fact r.Prime := ⟨hrp⟩
  let a : ZMod r := (g : ZMod r)
  have hpow1 : a ^ (p - 1) = 1 := by
    have h1 : g ^ (p - 1) % p = 1 := by
      rw [← powModAux_eq fuel g (p - 1) p (by omega), hfermat]
    have h2 : g ^ (p - 1) ≡ 1 [MOD p] := by
      rw [Nat.ModEq, h1, Nat.mod_eq_of_lt (by omega)]
    have h3 : g ^ (p - 1) ≡ 1 [MOD r] := h2.of_dvd hrdvd
    have h4 : ((g ^ (p - 1) : ℕ) : ZMod r) = ((1 : ℕ) : ZMod r) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h3
    simpa [a] using h4
  have hord_dvd_pm1 : orderOf a ∣ p - 1 := orderOf_dvd_of_pow_eq_one hpow1
  have hane : a ≠ 0 := by
    intro ha0
    rw [ha0, zero_pow (by omega : p - 1 ≠ 0)] at hpow1
    exact zero_ne_one hpow1
  have hord_dvd_rm1 : orderOf a ∣ r - 1 := by
    apply orderOf_dvd_of_pow_eq_one
    exact ZMod.pow_card_sub_one_eq_one hane
  have hqe_dvd : ∀ qe ∈ factors, qe.1 ^ qe.2 ∣ orderOf a := by
    intro qe hqe
    have hqp : qe.1.Prime := hprimes qe hqe
    have hqe_F : qe.1 ^ qe.2 ∣ F := by
      rw [← hprod]
      exact List.dvd_prod (List.mem_map.mpr ⟨qe, hqe, rfl⟩)
    have hqe_pm1 : qe.1 ^ qe.2 ∣ p - 1 := dvd_trans hqe_F hF
    by_contra hndvd
    rcases hord_dvd_pm1 with ⟨t, ht⟩
    have hqt : qe.1 ∣ t := by
      have : Fact qe.1.Prime := ⟨hqp⟩
      have hord_pos : 0 < orderOf a := by
        rcases Nat.eq_zero_or_pos (orderOf a) with h0 | hpos
        · rw [h0, zero_mul] at ht; omega
        · exact hpos
      have ht_pos : 0 < t := by
        rcases Nat.eq_zero_or_pos t with rfl | hpos
        · simp at ht; omega
        · exact hpos
      have hv_le : qe.2 ≤ padicValNat qe.1 (p - 1) :=
        (padicValNat_dvd_iff_le (by omega)).mp hqe_pm1
      have hv_lt : padicValNat qe.1 (orderOf a) < qe.2 := by
        by_contra hge
        push Not at hge
        exact hndvd ((padicValNat_dvd_iff_le hord_pos.ne').mpr hge)
      have hv_add : padicValNat qe.1 (p - 1) =
          padicValNat qe.1 (orderOf a) + padicValNat qe.1 t := by
        rw [ht, padicValNat.mul hord_pos.ne' ht_pos.ne']
      have hv_t : 1 ≤ padicValNat qe.1 t := by omega
      have hpow1_dvd : qe.1 ^ 1 ∣ t := (padicValNat_dvd_iff_le ht_pos.ne').mpr hv_t
      simpa using hpow1_dvd
    rcases hqt with ⟨t', rfl⟩
    have hdvd_quot : orderOf a ∣ (p - 1) / qe.1 := by
      refine ⟨t', ?_⟩
      have heq : p - 1 = qe.1 * (orderOf a * t') := by rw [ht]; ring
      rw [heq, Nat.mul_div_cancel_left _ hqp.pos]
    have haq : a ^ ((p - 1) / qe.1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp hdvd_quot
    have hpm := hgcd qe hqe
    set v := powModAux fuel g ((p - 1) / qe.1) p
    have hq_lt : (p - 1) / qe.1 < 2 ^ fuel :=
      lt_of_le_of_lt (Nat.div_le_self (p - 1) qe.1) (by omega)
    have hv_eq : v = g ^ ((p - 1) / qe.1) % p := powModAux_eq fuel g ((p - 1) / qe.1) p hq_lt
    have hv_mod : g ^ ((p - 1) / qe.1) ≡ v [MOD r] := by
      have : g ^ ((p - 1) / qe.1) ≡ v [MOD p] := by
        rw [Nat.ModEq, hv_eq, Nat.mod_mod]
      exact this.of_dvd hrdvd
    have hv_zmod : (v : ZMod r) = 1 := by
      have hcast : ((g ^ ((p - 1) / qe.1) : ℕ) : ZMod r) = (v : ZMod r) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hv_mod
      rw [← hcast]
      simpa [a] using haq
    have hrdvd_v1 : r ∣ v - 1 := by
      have h1 : ((v - 1 : ℕ) : ZMod r) = 0 := by
        rw [Nat.cast_sub hpm.1, hv_zmod, Nat.cast_one, sub_self]
      exact (ZMod.natCast_eq_zero_iff (v - 1) r).mp h1
    have hrdvd_gcd : r ∣ Nat.gcd (v - 1) p := Nat.dvd_gcd hrdvd_v1 hrdvd
    rw [hpm.2] at hrdvd_gcd
    exact hrp.not_dvd_one hrdvd_gcd
  have hF_dvd_ord : F ∣ orderOf a := by
    rw [← hprod]
    clear hprod hF hF2 hfermat hpow1 hord_dvd_pm1 hord_dvd_rm1 hane hgcd hpfuel
    induction factors with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [List.pairwise_cons] at hpair
      have hcop : Nat.Coprime (hd.1 ^ hd.2) ((tl.map fun qe => qe.1 ^ qe.2).prod) := by
        refine Nat.Coprime.pow_left hd.2 ?_
        have hall : ∀ y ∈ tl.map (fun qe => qe.1 ^ qe.2), Nat.Coprime hd.1 y := by
          intro y hy
          rcases List.mem_map.mp hy with ⟨qe, hqe, rfl⟩
          exact (hpair.1 qe hqe).pow_right qe.2
        clear ih hpair hqe_dvd hprimes
        generalize tl.map (fun qe => qe.1 ^ qe.2) = L at hall ⊢
        induction L with
        | nil => simp
        | cons x xs ihx =>
          simp only [List.prod_cons]
          exact Nat.Coprime.mul_right (hall x (by simp))
            (ihx fun y hy => hall y (by simp [hy]))
      exact hcop.mul_dvd_of_dvd_of_dvd (hqe_dvd hd (by simp))
        (ih (fun qe h => hprimes qe (by simp [h])) hpair.2 (fun qe h => hqe_dvd qe (by simp [h])))
  have hF_le : F ≤ r - 1 := Nat.le_of_dvd (by have := hrp.two_le; omega) (dvd_trans hF_dvd_ord hord_dvd_rm1)
  have hFr : F < r := by have := hrp.two_le; omega
  have hF2_le : F * F < r * r := Nat.mul_lt_mul'' hFr hFr
  omega

private def bigP : ℕ :=
  1000000000000000000000000001000000001000000001000000000000000000000000001

private def bigF : ℕ :=
  2 ^ 27 * 5 ^ 27 * 7 * 11 * 13 * 17 * 19 * 52579

private def pFactors : List (ℕ × ℕ) :=
  [(2, 27), (5, 27), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (52579, 1)]

set_option maxRecDepth 16000 in
private lemma bigP_prime : bigP.Prime := by
  refine pocklington_prime (g := 6) (F := bigF) (fuel := 250) (factors := pFactors)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_ (by decide) ?_
  · intro qe hqe
    simp only [pFactors, List.mem_cons, List.not_mem_nil, or_false] at hqe
    rcases hqe with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro qe hqe
    simp only [pFactors, List.mem_cons, List.not_mem_nil, or_false] at hqe
    rcases hqe with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private def witnessK : ℕ := 2977792 * bigP

private lemma witnessK_mem : witnessK ∈ palindromesWithFactorCount 14 := by
  have hKpos : 0 < witnessK := by decide
  have hKpal : (Nat.digits 10 witnessK).Palindrome := by decide
  have hPpal : (Nat.digits 10 bigP).Palindrome := by decide
  let L : List ℕ := [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 727, bigP]
  have hLprod : L.prod = witnessK := by decide
  have hLprime : ∀ q ∈ L, q.Prime := by
    intro q hq
    simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_two
    · exact Nat.prime_two
    · exact Nat.prime_two
    · exact Nat.prime_two
    · exact Nat.prime_two
    · exact Nat.prime_two
    · exact Nat.prime_two
    · exact Nat.prime_two
    · exact Nat.prime_two
    · exact Nat.prime_two
    · exact Nat.prime_two
    · norm_num
    · exact bigP_prime
  have hperm : witnessK.primeFactorsList.Perm L :=
    (Nat.primeFactorsList_unique hLprod hLprime).symm
  refine ⟨hKpos, hKpal, ?_, ?_⟩
  · rw [hperm.length_eq]; decide
  · intro q hq
    have hqL : q ∈ L := hperm.mem_iff.mp hq
    simp only [L, List.mem_cons, List.not_mem_nil, or_false] at hqL
    rcases hqL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · decide
    · exact hPpal

private lemma disproof_main : ¬ (∀ n k : ℕ,
    IsLeast (palindromesWithFactorCount n) k ↔ (n, k) ∈ knownTerms) := by
  classical
  intro h
  have hne : ∃ k, k ∈ palindromesWithFactorCount 14 := ⟨witnessK, witnessK_mem⟩
  let k0 := Nat.find hne
  have hleast : IsLeast (palindromesWithFactorCount 14) k0 :=
    ⟨Nat.find_spec hne, fun m hm => Nat.find_min' hne hm⟩
  have hmem : (14, k0) ∈ knownTerms := (h 14 k0).mp hleast
  have hno14 : ∀ p ∈ knownTerms, p.1 ≠ 14 := by decide
  exact hno14 (14, k0) hmem rfl

end OMA.S_oeis_a046385

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a046385.main) :=
  OMA.S_oeis_a046385.disproof_main
