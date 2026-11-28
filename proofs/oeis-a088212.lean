import OMAStatements.S_oeis_a088212

/-!
Source: https://oeis.org/A088212

For a prescribed least index m, force each earlier n + k² to be a proper
multiple of its own prime. The Chinese remainder theorem gives one progression
for n + m², and Dirichlet's theorem supplies a large prime in that progression.
-/

open scoped BigOperators

theorem OMA.solution : type_of% @OMA.S_oeis_a088212.main := by
  classical
  intro m hm
  let indices := Finset.Ico 2 m
  let q (k : ℕ) := Nat.nth Nat.Prime (m ^ 2 + 1 + k)
  have qprime (k : ℕ) : (q k).Prime :=
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime _
  have qlarge (k : ℕ) : m ^ 2 < q k := by
    have h : m ^ 2 + 1 + k ≤ q k :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le (m ^ 2 + 1 + k)
    exact (show m ^ 2 < m ^ 2 + 1 + k by omega).trans_le h
  have qmono : StrictMono q :=
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).comp
      (fun _ _ h => Nat.add_lt_add_left h _)
  have qcoprime : Set.Pairwise (↑indices : Set ℕ) (Function.onFun Nat.Coprime q) := by
    intro i _ j _ hij
    exact (Nat.coprime_primes (qprime i) (qprime j)).mpr (qmono.injective.ne hij)
  let modulus := ∏ k ∈ indices, q k
  have hmodulus : 0 < modulus :=
    Finset.prod_pos (fun k _ => (qprime k).pos)
  obtain ⟨a, ha⟩ := Nat.chineseRemainderOfFinset (fun k => m ^ 2 - k ^ 2) q indices
    (fun k _ => (qprime k).ne_zero) qcoprime
  have residue_coprime : a.Coprime modulus := by
    apply Nat.Coprime.prod_right
    intro k hk
    have hkm : k < m := (Finset.mem_Ico.mp hk).2
    have hsq : k ^ 2 < m ^ 2 := Nat.pow_lt_pow_left hkm (by decide)
    have hpos : 0 < m ^ 2 - k ^ 2 := Nat.sub_pos_of_lt hsq
    have hlt : m ^ 2 - k ^ 2 < q k := (Nat.sub_le _ _).trans_lt (qlarge k)
    apply Nat.Coprime.symm
    apply (qprime k).coprime_iff_not_dvd.mpr
    intro hd
    have hd' := ((ha k hk).dvd_iff (dvd_refl (q k))).mp hd
    exact hlt.not_ge (Nat.le_of_dvd hpos hd')
  obtain ⟨p, hplarge, hp, hpa⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (m ^ 2 + modulus) hmodulus.ne' residue_coprime
  let n := p - m ^ 2
  have hn : modulus < n := by dsimp [n]; omega
  have hnp : n + m ^ 2 = p := by dsimp [n]; omega
  have hin : m ∈ {k : ℕ | 1 < k ∧ (n + k ^ 2).Prime} := ⟨hm, by simpa only [hnp] using hp⟩
  refine ⟨n, by omega, ?_⟩
  change sInf {k : ℕ | 1 < k ∧ (n + k ^ 2).Prime} = m
  refine le_antisymm (Nat.sInf_le hin) ?_
  apply le_csInf ⟨m, hin⟩
  intro k hk
  change 1 < k ∧ (n + k ^ 2).Prime at hk
  by_contra! hkm
  have hki : k ∈ indices := Finset.mem_Ico.mpr ⟨hk.1, hkm⟩
  have hqdiv : q k ∣ modulus := Finset.dvd_prod_of_mem q hki
  have hqle : q k ≤ modulus := Nat.le_of_dvd hmodulus hqdiv
  have hsq : k ^ 2 < m ^ 2 := Nat.pow_lt_pow_left hkm (by decide)
  have hpk : p ≡ m ^ 2 - k ^ 2 [MOD q k] := (hpa.of_dvd hqdiv).trans (ha k hki)
  have hmultiple : q k ∣ n + k ^ 2 := by
    apply Nat.modEq_zero_iff_dvd.mp
    apply Nat.ModEq.add_left_cancel' (m ^ 2)
    calc
      m ^ 2 + (n + k ^ 2) = p + k ^ 2 := by omega
      _ ≡ (m ^ 2 - k ^ 2) + k ^ 2 [MOD q k] := hpk.add_right _
      _ = m ^ 2 + 0 := by omega
  have hqeq := (hk.2.eq_one_or_self_of_dvd (q k) hmultiple).resolve_left (qprime k).ne_one
  omega
