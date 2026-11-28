import OMAStatements.S_mo_404886
import Mathlib

open OMA.S_mo_404886

lemma qi_bound (J : Set ℕ) (h : IsQuasiIdeal {p | p.Prime} J) :
    ∃ m k, J = Set.Icc m (m + k) ∧ k ≤ 4 := by
  obtain ⟨k, _, m, rfl, a, ha, c, hc, hJ⟩ := h
  refine ⟨m, k, rfl, ?_⟩
  by_contra hk
  rw [not_le] at hk
  have hp : ∀ t ≤ 5, (a + c * (m + t)).Prime := fun t ht =>
    hJ (m + t) ⟨by omega, by omega⟩
  have h2 : ∀ x : ℕ, x.Prime → 2 ∣ x → x = 2 := fun x hx hd =>
    ((hx.eq_one_or_self_of_dvd 2 hd).resolve_left (by norm_num)).symm
  have h3 : ∀ x : ℕ, x.Prime → 3 ∣ x → x = 3 := fun x hx hd =>
    ((hx.eq_one_or_self_of_dvd 3 hd).resolve_left (by norm_num)).symm
  have hc0 : 0 < c := (show c.Prime from hc).pos
  set x := a + c * m with hx
  have e : ∀ t, a + c * (m + t) = x + c * t := fun t => by rw [hx]; ring
  simp only [e] at hp
  rcases (show c.Prime from hc).eq_two_or_odd' with hc2 | hodd
  · subst hc2
    have hmod : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
    rcases hmod with h | h | h
    · have := h3 _ (hp 0 (by norm_num)) (by omega)
      have := h3 _ (hp 3 (by norm_num)) (by omega)
      omega
    · have := h3 _ (hp 1 (by norm_num)) (by omega)
      have := h3 _ (hp 4 (by norm_num)) (by omega)
      omega
    · have := h3 _ (hp 2 (by norm_num)) (by omega)
      have := h3 _ (hp 5 (by norm_num)) (by omega)
      omega
  · obtain ⟨r, hr⟩ := hodd
    have hmod : x % 2 = 0 ∨ x % 2 = 1 := by omega
    rcases hmod with h | h
    · have := h2 _ (hp 0 (by norm_num)) (by omega)
      have := h2 _ (hp 2 (by norm_num)) (by omega)
      omega
    · have := h2 _ (hp 1 (by norm_num)) (by omega)
      have := h2 _ (hp 3 (by norm_num)) (by omega)
      omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_404886.main) := by
  intro h
  have hQ : QuasiNoetherian {p | p.Prime} := by
    intro s hs hmono
    have hb := fun i => qi_bound (s i) (hs i)
    choose m k hsi hk using hb
    have hmk : ∀ i j, i ≤ j → k i ≤ k j ∧ m j ≤ m i ∧ m i + k i ≤ m j + k j := by
      intro i j hij
      have hsub := hmono hij
      rw [hsi i, hsi j] at hsub
      rw [Set.Icc_subset_Icc_iff (by omega)] at hsub
      omega
    have hbdd : BddAbove (Set.range k) := ⟨4, by rintro _ ⟨i, rfl⟩; exact hk i⟩
    obtain ⟨N, hN⟩ := Nat.sSup_mem (Set.range_nonempty k) hbdd
    have hmax : ∀ n, k n ≤ k N := fun n => hN ▸ le_csSup hbdd ⟨n, rfl⟩
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hmk N n hn
    have := hmax n
    rw [hsi n, hsi N]
    have hk' : k n = k N := by omega
    have hm' : m n = m N := by omega
    rw [hk', hm']
  have := h {p | p.Prime} (fun n hn => (show n.Prime from hn).pos) hQ
  exact Nat.Primes.not_summable_one_div this
