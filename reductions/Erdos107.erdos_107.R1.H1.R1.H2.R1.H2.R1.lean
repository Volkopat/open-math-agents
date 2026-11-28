import OMAReductions.R_Erdos107_erdos_107_R1_H1_R1_H2_R1

/-!
Reduce the 17-point normalized Boolean signotope problem H2 to four symmetry-broken
16-point cup-cap signotope subproblems on the central 4-tuple (6, 7, 8, 9).

Restricting g to h a b c := g a.succ b.succ c.succ on Fin 16, we prove two structural
theorems for arbitrary rank-3 signotopes:
1. Cup-Cap Union Lemma: any 5-cap (together with vertex 0), any 6-cup, any (4, 4)
   cap-cup pair sharing endpoints, or any (3, 5) cap-cup pair sharing endpoints
   yields a 6-element anchored-even subset of Fin 17.
2. Left-Right Reflection Symmetry: reversing Fin 16 (i ↦ 15 - i) preserves the
   signotope axiom and all four cup-cap configurations, cutting the central 4-tuple
   case split in half.
-/

namespace OMA.R_Erdos107_erdos_107_R1_H1_R1_H2_R1_H2_R1

open Finset

private theorem packet_eq_of_ends {h : Fin 16 → Fin 16 → Fin 16 → Bool}
    (hp : ∀ a b c d, a < b → b < c → c < d →
      (h a b c = h a b d ∧ h a b d = h a c d) ∨
      (h a b c = h a b d ∧ h a c d = h b c d) ∨
      (h a b d = h a c d ∧ h a c d = h b c d))
    {a b c d : Fin 16} (hab : a < b) (hbc : b < c) (hcd : c < d) {v : Bool}
    (h1 : h a b c = v) (h2 : h b c d = v) :
    h a b d = v ∧ h a c d = v := by
  rcases hp a b c d hab hbc hcd with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> simp_all

private theorem packet_of_mid_ne {h : Fin 16 → Fin 16 → Fin 16 → Bool}
    (hp : ∀ a b c d, a < b → b < c → c < d →
      (h a b c = h a b d ∧ h a b d = h a c d) ∨
      (h a b c = h a b d ∧ h a c d = h b c d) ∨
      (h a b d = h a c d ∧ h a c d = h b c d))
    {a b c d : Fin 16} (hab : a < b) (hbc : b < c) (hcd : c < d) {u v : Bool}
    (hne : u ≠ v) (h1 : h a b d = u) (h2 : h a c d = v) :
    h a b c = u ∧ h b c d = v := by
  rcases hp a b c d hab hbc hcd with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact (hne (h1.symm.trans (e2.trans h2))).elim
  · exact ⟨e1.trans h1, e2.symm.trans h2⟩
  · exact (hne (h1.symm.trans (e1.trans h2))).elim

private theorem packet_of_last_ne {h : Fin 16 → Fin 16 → Fin 16 → Bool}
    (hp : ∀ a b c d, a < b → b < c → c < d →
      (h a b c = h a b d ∧ h a b d = h a c d) ∨
      (h a b c = h a b d ∧ h a c d = h b c d) ∨
      (h a b d = h a c d ∧ h a c d = h b c d))
    {a b c d : Fin 16} (hab : a < b) (hbc : b < c) (hcd : c < d) {u v : Bool}
    (hne : u ≠ v) (h1 : h a b d = u) (h2 : h a c d = v) (h3 : h b c d = v) :
    h a b c = u :=
  (packet_of_mid_ne hp hab hbc hcd hne h1 h2).1

private theorem packet_of_first_ne {h : Fin 16 → Fin 16 → Fin 16 → Bool}
    (hp : ∀ a b c d, a < b → b < c → c < d →
      (h a b c = h a b d ∧ h a b d = h a c d) ∨
      (h a b c = h a b d ∧ h a c d = h b c d) ∨
      (h a b d = h a c d ∧ h a c d = h b c d))
    {a b c d : Fin 16} (hab : a < b) (hbc : b < c) (hcd : c < d) {u v : Bool}
    (hne : u ≠ v) (h1 : h a b c = u) (h2 : h a b d = u) (h3 : h a c d = v) :
    h b c d = v :=
  (packet_of_mid_ne hp hab hbc hcd hne h2 h3).2

private theorem xor4_pair (u v : Bool) : (((u.xor u).xor v).xor v) = false := by
  cases u <;> cases v <;> rfl

private theorem chain4_all {h : Fin 16 → Fin 16 → Fin 16 → Bool}
    (hp : ∀ a b c d, a < b → b < c → c < d →
      (h a b c = h a b d ∧ h a b d = h a c d) ∨
      (h a b c = h a b d ∧ h a c d = h b c d) ∨
      (h a b d = h a c d ∧ h a c d = h b c d))
    {a b c d : Fin 16} (hab : a < b) (hbc : b < c) (hcd : c < d) {v : Bool}
    (h1 : h a b c = v) (h2 : h b c d = v) :
    ∀ p ∈ ({a, b, c, d} : Finset (Fin 16)),
    ∀ q ∈ ({a, b, c, d} : Finset (Fin 16)),
    ∀ r ∈ ({a, b, c, d} : Finset (Fin 16)),
      p < q → q < r → h p q r = v := by
  obtain ⟨habd, hacd⟩ := packet_eq_of_ends hp hab hbc hcd h1 h2
  intro p hp' q hq' r hr' hpq hqr
  simp only [mem_insert, mem_singleton] at hp' hq' hr'
  rcases hp' with rfl | rfl | rfl | rfl <;>
  rcases hq' with rfl | rfl | rfl | rfl <;>
  rcases hr' with rfl | rfl | rfl | rfl <;>
  first | exact h1 | exact h2 | exact habd | exact hacd | omega

private theorem chain5_all {h : Fin 16 → Fin 16 → Fin 16 → Bool}
    (hp : ∀ a b c d, a < b → b < c → c < d →
      (h a b c = h a b d ∧ h a b d = h a c d) ∨
      (h a b c = h a b d ∧ h a c d = h b c d) ∨
      (h a b d = h a c d ∧ h a c d = h b c d))
    {a b c d e : Fin 16} (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e) {v : Bool}
    (h1 : h a b c = v) (h2 : h b c d = v) (h3 : h c d e = v) :
    ∀ p ∈ ({a, b, c, d, e} : Finset (Fin 16)),
    ∀ q ∈ ({a, b, c, d, e} : Finset (Fin 16)),
    ∀ r ∈ ({a, b, c, d, e} : Finset (Fin 16)),
      p < q → q < r → h p q r = v := by
  obtain ⟨habd, hacd⟩ := packet_eq_of_ends hp hab hbc hcd h1 h2
  obtain ⟨hbce, hbde⟩ := packet_eq_of_ends hp hbc hcd hde h2 h3
  obtain ⟨habe, hade⟩ := packet_eq_of_ends hp hab (hbc.trans hcd) hde habd hbde
  obtain ⟨_, hace⟩ := packet_eq_of_ends hp hab hbc (hcd.trans hde) h1 hbce
  intro p hp' q hq' r hr' hpq hqr
  simp only [mem_insert, mem_singleton] at hp' hq' hr'
  rcases hp' with rfl | rfl | rfl | rfl | rfl <;>
  rcases hq' with rfl | rfl | rfl | rfl | rfl <;>
  rcases hr' with rfl | rfl | rfl | rfl | rfl <;>
  first | exact h1 | exact h2 | exact h3 | exact habd | exact hacd |
          exact hbce | exact hbde | exact habe | exact hade | exact hace | omega

private theorem chain6_all {h : Fin 16 → Fin 16 → Fin 16 → Bool}
    (hp : ∀ a b c d, a < b → b < c → c < d →
      (h a b c = h a b d ∧ h a b d = h a c d) ∨
      (h a b c = h a b d ∧ h a c d = h b c d) ∨
      (h a b d = h a c d ∧ h a c d = h b c d))
    {a b c d e f : Fin 16} (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e) (hef : e < f)
    {v : Bool} (h1 : h a b c = v) (h2 : h b c d = v) (h3 : h c d e = v) (h4 : h d e f = v) :
    ∀ p ∈ ({a, b, c, d, e, f} : Finset (Fin 16)),
    ∀ q ∈ ({a, b, c, d, e, f} : Finset (Fin 16)),
    ∀ r ∈ ({a, b, c, d, e, f} : Finset (Fin 16)),
      p < q → q < r → h p q r = v := by
  have c5a := chain5_all hp hab hbc hcd hde h1 h2 h3
  have c5b := chain5_all hp hbc hcd hde hef h2 h3 h4
  have habe : h a b e = v := c5a a (by simp) b (by simp) e (by simp) hab (hbc.trans (hcd.trans hde))
  have hbef : h b e f = v := c5b b (by simp) e (by simp) f (by simp) (hbc.trans (hcd.trans hde)) hef
  have hace : h a c e = v := c5a a (by simp) c (by simp) e (by simp) (hab.trans hbc) (hcd.trans hde)
  have hcef : h c e f = v := c5b c (by simp) e (by simp) f (by simp) (hcd.trans hde) hef
  have hade : h a d e = v := c5a a (by simp) d (by simp) e (by simp) (hab.trans (hbc.trans hcd)) hde
  obtain ⟨habf, haef⟩ := packet_eq_of_ends hp hab (hbc.trans (hcd.trans hde)) hef habe hbef
  obtain ⟨hacf, _⟩ := packet_eq_of_ends hp (hab.trans hbc) (hcd.trans hde) hef hace hcef
  obtain ⟨hadf, _⟩ := packet_eq_of_ends hp (hab.trans (hbc.trans hcd)) hde hef hade h4
  intro p hp' q hq' r hr' hpq hqr
  by_cases hpf : r = f
  · subst hpf
    by_cases hpa : p = a
    · subst hpa
      simp only [mem_insert, mem_singleton] at hq'
      rcases hq' with rfl | rfl | rfl | rfl | rfl | rfl
      · omega
      · exact habf
      · exact hacf
      · exact hadf
      · exact haef
      · omega
    · have hap : a ≤ p := by
        simp only [mem_insert, mem_singleton] at hp'
        rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
      apply c5b p _ q _ r (by simp) hpq hqr
      · simp only [mem_insert, mem_singleton] at hp' ⊢; tauto
      · simp only [mem_insert, mem_singleton] at hq' ⊢
        rcases hq' with rfl | hq''
        · omega
        · exact hq''
  · have hre : r ≤ e := by
      simp only [mem_insert, mem_singleton] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl | h
      · omega
      · omega
      · omega
      · omega
      · omega
      · exact (hpf h).elim
    apply c5a p _ q _ r _ hpq hqr
    · simp only [mem_insert, mem_singleton] at hp' ⊢
      rcases hp' with h | h | h | h | h | rfl
      · left; exact h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
      · omega
    · simp only [mem_insert, mem_singleton] at hq' ⊢
      rcases hq' with h | h | h | h | h | rfl
      · left; exact h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
      · omega
    · simp only [mem_insert, mem_singleton] at hr' ⊢
      rcases hr' with h | h | h | h | h | h
      · left; exact h
      · right; left; exact h
      · right; right; left; exact h
      · right; right; right; left; exact h
      · right; right; right; right; exact h
      · exact (hpf h).elim

private theorem union_cup_cap {h : Fin 16 → Fin 16 → Fin 16 → Bool}
    (hp : ∀ a b c d, a < b → b < c → c < d →
      (h a b c = h a b d ∧ h a b d = h a c d) ∨
      (h a b c = h a b d ∧ h a c d = h b c d) ∨
      (h a b d = h a c d ∧ h a c d = h b c d))
    {a b : Fin 16} (hab : a < b) (U L : Finset (Fin 16))
    (haU : a ∈ U) (hbU : b ∈ U) (haL : a ∈ L) (hbL : b ∈ L)
    (hbndU : ∀ x ∈ U, a ≤ x ∧ x ≤ b) (hbndL : ∀ x ∈ L, a ≤ x ∧ x ≤ b)
    (hU : ∀ p ∈ U, ∀ q ∈ U, ∀ r ∈ U, p < q → q < r → h p q r = true)
    (hL : ∀ p ∈ L, ∀ q ∈ L, ∀ r ∈ L, p < q → q < r → h p q r = false) :
    (U ∪ L).card + 2 = U.card + L.card ∧
    (∀ x ∈ U ∪ L, a ≤ x) ∧
    (∀ x ∈ U ∪ L, ∀ y ∈ U ∪ L, ∀ z ∈ U ∪ L, a < x → x < y → y < z →
      (((h a x y).xor (h a x z)).xor (h a y z)).xor (h x y z) = false) := by
  have hinter : U ∩ L = {a, b} := by
    ext p
    simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hpU, hpL⟩
      by_contra hne
      push_neg at hne
      have hpa : a < p := lt_of_le_of_ne (hbndU p hpU).1 (Ne.symm hne.1)
      have hpb : p < b := lt_of_le_of_ne (hbndU p hpU).2 hne.2
      have ht : h a p b = true := hU a haU p hpU b hbU hpa hpb
      have hf : h a p b = false := hL a haL p hpL b hbL hpa hpb
      exact Bool.noConfusion (ht.symm.trans hf)
    · rintro (rfl | rfl)
      · exact ⟨haU, haL⟩
      · exact ⟨hbU, hbL⟩
  have hcard : (U ∪ L).card + 2 = U.card + L.card := by
    have h1 := card_union_add_card_inter U L
    rw [hinter, card_pair hab.ne] at h1
    exact h1
  have hlo : ∀ x ∈ U ∪ L, a ≤ x := by
    intro x hx
    rcases mem_union.mp hx with hxU | hxL
    · exact (hbndU x hxU).1
    · exact (hbndL x hxL).1
  have hhi : ∀ x ∈ U ∪ L, x ≤ b := by
    intro x hx
    rcases mem_union.mp hx with hxU | hxL
    · exact (hbndU x hxU).2
    · exact (hbndL x hxL).2
  have hpair : ∀ p ∈ U ∪ L, ∀ q ∈ U ∪ L, a < p → p < q → q < b →
      h a p q = h a p b ∧ h p q b = h a q b := by
    intro p hp' q hq' hap hpq hqb
    rcases mem_union.mp hp' with hpU | hpL <;> rcases mem_union.mp hq' with hqU | hqL
    · rw [hU a haU p hpU q hqU hap hpq, hU a haU p hpU b hbU hap (hpq.trans hqb),
          hU p hpU q hqU b hbU hpq hqb, hU a haU q hqU b hbU (hap.trans hpq) hqb]
      exact ⟨rfl, rfl⟩
    · have h1 : h a p b = true := hU a haU p hpU b hbU hap (hpq.trans hqb)
      have h2 : h a q b = false := hL a haL q hqL b hbL (hap.trans hpq) hqb
      obtain ⟨r1, r2⟩ := packet_of_mid_ne hp hap hpq hqb (by decide) h1 h2
      rw [h1, h2, r1, r2]; exact ⟨rfl, rfl⟩
    · have h1 : h a p b = false := hL a haL p hpL b hbL hap (hpq.trans hqb)
      have h2 : h a q b = true := hU a haU q hqU b hbU (hap.trans hpq) hqb
      obtain ⟨r1, r2⟩ := packet_of_mid_ne hp hap hpq hqb (by decide) h1 h2
      rw [h1, h2, r1, r2]; exact ⟨rfl, rfl⟩
    · rw [hL a haL p hpL q hqL hap hpq, hL a haL p hpL b hbL hap (hpq.trans hqb),
          hL p hpL q hqL b hbL hpq hqb, hL a haL q hqL b hbL (hap.trans hpq) hqb]
      exact ⟨rfl, rfl⟩
  refine ⟨hcard, hlo, ?_⟩
  intro x hx y hy z hz hax hxy hyz
  rcases eq_or_lt_of_le (hhi z hz) with rfl | hzb
  · obtain ⟨h1, h2⟩ := hpair x hx y hy hax hxy hyz
    rw [h1, h2]
    exact xor4_pair (h a x z) (h a y z)
  · obtain ⟨haxy, hxyb⟩ := hpair x hx y hy hax hxy (hyz.trans hzb)
    obtain ⟨haxz, hxzb⟩ := hpair x hx z hz hax (hxy.trans hyz) hzb
    obtain ⟨hayz, hyzb⟩ := hpair y hy z hz (hax.trans hxy) hyz hzb
    have hxyz : h x y z = h a y b := by
      by_cases hyz_eq : h a y b = h a z b
      · by_cases hxy_eq : h a x b = h a y b
        · rcases mem_union.mp hx with hxU | hxL <;>
          rcases mem_union.mp hy with hyU | hyL <;>
          rcases mem_union.mp hz with hzU | hzL
          · rw [hU x hxU y hyU z hzU hxy hyz, hU a haU y hyU b hbU (hax.trans hxy) (hyz.trans hzb)]
          · have : h a y b = true := hU a haU y hyU b hbU (hax.trans hxy) (hyz.trans hzb)
            have : h a z b = false := hL a haL z hzL b hbL (hax.trans (hxy.trans hyz)) hzb
            simp_all
          · have : h a x b = true := hU a haU x hxU b hbU hax ((hxy.trans hyz).trans hzb)
            have : h a y b = false := hL a haL y hyL b hbL (hax.trans hxy) (hyz.trans hzb)
            simp_all
          · have : h a x b = true := hU a haU x hxU b hbU hax ((hxy.trans hyz).trans hzb)
            have : h a y b = false := hL a haL y hyL b hbL (hax.trans hxy) (hyz.trans hzb)
            simp_all
          · have : h a x b = false := hL a haL x hxL b hbL hax ((hxy.trans hyz).trans hzb)
            have : h a y b = true := hU a haU y hyU b hbU (hax.trans hxy) (hyz.trans hzb)
            simp_all
          · have : h a x b = false := hL a haL x hxL b hbL hax ((hxy.trans hyz).trans hzb)
            have : h a y b = true := hU a haU y hyU b hbU (hax.trans hxy) (hyz.trans hzb)
            simp_all
          · have : h a y b = false := hL a haL y hyL b hbL (hax.trans hxy) (hyz.trans hzb)
            have : h a z b = true := hU a haU z hzU b hbU (hax.trans (hxy.trans hyz)) hzb
            simp_all
          · rw [hL x hxL y hyL z hzL hxy hyz, hL a haL y hyL b hbL (hax.trans hxy) (hyz.trans hzb)]
        · exact packet_of_first_ne hp hax hxy hyz hxy_eq haxy haxz hayz
      · exact packet_of_last_ne hp hxy hyz hzb hyz_eq hxyb hxzb hyzb
    rw [haxy, haxz, hayz, hxyz]
    exact xor4_pair (h a x b) (h a y b)

private theorem lift_union {g : Fin 17 → Fin 17 → Fin 17 → Bool}
    (hp : ∀ a b c d, a < b → b < c → c < d →
      (g a b c = g a b d ∧ g a b d = g a c d) ∨
      (g a b c = g a b d ∧ g a c d = g b c d) ∨
      (g a b d = g a c d ∧ g a c d = g b c d))
    {a b : Fin 16} (hab : a < b) (U L : Finset (Fin 16))
    (hcard6 : U.card + L.card = 8)
    (haU : a ∈ U) (hbU : b ∈ U) (haL : a ∈ L) (hbL : b ∈ L)
    (hbndU : ∀ x ∈ U, a ≤ x ∧ x ≤ b) (hbndL : ∀ x ∈ L, a ≤ x ∧ x ≤ b)
    (hU : ∀ p ∈ U, ∀ q ∈ U, ∀ r ∈ U, p < q → q < r → g p.succ q.succ r.succ = true)
    (hL : ∀ p ∈ L, ∀ q ∈ L, ∀ r ∈ L, p < q → q < r → g p.succ q.succ r.succ = false) :
    ∃ S : Finset (Fin 17), S.card = 6 ∧ ∃ v ∈ S, (∀ x ∈ S, v ≤ x) ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, v < x → x < y → y < z →
        (((g v x y).xor (g v x z)).xor (g v y z)).xor (g x y z) = false := by
  let h : Fin 16 → Fin 16 → Fin 16 → Bool := fun p q r => g p.succ q.succ r.succ
  have hp16 : ∀ p q r s : Fin 16, p < q → q < r → r < s →
      (h p q r = h p q s ∧ h p q s = h p r s) ∨
      (h p q r = h p q s ∧ h p r s = h q r s) ∨
      (h p q s = h p r s ∧ h p r s = h q r s) := fun p q r s hpq hqr hrs =>
    hp p.succ q.succ r.succ s.succ (Fin.succ_lt_succ_iff.mpr hpq)
      (Fin.succ_lt_succ_iff.mpr hqr) (Fin.succ_lt_succ_iff.mpr hrs)
  obtain ⟨hULcard, hlo, heven⟩ := union_cup_cap hp16 hab U L haU hbU haL hbL hbndU hbndL hU hL
  let emb : Fin 16 ↪ Fin 17 := ⟨Fin.succ, Fin.succ_injective _⟩
  refine ⟨(U ∪ L).map emb, by rw [card_map]; omega, a.succ,
    mem_map.mpr ⟨a, mem_union_left L haU, rfl⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := mem_map.mp hx
    exact Fin.succ_le_succ_iff.mpr (hlo x₀ hx₀)
  · intro x hx y hy z hz hax hxy hyz
    obtain ⟨x₀, hx₀, rfl⟩ := mem_map.mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := mem_map.mp hy
    obtain ⟨z₀, hz₀, rfl⟩ := mem_map.mp hz
    exact heven x₀ hx₀ y₀ hy₀ z₀ hz₀
      (Fin.succ_lt_succ_iff.mp hax) (Fin.succ_lt_succ_iff.mp hxy) (Fin.succ_lt_succ_iff.mp hyz)

/-- Central 4-tuple (6, 7, 8, 9) all-false case (forces 0000). -/
def H1 : Prop :=
  let C := Fin 16 → Fin 16 → Fin 16 → Bool
  let packet (h : C) : Prop := ∀ a b c d, a < b → b < c → c < d →
    (h a b c = h a b d ∧ h a b d = h a c d) ∨
    (h a b c = h a b d ∧ h a c d = h b c d) ∨
    (h a b d = h a c d ∧ h a c d = h b c d)
  let cupCap6 (h : C) : Prop :=
    (∃ a b c d e, a < b ∧ b < c ∧ c < d ∧ d < e ∧
      h a b c = true ∧ h b c d = true ∧ h c d e = true) ∨
    (∃ a b c d e f, a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f ∧
      h a b c = false ∧ h b c d = false ∧ h c d e = false ∧ h d e f = false) ∨
    (∃ a b x y u v, a < x ∧ x < y ∧ y < b ∧ a < u ∧ u < v ∧ v < b ∧
      h a x y = true ∧ h x y b = true ∧ h a u v = false ∧ h u v b = false) ∨
    (∃ a b x u v w, a < x ∧ x < b ∧ a < u ∧ u < v ∧ v < w ∧ w < b ∧
      h a x b = true ∧ h a u v = false ∧ h u v w = false ∧ h v w b = false)
  ∀ h : C, packet h → h 6 7 8 = false → h 7 8 9 = false → cupCap6 h

/-- Central 4-tuple (6, 7, 8, 9) all-true case (forces 1111). -/
def H2 : Prop :=
  let C := Fin 16 → Fin 16 → Fin 16 → Bool
  let packet (h : C) : Prop := ∀ a b c d, a < b → b < c → c < d →
    (h a b c = h a b d ∧ h a b d = h a c d) ∨
    (h a b c = h a b d ∧ h a c d = h b c d) ∨
    (h a b d = h a c d ∧ h a c d = h b c d)
  let cupCap6 (h : C) : Prop :=
    (∃ a b c d e, a < b ∧ b < c ∧ c < d ∧ d < e ∧
      h a b c = true ∧ h b c d = true ∧ h c d e = true) ∨
    (∃ a b c d e f, a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f ∧
      h a b c = false ∧ h b c d = false ∧ h c d e = false ∧ h d e f = false) ∨
    (∃ a b x y u v, a < x ∧ x < y ∧ y < b ∧ a < u ∧ u < v ∧ v < b ∧
      h a x y = true ∧ h x y b = true ∧ h a u v = false ∧ h u v b = false) ∨
    (∃ a b x u v w, a < x ∧ x < b ∧ a < u ∧ u < v ∧ v < w ∧ w < b ∧
      h a x b = true ∧ h a u v = false ∧ h u v w = false ∧ h v w b = false)
  ∀ h : C, packet h → h 6 7 8 = true → h 7 8 9 = true → cupCap6 h

/-- Central 4-tuple (6, 7, 8, 9) mixed case 11*0 (covers 0*11 by reflection). -/
def H3 : Prop :=
  let C := Fin 16 → Fin 16 → Fin 16 → Bool
  let packet (h : C) : Prop := ∀ a b c d, a < b → b < c → c < d →
    (h a b c = h a b d ∧ h a b d = h a c d) ∨
    (h a b c = h a b d ∧ h a c d = h b c d) ∨
    (h a b d = h a c d ∧ h a c d = h b c d)
  let cupCap6 (h : C) : Prop :=
    (∃ a b c d e, a < b ∧ b < c ∧ c < d ∧ d < e ∧
      h a b c = true ∧ h b c d = true ∧ h c d e = true) ∨
    (∃ a b c d e f, a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f ∧
      h a b c = false ∧ h b c d = false ∧ h c d e = false ∧ h d e f = false) ∨
    (∃ a b x y u v, a < x ∧ x < y ∧ y < b ∧ a < u ∧ u < v ∧ v < b ∧
      h a x y = true ∧ h x y b = true ∧ h a u v = false ∧ h u v b = false) ∨
    (∃ a b x u v w, a < x ∧ x < b ∧ a < u ∧ u < v ∧ v < w ∧ w < b ∧
      h a x b = true ∧ h a u v = false ∧ h u v w = false ∧ h v w b = false)
  ∀ h : C, packet h → h 6 7 8 = true → h 6 7 9 = true → h 7 8 9 = false → cupCap6 h

/-- Central 4-tuple (6, 7, 8, 9) mixed case 1000 (covers 0001 by reflection). -/
def H4 : Prop :=
  let C := Fin 16 → Fin 16 → Fin 16 → Bool
  let packet (h : C) : Prop := ∀ a b c d, a < b → b < c → c < d →
    (h a b c = h a b d ∧ h a b d = h a c d) ∨
    (h a b c = h a b d ∧ h a c d = h b c d) ∨
    (h a b d = h a c d ∧ h a c d = h b c d)
  let cupCap6 (h : C) : Prop :=
    (∃ a b c d e, a < b ∧ b < c ∧ c < d ∧ d < e ∧
      h a b c = true ∧ h b c d = true ∧ h c d e = true) ∨
    (∃ a b c d e f, a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f ∧
      h a b c = false ∧ h b c d = false ∧ h c d e = false ∧ h d e f = false) ∨
    (∃ a b x y u v, a < x ∧ x < y ∧ y < b ∧ a < u ∧ u < v ∧ v < b ∧
      h a x y = true ∧ h x y b = true ∧ h a u v = false ∧ h u v b = false) ∨
    (∃ a b x u v w, a < x ∧ x < b ∧ a < u ∧ u < v ∧ v < w ∧ w < b ∧
      h a x b = true ∧ h a u v = false ∧ h u v w = false ∧ h v w b = false)
  ∀ h : C, packet h → h 6 7 8 = true → h 6 7 9 = false → h 7 8 9 = false → cupCap6 h

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos107_erdos_107_R1_H1_R1_H2_R1.H2 := by
  intro h1 h2 h3 h4 g hpack hapex
  let h : Fin 16 → Fin 16 → Fin 16 → Bool := fun a b c => g a.succ b.succ c.succ
  have hp16 : ∀ a b c d : Fin 16, a < b → b < c → c < d →
      (h a b c = h a b d ∧ h a b d = h a c d) ∨
      (h a b c = h a b d ∧ h a c d = h b c d) ∨
      (h a b d = h a c d ∧ h a c d = h b c d) := fun a b c d hab hbc hcd =>
    hpack a.succ b.succ c.succ d.succ (Fin.succ_lt_succ_iff.mpr hab)
      (Fin.succ_lt_succ_iff.mpr hbc) (Fin.succ_lt_succ_iff.mpr hcd)
  let rev (i : Fin 16) : Fin 16 := ⟨15 - i.val, by omega⟩
  have rev_lt : ∀ i j : Fin 16, i < j → rev j < rev i := by
    intro i j hij; rw [Fin.lt_def]; dsimp [rev]; have : i.val < j.val := hij; omega
  let hr : Fin 16 → Fin 16 → Fin 16 → Bool := fun a b c => h (rev c) (rev b) (rev a)
  have hpr : ∀ a b c d : Fin 16, a < b → b < c → c < d →
      (hr a b c = hr a b d ∧ hr a b d = hr a c d) ∨
      (hr a b c = hr a b d ∧ hr a c d = hr b c d) ∨
      (hr a b d = hr a c d ∧ hr a c d = hr b c d) := by
    intro a b c d hab hbc hcd
    rcases hp16 (rev d) (rev c) (rev b) (rev a)
        (rev_lt c d hcd) (rev_lt b c hbc) (rev_lt a b hab) with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inr (Or.inr ⟨e2.symm, e1.symm⟩)
    · exact Or.inr (Or.inl ⟨e2.symm, e1.symm⟩)
    · exact Or.inl ⟨e2.symm, e1.symm⟩
  let cc (k : Fin 16 → Fin 16 → Fin 16 → Bool) : Prop :=
    (∃ a b c d e, a < b ∧ b < c ∧ c < d ∧ d < e ∧
      k a b c = true ∧ k b c d = true ∧ k c d e = true) ∨
    (∃ a b c d e f, a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f ∧
      k a b c = false ∧ k b c d = false ∧ k c d e = false ∧ k d e f = false) ∨
    (∃ a b x y u v, a < x ∧ x < y ∧ y < b ∧ a < u ∧ u < v ∧ v < b ∧
      k a x y = true ∧ k x y b = true ∧ k a u v = false ∧ k u v b = false) ∨
    (∃ a b x u v w, a < x ∧ x < b ∧ a < u ∧ u < v ∧ v < w ∧ w < b ∧
      k a x b = true ∧ k a u v = false ∧ k u v w = false ∧ k v w b = false)
  have hcc : cc h := by
    have unrev : cc hr → cc h := by
      rintro (⟨a, b, c, d, e, hab, hbc, hcd, hde, e1, e2, e3⟩ |
              ⟨a, b, c, d, e, f, hab, hbc, hcd, hde, hef, e1, e2, e3, e4⟩ |
              ⟨a, b, x, y, u, v, hax, hxy, hyb, hau, huv, hvb, e1, e2, e3, e4⟩ |
              ⟨a, b, x, u, v, w, hax, hxb, hau, huv, hvw, hwb, e1, e2, e3, e4⟩)
      · exact Or.inl ⟨rev e, rev d, rev c, rev b, rev a,
          rev_lt d e hde, rev_lt c d hcd, rev_lt b c hbc, rev_lt a b hab, e3, e2, e1⟩
      · exact Or.inr (Or.inl ⟨rev f, rev e, rev d, rev c, rev b, rev a,
          rev_lt e f hef, rev_lt d e hde, rev_lt c d hcd, rev_lt b c hbc, rev_lt a b hab,
          e4, e3, e2, e1⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨rev b, rev a, rev y, rev x, rev v, rev u,
          rev_lt y b hyb, rev_lt x y hxy, rev_lt a x hax,
          rev_lt v b hvb, rev_lt u v huv, rev_lt a u hau, e2, e1, e4, e3⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rev b, rev a, rev x, rev w, rev v, rev u,
          rev_lt x b hxb, rev_lt a x hax,
          rev_lt w b hwb, rev_lt v w hvw, rev_lt u v huv, rev_lt a u hau, e1, e4, e3, e2⟩))
    cases h678 : h 6 7 8 <;> cases h789 : h 7 8 9
    · exact h1 h hp16 h678 h789
    · have hr678 : hr 6 7 8 = true := by simpa [hr, rev] using h789
      have hr789 : hr 7 8 9 = false := by simpa [hr, rev] using h678
      cases hr679 : hr 6 7 9
      · exact unrev (h4 hr hpr hr678 hr679 hr789)
      · exact unrev (h3 hr hpr hr678 hr679 hr789)
    · cases h679 : h 6 7 9
      · exact h4 h hp16 h678 h679 h789
      · exact h3 h hp16 h678 h679 h789
    · exact h2 h hp16 h678 h789
  rcases hcc with ⟨a, b, c, d, e, hab, hbc, hcd, hde, e1, e2, e3⟩ |
                  ⟨a, b, c, d, e, f, hab, hbc, hcd, hde, hef, e1, e2, e3, e4⟩ |
                  ⟨a, b, x, y, u, v, hax, hxy, hyb, hau, huv, hvb, e1, e2, e3, e4⟩ |
                  ⟨a, b, x, u, v, w, hax, hxb, hau, huv, hvw, hwb, e1, e2, e3, e4⟩
  · have hall := chain5_all hp16 hab hbc hcd hde e1 e2 e3
    let S : Finset (Fin 17) := {0, a.succ, b.succ, c.succ, d.succ, e.succ}
    have hcard : S.card = 6 := by
      simp only [S]
      have h0a : (0 : Fin 17) ≠ a.succ := (Fin.succ_ne_zero a).symm
      have h0b : (0 : Fin 17) ≠ b.succ := (Fin.succ_ne_zero b).symm
      have h0c : (0 : Fin 17) ≠ c.succ := (Fin.succ_ne_zero c).symm
      have h0d : (0 : Fin 17) ≠ d.succ := (Fin.succ_ne_zero d).symm
      have h0e : (0 : Fin 17) ≠ e.succ := (Fin.succ_ne_zero e).symm
      have hab' : a.succ ≠ b.succ := (Fin.succ_lt_succ_iff.mpr hab).ne
      have hac' : a.succ ≠ c.succ := (Fin.succ_lt_succ_iff.mpr (hab.trans hbc)).ne
      have had' : a.succ ≠ d.succ := (Fin.succ_lt_succ_iff.mpr ((hab.trans hbc).trans hcd)).ne
      have hae' : a.succ ≠ e.succ := (Fin.succ_lt_succ_iff.mpr (((hab.trans hbc).trans hcd).trans hde)).ne
      have hbc' : b.succ ≠ c.succ := (Fin.succ_lt_succ_iff.mpr hbc).ne
      have hbd' : b.succ ≠ d.succ := (Fin.succ_lt_succ_iff.mpr (hbc.trans hcd)).ne
      have hbe' : b.succ ≠ e.succ := (Fin.succ_lt_succ_iff.mpr ((hbc.trans hcd).trans hde)).ne
      have hcd' : c.succ ≠ d.succ := (Fin.succ_lt_succ_iff.mpr hcd).ne
      have hce' : c.succ ≠ e.succ := (Fin.succ_lt_succ_iff.mpr (hcd.trans hde)).ne
      have hde' : d.succ ≠ e.succ := (Fin.succ_lt_succ_iff.mpr hde).ne
      simp [h0a, h0b, h0c, h0d, h0e, hab', hac', had', hae', hbc', hbd', hbe', hcd', hce', hde']
    refine ⟨S, hcard, 0, by simp [S], fun x _ => Fin.zero_le x, ?_⟩
    intro x hx y hy z hz h0x hxy hyz
    have hx' : ∃ x₀ ∈ ({a, b, c, d, e} : Finset (Fin 16)), x = x₀.succ := by
      simp only [S, mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (lt_irrefl _ h0x).elim
      · exact ⟨a, by simp, rfl⟩
      · exact ⟨b, by simp, rfl⟩
      · exact ⟨c, by simp, rfl⟩
      · exact ⟨d, by simp, rfl⟩
      · exact ⟨e, by simp, rfl⟩
    have hy' : ∃ y₀ ∈ ({a, b, c, d, e} : Finset (Fin 16)), y = y₀.succ := by
      simp only [S, mem_insert, mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (lt_irrefl _ (h0x.trans hxy)).elim
      · exact ⟨a, by simp, rfl⟩
      · exact ⟨b, by simp, rfl⟩
      · exact ⟨c, by simp, rfl⟩
      · exact ⟨d, by simp, rfl⟩
      · exact ⟨e, by simp, rfl⟩
    have hz' : ∃ z₀ ∈ ({a, b, c, d, e} : Finset (Fin 16)), z = z₀.succ := by
      simp only [S, mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (lt_irrefl _ ((h0x.trans hxy).trans hyz)).elim
      · exact ⟨a, by simp, rfl⟩
      · exact ⟨b, by simp, rfl⟩
      · exact ⟨c, by simp, rfl⟩
      · exact ⟨d, by simp, rfl⟩
      · exact ⟨e, by simp, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hx'
    obtain ⟨y₀, hy₀, rfl⟩ := hy'
    obtain ⟨z₀, hz₀, rfl⟩ := hz'
    have hgt : g x₀.succ y₀.succ z₀.succ = true :=
      hall x₀ hx₀ y₀ hy₀ z₀ hz₀ (Fin.succ_lt_succ_iff.mp hxy) (Fin.succ_lt_succ_iff.mp hyz)
    rw [hapex _ _ h0x hxy, hapex _ _ h0x (hxy.trans hyz), hapex _ _ (h0x.trans hxy) hyz, hgt]
    rfl
  · have hall := chain6_all hp16 hab hbc hcd hde hef e1 e2 e3 e4
    let U : Finset (Fin 16) := {a, f}
    let L : Finset (Fin 16) := {a, b, c, d, e, f}
    have haf : a < f := (((hab.trans hbc).trans hcd).trans hde).trans hef
    have hUc : U.card = 2 := card_pair haf.ne
    have hLc : L.card = 6 := by
      simp only [L]
      simp [hab.ne, (hab.trans hbc).ne, ((hab.trans hbc).trans hcd).ne,
            (((hab.trans hbc).trans hcd).trans hde).ne, haf.ne,
            hbc.ne, (hbc.trans hcd).ne, ((hbc.trans hcd).trans hde).ne,
            (((hbc.trans hcd).trans hde).trans hef).ne,
            hcd.ne, (hcd.trans hde).ne, ((hcd.trans hde).trans hef).ne,
            hde.ne, (hde.trans hef).ne, hef.ne]
    refine lift_union hpack haf U L (by omega) (by simp [U]) (by simp [U])
      (by simp [L]) (by simp [L]) ?_ ?_ ?_ hall
    · intro p hp'; simp only [U, mem_insert, mem_singleton] at hp'
      rcases hp' with rfl | rfl <;> exact ⟨by omega, by omega⟩
    · intro p hp'; simp only [L, mem_insert, mem_singleton] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · intro p hp' q hq' r hr' hpq hqr
      simp only [U, mem_insert, mem_singleton] at hp' hq' hr'
      omega
  · have hUall := chain4_all hp16 hax hxy hyb e1 e2
    have hLall := chain4_all hp16 hau huv hvb e3 e4
    let U : Finset (Fin 16) := {a, x, y, b}
    let L : Finset (Fin 16) := {a, u, v, b}
    have hab : a < b := (hax.trans hxy).trans hyb
    have hUc : U.card = 4 := by
      simp only [U]
      simp [hax.ne, (hax.trans hxy).ne, hab.ne, hxy.ne, (hxy.trans hyb).ne, hyb.ne]
    have hLc : L.card = 4 := by
      simp only [L]
      simp [hau.ne, (hau.trans huv).ne, hab.ne, huv.ne, (huv.trans hvb).ne, hvb.ne]
    refine lift_union hpack hab U L (by omega) (by simp [U]) (by simp [U])
      (by simp [L]) (by simp [L]) ?_ ?_ hUall hLall
    · intro p hp'; simp only [U, mem_insert, mem_singleton] at hp'
      rcases hp' with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · intro p hp'; simp only [L, mem_insert, mem_singleton] at hp'
      rcases hp' with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
  · have hLall := chain5_all hp16 hau huv hvw hwb e2 e3 e4
    let U : Finset (Fin 16) := {a, x, b}
    let L : Finset (Fin 16) := {a, u, v, w, b}
    have hab : a < b := hax.trans hxb
    have hUc : U.card = 3 := by
      simp only [U]; simp [hax.ne, hab.ne, hxb.ne]
    have hLc : L.card = 5 := by
      simp only [L]
      simp [hau.ne, (hau.trans huv).ne, ((hau.trans huv).trans hvw).ne, hab.ne,
            huv.ne, (huv.trans hvw).ne, ((huv.trans hvw).trans hwb).ne,
            hvw.ne, (hvw.trans hwb).ne, hwb.ne]
    refine lift_union hpack hab U L (by omega) (by simp [U]) (by simp [U])
      (by simp [L]) (by simp [L]) ?_ ?_ ?_ hLall
    · intro p hp'; simp only [U, mem_insert, mem_singleton] at hp'
      rcases hp' with rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · intro p hp'; simp only [L, mem_insert, mem_singleton] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega⟩
    · intro p hp' q hq' r hr' hpq hqr
      simp only [U, mem_insert, mem_singleton] at hp' hq' hr'
      rcases hp' with rfl | rfl | rfl <;>
      rcases hq' with rfl | rfl | rfl <;>
      rcases hr' with rfl | rfl | rfl <;>
      first | exact e1 | omega

end OMA.R_Erdos107_erdos_107_R1_H1_R1_H2_R1_H2_R1
