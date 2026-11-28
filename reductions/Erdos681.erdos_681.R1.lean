import FormalConjectures.ErdosProblems.«681»

/-! Residual-prime reduction, adapted from Jared Wilder's September 2026
Erdos 681 archive. The two remaining prime classes can be attacked separately;
composite successors are already handled by shift one. The fourth-root and
parity restrictions from the archive give the finite window for each search. -/
namespace OMA.R_Erdos681_erdos_681_R1
open Filter Erdos681

def H1 : Prop := ∃ P : ℕ, ∀ p : ℕ, P < p → p.Prime → p % 3 = 1 →
  ∃ h : ℕ, 2 ≤ h ∧ h % 2 = 0 ∧ (h+1)^4 < p+h ∧
    (p+h).Composite ∧ (h+1)^2 < (p+h).minFac

def H2 : Prop := ∃ P : ℕ, ∀ p : ℕ, P < p → p.Prime → p % 3 = 2 →
  ∃ h : ℕ, 2 ≤ h ∧ h % 2 = 0 ∧ (h+1)^4 < p+h ∧
    (p+h).Composite ∧ (h+1)^2 < (p+h).minFac

lemma lpf_bridge {m k : ℕ} (h : k^2 < m.minFac) :
    ∀ p, IsLPF p m → p > k^2 := by
  intro p hp
  exact h.trans_le (Nat.minFac_le_of_dvd hp.1.two_le hp.2.1)

lemma fourth_root {p h : ℕ} (hc : (p+h).Composite)
    (hm : (h+1)^2 < (p+h).minFac) : (h+1)^4 < p+h := by
  have hpos : 0 < p+h := by have := hc.1; omega
  calc
    (h+1)^4 = ((h+1)^2)^2 := by ring
    _ < (p+h).minFac^2 := Nat.pow_lt_pow_left hm (by decide)
    _ ≤ p+h := Nat.minFac_sq_le_self hpos hc.2

theorem main : H1 → H2 → type_of% @Erdos681.erdos_681 := by
  rintro ⟨P,hP⟩ ⟨Q,hQ⟩
  apply eventually_atTop.2
  refine ⟨max (max P Q) 4, fun n hn => ?_⟩
  by_cases hp : (n+1).Prime
  · have hP' : P < n+1 := by omega
    have hQ' : Q < n+1 := by omega
    have h3 : (n+1)%3 ≠ 0 := by
      intro hz
      have hd : 3 ∣ n+1 := Nat.dvd_of_mod_eq_zero hz
      rcases hp.eq_one_or_self_of_dvd 3 hd with hh|hh <;> omega
    have hc : (n+1)%3 = 1 ∨ (n+1)%3 = 2 := by omega
    obtain ⟨h,hh,_,_,hc',hm⟩ := hc.elim (hP (n+1) hP' hp) (hQ (n+1) hQ' hp)
    refine ⟨h+1, by omega, ?_, ?_⟩
    · simpa only [Nat.add_assoc, Nat.add_comm 1 h] using hc'
    · apply lpf_bridge
      simpa only [Nat.add_assoc, Nat.add_comm 1 h] using hm
  · refine ⟨1, by decide, ⟨by omega,hp⟩, ?_⟩
    intro p hp'
    have := hp'.1.two_le
    norm_num
    omega
end OMA.R_Erdos681_erdos_681_R1
