import OMAStatements.S_oeis_a076771

-- Credit: @oh-meh
open OMA.S_oeis_a076771

theorem OMA.solution : type_of% @OMA.S_oeis_a076771.main := by
  rintro ⟨N, h⟩
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N+1)
  obtain ⟨a,b,ha,ha1,hac,_,hb1,_,hab,hs⟩ :=
    h (2*p) (by omega) ⟨p, by omega⟩
  let q := (a.gcd b).minFac
  have hq : q.Prime := Nat.minFac_prime hab
  have hqa : q ∣ a := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left a b)
  have hqb : q ∣ b := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right a b)
  have hd : q ∣ 2*p := hs ▸ dvd_add hqa hqb
  have hneq : q ≠ 2 := by
    intro he
    exact (Nat.not_even_iff_odd.mpr ha) (even_iff_two_dvd.mpr (he ▸ hqa))
  have hqp : q = p := (Nat.dvd_prime hp).mp ((hq.dvd_mul.mp hd).resolve_left
    (fun hh => hneq ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hh))) |>.resolve_left hq.ne_one
  rw [hqp] at hqa hqb
  obtain ⟨u, rfl⟩ := hqa
  obtain ⟨v, rfl⟩ := hqb
  have eq : u + v = 2 := by nlinarith [hp.pos]
  have hu : 0 < u := Nat.pos_of_mul_pos_left (by omega : 0 < p*u)
  have hv : 0 < v := Nat.pos_of_mul_pos_left (by omega : 0 < p*v)
  have : u = 1 := by omega
  exact hac (by simpa [this] using hp)
