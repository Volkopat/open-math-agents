import OMAReductions.R_OeisA247824_conjecture_2_R2_H1_R1
import Mathlib

/-! The index of the smaller prime in the prescribed counterexample.
The sieve checks the eight residue classes prime to 30 and certifies the
count at each block boundary before evaluating the last short block. -/

/- Certified wheel indices for counting primes using the eight reduced classes modulo thirty. -/
namespace SmallWitnessPrimeCount

def index (n : ℕ) : ℕ := 8*(n/30) + ((703383147439395582067753010374709520 : ℕ) >>> (4*(n%30)))%16

def number (i : ℕ) : ℕ := 30*(i/8) + ((1021784272097 : ℕ) >>> (5*(i%8)))%32

theorem shift_index (q r : ℕ) : index (30*q+r) = 8*q+index r := by
  unfold index
  rw [Nat.mul_add_div (by decide : 0<30),Nat.mul_add_mod]
  omega

theorem shift_number (q j : ℕ) : number (8*q+j) = 30*q+number j := by
  unfold number
  rw [Nat.mul_add_div (by decide : 0<8),Nat.mul_add_mod]
  omega

theorem wheel_step (n : ℕ) :
    (index (n+1) = index n ∧ (2 ∣ n+1 ∨ 3 ∣ n+1 ∨ 5 ∣ n+1)) ∨
    (index (n+1) = index n+1 ∧ number (index n) = n+1) := by
  have tab : ∀ r : Fin 30,
      (index (r.1+1) = index r.1 ∧ (2 ∣ r.1+1 ∨ 3 ∣ r.1+1 ∨ 5 ∣ r.1+1)) ∨
      (index (r.1+1) = index r.1+1 ∧ number (index r.1) = r.1+1) := by decide +kernel
  let q := n/30
  let r := n%30
  have split : n = 30*q+r := (Nat.div_add_mod n 30).symm
  have next : n+1 = 30*q+(r+1) := by omega
  rcases tab ⟨r,Nat.mod_lt _ (by decide)⟩ with ⟨eq,hd⟩ | ⟨eq,hn⟩
  · left
    constructor
    · rw [next,split,shift_index,shift_index,eq]
    · rw [next]
      rcases hd with h|h|h
      · exact Or.inl (dvd_add (dvd_mul_of_dvd_left (by decide : 2 ∣ 30) q) h)
      · exact Or.inr (Or.inl (dvd_add (dvd_mul_of_dvd_left (by decide : 3 ∣ 30) q) h))
      · exact Or.inr (Or.inr (dvd_add (dvd_mul_of_dvd_left (by decide : 5 ∣ 30) q) h))
  · change index (r+1) = index r+1 at eq
    change number (index r) = r+1 at hn
    right
    constructor
    · rw [next,split,shift_index,shift_index,eq]
      omega
    · rw [next,split,shift_index,shift_number,hn]

theorem skips_composite {n : ℕ} (large : 5 < n) (d : 2 ∣ n ∨ 3 ∣ n ∨ 5 ∣ n) : ¬ n.Prime := by
  intro h
  rcases d with hd|hd|hd
  all_goals rcases (Nat.dvd_prime h).mp hd with e|e <;> omega

theorem index_bound {n b : ℕ} (h : n ≤ b) : index n < 8*(b/30+2) := by
  have t : ∀ r : Fin 30, ((703383147439395582067753010374709520 : ℕ) >>> (4*r.val))%16 ≤ 8 := by decide +kernel
  have a := t ⟨n%30,Nat.mod_lt _ (by decide)⟩
  change ((703383147439395582067753010374709520 : ℕ) >>> (4*(n%30)))%16 ≤ 8 at a
  have d : n/30 ≤ b/30 := Nat.div_le_div_right h
  unfold index
  omega




private def radical : ℕ := 1726048751587872353799367615215722283148356607460993554666190916613601884197466038982733461069376517217158039868606474112919033662937635266214097984709177803311557461239755282449716026502086172880978807896308089730941334092063217169659196837926518037588495758160837193156083299753671381670524240405654937582755891553242128958512529091170368252782618012719576993401929013702240860020682082003778772351564388229076569100154964052189181763330892604106826991010530720170602758791628518315096802093868541758776357395938453976189979226877664077296029803955132145422315975807571579677701592809003743068534161856002948596739530104371044987622149077883206196209090999674574537438645802222645111952836844550031259525645382545540629259309567811602972875815604809995054637502397265129922114707032218124352784635117858717744588261016905417319424656617361916194137118931610392219479071794242195692773900613414607693835073469959956175498834527488276856736185284854503184291941305751488768455336839606646652765125620440330184253975567316241267475850618846470665707357704544437347142482109532453880630804947364023130897088129292560789179211180698955748478724571805921426824433793911585946998371344207191468183314109310067452393796737057644025370776258332891367981068913904819944591413059023250996279766703812830426469687172454578134544559958179990583582816820200706321643505931963759348197683716703151934454967253945279317468500847113900963301227806965444007791473349736535619107915081922755289659639124861072066321258227154320863069197348295205246346627229497135969779145144403846729543773550828048408577832464199685530320525611276540873184325205260066343989452895229701747287998514224284119465526364972802976276466946705276529850757067551003693359892105531964521719825098758902590612800073250179329130183578711785455045271709104028152978970180956167480212355938831445525604496153233034498346393965241325063167341734850478477316475797710771227713848710707759075835087798026114891563978094837358334193267378348587599807938893258718336220536511549981283099528255997531309368226776412290820330442883180706241255149666086433686751268243442544239278565560306248045852540613483548725304976506107726479516774011472863652121016212329057274713129440567960440793428434445557346247719430249407428578249556672683116016320758068475470865887911869197014563703627743236850256991405375312274884966514412034341262332260206277004728886871477855760637027596347665741210127469489986305449767871006106061456328147380101401892851372422633667450526396443694973100311770

private def light (n : ℕ) : Bool :=
  if n≤76 then decide n.Prime else n.gcd 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 == 1

private theorem light_ok {n : ℕ} (hn : n≤5895) : light n=true ↔ n.Prime := by
  unfold light
  split_ifs with small
  · simp
  · have fac : Nat.factorial 76 = 1885494701666050254987932260861146558230394535379329335672487982961844043495537923117729972224000000000000000000 := by decide +kernel
    rw [←fac,beq_iff_eq]
    constructor
    · intro cop
      by_contra no
      have prime := Nat.minFac_prime (n:=n) (by omega)
      have sq := Nat.minFac_sq_le_self (n:=n) (by omega) no
      have cut : n.minFac ≤ 76 := by
        by_contra! high
        have ge := Nat.mul_le_mul high high
        rw [pow_two] at sq
        omega
      have d := Nat.dvd_gcd (Nat.minFac_dvd n) (Nat.dvd_factorial (Nat.minFac_pos n) cut)
      rw [cop] at d
      exact prime.not_dvd_one d
    · intro prime
      exact prime.coprime_factorial_of_lt (by omega)

private def quick (n : ℕ) : Bool := if n≤5895 then light n else n.gcd radical == 1

private def smallCheck (p : ℕ) := decide (p≤1) || !(p.gcd radical == 1)
private def smallValid (lo count : ℕ) : Prop := (List.range' lo count).all smallCheck = true
private theorem joinSmall {lo a b : ℕ} (h : smallValid lo a) (k : smallValid (lo+a) b) :
    smallValid lo (a+b) := by
  unfold smallValid at *
  rw [← List.range'_append_1,List.all_append,h,k]
  rfl


private theorem sp0 : smallValid 0 46 := by unfold smallValid; decide +kernel

private theorem sp46 : smallValid 46 46 := by unfold smallValid; decide +kernel

private theorem sp92 : smallValid 92 46 := by unfold smallValid; decide +kernel

private theorem sp138 : smallValid 138 46 := by unfold smallValid; decide +kernel

private theorem sp184 : smallValid 184 46 := by unfold smallValid; decide +kernel

private theorem sp230 : smallValid 230 46 := by unfold smallValid; decide +kernel

private theorem sp276 : smallValid 276 46 := by unfold smallValid; decide +kernel

private theorem sp322 : smallValid 322 46 := by unfold smallValid; decide +kernel

private theorem sp368 : smallValid 368 46 := by unfold smallValid; decide +kernel

private theorem sp414 : smallValid 414 46 := by unfold smallValid; decide +kernel

private theorem sp460 : smallValid 460 46 := by unfold smallValid; decide +kernel

private theorem sp506 : smallValid 506 46 := by unfold smallValid; decide +kernel

private theorem sp552 : smallValid 552 46 := by unfold smallValid; decide +kernel

private theorem sp598 : smallValid 598 46 := by unfold smallValid; decide +kernel

private theorem sp644 : smallValid 644 46 := by unfold smallValid; decide +kernel

private theorem sp690 : smallValid 690 47 := by unfold smallValid; decide +kernel

private theorem sp737 : smallValid 737 46 := by unfold smallValid; decide +kernel

private theorem sp783 : smallValid 783 46 := by unfold smallValid; decide +kernel

private theorem sp829 : smallValid 829 46 := by unfold smallValid; decide +kernel

private theorem sp875 : smallValid 875 46 := by unfold smallValid; decide +kernel

private theorem sp921 : smallValid 921 46 := by unfold smallValid; decide +kernel

private theorem sp967 : smallValid 967 46 := by unfold smallValid; decide +kernel

private theorem sp1013 : smallValid 1013 46 := by unfold smallValid; decide +kernel

private theorem sp1059 : smallValid 1059 46 := by unfold smallValid; decide +kernel

private theorem sp1105 : smallValid 1105 46 := by unfold smallValid; decide +kernel

private theorem sp1151 : smallValid 1151 46 := by unfold smallValid; decide +kernel

private theorem sp1197 : smallValid 1197 46 := by unfold smallValid; decide +kernel

private theorem sp1243 : smallValid 1243 46 := by unfold smallValid; decide +kernel

private theorem sp1289 : smallValid 1289 46 := by unfold smallValid; decide +kernel

private theorem sp1335 : smallValid 1335 46 := by unfold smallValid; decide +kernel

private theorem sp1381 : smallValid 1381 46 := by unfold smallValid; decide +kernel

private theorem sp1427 : smallValid 1427 47 := by unfold smallValid; decide +kernel

private theorem sp1474 : smallValid 1474 46 := by unfold smallValid; decide +kernel

private theorem sp1520 : smallValid 1520 46 := by unfold smallValid; decide +kernel

private theorem sp1566 : smallValid 1566 46 := by unfold smallValid; decide +kernel

private theorem sp1612 : smallValid 1612 46 := by unfold smallValid; decide +kernel

private theorem sp1658 : smallValid 1658 46 := by unfold smallValid; decide +kernel

private theorem sp1704 : smallValid 1704 46 := by unfold smallValid; decide +kernel

private theorem sp1750 : smallValid 1750 46 := by unfold smallValid; decide +kernel

private theorem sp1796 : smallValid 1796 46 := by unfold smallValid; decide +kernel

private theorem sp1842 : smallValid 1842 46 := by unfold smallValid; decide +kernel

private theorem sp1888 : smallValid 1888 46 := by unfold smallValid; decide +kernel

private theorem sp1934 : smallValid 1934 46 := by unfold smallValid; decide +kernel

private theorem sp1980 : smallValid 1980 46 := by unfold smallValid; decide +kernel

private theorem sp2026 : smallValid 2026 46 := by unfold smallValid; decide +kernel

private theorem sp2072 : smallValid 2072 46 := by unfold smallValid; decide +kernel

private theorem sp2118 : smallValid 2118 46 := by unfold smallValid; decide +kernel

private theorem sp2164 : smallValid 2164 47 := by unfold smallValid; decide +kernel

private theorem sp2211 : smallValid 2211 46 := by unfold smallValid; decide +kernel

private theorem sp2257 : smallValid 2257 46 := by unfold smallValid; decide +kernel

private theorem sp2303 : smallValid 2303 46 := by unfold smallValid; decide +kernel

private theorem sp2349 : smallValid 2349 46 := by unfold smallValid; decide +kernel

private theorem sp2395 : smallValid 2395 46 := by unfold smallValid; decide +kernel

private theorem sp2441 : smallValid 2441 46 := by unfold smallValid; decide +kernel

private theorem sp2487 : smallValid 2487 46 := by unfold smallValid; decide +kernel

private theorem sp2533 : smallValid 2533 46 := by unfold smallValid; decide +kernel

private theorem sp2579 : smallValid 2579 46 := by unfold smallValid; decide +kernel

private theorem sp2625 : smallValid 2625 46 := by unfold smallValid; decide +kernel

private theorem sp2671 : smallValid 2671 46 := by unfold smallValid; decide +kernel

private theorem sp2717 : smallValid 2717 46 := by unfold smallValid; decide +kernel

private theorem sp2763 : smallValid 2763 46 := by unfold smallValid; decide +kernel

private theorem sp2809 : smallValid 2809 46 := by unfold smallValid; decide +kernel

private theorem sp2855 : smallValid 2855 46 := by unfold smallValid; decide +kernel

private theorem sp2901 : smallValid 2901 47 := by unfold smallValid; decide +kernel

private theorem sp2948 : smallValid 2948 46 := by unfold smallValid; decide +kernel

private theorem sp2994 : smallValid 2994 46 := by unfold smallValid; decide +kernel

private theorem sp3040 : smallValid 3040 46 := by unfold smallValid; decide +kernel

private theorem sp3086 : smallValid 3086 46 := by unfold smallValid; decide +kernel

private theorem sp3132 : smallValid 3132 46 := by unfold smallValid; decide +kernel

private theorem sp3178 : smallValid 3178 46 := by unfold smallValid; decide +kernel

private theorem sp3224 : smallValid 3224 46 := by unfold smallValid; decide +kernel

private theorem sp3270 : smallValid 3270 46 := by unfold smallValid; decide +kernel

private theorem sp3316 : smallValid 3316 46 := by unfold smallValid; decide +kernel

private theorem sp3362 : smallValid 3362 46 := by unfold smallValid; decide +kernel

private theorem sp3408 : smallValid 3408 46 := by unfold smallValid; decide +kernel

private theorem sp3454 : smallValid 3454 46 := by unfold smallValid; decide +kernel

private theorem sp3500 : smallValid 3500 46 := by unfold smallValid; decide +kernel

private theorem sp3546 : smallValid 3546 46 := by unfold smallValid; decide +kernel

private theorem sp3592 : smallValid 3592 46 := by unfold smallValid; decide +kernel

private theorem sp3638 : smallValid 3638 47 := by unfold smallValid; decide +kernel

private theorem sp3685 : smallValid 3685 46 := by unfold smallValid; decide +kernel

private theorem sp3731 : smallValid 3731 46 := by unfold smallValid; decide +kernel

private theorem sp3777 : smallValid 3777 46 := by unfold smallValid; decide +kernel

private theorem sp3823 : smallValid 3823 46 := by unfold smallValid; decide +kernel

private theorem sp3869 : smallValid 3869 46 := by unfold smallValid; decide +kernel

private theorem sp3915 : smallValid 3915 46 := by unfold smallValid; decide +kernel

private theorem sp3961 : smallValid 3961 46 := by unfold smallValid; decide +kernel

private theorem sp4007 : smallValid 4007 46 := by unfold smallValid; decide +kernel

private theorem sp4053 : smallValid 4053 46 := by unfold smallValid; decide +kernel

private theorem sp4099 : smallValid 4099 46 := by unfold smallValid; decide +kernel

private theorem sp4145 : smallValid 4145 46 := by unfold smallValid; decide +kernel

private theorem sp4191 : smallValid 4191 46 := by unfold smallValid; decide +kernel

private theorem sp4237 : smallValid 4237 46 := by unfold smallValid; decide +kernel

private theorem sp4283 : smallValid 4283 46 := by unfold smallValid; decide +kernel

private theorem sp4329 : smallValid 4329 46 := by unfold smallValid; decide +kernel

private theorem sp4375 : smallValid 4375 47 := by unfold smallValid; decide +kernel

private theorem sp4422 : smallValid 4422 46 := by unfold smallValid; decide +kernel

private theorem sp4468 : smallValid 4468 46 := by unfold smallValid; decide +kernel

private theorem sp4514 : smallValid 4514 46 := by unfold smallValid; decide +kernel

private theorem sp4560 : smallValid 4560 46 := by unfold smallValid; decide +kernel

private theorem sp4606 : smallValid 4606 46 := by unfold smallValid; decide +kernel

private theorem sp4652 : smallValid 4652 46 := by unfold smallValid; decide +kernel

private theorem sp4698 : smallValid 4698 46 := by unfold smallValid; decide +kernel

private theorem sp4744 : smallValid 4744 46 := by unfold smallValid; decide +kernel

private theorem sp4790 : smallValid 4790 46 := by unfold smallValid; decide +kernel

private theorem sp4836 : smallValid 4836 46 := by unfold smallValid; decide +kernel

private theorem sp4882 : smallValid 4882 46 := by unfold smallValid; decide +kernel

private theorem sp4928 : smallValid 4928 46 := by unfold smallValid; decide +kernel

private theorem sp4974 : smallValid 4974 46 := by unfold smallValid; decide +kernel

private theorem sp5020 : smallValid 5020 46 := by unfold smallValid; decide +kernel

private theorem sp5066 : smallValid 5066 46 := by unfold smallValid; decide +kernel

private theorem sp5112 : smallValid 5112 47 := by unfold smallValid; decide +kernel

private theorem sp5159 : smallValid 5159 46 := by unfold smallValid; decide +kernel

private theorem sp5205 : smallValid 5205 46 := by unfold smallValid; decide +kernel

private theorem sp5251 : smallValid 5251 46 := by unfold smallValid; decide +kernel

private theorem sp5297 : smallValid 5297 46 := by unfold smallValid; decide +kernel

private theorem sp5343 : smallValid 5343 46 := by unfold smallValid; decide +kernel

private theorem sp5389 : smallValid 5389 46 := by unfold smallValid; decide +kernel

private theorem sp5435 : smallValid 5435 46 := by unfold smallValid; decide +kernel

private theorem sp5481 : smallValid 5481 46 := by unfold smallValid; decide +kernel

private theorem sp5527 : smallValid 5527 46 := by unfold smallValid; decide +kernel

private theorem sp5573 : smallValid 5573 46 := by unfold smallValid; decide +kernel

private theorem sp5619 : smallValid 5619 46 := by unfold smallValid; decide +kernel

private theorem sp5665 : smallValid 5665 46 := by unfold smallValid; decide +kernel

private theorem sp5711 : smallValid 5711 46 := by unfold smallValid; decide +kernel

private theorem sp5757 : smallValid 5757 46 := by unfold smallValid; decide +kernel

private theorem sp5803 : smallValid 5803 46 := by unfold smallValid; decide +kernel

private theorem sp5849 : smallValid 5849 47 := by unfold smallValid; decide +kernel

private theorem smallPrimeDvd (p : ℕ) (bound : p≤5895) (hp : p.Prime) : p ∣ radical := by
  have all : smallValid 0 5896 := (joinSmall (lo:=0) (a:=2948) (b:=2948) (joinSmall (lo:=0) (a:=1474) (b:=1474) (joinSmall (lo:=0) (a:=737) (b:=737) (joinSmall (lo:=0) (a:=368) (b:=369) (joinSmall (lo:=0) (a:=184) (b:=184) (joinSmall (lo:=0) (a:=92) (b:=92) (joinSmall (lo:=0) (a:=46) (b:=46) sp0 sp46) (joinSmall (lo:=92) (a:=46) (b:=46) sp92 sp138)) (joinSmall (lo:=184) (a:=92) (b:=92) (joinSmall (lo:=184) (a:=46) (b:=46) sp184 sp230) (joinSmall (lo:=276) (a:=46) (b:=46) sp276 sp322))) (joinSmall (lo:=368) (a:=184) (b:=185) (joinSmall (lo:=368) (a:=92) (b:=92) (joinSmall (lo:=368) (a:=46) (b:=46) sp368 sp414) (joinSmall (lo:=460) (a:=46) (b:=46) sp460 sp506)) (joinSmall (lo:=552) (a:=92) (b:=93) (joinSmall (lo:=552) (a:=46) (b:=46) sp552 sp598) (joinSmall (lo:=644) (a:=46) (b:=47) sp644 sp690)))) (joinSmall (lo:=737) (a:=368) (b:=369) (joinSmall (lo:=737) (a:=184) (b:=184) (joinSmall (lo:=737) (a:=92) (b:=92) (joinSmall (lo:=737) (a:=46) (b:=46) sp737 sp783) (joinSmall (lo:=829) (a:=46) (b:=46) sp829 sp875)) (joinSmall (lo:=921) (a:=92) (b:=92) (joinSmall (lo:=921) (a:=46) (b:=46) sp921 sp967) (joinSmall (lo:=1013) (a:=46) (b:=46) sp1013 sp1059))) (joinSmall (lo:=1105) (a:=184) (b:=185) (joinSmall (lo:=1105) (a:=92) (b:=92) (joinSmall (lo:=1105) (a:=46) (b:=46) sp1105 sp1151) (joinSmall (lo:=1197) (a:=46) (b:=46) sp1197 sp1243)) (joinSmall (lo:=1289) (a:=92) (b:=93) (joinSmall (lo:=1289) (a:=46) (b:=46) sp1289 sp1335) (joinSmall (lo:=1381) (a:=46) (b:=47) sp1381 sp1427))))) (joinSmall (lo:=1474) (a:=737) (b:=737) (joinSmall (lo:=1474) (a:=368) (b:=369) (joinSmall (lo:=1474) (a:=184) (b:=184) (joinSmall (lo:=1474) (a:=92) (b:=92) (joinSmall (lo:=1474) (a:=46) (b:=46) sp1474 sp1520) (joinSmall (lo:=1566) (a:=46) (b:=46) sp1566 sp1612)) (joinSmall (lo:=1658) (a:=92) (b:=92) (joinSmall (lo:=1658) (a:=46) (b:=46) sp1658 sp1704) (joinSmall (lo:=1750) (a:=46) (b:=46) sp1750 sp1796))) (joinSmall (lo:=1842) (a:=184) (b:=185) (joinSmall (lo:=1842) (a:=92) (b:=92) (joinSmall (lo:=1842) (a:=46) (b:=46) sp1842 sp1888) (joinSmall (lo:=1934) (a:=46) (b:=46) sp1934 sp1980)) (joinSmall (lo:=2026) (a:=92) (b:=93) (joinSmall (lo:=2026) (a:=46) (b:=46) sp2026 sp2072) (joinSmall (lo:=2118) (a:=46) (b:=47) sp2118 sp2164)))) (joinSmall (lo:=2211) (a:=368) (b:=369) (joinSmall (lo:=2211) (a:=184) (b:=184) (joinSmall (lo:=2211) (a:=92) (b:=92) (joinSmall (lo:=2211) (a:=46) (b:=46) sp2211 sp2257) (joinSmall (lo:=2303) (a:=46) (b:=46) sp2303 sp2349)) (joinSmall (lo:=2395) (a:=92) (b:=92) (joinSmall (lo:=2395) (a:=46) (b:=46) sp2395 sp2441) (joinSmall (lo:=2487) (a:=46) (b:=46) sp2487 sp2533))) (joinSmall (lo:=2579) (a:=184) (b:=185) (joinSmall (lo:=2579) (a:=92) (b:=92) (joinSmall (lo:=2579) (a:=46) (b:=46) sp2579 sp2625) (joinSmall (lo:=2671) (a:=46) (b:=46) sp2671 sp2717)) (joinSmall (lo:=2763) (a:=92) (b:=93) (joinSmall (lo:=2763) (a:=46) (b:=46) sp2763 sp2809) (joinSmall (lo:=2855) (a:=46) (b:=47) sp2855 sp2901)))))) (joinSmall (lo:=2948) (a:=1474) (b:=1474) (joinSmall (lo:=2948) (a:=737) (b:=737) (joinSmall (lo:=2948) (a:=368) (b:=369) (joinSmall (lo:=2948) (a:=184) (b:=184) (joinSmall (lo:=2948) (a:=92) (b:=92) (joinSmall (lo:=2948) (a:=46) (b:=46) sp2948 sp2994) (joinSmall (lo:=3040) (a:=46) (b:=46) sp3040 sp3086)) (joinSmall (lo:=3132) (a:=92) (b:=92) (joinSmall (lo:=3132) (a:=46) (b:=46) sp3132 sp3178) (joinSmall (lo:=3224) (a:=46) (b:=46) sp3224 sp3270))) (joinSmall (lo:=3316) (a:=184) (b:=185) (joinSmall (lo:=3316) (a:=92) (b:=92) (joinSmall (lo:=3316) (a:=46) (b:=46) sp3316 sp3362) (joinSmall (lo:=3408) (a:=46) (b:=46) sp3408 sp3454)) (joinSmall (lo:=3500) (a:=92) (b:=93) (joinSmall (lo:=3500) (a:=46) (b:=46) sp3500 sp3546) (joinSmall (lo:=3592) (a:=46) (b:=47) sp3592 sp3638)))) (joinSmall (lo:=3685) (a:=368) (b:=369) (joinSmall (lo:=3685) (a:=184) (b:=184) (joinSmall (lo:=3685) (a:=92) (b:=92) (joinSmall (lo:=3685) (a:=46) (b:=46) sp3685 sp3731) (joinSmall (lo:=3777) (a:=46) (b:=46) sp3777 sp3823)) (joinSmall (lo:=3869) (a:=92) (b:=92) (joinSmall (lo:=3869) (a:=46) (b:=46) sp3869 sp3915) (joinSmall (lo:=3961) (a:=46) (b:=46) sp3961 sp4007))) (joinSmall (lo:=4053) (a:=184) (b:=185) (joinSmall (lo:=4053) (a:=92) (b:=92) (joinSmall (lo:=4053) (a:=46) (b:=46) sp4053 sp4099) (joinSmall (lo:=4145) (a:=46) (b:=46) sp4145 sp4191)) (joinSmall (lo:=4237) (a:=92) (b:=93) (joinSmall (lo:=4237) (a:=46) (b:=46) sp4237 sp4283) (joinSmall (lo:=4329) (a:=46) (b:=47) sp4329 sp4375))))) (joinSmall (lo:=4422) (a:=737) (b:=737) (joinSmall (lo:=4422) (a:=368) (b:=369) (joinSmall (lo:=4422) (a:=184) (b:=184) (joinSmall (lo:=4422) (a:=92) (b:=92) (joinSmall (lo:=4422) (a:=46) (b:=46) sp4422 sp4468) (joinSmall (lo:=4514) (a:=46) (b:=46) sp4514 sp4560)) (joinSmall (lo:=4606) (a:=92) (b:=92) (joinSmall (lo:=4606) (a:=46) (b:=46) sp4606 sp4652) (joinSmall (lo:=4698) (a:=46) (b:=46) sp4698 sp4744))) (joinSmall (lo:=4790) (a:=184) (b:=185) (joinSmall (lo:=4790) (a:=92) (b:=92) (joinSmall (lo:=4790) (a:=46) (b:=46) sp4790 sp4836) (joinSmall (lo:=4882) (a:=46) (b:=46) sp4882 sp4928)) (joinSmall (lo:=4974) (a:=92) (b:=93) (joinSmall (lo:=4974) (a:=46) (b:=46) sp4974 sp5020) (joinSmall (lo:=5066) (a:=46) (b:=47) sp5066 sp5112)))) (joinSmall (lo:=5159) (a:=368) (b:=369) (joinSmall (lo:=5159) (a:=184) (b:=184) (joinSmall (lo:=5159) (a:=92) (b:=92) (joinSmall (lo:=5159) (a:=46) (b:=46) sp5159 sp5205) (joinSmall (lo:=5251) (a:=46) (b:=46) sp5251 sp5297)) (joinSmall (lo:=5343) (a:=92) (b:=92) (joinSmall (lo:=5343) (a:=46) (b:=46) sp5343 sp5389) (joinSmall (lo:=5435) (a:=46) (b:=46) sp5435 sp5481))) (joinSmall (lo:=5527) (a:=184) (b:=185) (joinSmall (lo:=5527) (a:=92) (b:=92) (joinSmall (lo:=5527) (a:=46) (b:=46) sp5527 sp5573) (joinSmall (lo:=5619) (a:=46) (b:=46) sp5619 sp5665)) (joinSmall (lo:=5711) (a:=92) (b:=93) (joinSmall (lo:=5711) (a:=46) (b:=46) sp5711 sp5757) (joinSmall (lo:=5803) (a:=46) (b:=47) sp5803 sp5849)))))))
  have good : (List.range 5896).all smallCheck=true := by rw [List.range_eq_range'];exact all
  have h := List.all_eq_true.mp good p (List.mem_range.mpr (by omega))
  have hn : ¬ p≤1 := by have := hp.two_le; omega
  have ne : p.gcd radical ≠ 1 := by simpa [smallCheck,hn] using h
  have eq : p.gcd radical = p := ((Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p radical)).resolve_left ne
  simpa only [eq] using Nat.gcd_dvd_right p radical
set_option maxRecDepth 16000 in
private theorem quick_ok {n : ℕ} (hn : n ≤ 34751024) : quick n=true ↔ n.Prime := by
  unfold quick
  split_ifs with hs
  · exact light_ok hs
  · have hm : radical ∣ Nat.factorial 5895 := by decide +kernel
    rw [beq_iff_eq]
    constructor
    · intro eq
      by_contra hnp
      have hpr := Nat.minFac_prime (n:=n) (by omega)
      have hsq := Nat.minFac_sq_le_self (n:=n) (by omega) hnp
      have hfac : n.minFac ≤ 5895 := by
        by_contra! hi
        have hb := Nat.mul_le_mul hi hi
        rw [pow_two] at hsq
        omega
      have hd := Nat.dvd_gcd (Nat.minFac_dvd n) (smallPrimeDvd n.minFac hfac hpr)
      rw [eq] at hd
      exact hpr.not_dvd_one hd
    · intro hp
      exact Nat.Coprime.of_dvd_right hm (hp.coprime_factorial_of_lt (by omega))





def tally (f : ℕ → Bool) (s len : ℕ) : ℕ := (List.range' s len).countP f

theorem tally_succ (f : ℕ → Bool) (s len : ℕ) :
    tally f s (len+1) = tally f s len + (if f (s+len) then 1 else 0) := by
  unfold tally
  rw [← List.range'_append_1, List.countP_append]
  simp

def fromBlocks (c : ℕ → ℕ) (f : ℕ → Bool) (j : ℕ) : ℕ :=
  c (j/512) + tally f (512*(j/512)) (j%512)

theorem fromBlocks_succ (c : ℕ → ℕ) (f : ℕ → Bool) (j : ℕ)
    (boundary : c (j/512+1) = c (j/512) + tally f (512*(j/512)) 512) :
    fromBlocks c f (j+1) = fromBlocks c f j + (if f j then 1 else 0) := by
  have split := Nat.div_add_mod j 512
  have hs := tally_succ f (512*(j/512)) (j%512)
  rw [split] at hs
  unfold fromBlocks
  by_cases h : j%512=511
  · have div : (j+1)/512 = j/512+1 := by omega
    have rem : (j+1)%512 = 0 := by omega
    rw [div,rem,boundary]
    rw [show j%512+1=512 by omega] at hs
    simp [tally] at *
    omega
  · have div : (j+1)/512 = j/512 := by omega
    have rem : (j+1)%512 = j%512+1 := by omega
    rw [div,rem,hs]
    omega


private def packet (i : ℕ) : ℕ := (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0x234643e39d10d786312dc94e095242b1d98cac5362140c7840c0fe000022c023ee9d78db26522de14ec97a4311dd8cbc54a21a0ca84340fe0000223ba3e29d2cd966462df14f09684281d40c7853e21b0c80430104000021b523f49d80dc665a2e3950497c4351d88c9453c20c0c704281060000213073dd9cd4d7e6492e214f896c42e1d18c4c5102010c084380fe000020aa53ef9d44d9863b2dd950096c4261d28c7c52420c0c984281100000202613dc1ca8d566272ca946c92040c1c60bf850a2100c8044811e00001fa0a3e39cf8d566292d614889304141cb0c2c5262120bf83dc10a00001f1a53ed1d70da26552e9951c98843c1e10ccc5502160c9043811000001e94a3f09d5cda865c2ea150c9804311d30ca85462110c1041c10800001e0ef3f09d40d8e63c2d694dc9544221cd0c685582270cc842810800001d8783f41d70daa6532e7951c9804421de0cdc56a22f0d0042410800001d02f3e51cf4d766402d694d095c42b1d38c9853c21e0cb041810c00001c7c93ee9d40db66562e794f496a4311d58c7c5302130ca042c10c00001bf753e59d28da26492e5151096e4391da8cbc5602200cf845011e00001b6e83fb9dacdcc6692f0157c9944421d98c985582210cd04340f400001ae703f71d94dca6692ec955898043d1de8ce854421c0ca845810e00001a6053f39d80db26502df94c494641c1cc8c184f41f50b883c40e6000019d833f89d98dbc65f2ec15549b443d1d48c685322100c684240f20000194f34029dd4dcc65a2e995449904401dd8cc055421f0cc044010a000018c743f99ddcde66742f2956c98e4441e10ce456222d0d684981380000184123f41d60d9a64c2e614ec97242e1d60c7c5282160c384140fa000017b784079df8dde66d2ef15609a64501e68cfc56e2310cc84501120000172f13fd9dc0db26582ee952096a4331d68c9852a2080c6044c10e000016a7d3fb9d84dbe65c2e795389804301cd8c4c52a2110c884281140000161d14111e74e286842ff95c09d44581e58ce05522200cb044810e00001593040d1e30de86672ee150c98243b1d40c8452a2120c8841c0fc0000150854101e40e0467b2f395789a245e1e80d1458423a0d5845c1120000147d14101e50e186862fd15b09be4421e48d0457422f0d48434118000013f463fe9de4dca6592e9151498643e1d78ca454421e0ce844411000001369c40d9e24e1a6872fe95ac9ce45b1eb0d285842390d0045c116000012ddc4199eb4e346812ff95ac9ba4541e10cdc5642260cf04681180000125454081e44e126862fd95b89b24481e40cf055c21a0c8044810a000011c8d4139e88e3269730415d49da4671f00d3c58a23b0d984a81200000113d14189e90e2c68d30a96289e04571e38d0c56c23d0d70488128000010b014271f00e5c6a53111634a0246f1f08d645a22420d9846011e0000102444199e84e2e68f30415d89ca4681eb8d145802380d484a011800000f9754251efce5269030395ec9d24611e90d105662380ce044c11a00000f08b42c9f1ce766aa30f16249fa46e1f18d385842370d6048811e00000e7b84231ed4e466912fd95d89da45b1e20ce055c2280d3847c12400000dece4309f40e7a6b43121654a0e4711ee0d4c5a22420db849013000000d5d94319f44e7c6b4315966ca164781f90d8059e23d0da846811200000cce74329f48e826bb3189668a104781f28d6059c23e0d5847811800000c4064249f00e646b4313163c9f846e1f40d805a62450d984b012a00000bafa43f9fa8eb46c531c96aca2a4881fc0dac5aa2410de04a411800000b1e54411fbceba6c831d1690a2647e1f68d9059a2490d7048812c00000a8e243c1f84e946c431e1680a324881f88d945a62420dc0490118000009fb044ba01ced26db32116e0a464971ff8db85d02510dd049c120000009671454a038ef86ff3349744a744b42090e085c824c0db048c120000008d454502050efc6ef3359728a7e4b72100e045d02610e904d012a00000840c4502038f006e632a96f0a564911ff8da85a42360d4847811e000007ac4458a098f206e932696eca584942000db85b02460d4844c10a000007165463a0b4f226fd33c976caa84b220d8e105d424d0de849011e0000067d9476a164f8a72d34a97e4ab84c92188e405e02580dd049c120000005e5f46e20e0f44707339976ca944bb20f8e105fc25e0e604a01260000054bc480a1d0fb673834a97ecaba4ce21c0e6860e2670eb04fc130000004b0a488a1e8fb0739354984cb004ef2200e9861626c0e884c012600000412f49ea2a900875f36098a0b144f322b8ee064427c0f2050415200000374c4a0a2b8ffe76936318a8b124e12268ec062e2770e984fc138000002d1f4c5238907e79937e9998b7251b2390f4c6562910f4851c14e0000022c04dc24390d87c53959a08bc053924b0fbc69c2a91000584164000001820500a5411608083b19abcc0e55b25a90306b22ad1020558152000000cef54827652408733e31c48cc05ad281113c72a2e211505e817a00000000061eae05584a084a121f4f7e6ff31a95a893a3ca1790844244000 else 0x438d63ba1bd0cda5f12b593c08d03f41b88be85021f70ba83c00ea0000430e73bb9be4cf65fb2b713ac8e63e91b98bc04e61f00ba83e00e80000429023b69b98cea5f82bc13f88f23fa1be0c0051a2080c484181180000420f83c69c2cd2661e2d0946493241e1d30c6c5382170c7843412600004191d3b41bcccc85ef2b6139c8c23ed1b88bd84fe1ff0bc83f01000000411423ab1b6ccac5df2b393948ca3e81be0c2852220f0c8043c10c0000409473c01c1cd186102ce947492c4241ce0c5051a2040c2842010600004014c3be9bfccee6062bf943091440d1c68c1c50c1fb0c103f00fe00003f93e3c81c50d4461b2c7942091a4051c28c1850e2070c0043811c00003f18339f1b1cca85e12b513b48e03ed1b80bd84f81fe0bd83ec0fe00003e9463dd9ca4d5e62b2d714b094c4211ce0c445162130c6844010a00003e1623b39bd4cf45f22b993b48e03f91bd0bec4f820b0c1040410800003d97f3b11ba0cc45e02af138c8ca3f21b48ba84d81f20bd04000f800003d19b3ab9b84cbe5ef2bb14008f44001c60c3c5082020c2843c11a00003c9dd3a69b1cca85d72a993248a43da1b10b884dc1f30b9841010800003c2073b09b6ccb85e72b693bc8ee3fc1ba0c045101fc0c384100fc00003b9f13ca1c28d086022be941c90a4031bd0c045062050c2842811200003b1ec3bf1c1cd145fc2bd94048fc3f31bb0c084fe1f90bb83c40ee00003a9f93b59b98cd25f42b6938c8c03d01b00b644d61f30ba83f010400003a2073b99bf4d065ee2b613a08dc3f31c08bfc4fc2020b983d00f6000039a113bc9be4cf25f52b413ac8c83ed1b88bf44f21fc0c5042c1040000392053c51c28d206172c914189064071c60c345182080c58428108000038a083c09c18d026072c4941490e4111cc0c485062010be841c0f60000381e23d09c9cd3c6272d0145895241e1ca8c4052e21e0c884040fe0000379c13ce1c6cd306162cb144c90e40d1c68c4c5322110c504501160000371c93b89c10d1060a2c693f88f03f71bb8bd04f81f60ba83f81000000369ad3d49c58d286142d0147c93a4161c88c2c5202120c8042c1100000361a03c51c8cd4c61f2d4148493c4111c80c4c53020f0c884280f200003599c3be9bd0cde5f62c393f08ee4001c28c085062050c284301100000351af3bb1bbccec5fa2bb93dc9023f61bd0c004ec2030c384301200000349943cf9c64d3e6192c9946091840e1c58c145202160ca844411200003418b3c41c30d1460b2c8943c90e4041c28bf04ea1ff0c2843c1100000339893c21c10d0260f2cc14449064061c58c1c5122130c384281100000331853c21c20d0c60b2c5141c9064011c18be85042030c1842410e0000329863bf9be8cf85f82c093f49143ff1bf8c4c51c2040c284081080000321763cd9c68d386182ca14489364161ca8c505182050bb03cc0d400003192b3e61d14d7a63b2d914d495c4231cc0c6052e20e0c304000ec00003111f3c59c10d106162c9941c90c4081c68c2851820b0bf84301080000309143c81c0ccf85fe2bd14088fc4031c30c1050c1fc0bc03b40f20000300fa3ce1c68d2a61e2d4948895642a1ce8c6c52e2160cb043c11c00002f8d83d69ca8d4861f2cd147092c4131c78c245102070c2041c10400002f0bd3cd9ca4d5862b2d0949c9584261ca0c345262100c4842410000002e8953cf9c80d466272d1144490c40c1c98c345162160ca841810800002e0773cd9c68d486202d1949c9504231cc0c7454021a0cb047012e00002d84d3d99c94d3661f2ca945c9144101c78c344fc1ff0c304040ea00002d0203cf1cacd446262d214809524241d80cb052a2220cd040c10000002c80e3ca9c78d306142c8143492240a1bf0bfc5001f70b983f00f600002bfe23cd9c3cd2c6152cc14549284171c88c4052a21d0c6045411600002b7c43d01c90d286162c494449104031be0bec5041fe0bf03f010600002af913d59ce0d5862b2d1947492a4141cc8c785382180c8046811800002a7743d51cacd546202ca944892a4081c20c104fc20c0c40418100000029f493d09c5cd3260d2c5942090e4041c30c1851c20e0c2041411400002973a3c29c18d1c6032bf94049084041c00c2050a2110c603f00f4000028f1c3d11c54d226082c594249063fb1bb8bcc4fc2030c4041810e0000286be3e99d14d7a6342d614c094c4241ca0c3050820b0c704340fa000027e9d3d01c88d4c61c2c994449264011bf8bd84e81f80c103f010200002766f3d49c94d246162c5941c9264181ce0c405282090c404040f6000026e253e51d0cd766412d894c49544321dc0cbc5642240ca043c10e0000265ed3e01d00d706322d3149c9404141ce0c5052420b0bd04040f6000025db53de9cc4d4e62c2d3948c9384181c78c185021fe0c0040c1020000255773d81c98d526262d414709384231d08c6c52c2150c8041810e000024d383d61cbcd5262e2d594ac95842a1d28c785482240cd84281160000244e03e99d68daa6492e5951c9704301da0cb853a2120c70444120000023caa3d41c94d3861c2ca145091e4021c08bc84e41fb0b983dc0f6000) else (if i < 3 then 0x62b543b21b7ccb85df2b613bc8dc3eb1b10ba04d01e90bf83c40f60000623a63979accc885c52aa93808c63e91b28bb84ca1f30b583c40f0000061c033951ad0c665b429c13148a63dd1ad8b884d61e90bc83f40fa0000614573981abcc605ba29b13148943cd1a80b544be1e90b503cc0f2000060cbc3959a8cc525bb2a013188a63d71af8b984d81f00ba83c40ea00006050439e9af8c6e5c02a6936c8ba3e61b68ba84f21f90c103e80fe00005fd273aa9b70cc85ec2bb13e88fc3f91ba8bdc4f41f80bb83fc10200005f58d3901ab0c6e5bc29d92f08843ca1aa8b844c21e30b203d40ea00005edde3981ad0c6c5c22a513588c43ed1b48bbc4e61f10bb03d010000005e63239d9b04c8e5d12ab93648ae3d51af0ba44ea1f40bd04000fa00005de7b39e9b28ca85cc2a993288bc3ed1bc8be84e41f30b503cc10600005d6c739b1af0c925c62a893488ae3e31b80c005042050c203d00f000005cf2d3931ac0c6c5bc29e935c8b83d51b10bac4e61fa0ba03f00fc00005c7853949ac0c565ae2a0130c8943ce1aa0b304bc1e50b703b40ea00005bfbe3a79b4ccac5d62af93588b83df1b50b9c4c01ee0b603ec0f800005b7f73a21b3ccaa5d92ac13848ca3e21b30bb04ee1fa0bc03e80fe00005b04239d9b20c9e5d62ad13748d23ec1bb0be45062080bc03fc10400005a88939a9abcc7c5c62a5134c8bc3de1af8ba04ce1e80b483dc11800005a0c13a81b54c9a5d62b013848c23e11b40bb04ca1eb0ba83e81020000598ff3a41b40cbe5e92b513a08ce3ea1b78bcc4de1f90b903b80e600005915d3979ae4c745c22a6933c8903cb1ab0b684b41d90ae03a40e00000589793af9b5ccb25d92ad13708c43d71b00b984d81ed0b783d40e40000581a23ad9b70cc25de2ad93988e03fe1ba0bbc4d41f20b903c40e80000579f83979abcc725bc2a313208a83da1af8bbc4d01e70b803dc0fe00005722c3a59b44cb85dc2af13808d83f11ba0be84fa1fb0c384200fc000056a7939d1b24c9a5c62a113188923d71aa8b784b81dc0b883cc0fe0000562a83ac1b60cc45e02b213c48da3e91b88bdc4e01f60bb83f4110000055aef3a19b1cca45d72af13888b23d41ab0b604ca1eb0bc03f40fa0000553323a19b20ca25d82ac13648a63d51b28b884d41e20b783dc0ee000054b623a99b5ccd05e52b393cc9044071bf8c045001f50bf04201160000543893a91b80cc05f12b593a88da3e21b10bdc4e41f00b903e80fe000053bbf3a19b34c985d12ac13608c23e11b20b984dc1ee0b483b80ec0000533cc3b91bd8d146052c1943093a40d1c70c2c51820c0c283fc102000052c003a99b38c9a5d12ac93a08c63ee1b60b944c41ea0b503bc0ee0000524373a49b24c945ca2a913708ca3ee1b10b444b01da0b003840ec000051c573ae1b80cbc5db2b1139c8de3f91bf0be84e21f50bb83e80ee0000514a939e1afcc805c42a913388ac3d81ac8b584d81f70ba83c80f0000050cd93a79b38caa5cc2ac13948dc3f11bf0bf44fa20d0c2042c10e00005050e3a69b38c9e5de2af939c8ca3e01b20b984e01eb0be840010600004fd253bb1bc8cc85ed2ba941490a3f81be0be84e41f60bb03d00f600004f5663991af4c805c229e13188a83db1b48bb84e21eb0b583d810200004ed953aa9b4cca85e52ae939c8e23e81ba8be84de1fa0c3841410a00004e5bd3aa1b5ccb25e02b713cc8e43ee1b58bb04e02000bc83fc10600004dde43ad9b50ccc5f32b793b88e23e51b40bd04f41f90b583cc0fa00004d6233a01af8c8a5c22a793548b43e31b20b9c4d21ed0ba03ec0f800004ce5e3a51b50cb85ea2b713ac8d63ed1b78be44f42030c1042011200004c67b3ac9b70cc65e32b113808ca3ef1b78bb84e01f80ba83dc0e800004be733c31c1cd0a60c2c614309104041bc8bec5042070c4041010400004b6993ab1b58ca05d12ac132c8a23d11ac8b7c4c81e70b403cc0e400004aeb33b39b88ce45f82b993c48dc3f71c00c244e01f50b903e410600004a6f33a31b24ca65dc2aa13788c83e31b60bcc4fa1f90bf03d4104000049f1d3b09b88cac5db2b513e08e23eb1bb8bc44e81fa0ba84280f40000497583a19b10c985d52a913508bc3e11b60bc84e61f50c2040c10a000048f783b21bc4cf25fb2be13e890240b1c18c004f41fb0c584301100000487bd3a11b54cac5d92b213948da3f11ba0b904d81f00bb84040fc000047fbc3c29beccf86012bf142091040f1c88c305182080c184041100000477ca3bd9bf8d0c60a2ca147c92c4171c68c245162030c4044010c00004702239a9ad0c705b629b12ec88c3ce1ad0b704be1d90b483ac0e60000468363b39be4cfa5f02be13c08e43fb1c38c185042030be842010e0000460563b01bb4cde5ef2b593b88c63e91b68ba04e81f60bc04000e80000458553c61c44d286142c8943091a4081bf0bfc4ee1fa0bc03e00fc0000450743ad1b5ccc25e32af13988d43e91b20b884de1ee0b203a40f00000448a73a21b34caa5d62b213d08e03fa1b68bbc4d61ee0b583ac0f20000440ce3af9b8ccd45ed2b813fc9023f51b98bdc4e81ef0bb83c40f2000 else 0x8136e3a11b10c8e5d22b0938c8c43f61bd0bdc4f01f40be83e4104000080be13909aa0c505bd2a5133089e3d81b30bc84d01f20bb03f40fc0000804633839a48c2859428d129085a3b91a90b844d21e60b383f410a00007fceb37b9a1cc1e5a229292988623b71a00b4048e1d50ab83a40d600007f55b3889a64c5a5af29e132089a3db1b50b8c4e21f00b883ec10600007edc938d1a9cc6c5c02a393208aa3db1b00b8c4c21e90b783d40ec00007e63d38a9a64c585b129812d08823c41a70b604b61e10b603bc0ea00007dea238a1a64c465a929992f48923c61ad8ba04da1e60b083800ea00007d6f53971b18ca25d82b0136c8b43df1b20ba44da1f10b603cc0f200007cf7f37919f8c1858f28e927c85c3bc1a50af44981e00b683dc0ec00007c7cf39a9af0c805c72a4132889e3d41a78b784c21eb0b903b80d200007c04b3869a74c465b229792dc86c3c11ad0b604ca1e20b583fc0f600007b8ce3899a90c545b729c93008863cf1a98b5449c1ce0b083980e200007b13f3891aa8c645bb29d93308aa3df1af0b884c21e50b483a410200007a9a83921a94c545b429812f48923c31a70b584a61d80ad83ac0d600007a20f3901a88c5a5b429e132c8ac3d11b60be84e81fd0c2842c114000079a7c3921abcc705b229e131088c3d11aa0b604aa1e20ae83a80e80000792f73881a74c605ae29a92f88903cc1ac0b644c41e50bb03900d6000078b643931a84c545ab29a931089e3cf1ad0b844be1dc0b303c00e60000783c53939ab0c5e5b829c12f48943cd1a78b4049c1de0b303bc0e8000077c283909a8cc545ab29792d08743c41a08b284b61e70b783bc0e200007748d3901a88c5c5b229b13008923d01aa8b5c4b21db0b183d80e4000076cff3889a54c385a729612a889c3cc1ae0b784ca1e60b403d01040000765783829a60c3c5a029392a88683b519c8af84a41ca0ac03780da000075dd739a1ad0c6a5c42a993888b43e71b88be44fa2050bf03e80fc0000756383971ad8c805b52a1130888c3d11ae0b684c61e70b383900e6000074e9d3919ae4c8a5ca2a813508c43e81b78ba04d41f30b803e80e60000746ed3981ac8c765b029b92fc8883c61a30b144a61d70b403b80dc000073f5238e1aa4c5e5b129912d88863c51a50b404c01e40b503f01080000737a439c1ae8c945d12a6134089c3e11b90bf44ea1ee0bb03a80ea0000730023929ae0c645b429792ec8723c31a68b744ce1eb0b083940ee00007285e3951aa4c665af2a1931489c3e21ae8bb44de1eb0bc03fc0fc0000720903aa1b4ccbc5e22b313e08fc3fa1bf8be84f61fe0c183f80fc0000718f93931accc765b929912fc8863cc1ac8b604c01e80b283c41080000711573909aa4c5e5b329713008823c51a60b3c49c1c90aa83740d40000709c638a9a7cc4a5b229992dc87c3c71a70b544ae1e80b783e01120000702193969abcc6e5b529f12f88763bd1a78b5c4c41e60b703b40ec00006fa513a89b48ca45ce2ae93a48c63e61b68ba84e01ea0ba03dc0fe00006f2ba38c9a80c465a229512bc8843ca1aa0b644c81e60b703dc0f000006eb2438c1a84c445ad29c92f48943cf1ae8b984d41f10b983c40fa00006e3863979ae0c825c32a6134c8c03ed1bb8bcc4e81f10bc03e810a00006dbd339e9af0c845c32a793448a23ea1b98bdc4e81eb0b483e40f600006d4263989ac8c745c22a6135c8a43cc1aa0b744c61e70bc03ec0ea00006cc873911aacc685ad2a093348943c21aa0b544b61e20b603b00e800006c4cd39e1afcc7a5d42ad935c8a83d61aa8b8c4d21eb0b683f410800006bd323921ac8c5e5b42a1931c8ae3e01b00b9c4d21e90be83f010200006b59a38a9a74c485a829992d08743c71a70b6c4ca1f10ba03d80ec00006aded39a9ad4c705c12a793488b43e21b00b804de1ec0b983c80fa00006a68137a1a18c2459528b12848563b719e8b404c41e40b183900ec000069ee53909a98c485b129b92c088a3cc1a78b6c4ca1e90b703ec0fe0000697233a21b1cc8a5cd2a893508963e01b68bbc4fc2040c48400108000068f543a61b14ca65d72b093888d03e71af8b744d61eb0bc03e00f20000687a439e9ae0c785c52a193048823ca1a38b604b81e70b903b00e600006800f38c1a38c3e5a429092c08663b419d8b344a61dd0b603b00ee0000678663971ac4c625aa29492a08683c41a48b3c4ae1ea0b883d80f20000670ab3a39b2cc9c5ce2a893448c23d91b00ba84f81f00b783b00f600006690a3951ac0c5a5b529c93048983d41a90b5c4be1e80b703d40f000006615239d1b00c785c92a713488a03c91a88b604c61e20b203780ec0000659ad3971adcc7c5b92a092ec8783cd1aa0b544ca1f40bd03c80f200006520a38b1a84c625bb29e12e488a3c61ae0bcc4fa2070c103fc0fa000064a5439d9afcc8a5c32aa93488a63ce1a38b444b41d70b403c81080000642af3991aa0c4c5a529c930c8723ca1a50b644c81f00b903d4104000063b0039a9b04c7a5c62a593588b43e71b58ba84e61f20bd04000fe0000633283b19b8ccd45ea2b513b88dc3f21b50b9c4de1f30ba83e40f4000)) else (if i < 6 then (if i < 5 then 0x9f3d13851a40c1c5aa29b12cc8583b219d8b384b61eb0b983cc0f000009ec573801a1cc1e58d28b126c84e3b019b0b044a61d60b203ac0ea00009e4fc37219e0c0a59028a92588503b619f8b3049e1e40b103940e000009dd783879a30c1a59a28f12788483aa1970ad848e1d50b403c00ee00009d60937599e0c0258d28d92ac8763c11a50b5c4cc1e80bd03f80fc00009ce8938d1a74c4e5b529712cc8763c71a68b604c41e50b9840810200009c70f3801a0cc1e59f29512ac8783c71a48b704ce1e00b603d011000009bfa337999d8c1e59329412ac8763c51a80b344be1eb0b783e010e00009b80438f9a60c3a5a529412c88603b519e8b1c4c21e40bd03f010e00009b09b3779a00c2659328b92a88563af19e8b344941cb0aa83ac0e200009a9193839a30c2c5a929912f88803c51aa8b3c4aa1d60b283c40f200009a1a137f9a38c2059028e92b886c3c71a88b404b81e40b103bc0f4000099a3d37499d4c0859529492c885c3ad1a00b1c4a21ce0ae83980e60000992d837799f0c0a59128a92948683ba1a08b144981df0b303a40ea000098b7237819dcc0058e290128084e3ac19a0ae848a1d00b083ac0f20000983ed3851a6cc3c59829712c88703bf1a50b484b01db0ae837c0d0000097c6737f9a38c2859629392b08703b81a28b504c41f60bb83ec0fa0000974f43851a48c4459a29112948543ac19d8b0c4aa1dd0b503cc0f0000096d6f3859a60c405a229592d087a3c91ae8bac4c21ee0be83e80f20000965e438f9aa0c565b829e93188a23da1af8b804ce1f00b683c00f0000095e5d38a1a40c285a329012ac8823cf1ac0b784b81e90b583e01000000956e23819a44c3659a28a929084a3b819e8b0c4841d40ad83900e0000094f5638d9a78c4e5bb2a2130488e3c41a78b2c4b01d70b183bc0e80000947f037c19fcc0a58828d12a48643c41a90b844b81e00ae83c80f400009406438d1a88c4a5a829792a08683c21a28b484c01e50b603ac0f40000938f637919ecc1a58f28c92b48763ca1a28b2c4ae1da0ae83b80ea0000931ae367995cbd257827d120880639018e0a9045c1c10a303500cc000092a123919ac8c5c5b429c130889a3c91a70b2c4ae1e20b283c40fc0000922b337a19f0c0a583289927c8703c31a68b244b21de0b003a40f6000091b103961ab4c685b82a4133c8b03d51a98b8c4be1ed0b683d40fe0000913a337699dcc1459a29412a086a3b719b0b2c4b01d00b103a40ee000090c2637e1a34c0e58628a12748583c019f8b244b41f30b583bc1060000904b737d19ecc1659429392a48703c71a88b6c4bc1d10ae839c0fc00008fd543789998c00584287129484a3a81998afc4941d70ae03bc0fa00008f59d39a9ac8c585bb2a713688b83e91b90bbc4f01fb0c1040810c00008ee303819a30c2259229392cc8763be1a40b384ca1ed0b303c40f800008e69b38f9a98c465b129912d08703bc1a88b3c4b01df0b403ac0e800008df2c37899dcc04587284922881a39e1960af04961d40ac037c0ce00008d7833931aa8c6a5b329a92d48663bb1a60b744da1f60b983e80f600008d0023889a94c4c5b329c93008983d91af0b944cc1e50b483cc0f600008c8643949ad8c685bb2a413288a23d91b58be44ea2000c1840c10800008c0e23829a24c325ab29812f48883d31ac0b484a01df0b583e40f600008b94538f1ab4c6a5ba29f13408a83d61aa8b644c81e40b503e40f600008b1a738e1ab0c685b829e13288aa3dc1ad8b7c4d41f90bd03d810400008aa233831a4cc2459929192d487e3cd1a78b704bc1e60b483ac0e800008a2c737019b0bfc58a28e928084a3b419d0b344a01e40b603c80f0000089b4b3831a28c1a59728e12988683c619f8b1c4a81dd0b283a80de0000893ce37d1a04c14596284925883c3ab19b0ae44801ca0ac03c40ee000088c353911ab8c645b329812f08823ba1a28b284a01d70b183c80e60000884a738c9a88c585ab29d93008843c71a60b684cc1e80b283cc0fa000087d2138a1a58c505b929e92e087e3c51a48b444a21db0b3038c0dc0000875a03819a5cc365a929992f48883cd1ad0b904cc1e40b283cc0f8000086e0638c9aa0c425ad29f930089e3dd1b00b9c4de1ed0bb03d00ea00008667838a9a58c3e5a8297930888c3d31ad8b744ba1d80ad03a40e8000085ee03919ad0c725bf29b930c89e3d01a88b584b21d10af03c00ea00008575338c1aa8c685be2a4136c8ca3e31ab8b5c4c61e90b383d00f6000084ff537119a4bf058228512388463a91978b144aa1d60ae83800e600008485c38f9aa8c7c5c62a193508bc3e41b30b904e01ee0b683b00e80000840dc3889a4cc3259c28a12a08643bb1a20b544c01ea0b703c00ec00008396e37d1a10c1859f28e929085e3b419e8b304981d40ad038c0f40000831cf3901a74c4c5b329c92f088a3c21a50b404ba1e80b483d80e6000082a4438e1aacc6a5bf2a293048803ca1a78b5c4c81ec0b803d81020000822c93831a2cc2859e29612c48683c01a10b0047c1d20b003b40f6000081b313941a98c565ac29e932088a3c91a00b404aa1de0ab83840da000 else 0xbce0737d1a34c3059f29812c08603b41970b204a81dd0b503ec0ee0000bc6c036f19ccbfe58728612788583b519b8afc4901db0b083a40fc0000bbf7136a996cbcc57327f925082e39f1970ad447a1cc0aa83800e40000bb81137419d4be0579280924882639c1990ab446a1b50a703680e80000bb09a3821a24c3c5a029492e88803d01ab0b844cc1de0b683a80ea0000ba94d36b99c8bfa59129192c48843d31b08b8c4d61ed0ba83d80f20000ba1cb3831a0cc1058928992548503b619f8b244ae1e30b583ec0ee0000b9a703719990bec58628b126085a3b219b8aec4881d30ae83cc0f80000b92dd38e1a94c665c629d12f087c3c81aa8b644b61f00b683c80e60000b8b9036b9998be2581283925885c3b919f0b284a01de0b003880f20000b842b37d99e0c245a029412d48823d01a40b304b61e40b683d80f80000b7ccf36f1980bcc56727f122c82a39c1910ab84621be0a383740e60000b756f37119bcbf458327e92208303a21970ae44821d00b183940e40000b6e1136c9988bcc573284123483a3a21968ae84961d70ac83840e00000b66b737419c0bfc58b28612788503aa1998ad448a1ca0ac03a40f20000b5f5037799fcc245a029212748643b419c0b144a81de0b283880ea0000b57f736f199cc0459529212c48483a919c8af84821d80a883880fe0000b509c37019d4bfe59328e92a48563b81a70b404cc1e80b503b00ee0000b494b36c9998bc857227e921481e3a61968adc4981d50ab83940de0000b41e537619e0c0459329092a08543b11a00b384b41d80b583f01020000b3a633871a78c425a129212ac8683c41a60b404aa1dc0b483a80f80000b3323366192cbac56127291c47ec3891868a704481b30a303440d40000b2ba03849a70c485ae29c92dc8743c11a68b784c41ee0b603f41020000b243737a99f4c1a59d29292a48643b119b8b1049c1df0b203b80ee0000b1cba3811a1cc1858e28d129c85a3af19c0b0c48c1d40af03b00e60000b156b36c9978bd456e27c922482c3a51998af84921e10b483bc0e80000b0e1137399b4bea57d286927483a3a91988ae44901c50a783b00f60000b06923871a64c2259c29792dc87e3cc1ae0b7c4d61e70b803e40fe0000aff3837799b8c0858f28a124483a3a01948ac44821c70af03700dc0000af7c037e99e8c0c587284125c8423aa19a0abc4821cc0ad83ac0fc0000af0613799a0cc0c59528d12908503b11998b104981de0af03ac0e00000ae8f337a99d8bd657e281120881a3a31950abc4761c70ac03a40ce0000ae18d37399bcbf057d283924c83439c1960ac04841c20a983980e20000ada4036a9988bba56427691d880e3a51980ae84801d40ab838c0d80000ad2eb36e9988bc458028592308263971910ad04741d30ac038c0e60000acb6138b1a70c3459f29412bc87a3bb19c0b1c4981de0b203c80ea0000ac3ce3909a88c565b129b130889a3cf1ab0b604981d70b083c80f60000abc5d37c1a1cc165a129812c48603b41a08b204961db0b403b80f60000ab4f037c99e8bf4586285127485c3b419e0b144a21de0ae83cc0f60000aad9f37519c0be257b284125082c39c1998ac84761cf0ae83ac0e60000aa6153861a5cc2459b29312dc8723c11a68b5849e1d50b203b00e80000a9eb837119b4be857f28b12888503ae1a18b3c4c01e40b503e81080000a974237f9a28c1a59f29212948803c319d0b104961d70af03b80f80000a8fbc3891a64c485a529192a08723be1a80b504b21dc0b603d410a0000a884b37d1a38c2c5a029492c487a3c11a68b304b81e50b603d00fe0000a80c03881a54c445ab2a113408983d41b00b784ba1ea0b503ec1060000a795b37799dcc1a59629512d486c3b619d8b184b01db0af03a80e20000a71e337f1a0cc105a529d930c88e3c91a68b804ba1e60b983dc0fc0000a6a9137419c4bd456d280125c8443a11970adc4841db0b083a80e20000a63123801a2cc2859c297930489a3cc1ac8b684d61e90b703dc1080000a5ba537a19f4c18588287927084a3af1970b0c4a41e00b983b80f00000a543137c99ecc0857e284924083e3b019b0b044ae1de0b783c80f20000a4ce636c1970be0584286127884e3ac19c0b144921e10ab83900f60000a457437f9a24c365a229312d487e3d31ae0b5c4be1f20b783d80fe0000a3dff37b19f8c2659f29312e48663b71a48b384b41e40b583dc0fe0000a369037d9a2cc3259929292c486c3be1a48b6c4be1f30b803cc0f00000a2f213799a00c1059b29612e08743b91a38b2c4ba1de0b403a80f20000a27953871a44c3c59d29292a885a3c01a70b644c01e20b2039c0e80000a202f37719ccbe8585285926483c3af1998afc48c1d00af83a01000000a18db36f19e0c0658a28c926885a3b219f0af049e1d40af83b80f20000a116d37f19f4c2459c29592c48743bd1a68b5049a1d90ae039c0ea0000a0a0e37799e8c0657d28792688443b71a20b3c4b21dd0b803dc0ea0000a02a937519acbea58328a126884e3ad1a00b184981d40b683a80fe00009fb5736a9960bc056b28012448263941908ae448a1d10af03a40f2000) else (if i < 7 then 0xda3553639988bf857c281922081839518b0a884741c30aa03600e40000d9bfc36e99c8bee58328b127484a3a91978afc49e1dd0b503c00de0000d94b73699988bd457a28a12648343a21978b144a61d50b183dc0ee0000d8d4937999d4bee58928b92708463a719b0adc4821d60b183d00f20000d860136e1994be857428112088163a119c0af449c1d90b483c00ee0000d7e9637599c4be057d281926884e3b519f8b504a41d00ad83940ea0000d773737199a8bf8585285126484c3b51a30b344a81e20b903fc0fc0000d6fff36a196cbf858328792408463a719b0b0c4941d80b183d81040000d68cb360993cbaa56727b12108223a21950acc4881d20a583780f80000d6182365996cbd257927a120c8263991928aa046e1ca0b003940dc0000d5a3e3631990be656f281926084e3b51a18b1c4a01d30ae83ac1060000d52ff366995cbc057128192088243a419c0b084b61e30b983d00fa0000d4bb336d1994bea57b28792588463b019c8b1048a1d00b403c810a0000d444c37199c4bfc57f28912688483b41a20b244b01dc0b603e81040000d3cfc36f19a0bf258429092c48803c31a20b3c4a01e40b383c81000000d35ad36e9984bc6568281927884a3b519e8b184b81da0b483c00da0000d2e6a3639958bc456627a920c8283b319c0af049a1db0ac03940ea0000d271d36f99a4be4585288926c8443b21a00af048e1de0b203a80da0000d1fb137b1a20c2059b29292b48683bf1a40b544b81e70b403e81080000d186e36a1960bba56027b12108123991950af448a1ce0b183bc0ee0000d11113791a00c0c59028f12748503b31a08b284a21d90b083ac0d40000d09de362194cbce57228011f481038f18c8ab445e1b50a703880e80000d02b735598dcba455c27091c07e63781848a3c44c1ae0a183400d20000cfb713679968bba56a27811e081639b1930a944601c20aa03840dc0000cf3ff3821a48c2859728f12c086a3c91aa0b6c4ac1ec0bb83d80fe0000cecbd3691968bae56e27c12088203ab1978b304a41e30b183d00fa0000ce57f36c997cbcc57c280922882c3a31960ac44801cd0ac03940ec0000cde3f3661958bba56b27f121083439b1948ae44881cd0b083980f20000cd7223589908b9c56127311c47e037d1870a8445e1bf0aa83680e00000ccfb437719ecbfe587286124483a3b119a0b0c49e1d50af03800e00000cc84537c9a00c2059d28e92a48543b619d8b104941e10b403d010a0000cc10c36b99a4bd0576281922081e39b1928ab84661cb0aa83880dc0000cb9a237699c8bf8589288925083a3aa19e8b044881d80aa03840de0000cb23d37899e4c0858c28b925c8443b01908ad048e1d40ab03680de0000caac737519bcbee57327f124483a3ac19e8b084941cd0b183bc0ec0000ca37137419bcbfe581281921c81c39a1958ac447a1d30ab83900e40000c9c1d36c99b0bf458a289126085e3b71a20b184aa1e60b503b80ea0000c94ba37819f0c1259728b127c8783bf1a40b3049e1d70b283a00ec0000c8d5c37599c8c0858528a12688483a719a8af84821db0b0039c0e00000c862c3649940bba57627d120880e3931918ac046e1b50a103440ce0000c7eb93831a18c2a5a129992c486a3bd1a10b0048a1d10b083800e00000c777e363998cbd858728d12948543b219f8b5c4ae1e80b783b00f60000c702b36c99b8bf459629112988583af19d8b2c4aa1da0b483d40fe0000c68dc36e19b0bee580289127c85a3b419d8b484b21db0b503b80f20000c617b37119acbe057e281124c83a3a41998ae44821cd0af83bc0f40000c59ee3881a64c5c5ba2a293588a03d11a98b304ac1de0b0839c0dc0000c52b4360193cb96561278921881c39e1960ad04921d60b583c40f40000c4b2d3891a80c625a829692b48703ba1a38b4049e1e20b883cc0f20000c43c737b19d0c0459629192c48783be1a40b484b21e50b583ec10c0000c3c7e36d9998be257a28692888563b51a08b484c41f60b803dc0fc0000c352537399b4bf458128c927485039e1968ab047c1c40aa83800c20000c2dcc36e99b0be858828512448343a11970b144a41d60b003bc0fe0000c266b37999f8c1659629012a487a3d01a78b7c4c21e80b503bc0e00000c1f0837199d4c1c59528e12d88683c61a70b584b61e20b583cc0f80000c17ca361193cbbc56827d92308423a51978af049c1d80b583c41020000c106737419f4c2459e29492c48643b519a0aec4921d70b083980e80000c09143701980be857b280925c83c3a619a8b104b21e10b803c00ee0000c01bd36c19a4bde57f288127086a3bc1a38b3c4b61e10b683e80f20000bfa6437419f0c0657f28792a486a3be1a80b6c4c61e30b883ec0f20000bf2f637999f4c0c58328812848503b619d8b604d41df0af83900e80000beb9937219a8bee580282927084e3a819a0afc49a1ca0a983980ea0000be4223819a24c2e5a9292929885e3b31a80b604c01f20b803dc0f80000bdce13609944bb857027411e08023941970aec4841cf0b103a40fa0000bd57a37899f4c0c59328e92b885e3bd1a70b684ce1e90b503cc0f2000 else (if i < 8 then 0xf74933691974bd4574284926c8463a81960acc4821d20aa83840ec0000f6d673589938bae56527391cc7ee38e18f8aa04821d00ad03980f00000f661b366993cbac56527991fc80a38f1908aac4621c30aa038c0e60000f5ed4365997cbd057427d120882e3a01990b084941d30b1039c0e80000f5789369997cbd458328d926c8563b21968ac04861d00b003a80de0000f503137599dcc0458f28d12ac8663b91a38b344a81dc0b383b00fc0000f48e536c99b0c0658b286925c83c3b11a08b244aa1e30b483ac1040000f418b37499c0bf0583286924483a3a41978ac84801d20ad03900d20000f3a3d37019a8be658b285924c83a3b119f0b2849e1d80b383d81060000f332835218bcb9655926e91b87e838918b8aa44621bd0a7036c0c80000f2bfe35798d0b7e54a26d11847da37b1870a5c4541bc0a883640dc0000f24e63501894b6a54126a91b07de38318c8a584681d00b083b40f40000f1d973699988bce576283122882039b1938ac44761d40a9838c0f00000f165736a1980bd857e286923882c39e1930ad84901d30af83b80fa0000f0f1a3691978bc856f285121c82c3a91990aec4781cd0ab83800de0000f07bb37199c0bdc58028c92608403a91998b2449e1dd0af83b00e00000f006c36e99a4bd856727b921c8223aa1980b0849c1d10ac03c01020000ef95934f18b0b7654726a919c7fa38d1870a9c4641b90a6038c0ec0000ef20137519e4bfc588289925082839a1938ad448a1d10b0038c0ea0000eeac835e1940bbc57c27d920481a3991948ac44801cd0aa03840e40000ee37b36d996cbde582285927084c3b219b0b084ae1de0b583cc0f40000edc5435a993cbbe562275120082639618f8ac44841d60ae83a80ec0000ed4ff36d9998be858028a12708423a71988b0c4a81df0b783c40f40000ecdbc3679958bbe56e28192348363a61978af848c1d80b303f40f80000ec69a35518ccb9455127111c480438a18b8a8c4661bb0a403600cc0000ebf4d37319fcc0859028f92908483af19b0b084901cb0ae03a40f00000eb82734f98dcb9855c27011bc80e38a1890a984661bf0a7839c0d40000eb0ec362196cbb656727511f880c3931920ae04a41d10ae03d80fc0000ea9aa36e19a0be0578283124883e3a319b8b444c01f20b803e80f60000ea27635e993cbb4563275120081439118d0ab045c1c30a703700dc0000e9b333669928ba056327391e080e3a31918ab846c1c50ae037c0da0000e93c137799c8bfa580282123c8343ac19c8b044a61d50af838c0f00000e8c7836c998cbe657c283124c8403ad1970ae04841d10b783940e40000e854835c190cb9a55a27311ac7ee38618e0ac44741c10a703780c80000e7de436c998cbe057427e920c8263a21990acc4781c60a603a00de0000e76aa35e18f8ba856f27b923083239c1958ad84821d30ad037c0f00000e6f8b35e1928b9055d27811ec81a3961948af84901d40b403700de0000e682e36f199cbfa586286126483a3a719b8ae04861ca0aa03840ee0000e60e03689980bd257527e121c8243a419b0afc48e1d00ab83980ea0000e599c3679980bc256a27e12008283a319c8b1048a1d10b783c80f40000e525936d99a4bec58128992748543c01a50b684ba1d80ae83b40fc0000e4b1b3671978bec57a280923c8443aa19a0b104a81e10b383c00fa0000e43e83621944bce56c27c92248203a318f8afc48c1cc0ae83b80ea0000e3c8a37619d8c1e59c29192bc8703c51a38b444b01e50b103940f80000e351c37c9a00c2259b29812e087e3d11b10bc44ee1f80ba03a40e60000e2dd136b19a4bde57b283124483039f1988ac847a1d20b003e81040000e268f366995cbc856727a11fc82e39e1970ae44901d50b503a40e00000e1f2237b19fcc1258928a125884a3b619d0b3849e1e40b403e00fe0000e17d9374199cbe457f285926c82c3aa19c0ae04781cb0a783a80f40000e108d36a1998be257928392448383aa1970ad84801d30b303c80f00000e096f35f1930baa56427b121c82e39d1960af848e1d00ad03880fc0000e022636a9998bda578281123c83c3ae19f0b584a61d50b283b80f00000dfacd37599b0bdc588289129883e3bc1a58b684a41d30aa83840e40000df36c37899e8c0459228c928c8683c61a48b404a21d90b883e00f20000dec3d363991cbba56c27511b88103981928ab047a1cc0a983a80e60000de4e537519d4c0a58b28712748443b019a0b104961d70b403dc1040000dddb635f9920bb456d27d120080a39718b8adc48c1d50b483a40ea0000dd692358990cbac56427611f880e3981958ab046a1c30ae03c80fa0000dcf543649984bd856b281924883e3a619b0b244aa1e20b303e40ec0000dc7ef3799a0cc1a58c28a92a88703bb19e0b1448c1d50b103c00f60000dc09c3699998be457528092288283a71918ac048e1db0ad03a00da0000db93f37399d0bfc584282924481c39118f8ad047a1d30ad03a00e40000db1fc3679978bc056827c123082a39a1978ab84641c90b183b00f40000daa933771a0cbfe58228092348283941960ab84821d50b203a40e6000 else 0x1142cb35d98f8b9455627311ac7ee37b1850a5c4681c10a6036c0ca000113bb435298c4b7655426f11a47fa39b1968adc49c1d80b103a00e40001134723649950bc657527c91fc8043941910ad44761c80ab03980dc000112d5035b9944bba57527d12408203a51988adc48e1d20af83900f200011260836a1960bc456b27d121c82e3b019f0b204be1e00b183c00e8000111eee35218c0b8454f27111907f637b1868a804521b60a683780da00011179637499e0c0458d284121c83839a1928ae04821d10ac83980ee00011105835e9914b8e55926e91a47e437f1858a6c45e1bb0a683600c800011092635b1900b9e55a27391c880238d18d0a784641c20ae83740e40001101ca37719e4bfe58828512508323a71948ab84821c00a8036c0d200010fa9a35c1904b9e55e27511b48023891890a8046c1ca0ae03b00e200010f37135c1904ba055c27b123c8323a31940ae84981d90b183b00e000010ec0537a19e8c0257d28292288383aa1978b1c4921dc0b183980ee00010e4c53641920bbc56227392008143911908a9046e1c60a6035c0da00010dd9435f192cbb256127391d08163981960afc4a01db0b583ac0f600010d65b3619940b9a55d27991e880a39318c0a7c45e1c60aa83940ec00010cf4e34b9894b8054226d11807e03811868a6c45c1c30a683900d600010c83135318f8b8a55b27611ec81439c1948ab44781d50af03b80ec00010c118359990cba255e27891f881239018e0ab04761ca0ad037c0d000010b9e435c191cbac56e27f92408263a11958ad846a1bb0a803900e400010b2a4367995cbc657527d120881e3971938ab046a1b709d83440c800010ab7435f192cbb056727d922082a3a219a0afc4941ce0ac03900dc00010a42c36c99a0bec578283121882039618f8ac44921d30a9836c0ce000109cee366197cbd2572281120481e3981928a9c4741cc0b303cc0f200010957a37719e0bdc57d28592588403a11958ad44a01d60b083c00ee000108e4c35e1940bca57028091f882239d1950af84801d20af83940e800010871e35d18f8b9a55726f91e48123921948ae848e1cc0a983940e2000107ff03639914b9c55827491e081439a1980b104961d50af03d40f00001078b7362194cbd857c28592588563b61a10b0848e1cf0aa03940e400010717137019b8c00586287927882239d1968ae44961d30ab03ac0e6000106a3b365191cbb257027a120882a39d1930ad04741c40a683840ec0001062eb36d1980bde57427d122c8243931930ae848c1ca0ae83a80e4000105bc035a1904b9856127111cc8163a31958ae44961ce0ac03b00ec0001054843661978bae570280120c8183991978aec4a01dc0b303b80f4000104d5b3579908bac55927091b47f038518b0a8844c1b80a583740e20001045f337919e0bfe58c28d128c8523b31a00b2c4ac1e30b603d80f0000103eb53669934bb656927391bc80a39919b8af84901d90b103c80e80001037a435318c4b8254d27191ec82a3961958ab04861d20ab03940e400010307b35f9920baa56227291fc82c3a119a0adc48c1cb0b003c40e000010292237519d4bfc57b27d925483a3aa19e8b284981d10af03980fe00010220735698c8b6e54e26f11cc7fc3891978ac847e1c60b0038c0ea000101aaa36e99a0bf658e28d127481e39d1990af84921d60ac83b40fe00010137f3621914bb0562278920c81a38e1918aa84581cd0a883640ce000100c4435d191cbb456a27b91d881c3971900ae448c1d30ab83880d00001005443421854b6654026511807d03771868a6c4521bf0a8837c0e60000ffdf836f99a4bda576282123083c3ac19d0adc49e1d20ae03800e20000ff6b336c99b0bfe58528892a08523b019b8b084941d10b383c80e20000fef86361194cbc457227f123480a38d18f0ab04661c50a7838c0e80000fe81d37d19e0c0258c28d129486e3b319a8b144a41e80b783c80f20000fe0f83599918bb056227311cc81639b19a8adc47c1d40ae03980f00000fd9da3589910bae569283123082639c1898ab446c1bf0a9837c0cc0000fd2903671970bd056f27c122482c39f1930ad84921db0b383d80f40000fcb563651978bce57b28512408403b11a48b604b01e00b203d40f80000fc43e34e1870b6c542265918c80238a18a0a9446a1b90a303780de0000fbcfa36a1988bc656e27c920882c39d1910ad04821c60ad03880ec0000fb5c33641960bce56c27e122082e3a21950ae84861cc0b083a80f80000fae923611954bb856827a11e880439218f0a984701bd09e83500dc0000fa74736d99acbd8587289125083a3b319a8b2c4901d00ac838c0de0000fa0273561908bac55927811d07fc38c1870ab04821cf0ab837c0e00000f98c137919e0c0258828c129c8603b71a28b384981e40b703f80fa0000f915837799c4bfe582288927884a3b519d8b204ac1e00b683d00e60000f8a3735798ecba256027811dc80038d1898a944741c10ac838c0ce0000f83013659958bb656427f11ec81639e1978aec4941e00b183d41000000f7bca3661958bc4572281122c8263a819a8b204901c50ab83840ea000)))) else (if i < 13 then (if i < 11 then (if i < 10 then 0x130d1c34d18a0b6653c267116c7d637d18b8aac45c1b90a783940ea0001305d636b197cbce57328192248123961948b0c4ac1da0b203900da00012fec634d18acb5453826291407cc37e1860a5045c1c50ab039c0ea00012f7c43489894b5654226511887f838318b0a904621c30ad83a40f600012f0af35398d0b8a55727191dc80038d1918ad04861ce0a883a00de00012e9a335118d0b6e53d26491507cc37918a0a9046e1d00b083ac0e200012e29434b9894b6654526991a48123931900ab445a1b70a483740d600012db523669944bb456027511c07ec38e1920aa44881cd0ae837c0d000012d40e367197cbc055b27611dc81439a1970b084a01e40b803d010800012cce235918dcb9455227311dc7fa3991938ac84741cb0ae03880e800012c5b735318c4b7a55127191c480438f18f0ae44941d10ad83a80f800012be793631920bca56f28012188203a41980adc46e1b80a983900e000012b76134d98d4b7a55027291c87f238518d8aac4621c00a883980e600012b0333601928b8e55d27391c080238d1868a704481ba0aa83740d200012a92634c18a8b5c53d26091607c237e1850a604361bd0ad83a40f000012a1fc35618dcb8c55227091d47e83871890a7443c1b80aa037c0dc000129ad635a98f4ba256827511f480838718c0a9c45e1c30a703680d00001293ad35f98ecb8654e26c91d881439518e8a604421a909f032c0ae000128c8335698d4baa563274920082e3a01978b1449c1d00af83b00ee00012856a35818f8b7e54a269919c7fa3931948ac44861d00b103a80f2000127e3f35f1920ba655b27492087fa38918b8a784541c00a783c00f40001277203581914b8e55227011d881039a1958aec4761cf0af83a80ec00012700834a1884b6653c26911807e038018b8a9445e1b90a403880cc0001268af37599dcbee58228c126c8503af1a20b304c21db0af83900ce00012619135518d0b9a55126f91ac7e83781838aac4741d30ac83a40ec000125a7f35118f4b8656027a91e88263a11950af04a01de0ac03980ee00012534c35f993cbbc56e27e91f080038a18c8ac84901d60b383880d0000124c2235c991cb9855127191ac7fa38a1908aa04721cb0ab03840f400012450b35318e4ba056827991e480e39918e8ab847a1d70b183c40f0000123ddd3619940bba56727491e481039818f8ab44741c90ae03bc0fa00012369236d1980bc656c27d11f080a38b18f0ae848c1d40b003c40f6000122f93346185cb4c54226811707d837317f8a3043a1b70a483700ec00012285c365997cbde57c282123c83c3aa19b8b144a41dc0b103b80ec00012212435c9924bb456627711e88183931918abc4781c60a983680e80001219dd3679960bc4577285123c8283a619f0b244a21d90b503d00f00001212a935a9928ba056627a92048183941900ac84641c30ac03a40dc000120b7635f194cba656327a12108223991940adc4861d30ab03ac0ea00012046634e98bcb8254926711887fc3811860a644541be0a703880d800011fd663481870b4a53d26591407be36a17c8a3c4481b30a8836c0e600011f626360993cba456727d12208363a519d0b144a61d70af83880d800011eef835b1924bc456b28612788523b71a20b2049e1db0b403cc0ee00011e7d635998dcb8c55727291dc81439118e8ac44781c70aa83780e400011e0db3439840b3e53326091487e238418c0a7045a1bf0a903880d000011d9a03681960bc257828492448383a41938ac448c1cf0ab036c0e200011d25a362192cbac56327d922c8423a91958ae047a1db0b003bc0f800011cb1a3671944bc857e288925883a39d1930ac44861cc0a983800f800011c3be3799a04c1659528992588423a01938a9048c1d40b183c40e600011bc953589908b9254c27311e87fc39018c0ac847a1cd0aa03800d200011b5843569900baa56227b11e080a38c18a8a804701c50af839c0ee00011ae5a360994cbc656d280124c83c3a01958ad047e1ca0b003b00e000011a7283639968bbc56e27f12448483b519b0b184a61db0b483c80ea00011a02f3421808b2e52d26811687d83831810a4443e1ad0a2835c0d60001198f93619944bb856127691e08023921900acc49e1d90b303d00fa0001191ff3481888b6e54726b11787de3841840a644501b60a1835c0d8000118abd3639970bc856d280922c8383aa1998b0448c1d60ad83a80de00011835437799fcc14595291129085e3bd1a08b1c4961ce0ab83980ee000117c17364192cb9456027b11f880638e18f0aa446a1bf0a6038c0dc0001174fa35818e8baa55d27391b08103911880a7c4701c40a703880e8000116dbb366995cbcc56f283123c83639b1900a8c4521bb0a803700d20001166a934c18c4b7254527111a47ee38418b8a7045a1c50aa03780d6000115f673681968bf4585285923c8263ac19c8b484c21ec0bb03f40ec00011582b3629944bb656327911dc80038b18c0a9846e1c70a803a40e600011510d35518d4b8855b27c12288263a219c8b104ac1e20b683d00f00001149f635c9914b8e55427111f480a39d1958ae44841cb0ae03b40fc000 else 0x14d52335618d0b9454e27091b881c39a1940acc4681b50a483840d800014cde9360193cba2564279921c8323a21928ad047a1c60ab03a00f400014c6d53589920b9a55827211bc80a3991928ab84801d00ae839c0e400014bfe13451860b4052d260114c7c836c17e0a344521b70a083500ce00014b8d535418f4b9055c27011cc80c38b1958acc4881d10ae838c0ce00014b17f36c99a4bf258328512648543b419d8b2048e1c40ad03b40ec00014aa7b34a186cb56539263916c7d837617c0a2c4481b50a483780d600014a35535418acb6855027991dc7fc3881900ae84881c70a903780dc000149c3535318d0b8655126e91ac7f438b18a0a9846c1b90a703800cc00014951f3559900b9055927011887e637c18e0ab447c1c60ac83740dc000148e0c35298f4b7a54e26d11b88143931900ac447a1c20aa83a00e80001486b437399bcbfa592285927c8503a51998af04901db0b283b80ec000147fa235118e8b7454826c11747d43831868a8c45c1bf0a503540dc0001478a3346186cb7054126911807d037b18a0a744621c00ab03880da00014716b35d9934bb256427c91fc83e3b01a50b384b01ea0b803e4104000146a7c3439864b5c54926d91a47fe39c1948ad448c1d00ad83c80ea00014635e35698f8bac56127711e882c39418d8a784661bd0a983a40fe000145c5d3481880b4e53325f116c7de37a1848a7c45c1b60a283740de00014554135298c4b9e55327b11dc81039218f8a9c46a1bb0a883800da000144e1735a98f4b9055227191b88143981908ae84861d40af03900de0001446df3611948bbc55a27211d08043971938ae047c1cd0ad83a80fc000143fb935418ccb7e54326a11a080439118e0ad048e1cf0ae83a40f60001438b234c1880b5853626d11ac80639218d0ac84721c70a703880e20001431a9348187cb6053a26611887e237c1888a9045c1bb0aa03540d6000142a72363194cbae56d27d91fc8143991950ad447e1cf0ae03b00e000014234f3541920bb255c27811f882038d18a0a7c4581b40a1034c0d8000141c44351188cb7254927311dc80638d18f8acc4881cb0af03dc0fa00014153b35098d4b8055126a11787dc38318e8ac44701b70a4837c0e0000140e1d3559908b7c55427511fc80039018b8a984621c20aa838c0e80001406fb35618f8ba856127591e88083951930ad048a1d20a9837c0d600013ff9837919c0bf858528b128085e3c61aa0b4c4b61e20b783e40f800013f87e35098d4b7654626891a480839018c0ab447a1ca0a003340ba00013f16935418d0b9455627191e481e39818d0a844501b30a183500ce00013ea4435318c0b84555276120482e3a71968ae048c1cc0ab037c0c600013e31335e9928bb856f283120081e39418f8ac44601c20ad83b00e800013dc0e34d9884b5e54626a914c7d03781820a544641c60a9837c0de00013d4c53669934bbe56527a921882e3a51990adc4861d00af03a00ea00013cdba3479894b7054a27111d880a39c1910acc4761c50a403700e400013c6b23489898b5253325c11247b036917c0a204441b80a303680cc00013bfa134b1868b5453826711487ce3741860a604581c70a803880e000013b88435798ecb9856427b12008083991900acc4741c20a703980f600013b1523621934ba255d27291ac7fc38d18e8a9c46a1c00a6835c0d000013aa3835218ecb8255927291f88203a81998af448e1c90ac83b40ee00013a31c35018b4b8c54d27511e08003981948af048c1d30b103880e0000139c0f34b9888b8055026e91d47f83891878a8c45c1c40a8038c0f00001394eb35618f8b8a54f26c118c7ce3791878a704541bf0a203580da000138dfe3401850b58534266917c7ca37317e8a2c4541bf0a483640dc0001386ac36d998cbd4575281923c8203951930aac4681c60aa037c0e8000137f99353188cb78547264115c7da38a18e8aa846e1c70a803880dc00013788835198ccb8455727211e081239918c8a9446e1d00aa03880d00001371583599910bb2560278920c82039a1940ab047e1d40aa03780da000136a3635b1908b9256627591dc80c3941938abc46c1d60af03980e000013630635a18e0b9855b27591dc7f438918b0a984781c40a7837c0e6000135bdf35998e4b9255b26f91c87f837f18c0a8044c1b80a503540d40001354af365194cbc457327a91e48003971908ab84901c90a583840fa000134d6c3669964bc457928512648383ae19d0ae44801ce0ac83a40fa00013465534d98b4b8455127212008323a71968b1c4a41ca0ae03b40e6000133f3235c18d0b9e55f277120881439c1950af049a1d30ac83a00ee000133815352989cb7655626e11b87fe3951968ad447e1c40a9836c0e00001330ce36d99b4be658928a127885c3ac19c0b144a41d90b203c40ea0001329ab3581918ba456727b920082439b1950ad447a1ca0ae03a00f200013227f35a9920b9e55627111bc7e83831888a744621b80a7836c0c8000131b453659974be258228b126483a3aa19a0b0c49a1d90b403c40ec00013142435698e4b9455a27411d880e3901920ad04801ce0a903800e6000) else (if i < 12 then 0x169aa93419834b4053926991a47f63811880a944701c20a503700ee00016939135218f0b9055e274120080c38d1910acc4841c80a903840d8000168c8d345985cb44538262913c7c63751830a584521ba0a183600e600016858035018c0b4453e26c11987ea3961908ac84701d10b403980ec000167e4e35e192cba055c27691f881038d18a8a7c47e1cd0b003a40e80001677463469888b52541260115c7dc37c1838a7044a1b80a603880e200016706d33217acb0250a25410c07923581738a044281b40a083540d800016692f3679988bd457627c92108103ae19f0b1048c1e00b483ac0e000016622834d18c4b6c54526c11a480038918f8ad448c1d20ad03ac0e6000165b0e35a1910b9654f26e919c7f037d1860a604541ab0a383800d40001653d43659950bc0566278120081a3921918ab84761c70a883700d4000164cc534e189cb6e54226991b07e038418a8aac4601b40a383800f20001645bb34d189cb6c53f26a11607cc3791898a884741c00a883740d8000163ec13481888b8254d27291e080a38b1998afc4a01e00b603f40e400016378935e1910b8c55827091c87f238c1930ac44781d90b103ac0d400016308734a9884b6854127491bc8063961910ae84821d20aa03a40fe00016298a34a1878b5253a26911a87ee38618e0ad84901dd0b183c40ec00016227d35198acb7e55027191d48143961928ac446c1c20ac03a40e0000161b5e3589900ba256627611f481c3991900ab447e1cb0a9837c0e60001614283601914baa54e27011c08023841890a844621c90af839c0e0000160d1a35118bcb8655327011a87de38a18e8a9446c1be0af83b40e800016061d3449894b7053926991787de38118c8a944601bb0a3836c0ec00015fee935918e0b9655c27911dc8183a11948ad848a1c90ae03a00f600015f7d635498e4b8654a27011a87e838a18f0ac84701c20a583940ec00015f0a835d1928bb056227a91d07f03841838a904521b80a403640cc00015e9a33481890b5854526b11a87f83811898a8c45c1ba0a403800ee00015e2ab3469890b5053f26491607e237f1810a284541b70a483780d800015db8d35698f0b8c55227311c87fe38f1910ab84781ce0ae03b00e200015d47435118b0b6c54a26e91b87fa3931900ac847c1d70a903940d800015cd3636a1968bba56727d11f88083981928ae04aa1dc0ae83740cc00015c63234e18b4b8054226a91607ca37b1870a8c4501b00a4837c0e400015bf1c359993cbbc56c27d123082c3aa1950aa44641bf0a583540d400015b7ff35398dcb8e556277920481439b1950ad04941d40ae03a40dc00015b0d935d9934baa56a27811e480839318f8ac84801cb0aa83a00d800015a9ab361991cba656727f920081a39718c8aac47a1ca0ac839c0da00015a29c34d188cb5453c26b117c7e037e1880aa044a1b80a603540e0000159b7435618e0b9e55727111b08023901920ac04741c80ac03980e800015947d3411814b34538260110c7ac36c1838a4c44e1bf0a3836c0e4000158d5a358990cba255a26f11e082039418f0ad847c1ce0af03b40de00015865534e18b0b6c55127291d880038e1908ae048c1c70a983840da000157f653409854b42530261913c7be36c17d8a4444a1ba0a4832c0d000015783e35c992cbbe56d282120882039818f0a9c45e1c70a983980de00015712535418b0b7454026c11a47e837d1888abc48c1c80ae83980f0000156a1535198c4b8255226e11987ea38d18e8abc46c1ba0a883640ec0001563183421864b4e531264117c7dc3791880a584521b40a9039c0ea000155c263421854b3a52b25d91587bc37b1888a784581bf0ae83ac0e400015551434f98bcb8054e26d91b47f437b1880a5c4541c10a703640ea000154e0035518dcb8c54826f91b47ee38a18d0a9445c1be0a9836c0d20001546fc34a9874b5a533261117c7d437d1898a9445e1bd0a383680d600015401833f984cb3652d26691807ee3811848a7c4581bf0ae839c0e40001538e33671998bde581285124483c3a119b8af84921db0af83980d40001531be35a18fcb7e54c27091e880638518c8ac847c1c90ad83900de000152ab435118b4b8454726711707d837b1860a6c4561ca0a503740c60001523833639968bd456827d12548463b01a18b104901d20b383b80ea000151c4a35e991cbb456527811ec81639a1960abc4721c70aa83a40ea00015153334c18ccb8855d27591f082439a18d0a884701c20ab838c0e6000150e1335418d8b8054f27011c47fc38c18f0ab44761cb0ae037c0ce0001506f335818d4b8a54e27011d480a3931900aa44621bf0a7837c0f400014ffe234d1894b5254426d11c88063991930aa84761c50a683a40ea00014f8c13539880b6a54226d91c87f838f1850a5444a1b90a8038810200014f1903619934bae56f27791ec7fc39418e8ab847a1cc0b003a80e600014ea613651954bbe572280922c83639e1988afc4a41d60b283d810a00014e34235e9924bb456727b920081639c18f8aa44741c90ad03a00ee00014dc373489888b6c54126c11ac7fc38b18d8ab04741d50af03c40f6000 else 0x185d9735498c4b8455b27611e48083971968ab047e1c60a883980dc00018569f3401824b2451b25710fc7a836b17c0a144421aa0a0835c0da000184f9b34d9894b6254226c11b87e038a1928aac47c1d10ad839c0f000018486635e991cba0566274920080038d18e8aa04701bc0a503740d000018417f33a1844b1c52426211187bc37d1870a4844c1b20a583a40e0000183a553611948bc456b27b922c82639b18e0af04941da0af83b80fa00018338733517c8afc51625691107a23601788a0042a1ad09d03240d4000182c6635598dcba255a27291ac7fa38e1918a8c46e1cd0ae83900e800018255f34b98b0b7054326991587c036917a0a3c4521b40a6034c0da000181e403599934bbc55f27811bc7ee3851908ac847e1cc0a6037c0ca000181762338980cb3a52f25e91287ba3701828a744641c60ad03900e600018108c3381800b3652825b111c79236917e0a484441af0a283880e800018096c35718dcb9054b26f11d08123991978ab447a1c70b603c80e80001802ab32d17b8afa51325c110c7a635f1820a504541c40a983b40e800017fb793629960bd657628612448403a919b8ae848e1d70ad83b40e200017f46935098bcb7c55227311d880c38f18e0a9c46e1bf0a4835c0da00017ed5e34d1890b6a541266116c7b636a17e0a2c43e1b10a283440d400017e6653429850b5e54926e11b47fe38e18f8ab44801cd0ab03780d000017df59346988cb40536265917c7e43791860a6c4581c40aa83dc0ea00017d82b35a98f8b9855c27191b880a38c1898a9046e1b70a283980ea00017d1493371814b1e52425b91187b636f17b0a0c43c1a709903440ce00017ca3e35218a8b7654626611847ee38a18d8a804741c70a803840e400017c3213589940bbe56e27c11dc8143941938acc48e1db0b183b00e000017bc3733b180cb2a51f26091487bc36717a0a3443c1bb0a1036c0d600017b5413491884b6854326691747b236917e8a384541bc0a683b00f400017ae19359993cbae577281924083e3ae19a8af44801cd0a803600e000017a7333439858b4252d26091387bc36817c09f84341a80a483840e200017a00735f9910bae56026f91e481639a18e0ad048c1c10aa83a00e80001798cd3671968bd657d288124483a3ae1980afc4921d50ad03b00f20001791bc34c1894b6854926c11bc7e03791840a904781c80ac83880ea000178ab234e98d4b9a55627291d47ec37d18b8a744681c50a9037c0d00001783c5340187cb4253426311687cc3761838a784541b80a803840ee000177cb73499864b5053b26b11887e03791890aa84841cf0ad83900de00017759c34d98c4b8454926e91907f038218c0a9c45e1bb0a2036c0d0000176e8435418dcb9655027191847fa38718b0aac4781d30ae83d40f000017678a3469864b5852c25d90f87aa3751810a3443219e09a83400d60001760913429868b4c53926591647dc38b1858a7c4741c00a7036c0d40001759763551918bb255f27411d08103981920abc47a1c80a803940dc00017526434d9890b6e54e26d118c7d237e1858a7c43e1b80aa03940dc000174b5335198c8b7a54426a11647d637d1870a944721c10aa036c0dc00017444034c9898b7654c26d11e47f63941928abc47e1d20af03880e2000173d133591904bb8569280921482c39a1978ac04861c50a803800f000017360a3481878b7c55927111947fe3821870a5c4541be0a3038c0ea000172eda35e1950bac56327411dc7fc38c18f8abc46e1c80aa03740da0001727cb34f18c0b8655227591e481439918d0ab04761c00ac03b40e00001720a9359191cbb456b28212308343a919a8ae84781c90ac03a00e80001719a83441808b3a53625d91407ac35e1758a1842e1ad0a103740ec0001712ad3449844b4452b263915c7ac36517d0a544461bc0ac03a00e6000170b9634e18d4b9855327311e87f638c1900ab44741d00b183940e800017048934d9884b5c54326f11c07ee37917e8a4445a1bc0a4837c0da00016fd5935c9908baa56d27d122083a3aa19a0af448c1d60ad83bc10400016f64a34f9898b7e54d26b917c7ee38818b0aa44641c90a903900d800016ef543429884b6253526711ac7fe38118b8aa84661bf0a203740e800016e82a35a190cb9656327a123c83a3b319d8b0849c1d40ac038c0de00016e10035d1918bb456027b120c81439918d8ac047e1c90ad03c010200016da08347188cb4852e26091587b836d17f0a3045e1c30ac83a40e600016d30d3421884b7254f27291e481e38d18f0a9c4521bc0a483640da00016cbfe35098a4b7454c26c91c07f638718c8ac447e1d10b003a40ec00016c4e835398c0b8055327191cc7f438d18e8aa04701b30a6038c0f000016bdec3421868b5253d26611647d037f18c0a7845a1c00a403580e600016b6ed3499890b6c54a27091ac7fc39218e8aa445c1c80ab83a00f000016afd535398e8bae56127611e48123961950aec4721ca0ae03640de00016a8c13501880b5c54526d11b07f23871900ab448a1d90b183ac0f200016a1a235698f0b9455e27711f08023971960ad44941d80b103a00f0000)) else (if i < 15 then (if i < 14 then 0x1a1f1534c98a8b7054726a11787dc37d1838a6c43a1a909f03800e60001a1820348987cb6253826511587d838318c0ac04721cb0ad03a00f20001a113733e1838b3a53926591607d838c18d0aa44721c00a203540d40001a0a1135718bcb6a54527211c47f23871898aa04661c00ac039c0ee0001a030435718d4b7854526911847dc38718d0a944501c10a483500cc00019fc1a342986cb6453f26511987ea37e1828a644541b40a603640dc00019f5163489858b4e53226211607ce36c1868a644481b80a5836c0da00019ee1034e18dcb8654c26c91ac8103921918ac84841c90a803880de00019e7333331818b3e52a263915c7e837b1820a704601c70aa838c0dc00019e03d3421834b4e54026c11847ec38c18c0a884741c50a7039c0d600019d94f33f1824b2452425f916c7d03741800a284241b70a503900dc00019d25634798b4b7254a26d91807d637c1848a884661c90af03a810200019cb3e35898ccb9055d27311b07f438e18f8a884681cd0aa03880e600019c45133c181cb3c53125f11387c036f17e8a4c45a1c00a883700da00019bd1b365190cb9e55727291d080439518d0a984561c30a583600d000019b625340982cb3852825d11287ae36417b8a044321a509b83380c000019af1735198a4b8054e26d11887e23861878a984761c70af83d40f600019a80f35198acb72541268116c7d638418b8a8c4621c00ac03a40de00019a10a35118b4b8254d269117c7ca3741828a5c45a1be09c833c0d00001999f635098c8b8655726a11707f038918d0ad04841c30aa03ac0f00001992e934d1888b6e54f27091bc7fe38718d0ab04801cb0b003bc0ec000198bd835218b0b8654e26b11a87e038318c0aa04701bf0a683a80e60001984e433c984cb4052b26191247ce3691768a044401b30a483500e8000197dd134f98c4b6654d26811a87f038c1898aa847c1c60af83b40ea0001976d034a1850b4853525f11787fa3891910a904621b60a103500d2000196ffd33497ccb1e52225b911c79c36a1818a2843a1a909f83480cc0001968eb35218dcb9c56627a121882a39a1900a9045e1c20ae03a80f60001961f63451868b5a55227311b87f638118b0a684601d00af039c0ec000195aea34a188cb7654e26c11987de38618e8ac04681c20a883680dc0001953ea3489860b4e53725f11607c83761800a444401b40a103680d4000194ce734e98acb7e54a27091b87f038c1870a944541b10a283740e40001945d635198ccb9655f27511fc82c39a18d8aac46e1d20aa83600e6000193ed93461874b4e53826191407ba36017d0a4c42e1a909e83640d00001937a13641928baa55a277920080638f18b8acc4861cc0aa83a40d20001930913581910b92560274919c7f438618f0a884661bf0a0833c0e00001929bc33097c4b0252425a913c7d037b1898a644741ca0ae83b40f200019227536e9960bc657427d12548403a81940abc4801c20a903940d8000191b593549904ba455f27991d480a3951910abc4801d50b483b80ec00019147433d1844b4653325f11507be3741838a9c47c1d10aa83900d6000190d57355188cb6e53e26d11947e439118e0ab04781cd0ae83cc0f400019064535118c4b8855b27411dc80a3911968b0047e1cd0ac03940ec00018ff7732a1780afc51825390ac78c34b1750a384481c00ab03940ec00018f85835798e8b9e56427811dc81839e1928ac04701c90ac03980e600018f16d3411828b2c52426591687de37d1880a6c45c1ca0ad03a40d800018ea75345988cb70544269118c7e63781830a804541bf0a583680dc00018e3533589914ba0569279121882839b1930ad04821cd0ac03800e600018dc4d346989cb8455627811ec82039c1968af04861d60aa037c0d800018d5543441868b8054a26791a48063931910aac47c1c70a683740e600018ce4934a18e0b7c55227291887e238318a0a7c45c1c40a683980f600018c7583451864b4c539263116c7e038218a0a904521ca0ad83cc0ea00018c03834c1900b8e55026d91b47f03841880a544441ae09f833c0b800018b93c346187cb6054426b11b47fe38e1938abc4841d30aa03780e000018b2383451858b5253b26011687c037517c8a2c43e1b70a483840e400018ab2b34f18d0b8a55926a916c7ca3731810a584481bb0ac837c0ea00018a41c35198b0b6a55027011c88023951948b0447c1df0b483bc0f0000189d0035a98e0b9456027391947f03a31970adc4861ce0ad83b00e80001895f834d1878b52546269917c7da3761880a544501b309e83640d2000188ede35998f4b8655527191b880439418d8a884661c00a783580cc0001887d134b1884b56535260118c7e438918f0abc4961d20af839c0ec0001880b335498ccb8055126f11b47f03821870a784701d30b203a00f20001879de32c17acaec50225190d078c35e1750a2c4361b50a083a80ee0001872ac35e9914bba569279121482039c18a8aa046a1cd0b083a80e6000186bce33d1838b4452f25711307c036d1818a4c4541b80a2833c0c00001864ab35898c4b7254e27011b07f43781818a4844c1bd0a5036c0e0000 else 0x1bde5234c98b4b7053d26711787dc3841878a784641c20a603a80da0001bd7683419850b4853426391687d037718a8a984761cb0ad03740e80001bd0ac32817c4b1a51e25591087b636f1858a5444e1b70a283540d60001bc9b73449830b3c53426611547dc38818f8adc4901cf0ae03700d20001bc2973591924bac56d278120082438c18d8a944721c60a7835c0e80001bbb9935198acb66535269117c7e238b18a8a7844a1bd0a783940f40001bb47635b1900b9e56627711cc80e3981918ab44541c109f033c0d40001bad6035518c0b7a55427011b47ee38818a0ac047a1c40a403500e00001ba6a63291778ae050124b109078a36617d89f44081a609f032c0ce0001b9f92351189cb6454626811ac80239118b0aa444c1b20a5837c0ee0001b98b03379828b3452b25b110c7aa36217a8a244541c20a483540d60001b91bc342184cb3053426491287ce37c1848a8c45e1c40ae03800d40001b8ac13479884b7853c26891687da37d1810a7c4621bf0a703740dc0001b83c63481860b5454826691887e03741858a6444a1be0a783800f40001b7ce13371830b4452a26591947da3801850a8c4601c20a503840f00001b75e23471884b5253a26411747e237c1858a684601b90aa03900d60001b6eda349989cb7254826d91807ee3871870a8c4661c20a603780f40001b680a32c97dcb1a52525b11447c036917e89f8410195095830c0c00001b60ff35018a4b7a54726d11ac80439718e8a8c45e1b709d035c0c80001b5a073429858b3c53425e11307b637317d8a444481b50a183400ba0001b52f635018acb6654426891cc80038e18a0a904641be0a583500cc0001b4bea3489874b6e54c26b119c7f239818d8aa847a1c30a303800d40001b451133c183cb4453026611747f038d1918ab446e1c10a903680ca0001b3e4032c97b4b0a51025290b078635417109ec4181a409c03540d00001b372834d98b4b7855926e11a480038c18a8a8c46c1c50a9038c0d40001b304d33597f0b1451a25890c078636217309e041c1ab0a2833c0c80001b294c34e18d0b7853f26a918c7e837d1878a8c4561c20a803800dc0001b224f3459860b6454126791747f23841880a4044e1b80a383940e80001b1b4334e189cb5e54026811587d63751850a5c4501b80a403380c40001b144634f98dcb8654f26c91787f237f1830a4c45c1ba0a4036c0e20001b0d4d3439848b5253926d918c7d43801850a684501b50a2836c0da0001b065d33c1830b5c53526111747e03791880a744561bf0a783640d80001aff223621934ba856a27e91ec80038b18e0a684601bf0a703700e40001af8473379810b3852125b11387b03721838a3842e1b80a6836c0e20001af12835918e4b7a54e26b119c7f238c18d0ab84741c90a483540ca0001aea343461878b6e54f26c11a87f438b18e8ac047e1c70a783780ee0001ae35333e1864b4853326491707ca3751818a504401b00a703a00ea0001adc793371810b3252525f91407d63831858a7c4541b40a383800ea0001ad56335198d0b7254f26d11b87f437f1888aa04701c60ab837c0e20001ace3c35818acb7a54f26d11cc8243a11970ac848a1db0b003880ea0001ac7443441858b5654326b91987f438a18e0aa84581be0a883740d60001ac00e3609930ba456127011c88163a11978b044b01df0b603e80f20001ab93b33297dcb1a51c25791107c43761808a684641c40ab83b00fa0001ab23b348988cb7255426e91bc8243931918af048e1d50aa83980e60001aab433431840b4853526411447cc36f1800a5845a1be0a703840de0001aa44234b18b4b9e55d27391d47f438718c8aa848a1ca0af83940d80001a9d613381814b1c51e256910079835817989fc4221ae0a483b40f80001a965235098f0ba256827c92088083951930ae84981d30ac83740dc0001a8f523471858b4253125e91407b836617e0a644441b40a503800da0001a884634d18b8b9255b27411d47fe3961928ab84641c20ac03a00e80001a815433f1844b5653726691547b63771850a7c4641ba0a303580d80001a7a113649978bd456f282124083c3af19e8b184a41e10b903e810a0001a731734998a0b7c55827191d881a39318f8aac4801be0a6835c0de0001a6c2f33797f4b1052025d11307b436917e8a404481c10ac83a40e00001a654633f1838b3e53526691807d03771888ab847e1cc0ae037c0e60001a5e5e3389818b2452525a11247ca37e1878a6044e1b70a083380d60001a576f3431848b4a52d25b91047b23841908aac4701c60a883940f40001a50363621910ba055c267115c7e23791808a404401b40a583a40f00001a49413469874b5853625d91207b036b17c0a3443c1b90a903640da0001a424c33e183cb4853b26991887fa38c1880a9c45c1bd0a603800ee0001a3b5534618b4b6e54526c11b87fc3851880a8c45a1b50a7835c0de0001a344734e1900b9856227f923884c3a41960ae048a1c00a603880d00001a2d2735098acb70546267918c7ee37f18d8a8046e1c20a803780dc0001a262234918a8b6c543268918c7d83841828a484501b60a803600d6000) else (if i < 16 then 0x1d9c993351814b2e52a25b11307b237217e8a244461b70a183600d40001d95a23441854b5053d26391647d83781838a6445a1c00aa03800fc0001d8eb3344988cb5453025d11507d23741870a7445a1ba0a683a00d80001d87cb33c9854b5254026511707e83791888a744701c90ad038c0d40001d80cd3469858b3852f26291887e83891908ac84821ca0a983780f00001d79b534f1898b8655e277120c8383a21990ad84761cd0ae03680d80001d72e332d97c4b1051525110e479235517a8a104341af0a383700d20001d6bd334f18b8b6e53e26a11a87dc3891860a704621c70a883900de0001d64e53421874b6a53b26411607de37a1880a5c4621c10a583880d00001d5e2233297e4b1a51b25710f87983771840a4044e1be0a183580dc0001d570835618ecb9055027111d080a3881918ad048a1d30ac03a80e20001d50293391818b2851f25690e878636217d0a3843e1ad0a0833c0be0001d494033c1814b4853926411887d83751800a444541c40ad03a80e00001d428c3219768ad650624f10f47b236a1800a444401b309e03380ca0001d3b7435218a4b8055526d91b87f438c18f0ab448c1d00ae03980f80001d34b532417a4aec50f25390d479a3641780a044201a90a6036c0de0001d2dcf3399824b4052925d91187ae3701888a7844e1b40a303640da0001d26e133f9848b4452b25d11547da38518b8a604681ca0af03a80ee0001d1fd4353189cb7a54826a11c88023921908ad04741d10af83b80f40001d18dc3429868b5253d26811987dc3771818a5c43c1ab09d03400d80001d11d7347986cb6a54526b11bc7f23871830a4c4441b90a303680e40001d0ad933f9864b4453626591707e437e1878a484481b50aa03940f00001d03f2342184cb3c53326091647c23751848a684521be0a383840d80001cfd083419858b6053d26891ac7de3821860a4845e1c90a903680da0001cf61d3369810b2e53025d91307c23791860a704481be0a6038c0e20001cef21349185cb52540265118c7fe38d18d8ac84721c80a903a40ea0001ce7fc35618fcb8e55626a11887f23851878a6c4421b40a583700ce0001ce10c345984cb4652e264114c7c63731800a384301a70a183700ea0001cd9e335698ccb7854d26e11a87f438418c0a8c46e1c90aa03980f80001cd2e634b9878b5053926611987ea3901918ac84861d70b503ec0fe0001ccbe13469880b5c53f26b11a47f638c18b8a7c45a1be0a703640ce0001cc4fc33c9804b3853726691647d43731828a384501ba0a583700d00001cbe023431854b3e52d26091647d637a17d8a1c4401b80a883840de0001cb76131d1758ada50824d90a47883581720a1843e1a80a083600de0001cb0473561900b8c54e26b11cc7fc38918a8aac4781cb0af83cc0e20001ca95a33a980cb3252b26a11847ce3811870a984641ca0b103a00e00001ca24335798f4b9c56127c921883439e1980af848a1dd0ae83b80fc0001c9b3e35298f4b8054426e11b88023961978adc4881d60ae83c40e60001c944c345188cb76543263915c7d83721868a6445a1c10a703880e60001c8d6633717ecb2252525d11547d63761830a344521b00a503540dc0001c865635018b4b6654626c11a87da38518a0a904681bf0a983980e60001c7f4f347986cb5a54526a91907dc3821850a984661c50ab03700ce0001c78633411858b6254526e11b07ec38f1938ae44841cf0a483680e00001c715934b98a0b62540260113c7dc3811868a484481bd0a783840f60001c6a5435418e8b8a55a27b12188303aa19d0b1c4a21dd0af03880ea0001c63603419888b4e53b26591847da37a17c0a3c4481b30a7037c0de0001c5c5835018a8b7454d26f91cc7f63881900a9c4801ce0b203c80f00001c553b35598e8b9055a27211e880a3981938ab44921d90b483d00f00001c4e5533c9854b54533261115c7c636b17a0a0842c1b70a283680e40001c472c35a1930bae561272119c8003871858a6c44a1ba0a2835c0de0001c40323439820b48537260913c7ca37e1880a984741cd0ac838c0dc0001c392035698e0b7454b26991947ee38318c0aac4741c50a503680cc0001c31f935118e0b8054d26c11947ce37c1848a604661ba0a583640da0001c2b033411840b4453a26091347c237a1870a644621c60b003bc0e40001c242a3391828b4853225991207d43771828a544601bd0a683340d00001c1d763221790ae650d24f10b47803521760a0842e1ac09f03500c80001c164b35c192cba656827d92208203981940af047a1c20a9036c0d20001c0f4334b18b8b7e54426a91947f037c1838a544441b40a303840ee0001c083c34f98bcb56544267117c7f03831870a8c44c1b80a4835c0de0001c013f34b1874b4e53426311647da38018b8aa84901cf0ad83700d80001bfa3c3471874b6655026c91bc80c39d18e0aac46e1c00a783780de0001bf35533d983cb36529257911c7bc36a17b0a4844c1ba0a883900e80001bec4a34c18d4b7854226d91fc80c38f18e0ac44821cc0b003a40e60001be55d33f9868b2c52626311247a43721830a6c44e1c00ac03900e6000 else (if i < 17 then 0x1f58eb33f9830b4c54426a91807dc3771860a6c44e1b60a503880ea0001f51e03519900b8e54e26c91a47ee38918d8a944561c10ad03980f80001f4b0033a1804b2c52c25f111c7be37a1828a5c4461ac09f83540d40001f43f83471860b4853126391647d637f1870a784501bd0ab03940e20001f3d033391838b6a54326811687d83721818a3c43c1af09d034c0d80001f35fb35018bcb9455427291d480838d18d0aa046e1c20a583900de0001f2f103391830b3e53126291447bc3721800a344501c20ad03900c80001f282a3399834b3052c26111607d637e1890a904681c30aa036c0d60001f211f35318b8b8455b27391cc80c38d18e8ab848c1d50b303c40fc0001f1a4633617fcb3652925f91347c03791818a344421b109e03340cc0001f134a3491874b4853a26091447b036517e0a1c43c1b60a583800d20001f0c5933e984cb4253f265116c7b836f1860a644581c80a6836c0e40001f058e3319810b1052225690ec7983621800a2c44c1bf0ab83a40e40001efeb133b1804b3252825c11447bc3751850a5c4441be0a283900e40001ef7c03469868b5453626391647d637b1868a804581c20a9837c0e60001ef0b734f98acb6854b266116c7d438118a0aac46e1b90a1035c0dc0001ee9c333f9814b1e52625790f078a3531778a304381b009f83600de0001ee2bd34c1898b5c54026b91787ec3801850a5843c1b00a283600d00001edbe133897d8b1a52625d11207b436817b8a044341ac09e834c0d20001ed50333517ccb0c51025010e479435c17f0a504401be0a383680e40001ece053451888b6454727011b880039018a8a8c46a1c70a783b40ee0001ec73033697dcb1852c26011507b436717e8a404401b40ad03a00f20001ec04633f9834b2a52d26391647d43771810a7445c1c50a803600de0001eb947347987cb5a53426c11a07f239018c8a8c4641cc0ad83bc0dc0001eb24d3429870b5c54426e11947fe3971930aac4601b60a683900dc0001eab6f33717f8b2c53326411807da38418d0a904861d90b503cc0f80001ea48c33d984cb3e52d26591507d43751820a3444a1bb0a803a40f20001e9d7b34d18e8b7c54e26e11707e838918e8aac47a1c10a683a00e60001e968f33d182cb4653826111207d038418c8acc4681d00ab037c0e40001e8f9c33f9828b4e53426411307ce3751880a804501ba0a583a00de0001e889b34c18c4b8654b27411ac7ea3901910ae448e1df0b503b80ea0001e819134d1888b7254d27091d080a3921910ac84701c40ab038c0dc0001e7ab73379828b3853426811c47f238a18b0a8445e1c20a503740d00001e73c63401870b5e54526a91b07f83881898a684441b60a5833c0b80001e6cce345188cb6054726b919c7e037f18a8a8446c1c50a583940ec0001e65e0342184cb46536264116c7c436e1868a604441ba0a4037c0e40001e5edf347187cb6454c27111b48043951938ab046a1c10a583600dc0001e57ed33d9848b3c53b26591807c036c17e8a4c44c1b40a583a40f20001e50e134d98b0b8a55927411f080c3921908a8c4521c20a5035c0d20001e4a173381830b3252a25c91247ac36e1830a4c4581bf0a8036c0dc0001e434a33497e0b2052425a912c7b636517a8a2843a1ae09f83380e20001e3c4734a18c4b7855326c11907f63811898a9045e1b30a383500d00001e353635198ccb7854d27291f082e3ab19e8b344b01d50b583a00dc0001e2e413401824b44532262915c7e238b18d0a8c4721c50ab03b40e80001e275033d1848b5e53b260116c7ba3791850a684541b60a803840e20001e207a33097d0b1a51e25810f079836217f0a584461b50a403900fa0001e19953399820b3a53325f91287b03761820a0c4341a709b831c0ce0001e128a35118b8b6654126811887de37d1898a804601c30ab83b40fc0001e0ba83391818b3a52925b11287ac36417c0a504581c40ac036c0d80001e04c73369804b2a52825c90e47923611788a2c4201a309d83340ce0001dfdcf345987cb6a54326691607c23741830a684561c50a6837c0e20001df6bc34e18a8b5454626a91887d837b1880a7c4561bf0a183580e00001defab34f98b4b7655a27111cc7f639718d8ab846a1c00a803780d80001de8bb34618a8b8054726b91c07fa38818d8ab84701c90a8037c0ce0001de1e133397bcb1652225b112c7c03781810a604381aa0a0836c0c40001ddb1532a979caf24fe24b10a077035317289fc4541ab09c033c0d40001dd40134d9888b7654f26a11787e037e18d0aa846a1d30b283b80f00001dcd0533e983cb40536263917c7d037d1888a7c4641c40a803900d00001dc613346987cb6254a26d91747de3871898aa84701c10a503580e20001dbf2e339981cb2252b26291687d63791850a884541bf0ab83740d60001db80135d9930ba456727a120482c39a1930ac84781b80a783940fc0001db12a33497d0b0c51c25711047b036817a0a5045e1bb0a383780f00001daa4633e17fcb2e52925a11187a036e1850a944541b80a483580ca0001da36d3389808b2651d26091407c03761828a784521bf0a883740de000 else 0x2088210000000000000000000000000000000000001a90a483bc0e40002081523349814b2252e266918c7dc3741830a7c4541be0a3036c0e2000207a633381818b3853126011287c23791850a644681c30a7838c0f40002073af3231748ac24f4246107076034216789a840019809d033c0d4000206ce532b17ccb2452425911207b836917d8a1c4201a009b83300d80002065ee33f983cb3052c25d91807dc38018b8a804541c30aa03a80da000205f0f33617f8b3052425b91187a235917f0a184261b40a103700da00020582833817e4b2c51b25511247c836c1838a384481be0a9037c0e800020511c34d18a4b6c54926811847de3761858a804561c00a983940e4000204a293479854b4a53726991847f23851870a984661be0aa83b00ec000204335341182cb3453026391607c837417d0a1843c1b20a5034c0dc000203c5533a182cb5453025e11287ae3701820a604741c90ac837c0e20002035583429848b4653426511707f238b18e0a804541c10a803740d2000202e9832a17a0b0651625110e87b637018089e44261ab09e03440ca0002027ce33397fcb2852a25c90fc7a436617e0a2842e1a709e83680e00002020f43381810b2c53226111347ce3791838a5444e1b50a483480de0002019f33499890b7054626991a07ea38d1910a9c4681be0ac03940f000020133732817a4b0a52225791187a035d1750a244441a909e836c0ce000200c2f34b9894b7254f27191c47ec38618f0a8846e1ce0b203d00f400020057932617b0b1a51525390f87b236717b0a204341b40a303940d60001ffea33399824b3852f26291607c23781868a804561b80a103740ea0001ff7ba33f1860b5e54a26c91787f838a18e0abc47e1d00ad03b81000001ff0e03359808b3e52f26591487d63701810a4c4401b80a603540d60001fea0333c9808b1851f25a11487cc37c18b0a8c46a1c90b083b40f40001fe33333417e8b2051b25990f87ac36e1810a3043e1bd0ab83740ea0001fdc49340983cb4053526011247be3791830a3c42e1b10a503580ec0001fd57633497d8afc51625510e879835f1750a004281aa0a3038c0e80001fceaa32d97dcb1e51c25811187c23781838a7c45c1bc0a783600e20001fc7ce33917d0b08518257111c7bc3701810a6445a1b50a8838c0d20001fc0c63499874b5e54026791747fa38f1888ab04761ce0ad03980e20001fb9f533197c0b0c52025d11487a035e1790a104281ab09e83600d00001fb2eb3471870b42525257910479836017189f841a1a909c03340ca0001fabf43419874b6453e263116c7e637f1868a7845a1ba0a703840e00001fa4f63439860b3a52c26211407b236a17c8a144381b40a203400da0001f9e0833e9824b3c52f25b91747e43831880a884541b40a503700e00001f972533697dcb2652825791247ae35917609fc4241ab0a083400d00001f901f34b1890b5a53c26311647c637c1870a804681b80a583540d40001f894a33217d4b0e51b25611247c036917e0a2443e1b209e83580e20001f827332f17dcb0e51e25a910c79a36417409f842e1a309d83680dc0001f7b6d34a98a0b7254826a917c80c3951900ab446e1bd0a4836c0d80001f749133517f8b0651125110e079635917e8a2041e1a20a203700ea0001f6db43399824b2252c262116c7d43731820a944681cf0b103bc0f60001f66d53389800b3853a263113c7ca3721800a6043a1a809d83480dc0001f5fdc33f984cb4653426211487ce3761868a704481c10a883800ce000)))))

private def checkpoint (i : ℕ) : ℕ :=
  let word := (packet (i/1024) >>> (232*((i%1024)/16))) % (2^232)
  (word >>> 208) + ((word >>> (13*(i%16))) % 8192)

private def raw (j : ℕ) : ℕ := fromBlocks checkpoint (fun r => quick (number r)) j

private def small (n : ℕ) : ℕ := if 5≤n then 3 else if 3≤n then 2 else if 2≤n then 1 else 0
def fast (n : ℕ) : ℕ := raw (index n) + small n

private def step (i : ℕ) := checkpoint (i+1) == checkpoint i + tally (fun r => quick (number r)) (512*i) 512

private def valid (lo len : ℕ) : Prop := (List.range' lo len).all step = true
private theorem glue {lo a b : ℕ} (left : valid lo a) (right : valid (lo+a) b) : valid lo (a+b) := by
  unfold valid at *
  rw [←List.range'_append_1,List.all_append,left,right]
  rfl


private theorem halve (lo n : ℕ) (h : valid lo (n/2))
    (k : valid (lo+n/2) (n-n/2)) : valid lo n := by
  simpa only [show n/2+(n-n/2)=n by omega] using glue h k

private def covered (lo hi : ℕ) : Prop :=
  ∀ j, lo≤j → j<hi → step j=true

private theorem checked {lo hi : ℕ} (h : valid lo (hi-lo)) : covered lo hi := by
  intro j lower upper
  exact List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨lower,by omega⟩)

private theorem joinCoverage {lo mid hi : ℕ} (l : covered lo mid) (r : covered mid hi) :
    covered lo hi := by
  intro j lower upper
  by_cases isLeft : j < mid
  · exact l j lower isLeft
  · exact r j (by omega) upper


private theorem b0 : covered 0 70 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b70 : covered 70 141 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b141 : covered 141 211 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b211 : covered 211 282 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b282 : covered 282 352 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b352 : covered 352 423 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b423 : covered 423 494 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b494 : covered 494 565 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b565 : covered 565 635 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b635 : covered 635 706 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b706 : covered 706 777 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b777 : covered 777 848 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b848 : covered 848 918 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b918 : covered 918 989 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b989 : covered 989 1060 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b1060 : covered 1060 1131 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b1131 : covered 1131 1201 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b1201 : covered 1201 1272 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b1272 : covered 1272 1342 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b1342 : covered 1342 1413 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b1413 : covered 1413 1483 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b1483 : covered 1483 1554 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b1554 : covered 1554 1625 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b1625 : covered 1625 1696 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b1696 : covered 1696 1766 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b1766 : covered 1766 1837 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b1837 : covered 1837 1908 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b1908 : covered 1908 1979 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b1979 : covered 1979 2049 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b2049 : covered 2049 2120 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b2120 : covered 2120 2191 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b2191 : covered 2191 2262 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b2262 : covered 2262 2332 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b2332 : covered 2332 2403 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b2403 : covered 2403 2473 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b2473 : covered 2473 2544 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b2544 : covered 2544 2614 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b2614 : covered 2614 2685 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b2685 : covered 2685 2756 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b2756 : covered 2756 2827 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b2827 : covered 2827 2897 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b2897 : covered 2897 2968 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b2968 : covered 2968 3039 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b3039 : covered 3039 3110 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b3110 : covered 3110 3180 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b3180 : covered 3180 3251 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b3251 : covered 3251 3322 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b3322 : covered 3322 3393 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b3393 : covered 3393 3463 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b3463 : covered 3463 3534 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b3534 : covered 3534 3605 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b3605 : covered 3605 3676 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b3676 : covered 3676 3746 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b3746 : covered 3746 3817 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b3817 : covered 3817 3888 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b3888 : covered 3888 3959 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b3959 : covered 3959 4029 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b4029 : covered 4029 4100 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b4100 : covered 4100 4171 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b4171 : covered 4171 4242 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b4242 : covered 4242 4312 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b4312 : covered 4312 4383 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b4383 : covered 4383 4454 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b4454 : covered 4454 4525 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b4525 : covered 4525 4595 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b4595 : covered 4595 4666 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b4666 : covered 4666 4736 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b4736 : covered 4736 4807 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b4807 : covered 4807 4877 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b4877 : covered 4877 4948 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b4948 : covered 4948 5019 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b5019 : covered 5019 5090 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b5090 : covered 5090 5160 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b5160 : covered 5160 5231 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b5231 : covered 5231 5302 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b5302 : covered 5302 5373 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b5373 : covered 5373 5443 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b5443 : covered 5443 5514 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b5514 : covered 5514 5585 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b5585 : covered 5585 5656 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b5656 : covered 5656 5726 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b5726 : covered 5726 5797 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b5797 : covered 5797 5867 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b5867 : covered 5867 5938 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b5938 : covered 5938 6008 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b6008 : covered 6008 6079 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b6079 : covered 6079 6150 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b6150 : covered 6150 6221 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b6221 : covered 6221 6291 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b6291 : covered 6291 6362 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b6362 : covered 6362 6433 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b6433 : covered 6433 6504 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b6504 : covered 6504 6574 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b6574 : covered 6574 6645 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b6645 : covered 6645 6716 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b6716 : covered 6716 6787 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b6787 : covered 6787 6857 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b6857 : covered 6857 6928 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b6928 : covered 6928 6998 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b6998 : covered 6998 7069 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b7069 : covered 7069 7139 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b7139 : covered 7139 7210 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b7210 : covered 7210 7281 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b7281 : covered 7281 7352 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b7352 : covered 7352 7422 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b7422 : covered 7422 7493 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b7493 : covered 7493 7564 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b7564 : covered 7564 7635 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b7635 : covered 7635 7705 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b7705 : covered 7705 7776 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b7776 : covered 7776 7847 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b7847 : covered 7847 7918 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b7918 : covered 7918 7988 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b7988 : covered 7988 8059 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b8059 : covered 8059 8130 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b8130 : covered 8130 8201 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b8201 : covered 8201 8271 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b8271 : covered 8271 8342 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b8342 : covered 8342 8413 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b8413 : covered 8413 8484 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b8484 : covered 8484 8554 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b8554 : covered 8554 8625 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b8625 : covered 8625 8696 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b8696 : covered 8696 8767 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b8767 : covered 8767 8837 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b8837 : covered 8837 8908 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b8908 : covered 8908 8979 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b8979 : covered 8979 9050 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b9050 : covered 9050 9120 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b9120 : covered 9120 9191 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b9191 : covered 9191 9261 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b9261 : covered 9261 9332 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b9332 : covered 9332 9402 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b9402 : covered 9402 9473 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b9473 : covered 9473 9544 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b9544 : covered 9544 9615 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b9615 : covered 9615 9685 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b9685 : covered 9685 9756 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b9756 : covered 9756 9827 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b9827 : covered 9827 9898 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b9898 : covered 9898 9968 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b9968 : covered 9968 10039 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b10039 : covered 10039 10110 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b10110 : covered 10110 10181 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b10181 : covered 10181 10251 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b10251 : covered 10251 10322 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b10322 : covered 10322 10392 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b10392 : covered 10392 10463 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b10463 : covered 10463 10533 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b10533 : covered 10533 10604 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b10604 : covered 10604 10675 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b10675 : covered 10675 10746 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b10746 : covered 10746 10816 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b10816 : covered 10816 10887 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b10887 : covered 10887 10958 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b10958 : covered 10958 11029 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b11029 : covered 11029 11099 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b11099 : covered 11099 11170 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b11170 : covered 11170 11241 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b11241 : covered 11241 11312 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b11312 : covered 11312 11382 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b11382 : covered 11382 11453 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b11453 : covered 11453 11523 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b11523 : covered 11523 11594 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b11594 : covered 11594 11664 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b11664 : covered 11664 11735 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b11735 : covered 11735 11806 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b11806 : covered 11806 11877 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b11877 : covered 11877 11947 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b11947 : covered 11947 12018 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b12018 : covered 12018 12089 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b12089 : covered 12089 12160 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b12160 : covered 12160 12230 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b12230 : covered 12230 12301 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b12301 : covered 12301 12372 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b12372 : covered 12372 12443 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b12443 : covered 12443 12513 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b12513 : covered 12513 12584 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b12584 : covered 12584 12655 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b12655 : covered 12655 12726 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b12726 : covered 12726 12796 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b12796 : covered 12796 12867 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b12867 : covered 12867 12938 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b12938 : covered 12938 13009 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b13009 : covered 13009 13079 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b13079 : covered 13079 13150 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b13150 : covered 13150 13221 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b13221 : covered 13221 13292 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b13292 : covered 13292 13362 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b13362 : covered 13362 13433 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b13433 : covered 13433 13504 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b13504 : covered 13504 13575 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b13575 : covered 13575 13645 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b13645 : covered 13645 13716 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b13716 : covered 13716 13786 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b13786 : covered 13786 13857 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b13857 : covered 13857 13927 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b13927 : covered 13927 13998 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b13998 : covered 13998 14069 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b14069 : covered 14069 14140 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b14140 : covered 14140 14210 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b14210 : covered 14210 14281 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b14281 : covered 14281 14352 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b14352 : covered 14352 14423 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b14423 : covered 14423 14493 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b14493 : covered 14493 14564 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b14564 : covered 14564 14635 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b14635 : covered 14635 14706 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b14706 : covered 14706 14776 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b14776 : covered 14776 14847 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b14847 : covered 14847 14917 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b14917 : covered 14917 14988 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b14988 : covered 14988 15058 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b15058 : covered 15058 15129 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b15129 : covered 15129 15200 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b15200 : covered 15200 15271 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b15271 : covered 15271 15341 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b15341 : covered 15341 15412 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b15412 : covered 15412 15483 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b15483 : covered 15483 15554 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b15554 : covered 15554 15624 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b15624 : covered 15624 15695 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b15695 : covered 15695 15766 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b15766 : covered 15766 15837 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b15837 : covered 15837 15907 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b15907 : covered 15907 15978 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b15978 : covered 15978 16048 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b16048 : covered 16048 16119 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b16119 : covered 16119 16189 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b16189 : covered 16189 16260 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b16260 : covered 16260 16331 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b16331 : covered 16331 16402 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b16402 : covered 16402 16472 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b16472 : covered 16472 16543 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b16543 : covered 16543 16614 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b16614 : covered 16614 16685 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b16685 : covered 16685 16755 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b16755 : covered 16755 16826 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b16826 : covered 16826 16897 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b16897 : covered 16897 16968 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b16968 : covered 16968 17038 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b17038 : covered 17038 17109 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b17109 : covered 17109 17180 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b17180 : covered 17180 17251 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b17251 : covered 17251 17321 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b17321 : covered 17321 17392 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b17392 : covered 17392 17463 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b17463 : covered 17463 17534 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b17534 : covered 17534 17604 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b17604 : covered 17604 17675 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b17675 : covered 17675 17746 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b17746 : covered 17746 17817 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b17817 : covered 17817 17887 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b17887 : covered 17887 17958 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b17958 : covered 17958 18029 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

private theorem b18029 : covered 18029 18100 := checked (by apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> apply halve <;> unfold valid <;> decide +kernel)

set_option maxRecDepth 16000 in
private theorem allrows : covered 0 18100 := (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b0 b70) (joinCoverage b141 b211)) (joinCoverage (joinCoverage b282 b352) (joinCoverage b423 b494))) (joinCoverage (joinCoverage (joinCoverage b565 b635) (joinCoverage b706 b777)) (joinCoverage (joinCoverage b848 b918) (joinCoverage b989 b1060)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b1131 b1201) (joinCoverage b1272 b1342)) (joinCoverage (joinCoverage b1413 b1483) (joinCoverage b1554 b1625))) (joinCoverage (joinCoverage (joinCoverage b1696 b1766) (joinCoverage b1837 b1908)) (joinCoverage (joinCoverage b1979 b2049) (joinCoverage b2120 b2191))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b2262 b2332) (joinCoverage b2403 b2473)) (joinCoverage (joinCoverage b2544 b2614) (joinCoverage b2685 b2756))) (joinCoverage (joinCoverage (joinCoverage b2827 b2897) (joinCoverage b2968 b3039)) (joinCoverage (joinCoverage b3110 b3180) (joinCoverage b3251 b3322)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b3393 b3463) (joinCoverage b3534 b3605)) (joinCoverage (joinCoverage b3676 b3746) (joinCoverage b3817 b3888))) (joinCoverage (joinCoverage (joinCoverage b3959 b4029) (joinCoverage b4100 b4171)) (joinCoverage (joinCoverage b4242 b4312) (joinCoverage b4383 b4454)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b4525 b4595) (joinCoverage b4666 b4736)) (joinCoverage (joinCoverage b4807 b4877) (joinCoverage b4948 b5019))) (joinCoverage (joinCoverage (joinCoverage b5090 b5160) (joinCoverage b5231 b5302)) (joinCoverage (joinCoverage b5373 b5443) (joinCoverage b5514 b5585)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b5656 b5726) (joinCoverage b5797 b5867)) (joinCoverage (joinCoverage b5938 b6008) (joinCoverage b6079 b6150))) (joinCoverage (joinCoverage (joinCoverage b6221 b6291) (joinCoverage b6362 b6433)) (joinCoverage (joinCoverage b6504 b6574) (joinCoverage b6645 b6716))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b6787 b6857) (joinCoverage b6928 b6998)) (joinCoverage (joinCoverage b7069 b7139) (joinCoverage b7210 b7281))) (joinCoverage (joinCoverage (joinCoverage b7352 b7422) (joinCoverage b7493 b7564)) (joinCoverage (joinCoverage b7635 b7705) (joinCoverage b7776 b7847)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b7918 b7988) (joinCoverage b8059 b8130)) (joinCoverage (joinCoverage b8201 b8271) (joinCoverage b8342 b8413))) (joinCoverage (joinCoverage (joinCoverage b8484 b8554) (joinCoverage b8625 b8696)) (joinCoverage (joinCoverage b8767 b8837) (joinCoverage b8908 b8979))))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b9050 b9120) (joinCoverage b9191 b9261)) (joinCoverage (joinCoverage b9332 b9402) (joinCoverage b9473 b9544))) (joinCoverage (joinCoverage (joinCoverage b9615 b9685) (joinCoverage b9756 b9827)) (joinCoverage (joinCoverage b9898 b9968) (joinCoverage b10039 b10110)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b10181 b10251) (joinCoverage b10322 b10392)) (joinCoverage (joinCoverage b10463 b10533) (joinCoverage b10604 b10675))) (joinCoverage (joinCoverage (joinCoverage b10746 b10816) (joinCoverage b10887 b10958)) (joinCoverage (joinCoverage b11029 b11099) (joinCoverage b11170 b11241))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b11312 b11382) (joinCoverage b11453 b11523)) (joinCoverage (joinCoverage b11594 b11664) (joinCoverage b11735 b11806))) (joinCoverage (joinCoverage (joinCoverage b11877 b11947) (joinCoverage b12018 b12089)) (joinCoverage (joinCoverage b12160 b12230) (joinCoverage b12301 b12372)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b12443 b12513) (joinCoverage b12584 b12655)) (joinCoverage (joinCoverage b12726 b12796) (joinCoverage b12867 b12938))) (joinCoverage (joinCoverage (joinCoverage b13009 b13079) (joinCoverage b13150 b13221)) (joinCoverage (joinCoverage b13292 b13362) (joinCoverage b13433 b13504)))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b13575 b13645) (joinCoverage b13716 b13786)) (joinCoverage (joinCoverage b13857 b13927) (joinCoverage b13998 b14069))) (joinCoverage (joinCoverage (joinCoverage b14140 b14210) (joinCoverage b14281 b14352)) (joinCoverage (joinCoverage b14423 b14493) (joinCoverage b14564 b14635)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b14706 b14776) (joinCoverage b14847 b14917)) (joinCoverage (joinCoverage b14988 b15058) (joinCoverage b15129 b15200))) (joinCoverage (joinCoverage (joinCoverage b15271 b15341) (joinCoverage b15412 b15483)) (joinCoverage (joinCoverage b15554 b15624) (joinCoverage b15695 b15766))))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage (joinCoverage b15837 b15907) (joinCoverage b15978 b16048)) (joinCoverage (joinCoverage b16119 b16189) (joinCoverage b16260 b16331))) (joinCoverage (joinCoverage (joinCoverage b16402 b16472) (joinCoverage b16543 b16614)) (joinCoverage (joinCoverage b16685 b16755) (joinCoverage b16826 b16897)))) (joinCoverage (joinCoverage (joinCoverage (joinCoverage b16968 b17038) (joinCoverage b17109 b17180)) (joinCoverage (joinCoverage b17251 b17321) (joinCoverage b17392 b17463))) (joinCoverage (joinCoverage (joinCoverage b17534 b17604) (joinCoverage b17675 b17746)) (joinCoverage (joinCoverage b17817 b17887) (joinCoverage b17958 b18029))))))))

theorem fast_correct (n : ℕ) (bound : n ≤ 34751024) : fast n = Nat.primeCounting n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases smallN : n < 6
    · have tests : ∀ i : Fin 7, fast i.val = Nat.primeCounting i.val := by decide +kernel
      exact tests ⟨n+1,by omega⟩
    · have unchanged : small (n+1) = small n := by simp [small,show 5≤n by omega,show 5≤n+1 by omega]
      rw [show Nat.primeCounting (n+1) = Nat.primeCounting n + (if (n+1).Prime then 1 else 0)
          from Nat.count_succ Nat.Prime (n+1),←ih (by omega)]
      rcases wheel_step n with ⟨e,hd⟩ | ⟨e,whose⟩
      · have hp := skips_composite (by omega : 5<n+1) hd
        simp only [fast,e,unchanged,if_neg hp,Nat.add_zero]
      · have ix := index_bound (show n≤34751024 by omega)
        have within : index n / 512 < 18100 := by omega
        have chk := beq_iff_eq.mp (allrows _ (Nat.zero_le _) within)
        change checkpoint (index n/512+1) = checkpoint (index n/512) +
          tally (fun j => quick (number j)) (512*(index n/512)) 512 at chk
        have h := fromBlocks_succ checkpoint (fun j => quick (number j)) (index n) chk
        change raw (index n+1) = raw (index n) + (if quick (number (index n)) then 1 else 0) at h
        rw [whose] at h
        simp only [fast,e,h,unchanged]
        by_cases hp : (n+1).Prime
        · simp [hp,(quick_ok bound).mpr hp,Nat.add_right_comm]
        · simp [hp,mt (quick_ok bound).mp hp]
def prime (n : ℕ) : Bool := quick n

theorem prime_ok (n : ℕ) (hn : n≤34751024) : prime n=true ↔ n.Prime := quick_ok hn

end SmallWitnessPrimeCount

theorem OMA.solution : OMA.R_OeisA247824_conjecture_2_R2_H1_R1.H1 :=
  (SmallWitnessPrimeCount.fast_correct 20868473 (by decide)).symm.trans (by decide +kernel)
