import OMAStatements.S_oeis_a370578
import Mathlib.Algebra.Group.Nat.Defs

/-- A certificate for a partial binary exponent. -/
private structure Residue (m e r : ℕ) : Prop where
  value : 3 ^ e % m = r

private theorem bit_step {m e r : ℕ} (bit : ℕ) (h : Residue m e r) :
    Residue m (e + e + bit) ((r * r * 3^bit) % m) := by
  constructor
  rw [pow_add, pow_add, Nat.mul_mod (3^e * 3^e) (3^bit) m,
    Nat.mul_mod (3^e) (3^e) m, h.value, ← Nat.mul_mod]

private theorem divides_of_residue {k : ℕ} (h : Residue (k+1) k k) :
    (k+1) ∣ 3^k+1 := by
  apply Nat.dvd_of_mod_eq_zero
  calc
    _ = (3^k % (k+1) + 1 % (k+1)) % (k+1) := Nat.add_mod ..
    _ = (k % (k+1) + 1 % (k+1)) % (k+1) := by
      rw [h.value, Nat.mod_eq_of_lt (Nat.lt_succ_self k)]
    _ = (k+1) % (k+1) := (Nat.add_mod ..).symm
    _ = 0 := Nat.mod_self _

private theorem class1 : Residue 2 1 1 := by
  have p1 : Residue 2 1 1 := ⟨by decide⟩
  exact p1

private theorem class3 : Residue 4 3 3 := by
  have p1 : Residue 4 1 3 := ⟨by decide⟩
  have p2 : Residue 4 3 3 := bit_step 1 p1
  exact p2

private theorem class13 : Residue 5362888766 5362888765 5362888765 := by
  have p1 : Residue 5362888766 1 3 := ⟨by decide⟩
  have p2 : Residue 5362888766 2 9 := bit_step 0 p1
  have p3 : Residue 5362888766 4 81 := bit_step 0 p2
  have p4 : Residue 5362888766 9 19683 := bit_step 1 p3
  have p5 : Residue 5362888766 19 1162261467 := bit_step 1 p4
  have p6 : Residue 5362888766 39 5293542971 := bit_step 1 p5
  have p7 : Residue 5362888766 79 3847125051 := bit_step 1 p6
  have p8 : Residue 5362888766 159 4635749731 := bit_step 1 p7
  have p9 : Residue 5362888766 319 2003535623 := bit_step 1 p8
  have p10 : Residue 5362888766 639 351912501 := bit_step 1 p9
  have p11 : Residue 5362888766 1278 1426106555 := bit_step 0 p10
  have p12 : Residue 5362888766 2557 4029050267 := bit_step 1 p11
  have p13 : Residue 5362888766 5114 2089103659 := bit_step 0 p12
  have p14 : Residue 5362888766 10228 2185861959 := bit_step 0 p13
  have p15 : Residue 5362888766 20457 1485373595 := bit_step 1 p14
  have p16 : Residue 5362888766 40915 2853156175 := bit_step 1 p15
  have p17 : Residue 5362888766 81831 4271689925 := bit_step 1 p16
  have p18 : Residue 5362888766 163662 687707509 := bit_step 0 p17
  have p19 : Residue 5362888766 327324 3960958279 := bit_step 0 p18
  have p20 : Residue 5362888766 654649 343231343 := bit_step 1 p19
  have p21 : Residue 5362888766 1309299 3103776919 := bit_step 1 p20
  have p22 : Residue 5362888766 2618598 331696569 := bit_step 0 p21
  have p23 : Residue 5362888766 5237196 1263060461 := bit_step 0 p22
  have p24 : Residue 5362888766 10474392 1699822039 := bit_step 0 p23
  have p25 : Residue 5362888766 20948784 187238889 := bit_step 0 p24
  have p26 : Residue 5362888766 41897568 1766417503 := bit_step 0 p25
  have p27 : Residue 5362888766 83795136 1443850369 := bit_step 0 p26
  have p28 : Residue 5362888766 167590273 2292619659 := bit_step 1 p27
  have p29 : Residue 5362888766 335180547 1833518413 := bit_step 1 p28
  have p30 : Residue 5362888766 670361095 126698549 := bit_step 1 p29
  have p31 : Residue 5362888766 1340722191 310075957 := bit_step 1 p30
  have p32 : Residue 5362888766 2681444382 1211090435 := bit_step 0 p31
  have p33 : Residue 5362888766 5362888765 5362888765 := bit_step 1 p32
  exact p33

private theorem class25 : Residue 193264226 193264225 193264225 := by
  have p1 : Residue 193264226 1 3 := ⟨by decide⟩
  have p2 : Residue 193264226 2 9 := bit_step 0 p1
  have p3 : Residue 193264226 5 243 := bit_step 1 p2
  have p4 : Residue 193264226 11 177147 := bit_step 1 p3
  have p5 : Residue 193264226 23 23500765 := bit_step 1 p4
  have p6 : Residue 193264226 46 188343353 := bit_step 0 p5
  have p7 : Residue 193264226 92 143149685 := bit_step 0 p6
  have p8 : Residue 193264226 184 148884489 := bit_step 0 p7
  have p9 : Residue 193264226 368 110889067 := bit_step 0 p8
  have p10 : Residue 193264226 737 47701137 := bit_step 1 p9
  have p11 : Residue 193264226 1474 173639509 := bit_step 0 p10
  have p12 : Residue 193264226 2948 105062103 := bit_step 0 p11
  have p13 : Residue 193264226 5897 78054615 := bit_step 1 p12
  have p14 : Residue 193264226 11795 13051071 := bit_step 1 p13
  have p15 : Residue 193264226 23591 169404445 := bit_step 1 p14
  have p16 : Residue 193264226 47183 179832053 := bit_step 1 p15
  have p17 : Residue 193264226 94367 108145915 := bit_step 1 p16
  have p18 : Residue 193264226 188734 69944877 := bit_step 0 p17
  have p19 : Residue 193264226 377469 99560337 := bit_step 1 p18
  have p20 : Residue 193264226 754938 38511347 := bit_step 0 p19
  have p21 : Residue 193264226 1509876 69141911 := bit_step 0 p20
  have p22 : Residue 193264226 3019753 168541929 := bit_step 1 p21
  have p23 : Residue 193264226 6039507 116059323 := bit_step 1 p22
  have p24 : Residue 193264226 12079014 154743661 := bit_step 0 p23
  have p25 : Residue 193264226 24158028 96540403 := bit_step 0 p24
  have p26 : Residue 193264226 48316056 3730269 := bit_step 0 p25
  have p27 : Residue 193264226 96632112 75804587 := bit_step 0 p26
  have p28 : Residue 193264226 193264225 193264225 := bit_step 1 p27
  exact p28

private theorem class27 : Residue 28 27 27 := by
  have p1 : Residue 28 1 3 := ⟨by decide⟩
  have p2 : Residue 28 3 27 := bit_step 1 p1
  have p3 : Residue 28 6 1 := bit_step 0 p2
  have p4 : Residue 28 13 3 := bit_step 1 p3
  have p5 : Residue 28 27 27 := bit_step 1 p4
  exact p5

private theorem class37 : Residue 325963347734 325963347733 325963347733 := by
  have p1 : Residue 325963347734 1 3 := ⟨by decide⟩
  have p2 : Residue 325963347734 2 9 := bit_step 0 p1
  have p3 : Residue 325963347734 4 81 := bit_step 0 p2
  have p4 : Residue 325963347734 9 19683 := bit_step 1 p3
  have p5 : Residue 325963347734 18 387420489 := bit_step 0 p4
  have p6 : Residue 325963347734 37 93111336167 := bit_step 1 p5
  have p7 : Residue 325963347734 75 23069793215 := bit_step 1 p6
  have p8 : Residue 325963347734 151 260959857167 := bit_step 1 p7
  have p9 : Residue 325963347734 303 30062805045 := bit_step 1 p8
  have p10 : Residue 325963347734 607 305929599743 := bit_step 1 p9
  have p11 : Residue 325963347734 1214 72155272715 := bit_step 0 p10
  have p12 : Residue 325963347734 2428 315952728201 := bit_step 0 p11
  have p13 : Residue 325963347734 4857 262661642103 := bit_step 1 p12
  have p14 : Residue 325963347734 9714 286970811283 := bit_step 0 p13
  have p15 : Residue 325963347734 19428 111115510199 := bit_step 0 p14
  have p16 : Residue 325963347734 38857 127150982645 := bit_step 1 p15
  have p17 : Residue 325963347734 77715 209961783743 := bit_step 1 p16
  have p18 : Residue 325963347734 155431 210251238687 := bit_step 1 p17
  have p19 : Residue 325963347734 310862 76002859277 := bit_step 0 p18
  have p20 : Residue 325963347734 621725 137122206749 := bit_step 1 p19
  have p21 : Residue 325963347734 1243451 142369374755 := bit_step 1 p20
  have p22 : Residue 325963347734 2486902 321482740301 := bit_step 0 p21
  have p23 : Residue 325963347734 4973805 220298469671 := bit_step 1 p22
  have p24 : Residue 325963347734 9947611 286894689913 := bit_step 1 p23
  have p25 : Residue 325963347734 19895223 6267855529 := bit_step 1 p24
  have p26 : Residue 325963347734 39790447 195578601805 := bit_step 1 p25
  have p27 : Residue 325963347734 79580895 168912422243 := bit_step 1 p26
  have p28 : Residue 325963347734 159161790 278010065409 := bit_step 0 p27
  have p29 : Residue 325963347734 318323581 22033716713 := bit_step 1 p28
  have p30 : Residue 325963347734 636647163 49972070765 := bit_step 1 p29
  have p31 : Residue 325963347734 1273294327 39746562085 := bit_step 1 p30
  have p32 : Residue 325963347734 2546588654 210645846939 := bit_step 0 p31
  have p33 : Residue 325963347734 5093177308 120634669717 := bit_step 0 p32
  have p34 : Residue 325963347734 10186354616 271376164269 := bit_step 0 p33
  have p35 : Residue 325963347734 20372709233 233484610467 := bit_step 1 p34
  have p36 : Residue 325963347734 40745418466 212241375293 := bit_step 0 p35
  have p37 : Residue 325963347734 81490836933 255843915105 := bit_step 1 p36
  have p38 : Residue 325963347734 162981673866 212375166473 := bit_step 0 p37
  have p39 : Residue 325963347734 325963347733 325963347733 := bit_step 1 p38
  exact p39

private theorem class49 : Residue 17333186559533186 17333186559533185 17333186559533185 := by
  have p1 : Residue 17333186559533186 1 3 := ⟨by decide⟩
  have p2 : Residue 17333186559533186 3 27 := bit_step 1 p1
  have p3 : Residue 17333186559533186 7 2187 := bit_step 1 p2
  have p4 : Residue 17333186559533186 15 14348907 := bit_step 1 p3
  have p5 : Residue 17333186559533186 30 205891132094649 := bit_step 0 p4
  have p6 : Residue 17333186559533186 61 2820315798583977 := bit_step 1 p5
  have p7 : Residue 17333186559533186 123 16800003777333869 := bit_step 1 p6
  have p8 : Residue 17333186559533186 246 12549714863300275 := bit_step 0 p7
  have p9 : Residue 17333186559533186 492 4882374615605557 := bit_step 0 p8
  have p10 : Residue 17333186559533186 985 17044084856129437 := bit_step 1 p9
  have p11 : Residue 17333186559533186 1970 14215993538822573 := bit_step 0 p10
  have p12 : Residue 17333186559533186 3941 9682486286625461 := bit_step 1 p11
  have p13 : Residue 17333186559533186 7882 10775520165152251 := bit_step 0 p12
  have p14 : Residue 17333186559533186 15764 4671856583508307 := bit_step 0 p13
  have p15 : Residue 17333186559533186 31528 3049461382468163 := bit_step 0 p14
  have p16 : Residue 17333186559533186 63057 12012101901206737 := bit_step 1 p15
  have p17 : Residue 17333186559533186 126115 13411266662979649 := bit_step 1 p16
  have p18 : Residue 17333186559533186 252231 10644686532603157 := bit_step 1 p17
  have p19 : Residue 17333186559533186 504462 533182782199317 := bit_step 0 p18
  have p20 : Residue 17333186559533186 1008924 12549714863300275 := bit_step 0 p19
  have p21 : Residue 17333186559533186 2017848 4882374615605557 := bit_step 0 p20
  have p22 : Residue 17333186559533186 4035696 11459090471887541 := bit_step 0 p21
  have p23 : Residue 17333186559533186 8071393 16294122219296315 := bit_step 1 p22
  have p24 : Residue 17333186559533186 16142787 10705379898254599 := bit_step 1 p23
  have p25 : Residue 17333186559533186 32285575 16448340153832663 := bit_step 1 p24
  have p26 : Residue 17333186559533186 64571151 16781772420056819 := bit_step 1 p25
  have p27 : Residue 17333186559533186 129142303 17292833101200815 := bit_step 1 p26
  have p28 : Residue 17333186559533186 258284606 6715857000282531 := bit_step 0 p27
  have p29 : Residue 17333186559533186 516569213 630249228974899 := bit_step 1 p28
  have p30 : Residue 17333186559533186 1033138427 6695789550655213 := bit_step 1 p29
  have p31 : Residue 17333186559533186 2066276855 11828167226959979 := bit_step 1 p30
  have p32 : Residue 17333186559533186 4132553710 12227706582463137 := bit_step 0 p31
  have p33 : Residue 17333186559533186 8265107421 3558009597829219 := bit_step 1 p32
  have p34 : Residue 17333186559533186 16530214843 4201554931326721 := bit_step 1 p33
  have p35 : Residue 17333186559533186 33060429686 4780900310796637 := bit_step 0 p34
  have p36 : Residue 17333186559533186 66120859373 12650714902136269 := bit_step 1 p35
  have p37 : Residue 17333186559533186 132241718746 15783192422886721 := bit_step 0 p36
  have p38 : Residue 17333186559533186 264483437492 14622518542623519 := bit_step 0 p37
  have p39 : Residue 17333186559533186 528966874985 4107049357296161 := bit_step 1 p38
  have p40 : Residue 17333186559533186 1057933749971 5051332077405605 := bit_step 1 p39
  have p41 : Residue 17333186559533186 2115867499943 2692310502530759 := bit_step 1 p40
  have p42 : Residue 17333186559533186 4231734999886 13751873311933019 := bit_step 0 p41
  have p43 : Residue 17333186559533186 8463469999772 4275794407074913 := bit_step 0 p42
  have p44 : Residue 17333186559533186 16926939999544 6846849916777121 := bit_step 0 p43
  have p45 : Residue 17333186559533186 33853879999088 7658939133739985 := bit_step 0 p44
  have p46 : Residue 17333186559533186 67707759998176 9827637283864301 := bit_step 0 p45
  have p47 : Residue 17333186559533186 135415519996353 13384656750650549 := bit_step 1 p46
  have p48 : Residue 17333186559533186 270831039992706 15727249716108887 := bit_step 0 p47
  have p49 : Residue 17333186559533186 541662079985412 4072046449314107 := bit_step 0 p48
  have p50 : Residue 17333186559533186 1083324159970824 11546966555357717 := bit_step 0 p49
  have p51 : Residue 17333186559533186 2166648319941648 4186778788450653 := bit_step 0 p50
  have p52 : Residue 17333186559533186 4333296639883296 13397164895206221 := bit_step 0 p51
  have p53 : Residue 17333186559533186 8666593279766592 12294533034844619 := bit_step 0 p52
  have p54 : Residue 17333186559533186 17333186559533185 17333186559533185 := bit_step 1 p53
  exact p54

private theorem class51 : Residue 490372 490371 490371 := by
  have p1 : Residue 490372 1 3 := ⟨by decide⟩
  have p2 : Residue 490372 3 27 := bit_step 1 p1
  have p3 : Residue 490372 7 2187 := bit_step 1 p2
  have p4 : Residue 490372 14 369621 := bit_step 0 p3
  have p5 : Residue 490372 29 248859 := bit_step 1 p4
  have p6 : Residue 490372 59 262283 := bit_step 1 p5
  have p7 : Residue 490372 119 137091 := bit_step 1 p6
  have p8 : Residue 490372 239 325399 := bit_step 1 p7
  have p9 : Residue 490372 478 444729 := bit_step 0 p8
  have p10 : Residue 490372 957 59207 := bit_step 1 p9
  have p11 : Residue 490372 1915 379007 := bit_step 1 p10
  have p12 : Residue 490372 3831 4547 := bit_step 1 p11
  have p13 : Residue 490372 7662 79585 := bit_step 0 p12
  have p14 : Residue 490372 15324 127473 := bit_step 0 p13
  have p15 : Residue 490372 30648 399137 := bit_step 0 p14
  have p16 : Residue 490372 61296 250897 := bit_step 0 p15
  have p17 : Residue 490372 122592 250969 := bit_step 0 p16
  have p18 : Residue 490372 245185 293379 := bit_step 1 p17
  have p19 : Residue 490372 490371 490371 := bit_step 1 p18
  exact p19

private theorem class61 : Residue 24082420961006 24082420961005 24082420961005 := by
  have p1 : Residue 24082420961006 1 3 := ⟨by decide⟩
  have p2 : Residue 24082420961006 2 9 := bit_step 0 p1
  have p3 : Residue 24082420961006 5 243 := bit_step 1 p2
  have p4 : Residue 24082420961006 10 59049 := bit_step 0 p3
  have p5 : Residue 24082420961006 21 10460353203 := bit_step 1 p4
  have p6 : Residue 24082420961006 43 11293024251249 := bit_step 1 p5
  have p7 : Residue 24082420961006 87 4422428741255 := bit_step 1 p6
  have p8 : Residue 24082420961006 175 8767819006287 := bit_step 1 p7
  have p9 : Residue 24082420961006 350 22199542234559 := bit_step 0 p8
  have p10 : Residue 24082420961006 700 3762286638175 := bit_step 0 p9
  have p11 : Residue 24082420961006 1401 16223902646397 := bit_step 1 p10
  have p12 : Residue 24082420961006 2803 21973838474179 := bit_step 1 p11
  have p13 : Residue 24082420961006 5607 11298373536779 := bit_step 1 p12
  have p14 : Residue 24082420961006 11214 12374147271625 := bit_step 0 p13
  have p15 : Residue 24082420961006 22428 12789396709757 := bit_step 0 p14
  have p16 : Residue 24082420961006 44857 4422428741255 := bit_step 1 p15
  have p17 : Residue 24082420961006 89714 2922606335429 := bit_step 0 p16
  have p18 : Residue 24082420961006 179428 23873212213623 := bit_step 0 p17
  have p19 : Residue 24082420961006 358856 3019586373435 := bit_step 0 p18
  have p20 : Residue 24082420961006 717712 5613081788893 := bit_step 0 p19
  have p21 : Residue 24082420961006 1435424 15233538478593 := bit_step 0 p20
  have p22 : Residue 24082420961006 2870848 13443538450247 := bit_step 0 p21
  have p23 : Residue 24082420961006 5741696 19812320061269 := bit_step 0 p22
  have p24 : Residue 24082420961006 11483393 16569161431423 := bit_step 1 p23
  have p25 : Residue 24082420961006 22966786 18965058801541 := bit_step 0 p24
  have p26 : Residue 24082420961006 45933572 7082922887935 := bit_step 0 p25
  have p27 : Residue 24082420961006 91867145 1033274269083 := bit_step 1 p26
  have p28 : Residue 24082420961006 183734290 23235132351563 := bit_step 0 p27
  have p29 : Residue 24082420961006 367468581 16005236390233 := bit_step 1 p28
  have p30 : Residue 24082420961006 734937163 118851964975 := bit_step 1 p29
  have p31 : Residue 24082420961006 1469874326 19376439033449 := bit_step 0 p30
  have p32 : Residue 24082420961006 2939748652 21738696460817 := bit_step 0 p31
  have p33 : Residue 24082420961006 5879497304 1056708000617 := bit_step 0 p32
  have p34 : Residue 24082420961006 11758994609 11974571130279 := bit_step 1 p33
  have p35 : Residue 24082420961006 23517989219 4263530057611 := bit_step 1 p34
  have p36 : Residue 24082420961006 47035978439 12531252330433 := bit_step 1 p35
  have p37 : Residue 24082420961006 94071956878 7513259529583 := bit_step 0 p36
  have p38 : Residue 24082420961006 188143913757 8730334482611 := bit_step 1 p37
  have p39 : Residue 24082420961006 376287827515 22661971247203 := bit_step 1 p38
  have p40 : Residue 24082420961006 752575655031 6701892370321 := bit_step 1 p39
  have p41 : Residue 24082420961006 1505151310062 9201237892825 := bit_step 0 p40
  have p42 : Residue 24082420961006 3010302620125 7034215394303 := bit_step 1 p41
  have p43 : Residue 24082420961006 6020605240251 21165636369159 := bit_step 1 p42
  have p44 : Residue 24082420961006 12041210480502 12417622865203 := bit_step 0 p43
  have p45 : Residue 24082420961006 24082420961005 24082420961005 := bit_step 1 p44
  exact p45

private theorem witness (k r : ℕ) (hk : 0 < k) (hr : k % 72 = r)
    (hc : Residue (k+1) k k) :
    ∃ j : ℕ, 0 < j ∧ (j+1) ∣ 3^j+1 ∧ j % 72 = r :=
  ⟨k, hk, divides_of_residue hc, hr⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a370578.main := by
  intro r hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness 1 1 (by decide) (by decide) class1
  · exact witness 3 3 (by decide) (by decide) class3
  · exact witness 5362888765 13 (by decide) (by decide) class13
  · exact witness 193264225 25 (by decide) (by decide) class25
  · exact witness 27 27 (by decide) (by decide) class27
  · exact witness 325963347733 37 (by decide) (by decide) class37
  · exact witness 17333186559533185 49 (by decide) (by decide) class49
  · exact witness 490371 51 (by decide) (by decide) class51
  · exact witness 24082420961005 61 (by decide) (by decide) class61
