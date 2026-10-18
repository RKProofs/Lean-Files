import SSPLean.K3AllStagesPositiveSlopeLargeBase

/-! Extract the X coefficients before substituting the chart parameters. -/
set_option autoImplicit false
namespace SSP.K3AllStages

noncomputable def uniformFaceACoreX0AtOne (n T : ℝ) : ℝ :=
  (((-1 + n + (-1*T))^2)*(2 + n)*(-12 + (-36*(n^2)) + (12*(n^3)) + (36*n) + ((T^4)*(n^2)) + ((T^4)*(n^3)) + (-48*T*(n^2)) + (-12*n*(T^2)) + (-12*(T^2)*(n^2)) + (-8*n*(T^3)) + (8*(T^3)*(n^3)) + (24*T*n) + (24*T*(n^3)) + (24*(T^2)*(n^3))))

theorem uniformFaceACoreXC0_at_one (n T : ℝ) :
    uniformFaceACoreXC0 n T 1 = uniformFaceACoreX0AtOne n T := by
  unfold uniformFaceACoreXC0 uniformFaceACore uniformFaceACoreX0AtOne
  ring

noncomputable def uniformFaceACoreX1AtOne (n T : ℝ) : ℝ :=
  (n*(40 + (-144*n) + (-64*(n^3)) + (-24*(n^4)) + (16*(T^3)) + (16*(n^5)) + (32*(T^2)) + (56*T) + (176*(n^2)) + (-204*T*n) + (-104*T*(n^3)) + (-80*(T^2)*(n^3)) + (-62*(T^3)*(n^3)) + (-56*n*(T^2)) + (-24*T*(n^4)) + (-14*(T^3)*(n^2)) + (-9*(T^4)*(n^3)) + (-3*(T^4)*(n^2)) + (-2*(T^3)*(n^4)) + (2*(T^3)*(n^5)) + (16*(T^2)*(n^5)) + (18*n*(T^4)) + (20*T*(n^5)) + (20*(T^2)*(n^4)) + (60*n*(T^3)) + (68*(T^2)*(n^2)) + (256*T*(n^2))))

theorem uniformFaceACoreXC1_at_one (n T : ℝ) :
    uniformFaceACoreXC1 n T 1 = uniformFaceACoreX1AtOne n T := by
  unfold uniformFaceACoreXC1 uniformFaceACore uniformFaceACoreX1AtOne
  ring

noncomputable def uniformFaceACoreX2AtOne (n T : ℝ) : ℝ :=
  ((n^2)*(-1 + n)*(20 + (-32*n) + (4*(n^2)) + (8*(n^3)) + (26*(T^2)) + (32*T) + (-44*T*n) + (4*T*(n^2)) + (5*(T^2)*(n^3)) + (8*T*(n^3)) + (13*n*(T^2)) + (16*(T^2)*(n^2))))

theorem uniformFaceACoreXC2_at_one (n T : ℝ) :
    uniformFaceACoreXC2 n T 1 = uniformFaceACoreX2AtOne n T := by
  unfold uniformFaceACoreXC2 uniformFaceACore uniformFaceACoreX2AtOne
  ring

noncomputable def uniformFaceACoreX3AtOne (n _T : ℝ) : ℝ :=
  (6*(n^3)*(-1 + n))

theorem uniformFaceACoreXC3_at_one (n _T : ℝ) :
    uniformFaceACoreXC3 n _T 1 = uniformFaceACoreX3AtOne n _T := by
  unfold uniformFaceACoreXC3 uniformFaceACore uniformFaceACoreX3AtOne
  ring



noncomputable def LargeLNumerator (m s : ℝ) : ℝ :=
  2*m^6 + 72*m^5 + m^4*s + 1050*m^4 + 24*m^3*s + 7902*m^3 + 208*m^2*s + 32188*m^2 + 762*m*s + 66930*m + 972*s + 55440

theorem LargeL_eq (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformFaceACurrentM (m+4) (uniformFaceANonposT m s) 1 =
      LargeLNumerator m s / (m + 6) := by
  have hT := uniformFaceANonposT_pos m s hm hs
  have hD := uniformFaceAPositiveD_pos m s hm hs
  unfold uniformFaceACurrentM uniformReturnM
  unfold uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP
  unfold LargeLNumerator
  field_simp
  ring

noncomputable def LargeK0Numerator (m s : ℝ) : ℝ :=
  (m^3 + 18*m^2 + m*s + 101*m + 6*s + 168)*(4*m^6 + 132*m^5 + 4*m^4*s + 1766*m^4 + 86*m^3*s + 12234*m^3 + m^2*s^2 + 668*m^2*s + 46170*m^2 + 10*m*s^2 + 2210*m*s + 89802*m + 24*s^2 + 2616*s + 70308)

theorem LargeK0_eq (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformFaceACurrentK (m+4) (uniformFaceANonposT m s) (uniformFaceAPositiveQ0 m s) =
      LargeK0Numerator m s / ((m + 3)*(m + 7)*(m + 8)) := by
  have hT := uniformFaceANonposT_pos m s hm hs
  have hD := uniformFaceAPositiveD_pos m s hm hs
  unfold uniformFaceACurrentK uniformReturnK uniformFaceAPositiveQ0 uniformFaceAPositiveD
  unfold uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP
  unfold LargeK0Numerator
  field_simp
  ring

noncomputable def LargeK1Numerator (m s : ℝ) : ℝ :=
  12*m^10 + 688*m^9 + 16*m^8*s + 17492*m^8 + 728*m^7*s + 259480*m^7 + 7*m^6*s^2 + 14260*m^6*s + 2484866*m^6 + 236*m^5*s^2 + 156884*m^5*s + 16036586*m^5 + m^4*s^3 + 3261*m^4*s^2 + 1058970*m^4*s + 70572818*m^4 + 22*m^3*s^3 + 23604*m^3*s^2 + 4484910*m^3*s + 208946462*m^3 + 180*m^2*s^3 + 94212*m^2*s^2 + 11622672*m^2*s + 398062260*m^2 + 648*m*s^3 + 196128*m*s^2 + 16830720*m*s + 440450568*m + 864*s^3 + 165888*s^2 + 10418544*s + 214921728

theorem LargeK1_eq (m s : ℝ) (hm : 0 ≤ m) (hs : 0 ≤ s) :
    uniformFaceACurrentK (m+4) (uniformFaceANonposT m s) 1 =
      LargeK1Numerator m s / ((m + 6)^2) := by
  have hT := uniformFaceANonposT_pos m s hm hs
  have hD := uniformFaceAPositiveD_pos m s hm hs
  unfold uniformFaceACurrentK uniformReturnK
  unfold uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP
  unfold LargeK1Numerator
  field_simp
  ring



noncomputable def LargeX0Numerator (m s : ℝ) : ℝ :=
  (2*m^3 + 35*m^2 + m*s + 191*m + 6*s + 312)^2*(16*m^15 + 1360*m^14 + 32*m^13*s + 53440*m^13 + 2336*m^12*s + 1287360*m^12 + 24*m^11*s^2 + 77920*m^11*s + 21256672*m^11 + 1464*m^10*s^2 + 1572064*m^10*s + 254763152*m^10 + 8*m^9*s^3 + 40176*m^9*s^2 + 21397536*m^9*s + 2288936032*m^9 + 392*m^8*s^3 + 654576*m^8*s^2 + 207430224*m^8*s + 15694427200*m^8 + m^7*s^4 + 8456*m^7*s^3 + 7033464*m^7*s^2 + 1473019016*m^7*s + 82780409692*m^7 + 37*m^6*s^4 + 105384*m^6*s^3 + 52319844*m^6*s^2 + 7756217840*m^6*s + 335802574236*m^6 + 584*m^5*s^4 + 836048*m^5*s^3 + 274853484*m^5*s^2 + 30274988488*m^5*s + 1038890259748*m^5 + 5096*m^4*s^4 + 4377424*m^4*s^3 + 1019397432*m^4*s^2 + 86498716528*m^4*s + 2406813813188*m^4 + 26544*m^3*s^4 + 15121632*m^3*s^3 + 2615082624*m^3*s^2 + 175791590880*m^3*s + 4041296460096*m^3 + 82512*m^2*s^4 + 33220800*m^2*s^3 + 4417767648*m^2*s^2 + 240604677504*m^2*s + 4642610843952*m^2 + 141696*m*s^4 + 42097536*m*s^3 + 4421884608*m*s^2 + 198753810048*m*s + 3262656965760*m + 103680*s^4 + 23431680*s^3 + 1986114816*s^2 + 74830293504*s + 1057378204224)

theorem LargeX0_eq (m s : ℝ) (hm : 0 ≤ m) :
    uniformFaceACoreX0AtOne (m+4) (uniformFaceANonposT m s) =
      LargeX0Numerator m s / ((m + 6)^5) := by
  unfold uniformFaceACoreX0AtOne uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP LargeX0Numerator
  field_simp
  ring

noncomputable def LargeX1Numerator (m s : ℝ) : ℝ :=
  -(m + 4)*(128*m^15 + 10880*m^14 + 264*m^13*s + 426768*m^13 + 19224*m^12*s + 10244144*m^12 + 204*m^11*s^2 + 638312*m^11*s + 168235464*m^11 + 12372*m^10*s^2 + 12791720*m^10*s + 2001643088*m^10 + 70*m^9*s^3 + 336692*m^9*s^2 + 172554188*m^9*s + 17818950912*m^9 + 3394*m^8*s^3 + 5425220*m^8*s^2 + 1654000072*m^8*s + 120825652896*m^8 + 9*m^7*s^4 + 72206*m^7*s^3 + 57487724*m^7*s^2 + 11586410768*m^7*s + 629039018184*m^7 + 327*m^6*s^4 + 884286*m^6*s^3 + 420447864*m^6*s^2 + 60038406264*m^6*s + 2513945876832*m^6 + 5046*m^5*s^4 + 6866300*m^5*s^3 + 2164801116*m^5*s^2 + 230071478436*m^5*s + 7648476206560*m^5 + 42816*m^4*s^4 + 35031984*m^4*s^3 + 7843613112*m^4*s^2 + 643821975168*m^4*s + 17395250099088*m^4 + 215424*m^3*s^4 + 117351936*m^3*s^3 + 19591863120*m^3*s^2 + 1278633224304*m^3*s + 28628043749280*m^3 + 641520*m^2*s^4 + 248691168*m^2*s^3 + 32120569440*m^2*s^2 + 1706539179168*m^2*s + 32186746093104*m^2 + 1044576*m*s^4 + 302304960*m*s^3 + 31103004672*m*s^2 + 1371965257728*m*s + 22108595966496*m + 715392*s^4 + 160496640*s^3 + 13475185920*s^2 + 501842542464*s + 6995236070016)

theorem LargeX1_eq (m s : ℝ) (hm : 0 ≤ m) :
    uniformFaceACoreX1AtOne (m+4) (uniformFaceANonposT m s) =
      LargeX1Numerator m s / ((m + 6)^4) := by
  unfold uniformFaceACoreX1AtOne uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP LargeX1Numerator
  field_simp
  ring

noncomputable def LargeX2Numerator (m s : ℝ) : ℝ :=
  (m + 3)*(m + 4)^2*(20*m^9 + 1024*m^8 + 20*m^7*s + 22964*m^7 + 784*m^6*s + 295960*m^6 + 5*m^5*s^2 + 12988*m^5*s + 2415152*m^5 + 136*m^4*s^2 + 117920*m^4*s + 12938620*m^4 + 1473*m^3*s^2 + 633996*m^3*s + 45496140*m^3 + 7962*m^2*s^2 + 2019444*m^2*s + 101222988*m^2 + 21564*m*s^2 + 3528576*m*s + 129235860*m + 23544*s^2 + 2605392*s + 72092808)

theorem LargeX2_eq (m s : ℝ) (hm : 0 ≤ m) :
    uniformFaceACoreX2AtOne (m+4) (uniformFaceANonposT m s) =
      LargeX2Numerator m s / ((m + 6)^2) := by
  unfold uniformFaceACoreX2AtOne uniformFaceANonposT uniformFaceANonposZ uniformFaceANonposP LargeX2Numerator
  field_simp
  ring

noncomputable def LargeX3Numerator (m _s : ℝ) : ℝ :=
  6*(m + 3)*(m + 4)^3

theorem LargeX3_eq (m s : ℝ) (_hm : 0 ≤ m) :
    uniformFaceACoreX3AtOne (m+4) (uniformFaceANonposT m s) =
      LargeX3Numerator m s / (1) := by
  unfold uniformFaceACoreX3AtOne LargeX3Numerator
  ring


noncomputable def B3Power (i : Fin 4) (m s : ℝ) : ℝ :=
  let l := LargeLNumerator m s / (m+6)
  let k := LargeK0Numerator m s / ((m+3)*(m+7)*(m+8))
  let h := (LargeK1Numerator m s / (m+6)^2 - k)
  let a := (m+4)^3*l^3*(LargeX0Numerator m s / ((m + 6)^5))
  let b := (m+4)^2*l^2*(LargeX1Numerator m s / ((m + 6)^4))
  let c := (m+4)*l*(LargeX2Numerator m s / ((m + 6)^2))
  let d := LargeX3Numerator m s / (1)
  ![d*k^3, c*k^2+3*d*k^2*h, b*k+2*c*k*h+3*d*k*h^2, a+b*h+c*h^2+d*h^3] i

noncomputable def B3ShiftCoefficient (i : Fin 4) (m s : ℝ) : ℝ :=
  ![B3Power 0 m s / 1 + B3Power 1 m s / 2 + B3Power 2 m s / 4 + B3Power 3 m s / 8,
    B3Power 1 m s / 2 + B3Power 2 m s / 2 + 3*B3Power 3 m s / 8,
    B3Power 2 m s / 4 + 3*B3Power 3 m s / 8,
    B3Power 3 m s / 8] i



noncomputable def ReducedX0 (m s : ℝ) : ℝ :=
  (2*m^3 + 35*m^2 + m*s + 191*m + 6*s + 312)^2*(16*m^15 + 1360*m^14 + 32*m^13*s + 53440*m^13 + 2336*m^12*s + 1287360*m^12 + 24*m^11*s^2 + 77920*m^11*s + 21256672*m^11 + 1464*m^10*s^2 + 1572064*m^10*s + 254763152*m^10 + 8*m^9*s^3 + 40176*m^9*s^2 + 21397536*m^9*s + 2288936032*m^9 + 392*m^8*s^3 + 654576*m^8*s^2 + 207430224*m^8*s + 15694427200*m^8 + m^7*s^4 + 8456*m^7*s^3 + 7033464*m^7*s^2 + 1473019016*m^7*s + 82780409692*m^7 + 37*m^6*s^4 + 105384*m^6*s^3 + 52319844*m^6*s^2 + 7756217840*m^6*s + 335802574236*m^6 + 584*m^5*s^4 + 836048*m^5*s^3 + 274853484*m^5*s^2 + 30274988488*m^5*s + 1038890259748*m^5 + 5096*m^4*s^4 + 4377424*m^4*s^3 + 1019397432*m^4*s^2 + 86498716528*m^4*s + 2406813813188*m^4 + 26544*m^3*s^4 + 15121632*m^3*s^3 + 2615082624*m^3*s^2 + 175791590880*m^3*s + 4041296460096*m^3 + 82512*m^2*s^4 + 33220800*m^2*s^3 + 4417767648*m^2*s^2 + 240604677504*m^2*s + 4642610843952*m^2 + 141696*m*s^4 + 42097536*m*s^3 + 4421884608*m*s^2 + 198753810048*m*s + 3262656965760*m + 103680*s^4 + 23431680*s^3 + 1986114816*s^2 + 74830293504*s + 1057378204224)

theorem LargeX0_factor (m s : ℝ) :
    LargeX0Numerator m s = (m+4)^0*ReducedX0 m s := by
  unfold LargeX0Numerator ReducedX0
  ring

noncomputable def ReducedX1 (m s : ℝ) : ℝ :=
  -128*m^15 - 10880*m^14 - 264*m^13*s - 426768*m^13 - 19224*m^12*s - 10244144*m^12 - 204*m^11*s^2 - 638312*m^11*s - 168235464*m^11 - 12372*m^10*s^2 - 12791720*m^10*s - 2001643088*m^10 - 70*m^9*s^3 - 336692*m^9*s^2 - 172554188*m^9*s - 17818950912*m^9 - 3394*m^8*s^3 - 5425220*m^8*s^2 - 1654000072*m^8*s - 120825652896*m^8 - 9*m^7*s^4 - 72206*m^7*s^3 - 57487724*m^7*s^2 - 11586410768*m^7*s - 629039018184*m^7 - 327*m^6*s^4 - 884286*m^6*s^3 - 420447864*m^6*s^2 - 60038406264*m^6*s - 2513945876832*m^6 - 5046*m^5*s^4 - 6866300*m^5*s^3 - 2164801116*m^5*s^2 - 230071478436*m^5*s - 7648476206560*m^5 - 42816*m^4*s^4 - 35031984*m^4*s^3 - 7843613112*m^4*s^2 - 643821975168*m^4*s - 17395250099088*m^4 - 215424*m^3*s^4 - 117351936*m^3*s^3 - 19591863120*m^3*s^2 - 1278633224304*m^3*s - 28628043749280*m^3 - 641520*m^2*s^4 - 248691168*m^2*s^3 - 32120569440*m^2*s^2 - 1706539179168*m^2*s - 32186746093104*m^2 - 1044576*m*s^4 - 302304960*m*s^3 - 31103004672*m*s^2 - 1371965257728*m*s - 22108595966496*m - 715392*s^4 - 160496640*s^3 - 13475185920*s^2 - 501842542464*s - 6995236070016

theorem LargeX1_factor (m s : ℝ) :
    LargeX1Numerator m s = (m+4)^1*ReducedX1 m s := by
  unfold LargeX1Numerator ReducedX1
  ring

noncomputable def ReducedX2 (m s : ℝ) : ℝ :=
  (m + 3)*(20*m^9 + 1024*m^8 + 20*m^7*s + 22964*m^7 + 784*m^6*s + 295960*m^6 + 5*m^5*s^2 + 12988*m^5*s + 2415152*m^5 + 136*m^4*s^2 + 117920*m^4*s + 12938620*m^4 + 1473*m^3*s^2 + 633996*m^3*s + 45496140*m^3 + 7962*m^2*s^2 + 2019444*m^2*s + 101222988*m^2 + 21564*m*s^2 + 3528576*m*s + 129235860*m + 23544*s^2 + 2605392*s + 72092808)

theorem LargeX2_factor (m s : ℝ) :
    LargeX2Numerator m s = (m+4)^2*ReducedX2 m s := by
  unfold LargeX2Numerator ReducedX2
  ring

noncomputable def ReducedX3 (m _s : ℝ) : ℝ :=
  6*(m + 3)

theorem LargeX3_factor (m s : ℝ) :
    LargeX3Numerator m s = (m+4)^3*ReducedX3 m s := by
  unfold LargeX3Numerator ReducedX3
  ring

noncomputable def ReducedH (m s : ℝ) : ℝ :=
  6*m^7 + 236*m^6 + 5*m^5*s + 3896*m^5 + 138*m^4*s + 34932*m^4 + m^3*s^2 + 1489*m^3*s + 183370*m^3 + 16*m^2*s^2 + 7828*m^2*s + 562504*m^2 + 84*m*s^2 + 19980*m*s + 932280*m + 144*s^2 + 19728*s + 643608

theorem LargeH_factor (m s : ℝ) (hm : 0 ≤ m) :
    LargeK1Numerator m s / (m+6)^2 - LargeK0Numerator m s / ((m+3)*(m+7)*(m+8)) =
      LargeLNumerator m s * ReducedH m s / ((m+3)*(m+6)^2*(m+7)*(m+8)) := by
  unfold LargeK1Numerator LargeK0Numerator LargeLNumerator ReducedH
  field_simp
  ring

end SSP.K3AllStages
