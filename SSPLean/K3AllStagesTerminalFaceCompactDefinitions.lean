import SSPLean.K3AllStagesTerminalFaceBase
set_option autoImplicit false
namespace SSP.K3AllStages
/-! ### The compact terminal-scale range -/

noncomputable def sampledBern3C1 (f0 f1 f2 f3 : ℝ) : ℝ :=
  (7*f0 + 18*f1 - 9*f2 + 2*f3) / 18

noncomputable def sampledBern3C2 (f0 f1 f2 f3 : ℝ) : ℝ :=
  (2*f0 + 21*f1 - 6*f2 + f3) / 18

noncomputable def uniformFaceBCoreB1TC1 (n a Y : ℝ) : ℝ :=
  (uniformFaceBCoreB1 n a 0 Y + 4*uniformFaceBCoreB1 n a 1 Y
    - uniformFaceBCoreB1 n a 2 Y) / 4

noncomputable def sampledBern4C1 (f0 f1 f2 f3 f4 : ℝ) : ℝ :=
  (23*f0 + 48*f1 - 36*f2 + 16*f3 - 3*f4) / 48

noncomputable def sampledBern4C2 (f0 f1 f2 f3 f4 : ℝ) : ℝ :=
  (29*f0 + 184*f1 - 102*f2 + 40*f3 - 7*f4) / 144

noncomputable def sampledBern4C3 (f0 f1 f2 f3 f4 : ℝ) : ℝ :=
  (3*f0 + 58*f1 - 18*f2 + 6*f3 - f4) / 48

noncomputable def uniformFaceBCoreB2TC1 (n a Y : ℝ) : ℝ :=
  sampledBern4C1 (uniformFaceBCoreB2 n a 0 Y)
    (uniformFaceBCoreB2 n a 1 Y) (uniformFaceBCoreB2 n a 2 Y)
    (uniformFaceBCoreB2 n a 3 Y) (uniformFaceBCoreB2 n a 4 Y)

noncomputable def uniformFaceBCoreB2TC2 (n a Y : ℝ) : ℝ :=
  sampledBern4C2 (uniformFaceBCoreB2 n a 0 Y)
    (uniformFaceBCoreB2 n a 1 Y) (uniformFaceBCoreB2 n a 2 Y)
    (uniformFaceBCoreB2 n a 3 Y) (uniformFaceBCoreB2 n a 4 Y)

noncomputable def uniformFaceBCoreB2TC3 (n a Y : ℝ) : ℝ :=
  sampledBern4C3 (uniformFaceBCoreB2 n a 0 Y)
    (uniformFaceBCoreB2 n a 1 Y) (uniformFaceBCoreB2 n a 2 Y)
    (uniformFaceBCoreB2 n a 3 Y) (uniformFaceBCoreB2 n a 4 Y)

end SSP.K3AllStages
