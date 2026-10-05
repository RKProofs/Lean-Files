import SSPLean.K3AllStagesCore

/-!
# Exclusion of the interior KKT point for three stages

For `n = 3` the general elimination certificate collapses to a short identity.
The return-side polynomial is affine in `X = aY`; after eliminating `X`, the
terminal-side polynomial has a strictly positive constant and linear part.
-/

set_option autoImplicit false

namespace SSP.K3AllStages

private noncomputable def returnThree (T X q : ℝ) : ℝ :=
  -15*T^3*q-260*T^2*q+252*T*X*q-15*T*X+320*T*q-500*T+492*X+320

private noncomputable def terminalThree (T X q : ℝ) : ℝ :=
  12*T^3*q^2+15*T^2*X*q+400*T^2*q^2-228*T^2*q
    +260*T*X*q+480*T*q+15*X^2+20*X+80

private theorem terminalThree_pos_of_returnThree_pos
    (T X q : ℝ) (hT : 0 ≤ T) (hq : 0 ≤ q)
    (hR : 0 < returnThree T X q) :
    0 < terminalThree T X q := by
  let M := 3*(84*T*q-5*T+164)
  let J := 252*T^3*q^2+15*T^3*q+4368*T^2*q^2+752*T^2*q
    +8224*T*q+980*T+16
  let H := 21*T^2*q+700*T*q+1340
  let G := 75*T^2+1008*T*q-20*T+368
  have hJ : 0 < J := by dsimp [J]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hG : 0 < G := by
    dsimp [G]
    nlinarith [sq_nonneg (15*T-2)]
  have hid : M^2*terminalThree T X q =
      15*(returnThree T X q)^2+15*J*returnThree T X q
        +36*(T*q+1)^2*H*G := by
    dsimp [M, J, H, G, returnThree, terminalThree]
    ring
  have hrhs : 0 < 15*(returnThree T X q)^2+15*J*returnThree T X q
      +36*(T*q+1)^2*H*G := by
    have hlast : 0 < 36*(T*q+1)^2*H*G := by positivity
    positivity
  have hprod : 0 < M^2*terminalThree T X q := by rw [hid]; exact hrhs
  by_contra hnot
  have hS : terminalThree T X q ≤ 0 := le_of_not_gt hnot
  have := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg M) hS
  linarith

/-- Specialized normalized side implication.  This is the only fact needed
to rule out the strict interior KKT alternative at `n = 3`. -/
theorem uniformTerminalSide_three_nonneg_of_returnSide_pos
    (a T Y q : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q)
    (hreturn : 0 < uniformReturnSide 3 a T Y q) :
    0 ≤ uniformTerminalSide 3 a T Y q := by
  let X := a*Y
  let Z := (1-a)*Y
  have hX : 0 < X := by dsimp [X]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hreturn' : 0 < returnThree T X q := by
    rw [show uniformReturnSide 3 a T Y q = returnThree T X q by
      dsimp [X, returnThree]
      unfold uniformReturnSide uniformReturnM uniformReturnK
      ring] at hreturn
    exact hreturn
  have hbase := terminalThree_pos_of_returnThree_pos T X q hT.le hq.le hreturn'
  have hsplit : uniformTerminalSide 3 a T Y q =
      terminalThree T X q+Z*(15*T^2*q+500*T*q+15*X+500) := by
    dsimp [X, Z, terminalThree]
    unfold uniformTerminalSide uniformTerminalL uniformTerminalS0
    ring
  rw [hsplit]
  positivity

end SSP.K3AllStages
