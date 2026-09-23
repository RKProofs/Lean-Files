import SSPLean.K3AllStagesFaceNonposCore

set_option autoImplicit false

namespace SSP.K3AllStages

open SSP.K3S4Renewal
open SSP.K3S4KKT

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The terminal-face discriminant is completely independent of the return
mixture weight in normalized coordinates. -/
theorem sharpFaceB_mixture_coordinates
    (n a T Y p q : ℝ) (hn0 : n ≠ 0) (hn1 : n-1 ≠ 0)
    (hnp1 : n+1 ≠ 0) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) (hsum : p*Y+a ≠ 0)
    (hsum1 : Y+a ≠ 0) :
    sharpFaceB n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) =
      uniformSharpFaceB n a T Y q := by
  have hgap1 := sharpGap_mixture_coordinates n a T Y 1 q hn0 hn1 hnp1
    hT hY (by norm_num) hq (by simpa using hsum1) hsum1
  have hgrad1 := sharpGradB_mixture_coordinates n a T Y 1 q hn0 hn1 hnp1
    hT hY (by norm_num) hq (by simpa using hsum1)
  have hhbb1 := excursionHBB_mixture_coordinates n a T Y 1 q hn0 hn1 hnp1
    hT hY (by norm_num) hq (by simpa using hsum1)
  norm_num at hgap1 hgrad1 hhbb1
  unfold uniformSharpFaceB sharpFaceB
  rw [sharpGap_mixture_coordinates n a T Y p q hn0 hn1 hnp1 hT hY hp hq hsum hsum1,
    sharpGradB_mixture_coordinates n a T Y p q hn0 hn1 hnp1 hT hY hp hq hsum,
    excursionHBB_mixture_coordinates n a T Y p q hn0 hn1 hnp1 hT hY hp hq hsum,
    hgap1, hgrad1, hhbb1]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- Denominator-clearing identity connecting the terminal-face discriminant
to its compact polynomial numerator. -/
theorem uniformSharpFaceB_num_identity
    (n a T Y q : ℝ) (hn0 : n ≠ 0) (hn1 : n-1 ≠ 0)
    (hnp1 : n+1 ≠ 0) (hT : T ≠ 0) (hY : Y ≠ 0)
    (hq : q ≠ 0) (hsum : Y+a ≠ 0) :
    T^2*n*q*(n+1)*(n-1)^4*uniformSharpFaceB n a T Y q =
      4*uniformFaceBNum n a T Y q := by
  have hgap1 := sharpGap_mixture_coordinates n a T Y 1 q hn0 hn1 hnp1
    hT hY (by norm_num) hq (by simpa using hsum) hsum
  have hgrad1 := sharpGradB_mixture_coordinates n a T Y 1 q hn0 hn1 hnp1
    hT hY (by norm_num) hq (by simpa using hsum)
  have hhbb1 := excursionHBB_mixture_coordinates n a T Y 1 q hn0 hn1 hnp1
    hT hY (by norm_num) hq (by simpa using hsum)
  norm_num at hgap1 hgrad1 hhbb1
  unfold uniformSharpFaceB sharpFaceB
  rw [hgap1, hgrad1, hhbb1]
  have hgap := uniformSharpGap_eq_cornerPoly n a T Y q
    hn0 hn1 hnp1 hT hY hq hsum
  unfold uniformFaceBNum
  field_simp [hn0, hn1, hnp1, hT, hY, hq]
  rw [← hgap]
  ring

/-- Positivity of the polynomial numerator implies the normalized
terminal-face certificate in the genuine interior. -/
theorem uniformSharpFaceB_nonneg_of_num
    (n a T Y q : ℝ) (hn : 4 ≤ n)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q)
    (hsum : Y+a ≠ 0) (hnum : 0 ≤ uniformFaceBNum n a T Y q) :
    0 ≤ uniformSharpFaceB n a T Y q := by
  have hid := uniformSharpFaceB_num_identity n a T Y q
    (by linarith) (by linarith) (by linarith) hT.ne' hY.ne' hq.ne' hsum
  have hnpos : 0 < n := by linarith
  have hn1pos : 0 < n-1 := by linarith
  have hnp1pos : 0 < n+1 := by linarith
  have hscale : 0 < T^2*n*q*(n+1)*(n-1)^4 := by positivity
  have hrhs : 0 ≤ 4*uniformFaceBNum n a T Y q := by positivity
  rw [← hid] at hrhs
  exact (mul_nonneg_iff_of_pos_left hscale).mp hrhs

theorem uniform_sideA_polynomial_identity (n a T Y q : ℝ) :
    uniformHAA n a T Y q*uniformGradB n a T Y q
        -a*(n+3)*Y*n*(n+1)*uniformGradA n a T Y q =
      (n+2)*uniformSideFactor n a T Y q*uniformReturnSide n a T Y q := by
  unfold uniformHAA uniformGradA uniformGradB uniformSideFactor
  unfold uniformReturnSide uniformReturnM uniformReturnK
  ring

theorem uniform_sideB_polynomial_identity (n a T Y q : ℝ) :
    uniformHBB n a T Y q*uniformGradA n a T Y q
        -(n+3)*uniformGradB n a T Y q*T^2*n*q*(n+1) =
      (n+2)*uniformSideFactor n a T Y q*uniformTerminalSide n a T Y q := by
  unfold uniformHBB uniformGradA uniformGradB uniformSideFactor
  unfold uniformTerminalSide uniformTerminalL uniformTerminalS0
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- Exact return-side normalization at the sharp third-moment corner. -/
theorem sharpSideA_mixture_coordinates
    (n a T Y p q : ℝ) (hn0 : n ≠ 0) (hn1 : n-1 ≠ 0) (hnp1 : n+1 ≠ 0)
    (hT : T ≠ 0) (hY : Y ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hsum : p*Y+a ≠ 0) :
    Y^3*n*p^2*(n-1)^2*(n+1)*
      sharpSideA n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) =
      -4*a*(n+2)*uniformSideFactor n a T Y q*uniformReturnSide n a T Y q := by
  unfold sharpSideA
  rw [sharpGradA_mixture_coordinates n a T Y p q hn0 hn1 hnp1 hT hY hp hq hsum,
    sharpGradB_mixture_coordinates n a T Y p q hn0 hn1 hnp1 hT hY hp hq hsum,
    excursionHAA_mixture_coordinates n a T Y p q hn0 hn1 hnp1 hY hp hsum]
  unfold excursionHAB
  field_simp [hn0, hn1, hnp1, hT, hY, hp, hq]
  linear_combination -4*a*uniform_sideA_polynomial_identity n a T Y q

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- Exact terminal-side normalization at the sharp third-moment corner. -/
theorem sharpSideB_mixture_coordinates
    (n a T Y p q : ℝ) (hn0 : n ≠ 0) (hn1 : n-1 ≠ 0) (hnp1 : n+1 ≠ 0)
    (hT : T ≠ 0) (hY : Y ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hsum : p*Y+a ≠ 0) :
    T^2*Y*n*p*q*(n-1)^2*(n+1)*
      sharpSideB n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) =
      4*a*(n+2)*uniformSideFactor n a T Y q*uniformTerminalSide n a T Y q := by
  unfold sharpSideB
  rw [sharpGradA_mixture_coordinates n a T Y p q hn0 hn1 hnp1 hT hY hp hq hsum,
    sharpGradB_mixture_coordinates n a T Y p q hn0 hn1 hnp1 hT hY hp hq hsum,
    excursionHBB_mixture_coordinates n a T Y p q hn0 hn1 hnp1 hT hY hp hq hsum]
  unfold excursionHAB
  field_simp [hn0, hn1, hnp1, hT, hY, hp, hq]
  linear_combination 4*a*uniform_sideB_polynomial_identity n a T Y q

/-- Reduction of the sharp corner to the normalized five-variable box. -/
theorem sharpGap_nonneg_of_uniform
    (n a T Y p q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (hT : 0 < T)
    (hY : 0 < Y) (hp : 0 < p) (hq : 0 < q)
    (hpoly : 0 ≤ uniformSharpGap n a T Y q) :
    0 ≤ sharpGap n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) := by
  rw [sharpGap_mixture_coordinates n a T Y p q (by linarith) (by linarith)
    (by linarith) hT.ne' hY.ne' hp.ne' hq.ne' (by positivity) (by positivity)]
  exact hpoly

/-- The return-face KKT implication in mixture coordinates is exactly the
normalized implication `GradA < 0 → ReturnSide ≤ 0 → FaceA ≥ 0`. -/
theorem sharpFaceA_nonneg_of_uniform
    (n a T Y p q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (hT : 0 < T)
    (hY : 0 < Y) (hp : 0 < p) (hq : 0 < q)
    (hpoly : uniformGradA n a T Y q < 0 →
      uniformReturnSide n a T Y q ≤ 0 →
      0 ≤ uniformSharpFaceA n a T Y q)
    (hgrad : sharpGradA n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) < 0)
    (hside : 0 ≤ sharpSideA n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1))) :
    0 ≤ sharpFaceA n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) := by
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n-1 ≠ 0 := by linarith
  have hnp1 : n+1 ≠ 0 := by linarith
  have hsum : p*Y+a ≠ 0 := by positivity
  have hfactor := uniformSideFactor_pos n a T Y q (by linarith)
    ha.le hT.le hY.le hq.le
  have hgradId := sharpGradA_mixture_coordinates n a T Y p q hn0 hn1 hnp1
    hT.ne' hY.ne' hp.ne' hq.ne' hsum
  have hgradU : uniformGradA n a T Y q < 0 := by
    rw [hgradId] at hgrad
    by_contra hnot
    have hu0 : 0 ≤ uniformGradA n a T Y q := le_of_not_gt hnot
    have : 0 ≤ 2*a*uniformGradA n a T Y q/(Y*p*(n-1)^2) := by positivity
    linarith
  have hsideId := sharpSideA_mixture_coordinates n a T Y p q hn0 hn1 hnp1
    hT.ne' hY.ne' hp.ne' hq.ne' hsum
  have hreturn : uniformReturnSide n a T Y q ≤ 0 := by
    have hden : 0 < Y^3*n*p^2*(n-1)^2*(n+1) := by positivity
    have hs : 0 ≤ Y^3*n*p^2*(n-1)^2*(n+1)*
        sharpSideA n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) :=
      mul_nonneg hden.le hside
    rw [hsideId] at hs
    have hc : 0 < 4*a*(n+2)*uniformSideFactor n a T Y q := by positivity
    nlinarith
  have hfaceU := hpoly hgradU hreturn
  have hfaceId := sharpFaceA_mixture_coordinates n a T Y p q hn0 hn1 hnp1
    hT.ne' hY.ne' hp.ne' hq.ne' hsum (by positivity)
  have hs : 0 ≤ p^2*sharpFaceA n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) := by
    rw [hfaceId]
    exact hfaceU
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos hp)).mp hs

/-- The terminal-face KKT implication similarly reduces to
`GradB > 0 → TerminalSide ≥ 0 → FaceB ≥ 0`. -/
theorem sharpFaceB_nonneg_of_uniform
    (n a T Y p q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (hT : 0 < T)
    (hY : 0 < Y) (hp : 0 < p) (hq : 0 < q)
    (hpoly : 0 < uniformGradB n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q →
      0 ≤ uniformSharpFaceB n a T Y q)
    (hgrad : sharpGradB n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) < 0)
    (hside : 0 ≤ sharpSideB n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1))) :
    0 ≤ sharpFaceB n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) := by
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n-1 ≠ 0 := by linarith
  have hnp1 : n+1 ≠ 0 := by linarith
  have hsum : p*Y+a ≠ 0 := by positivity
  have hfactor := uniformSideFactor_pos n a T Y q (by linarith)
    ha.le hT.le hY.le hq.le
  have hgradId := sharpGradB_mixture_coordinates n a T Y p q hn0 hn1 hnp1
    hT.ne' hY.ne' hp.ne' hq.ne' hsum
  have hgradU : 0 < uniformGradB n a T Y q := by
    rw [hgradId] at hgrad
    by_contra hnot
    have hu0 : uniformGradB n a T Y q ≤ 0 := le_of_not_gt hnot
    have hden : 0 < (n-1)^2 := sq_pos_of_ne_zero hn1
    have hnum : 0 ≤ -2*uniformGradB n a T Y q := by linarith
    have : 0 ≤ (-2*uniformGradB n a T Y q)/(n-1)^2 :=
      div_nonneg hnum hden.le
    linarith
  have hsideId := sharpSideB_mixture_coordinates n a T Y p q hn0 hn1 hnp1
    hT.ne' hY.ne' hp.ne' hq.ne' hsum
  have hterminal : 0 ≤ uniformTerminalSide n a T Y q := by
    have hden : 0 < T^2*Y*n*p*q*(n-1)^2*(n+1) := by positivity
    have hs : 0 ≤ T^2*Y*n*p*q*(n-1)^2*(n+1)*
        sharpSideB n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
          (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) :=
      mul_nonneg hden.le hside
    rw [hsideId] at hs
    have hc : 0 < 4*a*(n+2)*uniformSideFactor n a T Y q := by positivity
    nlinarith
  have hfaceU := hpoly hgradU hterminal
  rw [sharpFaceB_mixture_coordinates n a T Y p q hn0 hn1 hnp1 hT.ne'
    hY.ne' hp.ne' hq.ne' hsum (by positivity)]
  exact hfaceU

/-- The two strict interior side conditions are contradictory as soon as the
remaining scale-free polynomial implication is known.  This isolates the exact
semialgebraic statement needed for every stage. -/
theorem sharpSides_interior_impossible_of_uniform_implication
    (n a T Y p q : ℝ) (hn : 2 ≤ n) (ha : 0 < a) (hT : 0 < T)
    (hY : 0 < Y) (hp : 0 < p) (hq : 0 < q)
    (hpoly : 0 < uniformReturnSide n a T Y q →
      0 ≤ uniformTerminalSide n a T Y q)
    (hsideA : sharpSideA n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) < 0)
    (hsideB : sharpSideB n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
      (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) < 0) : False := by
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n-1 ≠ 0 := by linarith
  have hnp1 : n+1 ≠ 0 := by linarith
  have hsum : p*Y+a ≠ 0 := by positivity
  have hfactor := uniformSideFactor_pos n a T Y q hn ha.le hT.le hY.le hq.le
  have hdenA : 0 < Y^3*n*p^2*(n-1)^2*(n+1) := by positivity
  have hscaledA : Y^3*n*p^2*(n-1)^2*(n+1)*
      sharpSideA n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) < 0 :=
    mul_neg_of_pos_of_neg hdenA hsideA
  rw [sharpSideA_mixture_coordinates n a T Y p q hn0 hn1 hnp1
    hT.ne' hY.ne' hp.ne' hq.ne' hsum] at hscaledA
  have hcoefA : 0 < 4*a*(n+2)*uniformSideFactor n a T Y q := by positivity
  have hreturn : 0 < uniformReturnSide n a T Y q := by
    have : 0 < (4*a*(n+2)*uniformSideFactor n a T Y q)
        *uniformReturnSide n a T Y q := by nlinarith
    exact (mul_pos_iff_of_pos_left hcoefA).mp this
  have hterminal := hpoly hreturn
  have hdenB : 0 < T^2*Y*n*p*q*(n-1)^2*(n+1) := by positivity
  have hscaledB : T^2*Y*n*p*q*(n-1)^2*(n+1)*
      sharpSideB n (a/(p*Y)) (p*Y*(1-a)/(p*Y+a))
        (p*Y) (n*p*Y^2/(n-1)) (q*T) (n*q*T^2/(n-1)) < 0 :=
    mul_neg_of_pos_of_neg hdenB hsideB
  rw [sharpSideB_mixture_coordinates n a T Y p q hn0 hn1 hnp1
    hT.ne' hY.ne' hp.ne' hq.ne' hsum] at hscaledB
  have hcoefB : 0 < 4*a*(n+2)*uniformSideFactor n a T Y q := by positivity
  have : 0 ≤ 4*a*(n+2)*uniformSideFactor n a T Y q
      *uniformTerminalSide n a T Y q := mul_nonneg hcoefB.le hterminal
  linarith

/-- At four stages the two uniform polynomials specialize to twelve times the
polynomials used in the completed `s = 4` proof. -/
theorem uniformReturnSide_four (a T Y q : ℝ) :
    uniformReturnSide 4 a T Y q = 12*
      (-2*T^3*q-54*T^2*q+56*T*Y*a*q-2*T*Y*a+81*T*q-108*T
        +110*Y*a+81) := by
  unfold uniformReturnSide uniformReturnM uniformReturnK
  norm_num
  ring

theorem uniformTerminalSide_four (a T Y q : ℝ) :
    uniformTerminalSide 4 a T Y q = 12*
      (2*T^3*q^2+2*T^2*Y*q+108*T^2*q^2-52*T^2*q
        -54*T*Y*a*q+108*T*Y*q+135*T*q+2*Y^2*a-108*Y*a+108*Y+27) := by
  unfold uniformTerminalSide uniformTerminalL uniformTerminalS0
  norm_num
  ring

/-! ### Quadratic elimination of the normalized implication

As a polynomial in `Y`, the return side is affine and the terminal side is
quadratic.  Eliminating `Y` gives a quadratic in the positive return-side value.
The following definitions and lemmas isolate two smaller certificates: a
nonnegative constant term and either a nonnegative linear term or a
nonpositive discriminant. -/

noncomputable def uniformAlpha (n a T q : ℝ) : ℝ :=
  a*n*uniformReturnM n a T (T*q)

noncomputable def uniformBeta (n a : ℝ) : ℝ := a*n*(n+2)

noncomputable def uniformElimQ1 (n a T q : ℝ) : ℝ :=
  uniformTerminalL n a T (T*q)*uniformAlpha n a T q
    -2*uniformBeta n a*uniformReturnK n T (T*q)

noncomputable def uniformElimQ0 (n a T q : ℝ) : ℝ :=
  uniformBeta n a*(uniformReturnK n T (T*q))^2
    -uniformTerminalL n a T (T*q)*uniformAlpha n a T q
      *uniformReturnK n T (T*q)
    +uniformTerminalS0 n T (T*q)*(uniformAlpha n a T q)^2

noncomputable def uniformElimH (n T z : ℝ) : ℝ :=
  T*n^2*z+4*T*n*z+2*n^4*z+4*n^4+14*n^3*z+28*n^3
    +24*n^2*z+42*n^2-8*n*z-22*n-32*z-52

noncomputable def uniformElimG (n T z : ℝ) : ℝ :=
  T^2*n^3+4*T^2*n^2+4*T^2*n-2*T*n^4-2*T*n^3+20*T*n^2
    +16*T*n-32*T+2*n^5*z+2*n^5+10*n^4*z+6*n^4-2*n^3*z
    -22*n^3-34*n^2*z-22*n^2+24*n*z+76*n-40

noncomputable def uniformElimN (n a T z : ℝ) : ℝ :=
  (1-a)*(n+2)*(-uniformReturnK n T z)+a*(z+1)*uniformElimG n T z

theorem uniformReturnSide_affine (n a T Y q : ℝ) :
    uniformReturnSide n a T Y q =
      uniformAlpha n a T q*Y+uniformReturnK n T (T*q) := by
  unfold uniformReturnSide uniformAlpha
  ring

theorem uniformTerminalSide_quadratic (n a T Y q : ℝ) :
    uniformTerminalSide n a T Y q =
      uniformBeta n a*Y^2+uniformTerminalL n a T (T*q)*Y
        +uniformTerminalS0 n T (T*q) := by
  rfl

/-- Exact elimination identity obtained by substituting
`αY = uniformReturnSide - K` into the terminal quadratic. -/
theorem uniform_elimination_identity (n a T Y q : ℝ) :
    (uniformAlpha n a T q)^2*uniformTerminalSide n a T Y q =
      uniformBeta n a*(uniformReturnSide n a T Y q)^2
        +uniformElimQ1 n a T q*uniformReturnSide n a T Y q
        +uniformElimQ0 n a T q := by
  unfold uniformElimQ1 uniformElimQ0
  unfold uniformAlpha uniformBeta
  unfold uniformReturnSide uniformTerminalSide
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Factorization of the elimination constant term. -/
theorem uniformElimQ0_factor (n a T q : ℝ) :
    uniformElimQ0 n a T q =
      a*n*(n-1)*(n+3)*(T*q+1)*uniformElimH n T (T*q)
        *uniformElimN n a T (T*q) := by
  unfold uniformElimQ0 uniformAlpha uniformBeta uniformElimN
  unfold uniformElimH uniformElimG uniformReturnM uniformReturnK
  unfold uniformTerminalL uniformTerminalS0
  ring

theorem uniformElimH_pos
    (n T z : ℝ) (hn : 4 ≤ n) (hT : 0 ≤ T) (hz : 0 ≤ z) :
    0 < uniformElimH n T z := by
  let m := n-4
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hid : uniformElimH n T z =
      32*T*z+m^4*(2*z+4)+m^3*(46*z+92)
        +m^2*(T*z+384*z+762)+m*(12*T*z+1368*z+2682)
        +1728*z+3348 := by
    dsimp [m, uniformElimH]
    ring
  rw [hid]
  positivity

noncomputable def uniformElimR (n z : ℝ) : ℝ :=
  2*n^4*z+n^4+14*n^3*z+10*n^3+24*n^2*z+12*n^2-40*n-64

theorem uniformElimR_pos (n z : ℝ) (hn : 4 ≤ n) (hz : 0 ≤ z) :
    0 < uniformElimR n z := by
  let m := n-4
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hid : uniformElimR n z =
      m^4*(2*z+1)+m^3*(46*z+26)+m^2*(384*z+228)
        +m*(1376*z+792)+1792*z+864 := by
    dsimp [m, uniformElimR]
    ring
  rw [hid]
  positivity

/-- The second endpoint of `uniformElimN` is positive.  Its dependence on `T`
is quadratic, and completing the square leaves the positive polynomial
`uniformElimR`. -/
theorem uniformElimG_pos
    (n T z : ℝ) (hn : 4 ≤ n) (hz : 0 ≤ z) :
    0 < uniformElimG n T z := by
  have hn0 : 0 < n := by linarith
  have hn2 : 0 < n+2 := by linarith
  have hR := uniformElimR_pos n z hn hz
  let A := n*(n+2)^2
  let B := -2*(n^4+n^3-10*n^2-8*n+16)
  have hA : 0 < A := by dsimp [A]; positivity
  have hid : 4*A*uniformElimG n T z =
      (2*A*T+B)^2+4*(n-1)^2*(n+2)^2*uniformElimR n z := by
    dsimp [A, B, uniformElimG, uniformElimR]
    ring
  have hscaled : 0 < 4*A*uniformElimG n T z := by
    rw [hid]
    have hn1 : 0 < n-1 := by linarith
    have : 0 < 4*(n-1)^2*(n+2)^2*uniformElimR n z := by
      exact mul_pos
        (mul_pos (mul_pos (by norm_num) (pow_pos hn1 2)) (pow_pos hn2 2)) hR
    nlinarith [sq_nonneg (2*A*T+B)]
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < 4*A)).mp hscaled

/-- In the `K ≤ 0` branch the elimination constant term is automatically
nonnegative throughout the mixture box. -/
theorem uniformElimQ0_nonneg_of_K_nonpos
    (n a T q : ℝ) (hn : 4 ≤ n) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hq : 0 ≤ q) (hK : uniformReturnK n T (T*q) ≤ 0) :
    0 ≤ uniformElimQ0 n a T q := by
  have hz : 0 ≤ T*q := mul_nonneg hT hq
  have hH := uniformElimH_pos n T (T*q) hn hT hz
  have hG := uniformElimG_pos n T (T*q) hn hz
  have hN : 0 ≤ uniformElimN n a T (T*q) := by
    unfold uniformElimN
    have h1a : 0 ≤ 1-a := sub_nonneg.mpr ha1
    have hn2 : 0 ≤ n+2 := by linarith
    have hnK : 0 ≤ -uniformReturnK n T (T*q) := neg_nonneg.mpr hK
    have hleft : 0 ≤ (1-a)*(n+2)*(-uniformReturnK n T (T*q)) := by
      positivity
    have hright : 0 ≤ a*(T*q+1)*uniformElimG n T (T*q) := by
      positivity
    exact add_nonneg hleft hright
  rw [uniformElimQ0_factor]
  have hn0 : 0 ≤ n := by linarith
  have hn1 : 0 ≤ n-1 := by linarith
  have hn3 : 0 ≤ n+3 := by linarith
  positivity

/-- In the complementary `K ≥ 0` branch, the constant coefficient of the
terminal quadratic is nonnegative.  The proof extracts a sharp upper bound on
`T` from `K ≥ 0` and substitutes it into that constant coefficient. -/
theorem uniformTerminalS0_nonneg_of_K_nonneg
    (n T z : ℝ) (hn : 4 ≤ n) (hT : 0 ≤ T) (hz : 0 ≤ z)
    (hK : 0 ≤ uniformReturnK n T z) :
    0 ≤ uniformTerminalS0 n T z := by
  let m := n-4
  let cp := 2*n^3+6*n^2-8
  let c0 := 2*n^3+6*n^2-18*n+10
  let az := n^3+2*n^2+5*n-8
  let cneg := n^3+7*n^2+8*n
  let P := (4*n^3+12*n^2-16)*z^2
    +(6*n^3+12*n^2-6*n-12)*z+(2*n^3-6*n+4)
  let I := n*T^2*z+T*z*az+T*cp-c0*(z+1)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n-1 := by linarith
  have hn2 : 0 < n+2 := by linarith
  have hcp : 0 < cp := by
    have hid : cp = 2*m^3+30*m^2+144*m+216 := by
      dsimp [cp, m]
      ring
    rw [hid]
    positivity
  have hc0 : 0 < c0 := by
    have hid : c0 = 2*m^3+30*m^2+126*m+162 := by
      dsimp [c0, m]
      ring
    rw [hid]
    positivity
  have haz : 0 < az := by
    have hid : az = m^3+14*m^2+69*m+108 := by
      dsimp [az, m]
      ring
    rw [hid]
    positivity
  have hcneg : 0 < cneg := by
    have hid : cneg = m^3+19*m^2+112*m+208 := by
      dsimp [cneg, m]
      ring
    rw [hid]
    positivity
  have hI : I ≤ 0 := by
    have hKid : uniformReturnK n T z = -(n+2)*I := by
      dsimp [I, cp, c0, az, uniformReturnK]
      ring
    rw [hKid] at hK
    by_contra hnot
    have hIp : 0 < I := lt_of_not_ge hnot
    have : -(n+2)*I < 0 := by
      have : 0 < (n+2)*I := mul_pos hn2 hIp
      linarith
    linarith
  have hbound : cp*T ≤ c0*(z+1) := by
    have hfirst : 0 ≤ n*T^2*z := by positivity
    have hsecond : 0 ≤ T*z*az := by positivity
    dsimp [I] at hI
    nlinarith
  have hboundz : cp*(cneg*T*z) ≤ cneg*c0*z*(z+1) := by
    have hzbound := mul_le_mul_of_nonneg_right hbound hz
    have := mul_le_mul_of_nonneg_left hzbound hcneg.le
    nlinarith
  let R := 3*n^4*z+2*n^4+20*n^3*z+10*n^3+53*n^2*z+12*n^2
    +88*n*z-8*n+64*z-16
  have hR : 0 < R := by
    have hid : R = m^4*(3*z+2)+m^3*(68*z+42)+m^2*(581*z+324)
        +m*(2240*z+1080)+3312*z+1296 := by
      dsimp [R, m]
      ring
    rw [hid]
    positivity
  have hrem : 0 ≤ cp*P-cneg*c0*z*(z+1) := by
    have hid : cp*P-cneg*c0*z*(z+1) = 2*(n-1)^2*(z+1)*R := by
      dsimp [cp, P, cneg, c0, R]
      ring
    rw [hid]
    positivity
  have hcompare : cneg*T*z ≤ P := by
    have hscaled : cp*(cneg*T*z) ≤ cp*P := le_trans hboundz (by linarith)
    by_contra hnot
    have hlt : P < cneg*T*z := lt_of_not_ge hnot
    have := mul_lt_mul_of_pos_left hlt hcp
    linarith
  have hcore : 0 ≤ 2*n*T*z^2-cneg*T*z+P := by
    have : 0 ≤ 2*n*T*z^2 := by positivity
    linarith
  have hSid : uniformTerminalS0 n T z =
      (n-1)*(2*n*T*z^2-cneg*T*z+P) := by
    dsimp [uniformTerminalS0, cneg, P]
    ring
  rw [hSid]
  exact mul_nonneg hn1.le hcore

noncomputable def uniformTerminalDisc (n a T z : ℝ) : ℝ :=
  (uniformTerminalL n a T z)^2
    -4*uniformBeta n a*uniformTerminalS0 n T z

noncomputable def uniformKposMultiplierA (m z : ℝ) : ℝ :=
  32+(184/9)*m+2*m^2+(272/9)*z+(268/27)*m*z+(95/81)*m^2*z

noncomputable def uniformKposMultiplierB (m z : ℝ) : ℝ :=
  z*((1504/3)+(11498/27)*m+(66991/486)*m^2
    +(352081/17496)*m^3+m^4)

private theorem uniformKpos_remainder_nonneg
    (m z w : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    0 ≤ -uniformKposMultiplierA m z*uniformReturnK (m+4) (z+w) z
      +uniformKposMultiplierB m z*uniformTerminalL (m+4) 1 (z+w) z
      -uniformTerminalDisc (m+4) 1 (z+w) z := by
  unfold uniformKposMultiplierA uniformKposMultiplierB uniformReturnK
  unfold uniformTerminalDisc
  unfold uniformTerminalL uniformBeta uniformTerminalS0
  ring_nf
  positivity

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Endpoint discriminant certificate used when `K ≥ 0` and the terminal
linear coefficient is negative. -/
theorem uniformTerminalDisc_at_one_nonpos
    (n T z : ℝ) (hn : 4 ≤ n) (_hT : 0 ≤ T) (hz : 0 ≤ z) (hzT : z ≤ T)
    (hK : 0 ≤ uniformReturnK n T z)
    (hL : uniformTerminalL n 1 T z ≤ 0) :
    uniformTerminalDisc n 1 T z ≤ 0 := by
  let m := n-4
  let w := T-z
  let A := uniformKposMultiplierA m z
  let B := uniformKposMultiplierB m z
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hw : 0 ≤ w := by dsimp [w]; linarith
  have hA : 0 ≤ A := by dsimp [A, uniformKposMultiplierA]; positivity
  have hB : 0 ≤ B := by dsimp [B, uniformKposMultiplierB]; positivity
  have hrem : 0 ≤ -A*uniformReturnK n T z
      +B*uniformTerminalL n 1 T z-uniformTerminalDisc n 1 T z := by
    have hbase := uniformKpos_remainder_nonneg m z w hm hz hw
    dsimp only [A, B]
    convert hbase using 1
    all_goals
      dsimp [m, w]
      ring_nf
  have hAK : 0 ≤ A*uniformReturnK n T z := mul_nonneg hA hK
  have hBL : B*uniformTerminalL n 1 T z ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hB hL
  linarith

/-- The endpoint certificate propagates from `a=1` to every `0<a≤1` for
which the terminal linear coefficient is negative. -/
theorem uniformTerminalDisc_nonpos_of_K_nonneg_of_L_neg
    (n a T z : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hz : 0 ≤ z) (hzT : z ≤ T)
    (hK : 0 ≤ uniformReturnK n T z)
    (hL : uniformTerminalL n a T z < 0) :
    uniformTerminalDisc n a T z ≤ 0 := by
  let m := n-4
  let L0 := uniformTerminalL n 0 T z
  let LA := n*(n-1)*(n+2)*(n+5)*(z+2)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n-1 := by linarith
  have hn2 : 0 < n+2 := by linarith
  have hn5 : 0 < n+5 := by linarith
  have hLA : 0 < LA := by dsimp [LA]; positivity
  have hL0 : 0 < L0 := by
    have hid : L0 = 24*T*z+m^4*(2*z+2)+m^3*(42*z+42)
        +m^2*(T*z+324*z+324)+m*(10*T*z+1080*z+1080)
        +1296*z+1296 := by
      dsimp [L0, m, uniformTerminalL]
      ring
    rw [hid]
    positivity
  have hLa : uniformTerminalL n a T z = L0-a*LA := by
    dsimp [L0, LA, uniformTerminalL]
    ring
  have hLone : uniformTerminalL n 1 T z = L0-LA := by
    dsimp [L0, LA, uniformTerminalL]
    ring
  have hL1 : uniformTerminalL n 1 T z < 0 := by
    rw [hLa] at hL
    rw [hLone]
    have h1a : 0 ≤ 1-a := sub_nonneg.mpr ha1
    have : 0 ≤ (1-a)*LA := mul_nonneg h1a hLA.le
    nlinarith
  have hD1 := uniformTerminalDisc_at_one_nonpos n T z hn hT hz hzT hK hL1.le
  have hL0lt : L0 < a*LA := by rw [hLa] at hL; linarith
  have hsquares : L0^2 < (a*LA)^2 :=
    (sq_lt_sq₀ hL0.le (mul_nonneg ha.le hLA.le)).mpr hL0lt
  have haa : a^2 ≤ a := by
    have : 0 ≤ a*(1-a) := mul_nonneg ha.le (sub_nonneg.mpr ha1)
    nlinarith
  have hscaleSq : (a*LA)^2 ≤ a*LA^2 := by
    have := mul_le_mul_of_nonneg_right haa (sq_nonneg LA)
    nlinarith
  have hbracket : L0^2-a*LA^2 ≤ 0 := by linarith
  have hid : uniformTerminalDisc n a T z =
      a*uniformTerminalDisc n 1 T z+(1-a)*(L0^2-a*LA^2) := by
    unfold uniformTerminalDisc uniformBeta
    rw [hLa, hLone]
    ring
  rw [hid]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha.le hD1)
    (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha1) hbracket)

theorem uniform_K_nonneg_discriminant_certificate
    (n a T z : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hz : 0 ≤ z) (hzT : z ≤ T)
    (hK : 0 ≤ uniformReturnK n T z) :
    0 ≤ uniformTerminalL n a T z ∨
      (uniformTerminalL n a T z)^2 ≤
        4*uniformBeta n a*uniformTerminalS0 n T z := by
  by_cases hL : 0 ≤ uniformTerminalL n a T z
  · exact Or.inl hL
  · right
    have hdisc := uniformTerminalDisc_nonpos_of_K_nonneg_of_L_neg
      n a T z hn ha ha1 hT hz hzT hK (lt_of_not_ge hL)
    unfold uniformTerminalDisc at hdisc
    linarith

noncomputable def uniformJ2 (n a T z : ℝ) : ℝ :=
  uniformTerminalL n a T z*uniformReturnM n a T z
    -2*(n+2)*uniformReturnK n T z

theorem uniformElimQ1_eq_J2 (n a T q : ℝ) :
    uniformElimQ1 n a T q = a*n*uniformJ2 n a T (T*q) := by
  unfold uniformElimQ1 uniformAlpha uniformBeta uniformJ2
  ring

private theorem uniformJ2_at_zero_pos_shifted
    (m T z : ℝ) (hm : 0 ≤ m) (hT : 0 ≤ T) (hz : 0 ≤ z) :
    0 < uniformJ2 (m+4) 0 T z := by
  unfold uniformJ2 uniformTerminalL uniformReturnM uniformReturnK
  ring_nf
  positivity

theorem uniformJ2_at_zero_pos
    (n T z : ℝ) (hn : 4 ≤ n) (hT : 0 ≤ T) (hz : 0 ≤ z) :
    0 < uniformJ2 n 0 T z := by
  let m := n-4
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have h := uniformJ2_at_zero_pos_shifted m T z hm hT hz
  convert h using 1
  all_goals
    dsimp [m]
    ring_nf

theorem uniformJ2_affine (n a T z : ℝ) :
    uniformJ2 n a T z =
      (1-a)*uniformJ2 n 0 T z+a*uniformJ2 n 1 T z := by
  unfold uniformJ2 uniformTerminalL uniformReturnM uniformReturnK
  ring

noncomputable def uniformKnegMultiplierB (m z w : ℝ) : ℝ :=
  3/2+2*m+2*w+(3151/168)*z+(48557/6912)*m*z
    +(7027289/5902848)*m^2*z

private theorem uniformKneg_remainder_nonneg
    (m z w : ℝ) (hm : 0 ≤ m) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    0 ≤ uniformKnegMultiplierB m z w*uniformJ2 (m+4) 1 (z+w) z
      -2*(m+6)*uniformTerminalDisc (m+4) 1 (z+w) z := by
  unfold uniformKnegMultiplierB uniformJ2 uniformTerminalDisc
  unfold uniformTerminalL uniformReturnM uniformReturnK
  unfold uniformBeta uniformTerminalS0
  ring_nf
  positivity

theorem uniformTerminalDisc_at_one_nonpos_of_J2_nonpos
    (n T z : ℝ) (hn : 4 ≤ n) (hz : 0 ≤ z) (hzT : z ≤ T)
    (hJ : uniformJ2 n 1 T z ≤ 0) :
    uniformTerminalDisc n 1 T z ≤ 0 := by
  let m := n-4
  let w := T-z
  let B := uniformKnegMultiplierB m z w
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hw : 0 ≤ w := by dsimp [w]; linarith
  have hB : 0 ≤ B := by dsimp [B, uniformKnegMultiplierB]; positivity
  have hrem : 0 ≤ B*uniformJ2 n 1 T z
      -2*(n+2)*uniformTerminalDisc n 1 T z := by
    have hbase := uniformKneg_remainder_nonneg m z w hm hz hw
    dsimp only [B]
    convert hbase using 1
    all_goals
      dsimp [m, w]
      ring_nf
  have hBJ : B*uniformJ2 n 1 T z ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hB hJ
  have hn2 : 0 < n+2 := by linarith
  by_contra hnot
  have hD : 0 < uniformTerminalDisc n 1 T z := lt_of_not_ge hnot
  have : 0 < 2*(n+2)*uniformTerminalDisc n 1 T z := by positivity
  linarith

/-- Propagation of a nonpositive endpoint discriminant from `a=1` to any
`0<a≤1` where the terminal linear coefficient is negative. -/
theorem uniformTerminalDisc_nonpos_of_at_one_of_L_neg
    (n a T z : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hz : 0 ≤ z)
    (hD1 : uniformTerminalDisc n 1 T z ≤ 0)
    (hL : uniformTerminalL n a T z < 0) :
    uniformTerminalDisc n a T z ≤ 0 := by
  let m := n-4
  let L0 := uniformTerminalL n 0 T z
  let LA := n*(n-1)*(n+2)*(n+5)*(z+2)
  have hm : 0 ≤ m := by dsimp [m]; linarith
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n-1 := by linarith
  have hn2 : 0 < n+2 := by linarith
  have hn5 : 0 < n+5 := by linarith
  have hLA : 0 < LA := by dsimp [LA]; positivity
  have hL0 : 0 < L0 := by
    have hid : L0 = 24*T*z+m^4*(2*z+2)+m^3*(42*z+42)
        +m^2*(T*z+324*z+324)+m*(10*T*z+1080*z+1080)
        +1296*z+1296 := by
      dsimp [L0, m, uniformTerminalL]
      ring
    rw [hid]
    positivity
  have hLa : uniformTerminalL n a T z = L0-a*LA := by
    dsimp [L0, LA, uniformTerminalL]
    ring
  have hLone : uniformTerminalL n 1 T z = L0-LA := by
    dsimp [L0, LA, uniformTerminalL]
    ring
  have hL0lt : L0 < a*LA := by rw [hLa] at hL; linarith
  have hsquares : L0^2 < (a*LA)^2 :=
    (sq_lt_sq₀ hL0.le (mul_nonneg ha.le hLA.le)).mpr hL0lt
  have haa : a^2 ≤ a := by
    have : 0 ≤ a*(1-a) := mul_nonneg ha.le (sub_nonneg.mpr ha1)
    nlinarith
  have hscaleSq : (a*LA)^2 ≤ a*LA^2 := by
    have := mul_le_mul_of_nonneg_right haa (sq_nonneg LA)
    nlinarith
  have hbracket : L0^2-a*LA^2 ≤ 0 := by linarith
  have hid : uniformTerminalDisc n a T z =
      a*uniformTerminalDisc n 1 T z+(1-a)*(L0^2-a*LA^2) := by
    unfold uniformTerminalDisc uniformBeta
    rw [hLa, hLone]
    ring
  rw [hid]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha.le hD1)
    (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha1) hbracket)

/-- The `K < 0` discriminant alternative.  In its application, positivity of
`M` follows from positivity of the affine return side. -/
theorem uniform_K_neg_discriminant_certificate
    (n a T z : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hz : 0 ≤ z) (hzT : z ≤ T)
    (hK : uniformReturnK n T z < 0)
    (hM : 0 < uniformReturnM n a T z) :
    0 ≤ uniformJ2 n a T z ∨ uniformTerminalDisc n a T z ≤ 0 := by
  by_cases hJ : 0 ≤ uniformJ2 n a T z
  · exact Or.inl hJ
  · right
    have hJneg : uniformJ2 n a T z < 0 := lt_of_not_ge hJ
    have hJ0 := uniformJ2_at_zero_pos n T z hn hT hz
    have hJ1 : uniformJ2 n 1 T z < 0 := by
      rw [uniformJ2_affine] at hJneg
      by_contra hnot
      have hJ1nonneg : 0 ≤ uniformJ2 n 1 T z := le_of_not_gt hnot
      have h1a : 0 ≤ 1-a := sub_nonneg.mpr ha1
      have : 0 ≤ (1-a)*uniformJ2 n 0 T z+a*uniformJ2 n 1 T z := by
        positivity
      linarith
    have hD1 := uniformTerminalDisc_at_one_nonpos_of_J2_nonpos
      n T z hn hz hzT hJ1.le
    have hLneg : uniformTerminalL n a T z < 0 := by
      unfold uniformJ2 at hJneg
      have hn2 : 0 < n+2 := by linarith
      have hpos : 0 < -2*(n+2)*uniformReturnK n T z := by
        rw [show -2*(n+2)*uniformReturnK n T z =
          (2*(n+2))*(-uniformReturnK n T z) by ring]
        exact mul_pos (by positivity) (neg_pos.mpr hK)
      have hprod : uniformTerminalL n a T z*uniformReturnM n a T z < 0 := by
        linarith
      by_contra hnot
      have hLnonneg : 0 ≤ uniformTerminalL n a T z := le_of_not_gt hnot
      have := mul_nonneg hLnonneg hM.le
      linarith
    exact uniformTerminalDisc_nonpos_of_at_one_of_L_neg
      n a T z hn ha ha1 hT hz hD1 hLneg

theorem uniform_elimination_discriminant_identity (n a T q : ℝ) :
    (uniformElimQ1 n a T q)^2
        -4*uniformBeta n a*uniformElimQ0 n a T q =
      (uniformAlpha n a T q)^2*uniformTerminalDisc n a T (T*q) := by
  unfold uniformElimQ1 uniformElimQ0 uniformTerminalDisc
  unfold uniformAlpha uniformBeta
  ring

private theorem quadratic_nonneg_of_linear_or_discriminant
    (β P Q1 Q0 : ℝ) (hβ : 0 < β) (hP : 0 ≤ P) (hQ0 : 0 ≤ Q0)
    (hcert : 0 ≤ Q1 ∨ Q1^2 ≤ 4*β*Q0) :
    0 ≤ β*P^2+Q1*P+Q0 := by
  rcases hcert with hQ1 | hdisc
  · positivity
  · have hid :
        4*β*(β*P^2+Q1*P+Q0) =
          (2*β*P+Q1)^2+(4*β*Q0-Q1^2) := by ring
    apply (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4*β)).mp
    rw [hid]
    nlinarith [sq_nonneg (2*β*P+Q1)]

/-- The difficult `K < 0` branch of the uniform side implication is reduced to
two elimination certificates independent of the unbounded variable `Y`. -/
theorem uniformTerminalSide_nonneg_of_elimination_certificates
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (hY : 0 < Y)
    (hreturn : 0 < uniformReturnSide n a T Y q)
    (hK : uniformReturnK n T (T*q) < 0)
    (hQ0 : 0 ≤ uniformElimQ0 n a T q)
    (hcert : 0 ≤ uniformElimQ1 n a T q ∨
      (uniformElimQ1 n a T q)^2 ≤
        4*uniformBeta n a*uniformElimQ0 n a T q) :
    0 ≤ uniformTerminalSide n a T Y q := by
  have hn0 : 0 < n := by linarith
  have hβ : 0 < uniformBeta n a := by
    unfold uniformBeta
    positivity
  have haY : 0 < uniformAlpha n a T q*Y := by
    rw [uniformReturnSide_affine] at hreturn
    linarith
  have hα : 0 < uniformAlpha n a T q :=
    (mul_pos_iff_of_pos_right hY).mp haY
  have hquad := quadratic_nonneg_of_linear_or_discriminant
    (uniformBeta n a) (uniformReturnSide n a T Y q)
    (uniformElimQ1 n a T q) (uniformElimQ0 n a T q)
    hβ hreturn.le hQ0 hcert
  rw [← uniform_elimination_identity n a T Y q] at hquad
  exact (mul_nonneg_iff_of_pos_left (sq_pos_of_pos hα)).mp hquad

/-- Complete reduction of the normalized side implication to two
`Y`-independent discriminant alternatives. -/
theorem uniformTerminalSide_nonneg_of_discriminant_certificates
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 ≤ T) (hY : 0 < Y) (hq : 0 ≤ q)
    (hreturn : 0 < uniformReturnSide n a T Y q)
    (hKnonnegCert : 0 ≤ uniformReturnK n T (T*q) →
      0 ≤ uniformTerminalL n a T (T*q) ∨
        (uniformTerminalL n a T (T*q))^2 ≤
          4*uniformBeta n a*uniformTerminalS0 n T (T*q))
    (hKnegCert : uniformReturnK n T (T*q) < 0 →
      0 ≤ uniformElimQ1 n a T q ∨
        (uniformElimQ1 n a T q)^2 ≤
          4*uniformBeta n a*uniformElimQ0 n a T q) :
    0 ≤ uniformTerminalSide n a T Y q := by
  have hn0 : 0 < n := by linarith
  have hβ : 0 < uniformBeta n a := by
    unfold uniformBeta
    positivity
  by_cases hK : 0 ≤ uniformReturnK n T (T*q)
  · have hS0 := uniformTerminalS0_nonneg_of_K_nonneg n T (T*q)
      hn hT (mul_nonneg hT hq) hK
    have hquad := quadratic_nonneg_of_linear_or_discriminant
      (uniformBeta n a) Y (uniformTerminalL n a T (T*q))
      (uniformTerminalS0 n T (T*q)) hβ hY.le hS0 (hKnonnegCert hK)
    rwa [← uniformTerminalSide_quadratic] at hquad
  · have hKneg : uniformReturnK n T (T*q) < 0 := lt_of_not_ge hK
    have hQ0 := uniformElimQ0_nonneg_of_K_nonpos n a T q hn ha.le ha1
      hT hq hKneg.le
    exact uniformTerminalSide_nonneg_of_elimination_certificates
      n a T Y q hn ha hY hreturn hKneg hQ0 (hKnegCert hKneg)

/-- The normalized side implication required to exclude the interior KKT
candidate, now with no polynomial hypotheses left. -/
theorem uniformTerminalSide_nonneg_of_returnSide_pos
    (n a T Y q : ℝ) (hn : 4 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1)
    (hT : 0 < T) (hY : 0 < Y) (hq : 0 < q) (hq1 : q ≤ 1)
    (hreturn : 0 < uniformReturnSide n a T Y q) :
    0 ≤ uniformTerminalSide n a T Y q := by
  have hn0 : 0 < n := by linarith
  have hz : 0 ≤ T*q := by positivity
  have hzT : T*q ≤ T := by
    have := mul_le_mul_of_nonneg_left hq1 hT.le
    nlinarith
  apply uniformTerminalSide_nonneg_of_discriminant_certificates
    n a T Y q hn ha ha1 hT.le hY hq.le hreturn
  · intro hK
    exact uniform_K_nonneg_discriminant_certificate
      n a T (T*q) hn ha ha1 hT.le hz hzT hK
  · intro hK
    have hαY : 0 < uniformAlpha n a T q*Y := by
      rw [uniformReturnSide_affine] at hreturn
      linarith
    have hα : 0 < uniformAlpha n a T q :=
      (mul_pos_iff_of_pos_right hY).mp hαY
    have hM : 0 < uniformReturnM n a T (T*q) := by
      unfold uniformAlpha at hα
      have han : 0 < a*n := mul_pos ha hn0
      by_contra hnot
      have hMnonpos : uniformReturnM n a T (T*q) ≤ 0 := le_of_not_gt hnot
      have := mul_nonpos_of_nonneg_of_nonpos han.le hMnonpos
      linarith
    rcases uniform_K_neg_discriminant_certificate
      n a T (T*q) hn ha ha1 hT.le hz hzT hK hM with hJ | hdisc
    · left
      rw [uniformElimQ1_eq_J2]
      positivity
    · right
      have hscaled : (uniformAlpha n a T q)^2
          *uniformTerminalDisc n a T (T*q) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hdisc
      rw [← uniform_elimination_discriminant_identity] at hscaled
      linarith

end SSP.K3AllStages
