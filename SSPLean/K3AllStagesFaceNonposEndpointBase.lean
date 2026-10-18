import SSPLean.K3AllStagesFaceNonposPolynomial
set_option autoImplicit false
namespace SSP.K3AllStages
open SSP.K3S4Renewal SSP.K3S4KKT
noncomputable def uniformFaceAEndpointScaled (m z w : ℝ) : ℝ :=
  (m+4)^3*(uniformFaceALargeM m z)^3*
    uniformFaceAQB3 (m+4)
      (w*uniformFaceALargeK m z/((m+4)*uniformFaceALargeM m z))
      (m+3+z)

noncomputable def uniformFaceAEndpointB0 (m z : ℝ) : ℝ :=
  uniformFaceAEndpointScaled m z 0

noncomputable def uniformFaceAEndpointB1 (m z : ℝ) : ℝ :=
  -(5/6)*uniformFaceAEndpointScaled m z 0
    +(1/3)*uniformFaceAEndpointScaled m z 1
    +3*uniformFaceAEndpointScaled m z (1/3)
    -(3/2)*uniformFaceAEndpointScaled m z (2/3)

noncomputable def uniformFaceAEndpointB2 (m z : ℝ) : ℝ :=
  (1/3)*uniformFaceAEndpointScaled m z 0
    -(5/6)*uniformFaceAEndpointScaled m z 1
    -(3/2)*uniformFaceAEndpointScaled m z (1/3)
    +3*uniformFaceAEndpointScaled m z (2/3)

noncomputable def uniformFaceAEndpointB3 (m z : ℝ) : ℝ :=
  uniformFaceAEndpointScaled m z 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
noncomputable def EndpointReducedX0 (n T : ℝ) : ℝ :=
  (n + 2)*(-T + n - 1)^2*(T^4*n^3 + T^4*n^2 + 8*T^3*n^3 - 8*T^3*n + 24*T^2*n^3 - 12*T^2*n^2 - 12*T^2*n + 24*T*n^3 - 48*T*n^2 + 24*T*n + 12*n^3 - 36*n^2 + 36*n - 12)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
noncomputable def EndpointReducedX1 (n T : ℝ) : ℝ :=
  -9*T^4*n^3 - 3*T^4*n^2 + 18*T^4*n + 2*T^3*n^5 - 2*T^3*n^4 - 62*T^3*n^3 - 14*T^3*n^2 + 60*T^3*n + 16*T^3 + 16*T^2*n^5 + 20*T^2*n^4 - 80*T^2*n^3 + 68*T^2*n^2 - 56*T^2*n + 32*T^2 + 20*T*n^5 - 24*T*n^4 - 104*T*n^3 + 256*T*n^2 - 204*T*n + 56*T + 16*n^5 - 24*n^4 - 64*n^3 + 176*n^2 - 144*n + 40

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
noncomputable def EndpointReducedX2 (n T : ℝ) : ℝ :=
  (n - 1)*(5*T^2*n^3 + 16*T^2*n^2 + 13*T^2*n + 26*T^2 + 8*T*n^3 + 4*T*n^2 - 44*T*n + 32*T + 8*n^3 + 4*n^2 - 32*n + 20)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
noncomputable def EndpointReducedX3 (n _T : ℝ) : ℝ :=
  6*(n - 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem EndpointReduced_power (n X T : ℝ) :
    uniformFaceAQB3 n X T = EndpointReducedX0 n T+n*EndpointReducedX1 n T*X
      +n^2*EndpointReducedX2 n T*X^2+n^3*EndpointReducedX3 n T*X^3 := by
  unfold uniformFaceAQB3 uniformFaceACore EndpointReducedX0 EndpointReducedX1
    EndpointReducedX2 EndpointReducedX3
  ring

noncomputable def EndpointReducedCompact (n T L K w : ℝ) : ℝ :=
  n^3*(L^3*EndpointReducedX0 n T+L^2*K*w*EndpointReducedX1 n T
    +L*K^2*w^2*EndpointReducedX2 n T+K^3*w^3*EndpointReducedX3 n T)

theorem EndpointReducedCompact_eq (m z w : ℝ) (hM : uniformFaceALargeM m z ≠ 0) :
    uniformFaceAEndpointScaled m z w =
      EndpointReducedCompact (m+4) (m+3+z) (uniformFaceALargeM m z) (uniformFaceALargeK m z) w := by
  by_cases hn : m+4 = 0
  · simp [uniformFaceAEndpointScaled, EndpointReducedCompact, hn]
  · unfold uniformFaceAEndpointScaled
    rw [EndpointReduced_power]
    unfold EndpointReducedCompact
    field_simp [hM, hn]

noncomputable def EndpointReducedC0 (n T _L _K : ℝ) : ℝ :=
  (EndpointReducedX0 n T)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem EndpointReducedB0_eq (m z : ℝ) (hM : uniformFaceALargeM m z ≠ 0) :
    uniformFaceAEndpointB0 m z = (m+4)^3*(uniformFaceALargeM m z)^3*
      EndpointReducedC0 (m+4) (m+3+z) (uniformFaceALargeM m z) (uniformFaceALargeK m z) := by
  unfold uniformFaceAEndpointB0
  simp only [EndpointReducedCompact_eq m z _ hM]
  unfold EndpointReducedCompact EndpointReducedC0
  ring

noncomputable def EndpointReducedC1 (n T L K : ℝ) : ℝ :=
  K*(EndpointReducedX1 n T)/3 + L*(EndpointReducedX0 n T)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem EndpointReducedB1_eq (m z : ℝ) (hM : uniformFaceALargeM m z ≠ 0) :
    uniformFaceAEndpointB1 m z = (m+4)^3*(uniformFaceALargeM m z)^2*
      EndpointReducedC1 (m+4) (m+3+z) (uniformFaceALargeM m z) (uniformFaceALargeK m z) := by
  unfold uniformFaceAEndpointB1
  simp only [EndpointReducedCompact_eq m z _ hM]
  unfold EndpointReducedCompact EndpointReducedC1
  ring

noncomputable def EndpointReducedC2 (n T L K : ℝ) : ℝ :=
  K^2*(EndpointReducedX2 n T)/3 + 2*K*L*(EndpointReducedX1 n T)/3 + L^2*(EndpointReducedX0 n T)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem EndpointReducedB2_eq (m z : ℝ) (hM : uniformFaceALargeM m z ≠ 0) :
    uniformFaceAEndpointB2 m z = (m+4)^3*(uniformFaceALargeM m z)^1*
      EndpointReducedC2 (m+4) (m+3+z) (uniformFaceALargeM m z) (uniformFaceALargeK m z) := by
  unfold uniformFaceAEndpointB2
  simp only [EndpointReducedCompact_eq m z _ hM]
  unfold EndpointReducedCompact EndpointReducedC2
  ring

noncomputable def EndpointReducedC3 (n T L K : ℝ) : ℝ :=
  K^3*(EndpointReducedX3 n T) + K^2*L*(EndpointReducedX2 n T) + K*L^2*(EndpointReducedX1 n T) + L^3*(EndpointReducedX0 n T)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem EndpointReducedB3_eq (m z : ℝ) (hM : uniformFaceALargeM m z ≠ 0) :
    uniformFaceAEndpointB3 m z = (m+4)^3*(uniformFaceALargeM m z)^0*
      EndpointReducedC3 (m+4) (m+3+z) (uniformFaceALargeM m z) (uniformFaceALargeK m z) := by
  unfold uniformFaceAEndpointB3
  simp only [EndpointReducedCompact_eq m z _ hM]
  unfold EndpointReducedCompact EndpointReducedC3
  ring


end SSP.K3AllStages
