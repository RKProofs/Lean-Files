import SSPLean.K3CyclicComplexMiddleOscillation

/-! # Exact coefficient pairing for the complex-middle start -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

open scoped BigOperators

/-- Exact division-bearing pairing away from the degenerate frequency `omega = 0`. -/
theorem scalarCurvatureCoefficient_complex_pairing
    {rhoValue etaValue omega : ℝ} {N : ℕ}
    (hN : 3 ≤ N) (homega : omega ≠ 0)
    (hz : scalarZ rhoValue = omega ^ 2) :
    (scalarCurvatureCoefficient rhoValue etaValue N : ℂ) =
      (scalarA rhoValue etaValue : ℂ) ^ 2 * (2 : ℂ) ^ N +
      middleAmplitude (scalarA rhoValue etaValue)
          (scalarB rhoValue etaValue) omega ^ 2 *
        (2 * middleFrequency omega) ^ N +
      (starRingEnd ℂ) (middleAmplitude (scalarA rhoValue etaValue)
          (scalarB rhoValue etaValue) omega) ^ 2 *
        (-2 * middleFrequency omega) ^ N +
      2 * (scalarA rhoValue etaValue : ℂ) *
        middleAmplitude (scalarA rhoValue etaValue)
          (scalarB rhoValue etaValue) omega *
        geometricPairClosed N 1 (middleFrequency omega) +
      2 * (scalarA rhoValue etaValue : ℂ) *
        (starRingEnd ℂ) (middleAmplitude (scalarA rhoValue etaValue)
          (scalarB rhoValue etaValue) omega) *
        geometricPairClosed N 1 (-middleFrequency omega) := by
  unfold scalarCurvatureCoefficient
  push_cast
  simp_rw [scalarDerivative_complex_representation rhoValue etaValue omega
    homega hz]
  unfold complexOscillation
  simpa only [add_assoc] using three_geometric_opposite_pairing hN
    (scalarA rhoValue etaValue : ℂ)
    (middleAmplitude (scalarA rhoValue etaValue)
      (scalarB rhoValue etaValue) omega)
    ((starRingEnd ℂ) (middleAmplitude (scalarA rhoValue etaValue)
      (scalarB rhoValue etaValue) omega))
    (middleFrequency omega)

end SSP.K3CyclicComplex.MiddleCoeff
