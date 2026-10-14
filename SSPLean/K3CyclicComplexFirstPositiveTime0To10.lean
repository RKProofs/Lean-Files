import SSPLean.K3CyclicComplexFirstPositiveCoefficient

/-! # Positive-m compact-time Bernstein certificate: time indices 0--10 -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.PositiveCoeff

set_option maxRecDepth 100000 in
theorem certificate_time_zero_through_ten : certificateBlock 0 11 = true := by
  native_decide

end SSP.K3CyclicComplex.PositiveCoeff
