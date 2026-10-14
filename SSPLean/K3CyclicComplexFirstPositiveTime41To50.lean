import SSPLean.K3CyclicComplexFirstPositiveCoefficient

/-! # Positive-m compact-time Bernstein certificate: time indices 41--50 -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.PositiveCoeff

set_option maxRecDepth 100000 in
theorem certificate_time_forty_one_through_fifty :
    certificateBlock 41 10 = true := by
  native_decide

end SSP.K3CyclicComplex.PositiveCoeff
