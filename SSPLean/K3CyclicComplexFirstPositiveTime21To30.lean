import SSPLean.K3CyclicComplexFirstPositiveCoefficient

/-! # Positive-m compact-time Bernstein certificate: time indices 21--30 -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.PositiveCoeff

set_option maxRecDepth 100000 in
theorem certificate_time_twenty_one_through_thirty :
    certificateBlock 21 10 = true := by
  native_decide

end SSP.K3CyclicComplex.PositiveCoeff
