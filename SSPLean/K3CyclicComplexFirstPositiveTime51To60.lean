import SSPLean.K3CyclicComplexFirstPositiveCoefficient

/-! # Positive-m compact-time Bernstein certificate: time indices 51--60 -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.PositiveCoeff

set_option maxRecDepth 100000 in
theorem certificate_time_fifty_one_through_sixty :
    certificateBlock 51 10 = true := by
  native_decide

end SSP.K3CyclicComplex.PositiveCoeff
