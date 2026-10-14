import SSPLean.K3CyclicComplexFirstNegativeCoefficient

/-! # Negative-m complex first-start certificate: degrees 51--60 -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.NegativeCoeff

set_option maxRecDepth 100000 in
theorem certificate_fifty_one_through_sixty :
    ((List.range 10).map (· + 51)).all certificateOK = true := by
  native_decide

end SSP.K3CyclicComplex.NegativeCoeff
