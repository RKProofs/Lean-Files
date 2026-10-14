import SSPLean.K3CyclicComplexFirstCoefficient

/-! # Complex first-start compact certificate: degrees 31--40 -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.ComplexCoeff

set_option maxRecDepth 100000 in
theorem certificate_thirty_one_through_forty :
    ((List.range 10).map (· + 31)).all certificateOK = true := by
  native_decide

end SSP.K3CyclicComplex.ComplexCoeff
