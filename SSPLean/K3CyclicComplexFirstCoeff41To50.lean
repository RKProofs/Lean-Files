import SSPLean.K3CyclicComplexFirstCoefficient

/-! # Complex first-start compact certificate: degrees 41--50 -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.ComplexCoeff

set_option maxRecDepth 100000 in
theorem certificate_forty_one_through_fifty :
    ((List.range 10).map (· + 41)).all certificateOK = true := by
  native_decide

end SSP.K3CyclicComplex.ComplexCoeff
