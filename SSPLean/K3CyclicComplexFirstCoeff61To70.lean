import SSPLean.K3CyclicComplexFirstCoefficient

/-! # Complex first-start compact certificate: degrees 61--70 -/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.ComplexCoeff

set_option maxRecDepth 100000 in
theorem certificate_sixty_one_through_seventy :
    ((List.range 10).map (· + 61)).all certificateOK = true := by
  native_decide

end SSP.K3CyclicComplex.ComplexCoeff
