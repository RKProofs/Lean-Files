import SSPLean.K3CyclicComplexFirstCoefficient

/-! # Complex first-start compact certificate: degrees 61--70 -/

-- These finite certificates deliberately use native_decide; the native trust
-- dependency is documented in README.md. Keep the exception local to the certificates.
set_option autoImplicit false

namespace SSP.K3CyclicComplex.ComplexCoeff

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
theorem certificate_sixty_one_through_seventy :
    ((List.range 10).map (· + 61)).all certificateOK = true := by
  native_decide

end SSP.K3CyclicComplex.ComplexCoeff
