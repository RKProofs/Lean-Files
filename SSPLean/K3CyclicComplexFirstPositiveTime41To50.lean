import SSPLean.K3CyclicComplexFirstPositiveCoefficient

/-! # Positive-m compact-time Bernstein certificate: time indices 41--50 -/

-- These finite certificates deliberately use native_decide; the native trust
-- dependency is documented in README.md. Keep the exception local to the certificates.
set_option autoImplicit false

namespace SSP.K3CyclicComplex.PositiveCoeff

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
theorem certificate_time_forty_one_through_fifty :
    certificateBlock 41 10 = true := by
  native_decide

end SSP.K3CyclicComplex.PositiveCoeff
