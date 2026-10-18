import SSPLean.K3CyclicComplexFirstPositiveCoefficient

/-! # Positive-m compact-time Bernstein certificate: time indices 51--60 -/

-- These finite certificates deliberately use native_decide; the native trust
-- dependency is documented in README.md. Keep the exception local to the certificates.
set_option autoImplicit false

namespace SSP.K3CyclicComplex.PositiveCoeff

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
theorem certificate_time_fifty_one_through_sixty :
    certificateBlock 51 10 = true := by
  native_decide

end SSP.K3CyclicComplex.PositiveCoeff
