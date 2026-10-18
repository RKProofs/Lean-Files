import SSPLean.K3CyclicComplexFirstPositiveCoefficient

/-! # Positive-m compact-time Bernstein certificate: time indices 0--10 -/

-- These finite certificates deliberately use native_decide; the native trust
-- dependency is documented in README.md. Keep the exception local to the certificates.
set_option autoImplicit false

namespace SSP.K3CyclicComplex.PositiveCoeff

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
theorem certificate_time_zero_through_ten : certificateBlock 0 11 = true := by
  native_decide

end SSP.K3CyclicComplex.PositiveCoeff
