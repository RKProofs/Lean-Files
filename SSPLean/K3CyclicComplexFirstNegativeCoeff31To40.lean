import SSPLean.K3CyclicComplexFirstNegativeCoefficient

/-! # Negative-m complex first-start certificate: degrees 31--40 -/

-- These finite certificates deliberately use native_decide; the native trust
-- dependency is documented in README.md. Keep the exception local to the certificates.
set_option autoImplicit false

namespace SSP.K3CyclicComplex.NegativeCoeff

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
theorem certificate_thirty_one_through_forty :
    ((List.range 10).map (· + 31)).all certificateOK = true := by
  native_decide

end SSP.K3CyclicComplex.NegativeCoeff
