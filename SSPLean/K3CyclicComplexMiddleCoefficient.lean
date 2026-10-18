import SSPLean.K3CyclicComplexFirstBernsteinConversion

/-! # Exact compact-chart coefficients for the complex middle start -/

-- These finite certificates deliberately use native_decide; the native trust
-- dependency is documented in README.md. Keep the exception local to the certificates.
set_option autoImplicit false

namespace SSP.K3CyclicComplex.MiddleCoeff

open SSP.K3CyclicComplex.Dense

def bone : Bi := brat 1
def bzero : Bi := []
def rho : Bi := br
def eta : Bi := btau

def z : Bi := bmul (brat (1 / 3)) (bsub bone (bpow rho 2))

def A : Bi :=
  bmul (brat (1 / 3))
    (badd (bsub (brat 2) (bmul (brat 2) rho)) (bmul rho eta))

def B : Bi := badd (bsub bone A) z

def cosineSign (n : ℕ) : ℚ :=
  match n % 4 with
  | 0 => 1
  | 2 => -1
  | _ => 0

def sineSign (n : ℕ) : ℚ :=
  match n % 4 with
  | 1 => 1
  | 3 => -1
  | _ => 0

/-- `K⁽ⁿ⁾(0)` after the complete `(rho,eta)` chart substitution. -/
def derivative (n : ℕ) : Bi :=
  badd
    (bmul A (bsub bone (bmul (brat (cosineSign n)) (bpow z (n / 2)))))
    (bmul B (bmul (brat (sineSign n)) (bpow z ((n - 1) / 2))))

def kernel (N j : ℕ) : ℚ :=
  ((((2 : ℤ) - N + ((N : ℤ) - 2 * j) ^ 2 : ℤ) : ℚ) / 2) *
    Nat.choose N j

def curvatureCoefficient (N : ℕ) : Bi :=
  (List.range (N + 1)).foldl (fun p j =>
    badd p (bmul (brat (kernel N j))
      (bmul (derivative j) (derivative (N - j))))) bzero

def certificateDegree (N : ℕ) : ℕ := N + 3

def certificateOK (N : ℕ) : Bool :=
  let degree := certificateDegree N
  let coeffs := SSP.K3CyclicComplex.ComplexCoeff.bernTable
    (curvatureCoefficient N) degree
  (List.range (degree + 1)).all fun i =>
    (List.range (degree / 2 + 1)).all fun j =>
      decide (0 ≤ SSP.K3CyclicComplex.ComplexCoeff.bcoeff coeffs i j)

def degreeOK (N : ℕ) : Bool :=
  let degree := certificateDegree N
  let source := curvatureCoefficient N
  decide (source.length ≤ degree / 2 + 1 ∧
    ∀ row ∈ source, row.length ≤ degree + 1)

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
theorem certificate_four_through_twelve :
    ((List.range 9).map (· + 4)).all certificateOK = true := by native_decide

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
theorem certificate_thirteen_through_eighteen :
    ((List.range 6).map (· + 13)).all certificateOK = true := by native_decide

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
theorem certificate_nineteen_through_twenty_four :
    ((List.range 6).map (· + 19)).all certificateOK = true := by native_decide

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
theorem degree_four_through_twenty_four :
    ((List.range 21).map (· + 4)).all degreeOK = true := by native_decide

end SSP.K3CyclicComplex.MiddleCoeff
