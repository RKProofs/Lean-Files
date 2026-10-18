import SSPLean.K3CyclicComplexFirstCoefficient

/-! # Negative-m compact coefficients for the complex first start

Here `r = -3m`.  The lower boundary of the root chart is interpolated with
`tau` so that both parameters range over the unit interval.
-/

-- These finite certificates deliberately use native_decide; the native trust
-- dependency is documented in README.md. Keep the exception local to the certificates.
set_option autoImplicit false

namespace SSP.K3CyclicComplex

open Dense

namespace NegativeCoeff

def bone : Bi := brat 1
def bzero : Bi := []

def trace : Bi := bsub bone br

def z : Bi :=
  badd
    (bmul (brat (1 / 3)) (bmul br (bsub (brat 2) br)))
    (bmul (brat (1 / 4))
      (bmul btau (bpow (bsub bone br) 2)))

def pair : Bi :=
  badd (bsub (bmul (brat (1 / 3)) (bpow br 2))
    (bmul (brat (2 / 3)) br)) z

def feedback : Bi :=
  bmul (bsub bone (bmul (brat (1 / 3)) br))
    (badd (bmul (brat (1 / 9)) (bpow br 2)) z)

def initialTriple : Bi × Bi × Bi := (bone, bzero, bzero)

def nextTriple (q : Bi × Bi × Bi) : Bi × Bi × Bi :=
  (q.2.1, q.2.2,
    badd (bsub (bmul trace q.2.2) (bmul pair q.2.1))
      (bmul feedback q.1))

def derivativeTriple : ℕ → Bi × Bi × Bi
  | 0 => initialTriple
  | n + 1 => nextTriple (derivativeTriple n)

def derivativeTableAux : ℕ → List Bi × (Bi × Bi × Bi)
  | 0 => ([], initialTriple)
  | n + 1 =>
      let q := derivativeTableAux n
      (q.2.1 :: q.1, nextTriple q.2)

def derivativeTable (count : ℕ) : List Bi :=
  (derivativeTableAux count).1.reverse

def curvatureCoefficient (N : ℕ) : Bi :=
  let derivatives := derivativeTable (N + 1)
  (List.range (N + 1)).foldl (fun p j =>
    badd p (bmul (brat (ComplexCoeff.kernel N j))
      (bmul (derivatives.getD j bzero)
        (derivatives.getD (N - j) bzero)))) bzero

def bernCoeff (N i j : ℕ) : ℚ :=
  ComplexCoeff.bernCoeffOf (curvatureCoefficient N) N i j

def certificateOK (N : ℕ) : Bool :=
  let source := curvatureCoefficient N
  let coeffs := ComplexCoeff.bernTable source N
  (List.range (N + 1)).all fun i =>
    (List.range (N / 2 + 1)).all fun j =>
      decide (0 ≤ ComplexCoeff.bcoeff coeffs i j)

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
theorem certificate_through_ten :
    (List.range 11).all certificateOK = true := by native_decide

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
theorem certificate_eleven_through_twenty :
    ((List.range 10).map (· + 11)).all certificateOK = true := by native_decide

set_option maxRecDepth 100000 in
set_option linter.style.nativeDecide false in
theorem certificate_twenty_one_through_thirty :
    ((List.range 10).map (· + 21)).all certificateOK = true := by native_decide

end NegativeCoeff

end SSP.K3CyclicComplex
