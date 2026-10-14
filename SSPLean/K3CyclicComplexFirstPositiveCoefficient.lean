import SSPLean.K3CyclicComplexFirstCoefficient

/-! # Positive-m full compact certificate for the complex first start

This is the unshifted normalized component `F = H / (1 + z)`, with
`m = r/3` and `z = tau * (3 - 2r - r^2) / 12`.  Unlike the negative chart,
its individual curvature coefficients need not be positive.  We therefore
convert the complete degree-70 Taylor polynomial at `x = 10u` to a
three-variable tensor Bernstein basis.
-/

set_option autoImplicit false

namespace SSP.K3CyclicComplex

open Dense

namespace PositiveCoeff

def order : ℕ := 70

def bone : Bi := brat 1
def bzero : Bi := []
def m : Bi := bmul (brat (1 / 3)) br

def z : Bi :=
  bmul (brat (1 / 12))
    (bmul btau (bsub (bsub (brat 3) (bmul (brat 2) br)) (bpow br 2)))

def initialTriple : Bi × Bi × Bi :=
  (bone, bneg m, bpow m 2)

def nextTriple (q : Bi × Bi × Bi) : Bi × Bi × Bi :=
  (q.2.1, q.2.2,
    badd (bsub q.2.2 (bmul z q.2.1)) (bmul z q.1))

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

def curvatureCoefficientFrom (derivatives : List Bi) (N : ℕ) : Bi :=
  (List.range (N + 1)).foldl (fun p j =>
    badd p (bmul (brat (ComplexCoeff.kernel N j))
      (bmul (derivatives.getD j bzero)
        (derivatives.getD (N - j) bzero)))) bzero

def powerTableUpTo (count : ℕ) : List Bi :=
  let derivatives := derivativeTable count
  (List.range count).map fun N =>
    bmul (brat ((10 : ℚ) ^ N / Nat.factorial N))
      (curvatureCoefficientFrom derivatives N)

/-- The coefficient polynomial of the `k`th degree-70 Bernstein basis
function in the compact-time variable `u`. -/
def timeBernPolyFrom (powers : List Bi) (k : ℕ) : Bi :=
  (List.range (k + 1)).foldl (fun total N =>
    badd total (bmul
      (brat ((Nat.choose k N : ℚ) / Nat.choose order N))
      (powers.getD N bzero))) bzero

def spatialBernTableFrom (powers : List Bi) (k : ℕ) : Bi :=
  ComplexCoeff.bernTable (timeBernPolyFrom powers k) order

def certificateAtFrom (powers : List Bi) (k : ℕ) : Bool :=
  let coeffs := spatialBernTableFrom powers k
  (List.range (order + 1)).all fun i =>
    (List.range (order / 2 + 1)).all fun j =>
      decide (1 < ComplexCoeff.bcoeff coeffs i j)

def certificateAt (k : ℕ) : Bool :=
  certificateAtFrom (powerTableUpTo (k + 1)) k

def certificateBlock (start count : ℕ) : Bool :=
  let powers := powerTableUpTo (start + count)
  ((List.range count).map (· + start)).all (certificateAtFrom powers)

set_option maxRecDepth 100000 in
theorem certificate_at_zero : certificateAt 0 = true := by
  native_decide

end PositiveCoeff

end SSP.K3CyclicComplex
