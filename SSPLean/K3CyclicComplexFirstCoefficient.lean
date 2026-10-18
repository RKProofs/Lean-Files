import SSPLean.K3CyclicDensePoly

/-! # Reflected compact coefficients for the complex first start -/

-- These finite certificates deliberately use native_decide; the native trust
-- dependency is documented in README.md. Keep the exception local to the certificates.
set_option autoImplicit false

namespace SSP.K3CyclicComplex

open Dense

namespace ComplexCoeff

def bone : Bi := brat 1
def bzero : Bi := []

def trace : Bi := badd bone br

def z : Bi :=
  bmul (brat (1 / 12))
    (bmul btau (bsub (bsub (brat 3) (bmul (brat 2) br)) (bpow br 2)))

def pair : Bi :=
  badd (badd (bmul (brat (1 / 3)) (bpow br 2))
    (bmul (brat (2 / 3)) br)) z

def feedback : Bi :=
  bmul (badd bone (bmul (brat (1 / 3)) br))
    (badd (bmul (brat (1 / 9)) (bpow br 2)) z)

def initialTriple : Bi × Bi × Bi := (bone, bzero, bzero)

def nextTriple (q : Bi × Bi × Bi) : Bi × Bi × Bi :=
  (q.2.1, q.2.2,
    badd (bsub (bmul trace q.2.2) (bmul pair q.2.1))
      (bmul feedback q.1))

/-- `(hₙ,hₙ₊₁,hₙ₊₂)` for the unshifted first component. -/
def derivativeTriple : ℕ → Bi × Bi × Bi
  | 0 => initialTriple
  | n + 1 => nextTriple (derivativeTriple n)

def derivative (n : ℕ) : Bi := (derivativeTriple n).1

/-- A shared table avoids rebuilding the recurrence separately at every cut
of every curvature coefficient.  The table is stored in reverse while it is
built and reversed only once at the end. -/
def derivativeTableAux : ℕ → List Bi × (Bi × Bi × Bi)
  | 0 => ([], initialTriple)
  | n + 1 =>
      let q := derivativeTableAux n
      (q.2.1 :: q.1, nextTriple q.2)

def derivativeTable (count : ℕ) : List Bi := (derivativeTableAux count).1.reverse

def kernel (N j : ℕ) : ℚ :=
  ((((4 : ℤ) - N + ((N : ℤ) - 2 * j) ^ 2 : ℤ) : ℚ) / 2) * Nat.choose N j

def curvatureCoefficient (N : ℕ) : Bi :=
  let derivatives := derivativeTable (N + 1)
  (List.range (N + 1)).foldl (fun p j =>
    badd p (bmul (brat (kernel N j))
      (bmul (derivatives.getD j bzero) (derivatives.getD (N - j) bzero)))) bzero

def ucoeff (p : Uni) (i : ℕ) : ℚ := p.getD i 0
def bcoeff (p : Bi) (i j : ℕ) : ℚ := ucoeff (p.getD j []) i

/-- First convert every `r`-row.  Materializing this intermediate table
changes the executable certificate from a repeated fourfold conversion to
two shared triangular conversions. -/
def innerBernCoeff (p : Bi) (N i b : ℕ) : ℚ :=
  (List.range (i + 1)).foldl (fun total a =>
    total + bcoeff p a b *
      (Nat.choose i a : ℚ) / Nat.choose N a) 0

def innerBernTable (p : Bi) (N : ℕ) : Bi :=
  (List.range (N / 2 + 1)).map fun b =>
    (List.range (N + 1)).map fun i => innerBernCoeff p N i b

def outerBernCoeff (inner : Bi) (N i j : ℕ) : ℚ :=
  (List.range (j + 1)).foldl (fun total b =>
    total + bcoeff inner i b *
      (Nat.choose j b : ℚ) / Nat.choose (N / 2) b) 0

def bernTable (p : Bi) (N : ℕ) : Bi :=
  let inner := innerBernTable p N
  (List.range (N / 2 + 1)).map fun j =>
    (List.range (N + 1)).map fun i => outerBernCoeff inner N i j

def bernCoeffOf (p : Bi) (N i j : ℕ) : ℚ := bcoeff (bernTable p N) i j

def bernCoeff (N i j : ℕ) : ℚ := bernCoeffOf (curvatureCoefficient N) N i j

def bernInner (n i : ℕ) : Bi :=
  bmul (brat (Nat.choose n i : ℚ))
    (bmul (bpow br i) (bpow (bsub bone br) (n - i)))

def bernOuter (n i : ℕ) : Bi :=
  bmul (brat (Nat.choose n i : ℚ))
    (bmul (bpow btau i) (bpow (bsub bone btau) (n - i)))

def bernsteinReconstruction (N : ℕ) : Bi :=
  let source := curvatureCoefficient N
  (List.range (N + 1)).foldl (fun acc i =>
    (List.range (N / 2 + 1)).foldl (fun acc j =>
      badd acc (bmul (brat (bernCoeffOf source N i j))
        (bmul (bernInner N i) (bernOuter (N / 2) j)))) acc) bzero

def certificateOK (N : ℕ) : Bool :=
  let source := curvatureCoefficient N
  let coeffs := bernTable source N
  (List.range (N + 1)).all fun i =>
    (List.range (N / 2 + 1)).all fun j => decide (0 ≤ bcoeff coeffs i j)

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

end ComplexCoeff

end SSP.K3CyclicComplex
