import SSPLean.K3CyclicComplexFirstTail

/-! # Small computable dense bivariate polynomials

This purpose-built representation is used only for exact rational
certificates.  Unlike Mathlib's abstract `Polynomial`, all operations here
are executable by `native_decide`.
-/

set_option autoImplicit false

namespace SSP.K3CyclicComplex.Dense

abbrev Uni := List ℚ
abbrev Bi := List Uni

def uadd : Uni → Uni → Uni
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: uadd p q

def uscale (a : ℚ) : Uni → Uni := List.map (a * ·)

def umul : Uni → Uni → Uni
  | [], _ => []
  | _ :: _, [] => []
  | a :: p, q => uadd (uscale a q) (0 :: umul p q)

def upow (p : Uni) : ℕ → Uni
  | 0 => [1]
  | n + 1 => umul p (upow p n)

def badd : Bi → Bi → Bi
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => uadd a b :: badd p q

def bscale (a : Uni) : Bi → Bi := List.map (umul a ·)

def bmul : Bi → Bi → Bi
  | [], _ => []
  | _ :: _, [] => []
  | a :: p, q => badd (bscale a q) ([] :: bmul p q)

def bpow (p : Bi) : ℕ → Bi
  | 0 => [[1]]
  | n + 1 => bmul p (bpow p n)

def brat (q : ℚ) : Bi := [[q]]
def br : Bi := [[0, 1]]
def btau : Bi := [[], [1]]
def bneg (p : Bi) : Bi := bscale [-1] p
def bsub (p q : Bi) : Bi := badd p (bneg q)

def ueval (p : Uni) (r : ℝ) : ℝ :=
  p.foldr (fun a v => (a : ℝ) + r * v) 0

def beval (p : Bi) (r t : ℝ) : ℝ :=
  p.foldr (fun a v => ueval a r + t * v) 0

/-- Remove trailing zero coefficients from a univariate dense polynomial. -/
def unorm : Uni → Uni
  | [] => []
  | a :: p =>
      let q := unorm p
      if q.isEmpty then if a = 0 then [] else [a] else a :: q

/-- Normalize inner coefficients and remove trailing zero rows. -/
def bnorm : Bi → Bi
  | [] => []
  | a :: p =>
      let a' := unorm a
      let q := bnorm p
      if q.isEmpty then if a'.isEmpty then [] else [a'] else a' :: q

@[simp] theorem ueval_nil (r : ℝ) : ueval [] r = 0 := rfl
@[simp] theorem ueval_cons (a : ℚ) (p : Uni) (r : ℝ) :
    ueval (a :: p) r = (a : ℝ) + r * ueval p r := rfl

theorem ueval_add (p q : Uni) (r : ℝ) :
    ueval (uadd p q) r = ueval p r + ueval q r := by
  induction p generalizing q with
  | nil => simp [uadd]
  | cons a p ih =>
      cases q with
      | nil => simp [uadd]
      | cons b q =>
          simp only [uadd, ueval_cons, ih]
          push_cast
          ring

theorem ueval_scale (a : ℚ) (p : Uni) (r : ℝ) :
    ueval (uscale a p) r = (a : ℝ) * ueval p r := by
  induction p with
  | nil => simp [uscale]
  | cons b p ih =>
      simp only [uscale, List.map, ueval_cons]
      rw [show ueval (List.map (fun x => a * x) p) r =
          (a : ℝ) * ueval p r by simpa [uscale] using ih]
      push_cast
      ring

theorem ueval_mul (p q : Uni) (r : ℝ) :
    ueval (umul p q) r = ueval p r * ueval q r := by
  induction p with
  | nil => simp [umul]
  | cons a p ih =>
      cases q with
      | nil => simp [umul]
      | cons b q =>
          simp only [umul, ueval_add, ueval_scale, ueval_cons, ih]
          ring

theorem ueval_pow (p : Uni) (n : ℕ) (r : ℝ) :
    ueval (upow p n) r = ueval p r ^ n := by
  induction n with
  | zero => simp [upow, ueval]
  | succ n ih => simp [upow, ueval_mul, ih, pow_succ, mul_comm]

theorem ueval_unorm (p : Uni) (r : ℝ) : ueval (unorm p) r = ueval p r := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      simp only [unorm]
      generalize hq : unorm p = q
      cases q with
      | nil =>
          simp only [List.isEmpty_nil, Bool.true_eq, if_true]
          by_cases ha : a = 0
          · simp [ha, ← ih, hq]
          · simp [ha, ← ih, hq]
      | cons b q =>
          simp only [List.isEmpty_cons]
          simp only [Bool.false_eq_true, if_false, ueval_cons]
          have hv : ueval (b :: q) r = ueval p r := by
            rw [← hq]
            exact ih
          change (a : ℝ) + r * ueval (b :: q) r =
            (a : ℝ) + r * ueval p r
          rw [hv]

@[simp] theorem beval_nil (r t : ℝ) : beval [] r t = 0 := rfl
@[simp] theorem beval_cons (a : Uni) (p : Bi) (r t : ℝ) :
    beval (a :: p) r t = ueval a r + t * beval p r t := rfl

theorem beval_add (p q : Bi) (r t : ℝ) :
    beval (badd p q) r t = beval p r t + beval q r t := by
  induction p generalizing q with
  | nil => simp [badd]
  | cons a p ih =>
      cases q with
      | nil => simp [badd]
      | cons b q =>
          simp only [badd, beval_cons, ueval_add, ih]
          ring

theorem beval_scale (a : Uni) (p : Bi) (r t : ℝ) :
    beval (bscale a p) r t = ueval a r * beval p r t := by
  induction p with
  | nil => simp [bscale]
  | cons b p ih =>
      simp only [bscale, List.map, beval_cons, ueval_mul]
      rw [show beval (List.map (fun x => umul a x) p) r t =
          ueval a r * beval p r t by simpa [bscale] using ih]
      ring

theorem beval_mul (p q : Bi) (r t : ℝ) :
    beval (bmul p q) r t = beval p r t * beval q r t := by
  induction p with
  | nil => simp [bmul]
  | cons a p ih =>
      cases q with
      | nil => simp [bmul]
      | cons b q =>
          simp only [bmul, beval_add, beval_scale, beval_cons, ih, ueval_nil]
          ring

theorem beval_pow (p : Bi) (n : ℕ) (r t : ℝ) :
    beval (bpow p n) r t = beval p r t ^ n := by
  induction n with
  | zero => simp [bpow, beval, ueval]
  | succ n ih => simp [bpow, beval_mul, ih, pow_succ, mul_comm]

@[simp] theorem beval_neg (p : Bi) (r t : ℝ) :
    beval (bneg p) r t = -beval p r t := by
  simp [bneg, beval_scale, ueval]

@[simp] theorem beval_sub (p q : Bi) (r t : ℝ) :
    beval (bsub p q) r t = beval p r t - beval q r t := by
  simp [bsub, beval_add]
  ring

theorem beval_bnorm (p : Bi) (r t : ℝ) : beval (bnorm p) r t = beval p r t := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      simp only [bnorm]
      generalize ha' : unorm a = a'
      generalize hq : bnorm p = q
      cases q with
      | nil =>
          simp only [List.isEmpty_nil, Bool.true_eq, if_true]
          cases a' with
          | nil => simp [← ueval_unorm a r, ha', ← ih, hq]
          | cons b a' => simp [← ueval_unorm a r, ha', ← ih, hq]
      | cons b q =>
          simp only [List.isEmpty_cons]
          simp only [Bool.false_eq_true, if_false, beval_cons]
          have hva : ueval a' r = ueval a r := by
            rw [← ha']
            exact ueval_unorm a r
          have hvp : beval (b :: q) r t = beval p r t := by
            rw [← hq]
            exact ih
          change ueval a' r + t * beval (b :: q) r t =
            ueval a r + t * beval p r t
          rw [hva, hvp]

theorem beval_eq_of_bnorm_eq {p q : Bi} (h : bnorm p = bnorm q) (r t : ℝ) :
    beval p r t = beval q r t := by
  rw [← beval_bnorm p r t, ← beval_bnorm q r t, h]

@[simp] theorem beval_brat (q : ℚ) (r t : ℝ) :
    beval (brat q) r t = (q : ℝ) := by simp [brat, beval, ueval]

@[simp] theorem beval_br (r t : ℝ) : beval br r t = r := by
  simp [br, beval, ueval]

@[simp] theorem beval_btau (r t : ℝ) : beval btau r t = t := by
  simp [btau, beval, ueval]

end SSP.K3CyclicComplex.Dense
