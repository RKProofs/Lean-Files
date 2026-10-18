import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Data.List.GetD
import SSPLean.K3CyclicComplexFirstCoefficient

/-! # Tensor Bernstein conversion for dense bivariate polynomials

This module proves that the executable two-pass Bernstein conversion used by
the compact complex first-start certificate reconstructs the original dense
polynomial exactly.
-/

set_option autoImplicit false

open Polynomial
open scoped BigOperators Polynomial

namespace SSP.K3CyclicComplex

open Dense ComplexCoeff

theorem triangle_swap {M : Type*} [AddCommMonoid M]
    (F : ℕ → ℕ → M) (n : ℕ) :
    (∑ a ∈ Finset.range (n + 1),
      ∑ j ∈ Finset.range (n - a + 1), F a (a + j)) =
    ∑ i ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (i + 1), F a i := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij'
      (fun x _ => ⟨x.1 + x.2, x.1⟩)
      (fun x _ => ⟨x.2, x.1 - x.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    have ha : x.1 ≤ n := by omega
    have hj : x.2 ≤ n - x.1 := by omega
    have haj : x.1 + x.2 ≤ n := by
      rw [add_comm]
      exact (Nat.le_sub_iff_add_le ha).mp hj
    constructor <;> omega
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx ⊢
    have ha : x.2 ≤ x.1 := by omega
    have hi : x.1 ≤ n := by omega
    have hsub : x.1 - x.2 ≤ n - x.2 := Nat.sub_le_sub_right hi _
    constructor <;> omega
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    simp
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    have ha : x.2 ≤ x.1 := by omega
    apply Sigma.ext
    · change x.2 + (x.1 - x.2) = x.1
      exact Nat.add_sub_of_le ha
    · simp only [heq_eq_eq]
  · intro x hx
    rfl

theorem monomial_bern (n k : ℕ) (hk : k ≤ n) :
    X ^ k = ∑ j ∈ Finset.range (n - k + 1),
      C ((Nat.choose (k + j) k : ℚ) / Nat.choose n k) *
        bernsteinPolynomial ℚ n (k + j) := by
  symm
  calc
    _ = ∑ j ∈ Finset.range (n - k + 1),
        X ^ k * bernsteinPolynomial ℚ (n - k) j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjle : j ≤ n - k := by
        have := Finset.mem_range.mp hj
        omega
      have hkj : k + j ≤ n := by omega
      have hchooseNat := Nat.choose_mul (n := n) (k := k + j) (s := k)
        (by omega : k ≤ k + j)
      have hchoose : (Nat.choose n k : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos hk).ne'
      have hc :
          (Nat.choose (k + j) k : ℚ) / Nat.choose n k *
              Nat.choose n (k + j) = Nat.choose (n - k) j := by
        rw [div_mul_eq_mul_div, div_eq_iff hchoose]
        exact_mod_cast (by simpa [mul_comm] using hchooseNat)
      unfold bernsteinPolynomial
      rw [show n - (k + j) = n - k - j by omega,
        show X ^ (k + j) = X ^ k * X ^ j by rw [pow_add]]
      have hcP :
          C ((Nat.choose (k + j) k : ℚ) / Nat.choose n k) *
              (Nat.choose n (k + j) : ℚ[X]) =
            (Nat.choose (n - k) j : ℚ[X]) := by
        change C ((Nat.choose (k + j) k : ℚ) / Nat.choose n k) *
            C (Nat.choose n (k + j) : ℚ) = C (Nat.choose (n - k) j : ℚ)
        simpa only [map_mul] using congrArg C hc
      calc
        _ = (C ((Nat.choose (k + j) k : ℚ) / Nat.choose n k) *
              (Nat.choose n (k + j) : ℚ[X])) *
              (X ^ k * X ^ j) * (1 - X) ^ (n - k - j) := by ring
        _ = (Nat.choose (n - k) j : ℚ[X]) *
              (X ^ k * X ^ j) * (1 - X) ^ (n - k - j) := by rw [hcP]
        _ = _ := by ring
    _ = X ^ k * (∑ j ∈ Finset.range (n - k + 1),
        bernsteinPolynomial ℚ (n - k) j) := by rw [Finset.mul_sum]
    _ = X ^ k := by rw [bernsteinPolynomial.sum]; simp

noncomputable def bernCoeffPoly (p : ℚ[X]) (n i : ℕ) : ℚ :=
  ∑ a ∈ Finset.range (i + 1),
    p.coeff a * (Nat.choose i a : ℚ) / Nat.choose n a

theorem poly_eq_bernstein (p : ℚ[X]) (n : ℕ) (hdeg : p.natDegree ≤ n) :
    p = ∑ i ∈ Finset.range (n + 1),
      C (bernCoeffPoly p n i) * bernsteinPolynomial ℚ n i := by
  calc
    p = ∑ a ∈ Finset.range (n + 1), C (p.coeff a) * X ^ a :=
      p.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hdeg)
    _ = ∑ a ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (n - a + 1),
          C (p.coeff a * (Nat.choose (a + j) a : ℚ) / Nat.choose n a) *
            bernsteinPolynomial ℚ n (a + j) := by
      apply Finset.sum_congr rfl
      intro a ha
      have han : a ≤ n := by
        have := Finset.mem_range.mp ha
        omega
      rw [monomial_bern n a han, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← mul_assoc, ← map_mul]
      ring_nf
    _ = ∑ i ∈ Finset.range (n + 1),
        ∑ a ∈ Finset.range (i + 1),
          C (p.coeff a * (Nat.choose i a : ℚ) / Nat.choose n a) *
            bernsteinPolynomial ℚ n i := by
      exact triangle_swap (fun a i =>
        C (p.coeff a * (Nat.choose i a : ℚ) / Nat.choose n a) *
          bernsteinPolynomial ℚ n i) n
    _ = ∑ i ∈ Finset.range (n + 1),
        C (bernCoeffPoly p n i) * bernsteinPolynomial ℚ n i := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold bernCoeffPoly
      rw [map_sum, Finset.sum_mul]

noncomputable def upoly : List ℚ → ℚ[X]
  | [] => 0
  | a :: p => C a + X * upoly p

theorem upoly_coeff (p : List ℚ) (m : ℕ) :
    (upoly p).coeff m = p.getD m 0 := by
  induction p generalizing m with
  | nil => simp [upoly]
  | cons a p ih =>
      cases m with
      | zero => simp [upoly]
      | succ m => simp [upoly, ih]

theorem upoly_natDegree_le {p : List ℚ} {n : ℕ} (h : p.length ≤ n + 1) :
    (upoly p).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [upoly_coeff, List.getD_eq_default]
  omega

theorem upoly_eval (p : List ℚ) (r : ℝ) :
    (upoly p).eval₂ (algebraMap ℚ ℝ) r =
      p.foldr (fun a v => (a : ℝ) + r * v) 0 := by
  induction p with
  | nil => simp [upoly]
  | cons a p ih => simp [upoly, ih]

theorem range_foldl_add {R : Type*} [AddCommMonoid R]
    (f : ℕ → R) (n : ℕ) :
    (List.range n).foldl (fun total i => total + f i) 0 =
      ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ih]
      simp

theorem horner_eq_sum_getD {R : Type*} [CommSemiring R]
    (l : List R) (x : R) (n : ℕ) (h : l.length ≤ n) :
    l.foldr (fun a v => a + x * v) 0 =
      ∑ i ∈ Finset.range n, l.getD i 0 * x ^ i := by
  induction n generalizing l with
  | zero =>
      have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [this]
  | succ n ih =>
      cases l with
      | nil => simp
      | cons a l =>
          have hl : l.length ≤ n := by simpa using h
          rw [Finset.sum_range_succ']
          simp only [List.foldr_cons, List.getD_cons_zero, pow_zero, mul_one,
            List.getD_cons_succ, pow_succ]
          rw [ih l hl, Finset.mul_sum]
          rw [add_comm a]
          apply congrArg (· + a)
          apply Finset.sum_congr rfl
          intro i hi
          ring

theorem ueval_eq_sum_getD (l : List ℚ) (x : ℝ) (n : ℕ)
    (h : l.length ≤ n) :
    ueval l x =
      ∑ i ∈ Finset.range n, (l.getD i 0 : ℝ) * x ^ i := by
  induction n generalizing l with
  | zero =>
      have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
      simp [this]
  | succ n ih =>
      cases l with
      | nil => simp
      | cons a l =>
          have hl : l.length ≤ n := by simpa using h
          rw [Finset.sum_range_succ']
          simp only [ueval_cons, List.getD_cons_zero, pow_zero, mul_one,
            List.getD_cons_succ, pow_succ]
          rw [ih l hl, Finset.mul_sum]
          rw [add_comm (a : ℝ)]
          apply congrArg (· + (a : ℝ))
          apply Finset.sum_congr rfl
          intro i hi
          ring


theorem innerBernCoeff_eq_poly (p : Bi) (N i b : ℕ) :
    innerBernCoeff p N i b =
      bernCoeffPoly (upoly (p.getD b [])) N i := by
  unfold innerBernCoeff bernCoeffPoly
  rw [range_foldl_add]
  apply Finset.sum_congr rfl
  intro a ha
  rw [upoly_coeff]
  rfl

def innerColumn (p : Bi) (i : ℕ) : Uni := p.map fun row => ucoeff row i

theorem outerBernCoeff_eq_poly (p : Bi) (N i j : ℕ) :
    outerBernCoeff p N i j =
      bernCoeffPoly (upoly (innerColumn p i)) (N / 2) j := by
  unfold outerBernCoeff bernCoeffPoly innerColumn
  rw [range_foldl_add]
  apply Finset.sum_congr rfl
  intro b hb
  rw [upoly_coeff]
  have hc : (p.map fun row => ucoeff row i).getD b 0 = bcoeff p i b := by
    change (p.map fun row => ucoeff row i).getD b (ucoeff [] i) = _
    rw [List.getD_map]
    rfl
  rw [hc]

theorem bcoeff_innerBernTable {p : Bi} {N i b : ℕ}
    (hi : i ≤ N) (hb : b ≤ N / 2) :
    bcoeff (innerBernTable p N) i b = innerBernCoeff p N i b := by
  unfold innerBernTable bcoeff
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range, ucoeff]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem bernCoeffOf_eq_outer {p : Bi} {N i j : ℕ}
    (hi : i ≤ N) (hj : j ≤ N / 2) :
    bernCoeffOf p N i j = outerBernCoeff (innerBernTable p N) N i j := by
  unfold bernCoeffOf bernTable bcoeff
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range, ucoeff]
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem beval_eq_sum_rows (p : Bi) (r t : ℝ) (m : ℕ)
    (h : p.length ≤ m) :
    beval p r t = ∑ b ∈ Finset.range m,
      ueval (p.getD b []) r * t ^ b := by
  have hs := horner_eq_sum_getD
    (p.map fun row => ueval row r) t m (by simpa using h)
  change (p.map fun row => ueval row r).foldr
      (fun a v => a + t * v) 0 = _ at hs
  change p.foldr (fun row v => ueval row r + t * v) 0 = _
  have hmap : (p.map fun row => ueval row r).foldr
      (fun a v => a + t * v) 0 =
      p.foldr (fun row v => ueval row r + t * v) 0 := List.foldr_map
  rw [← hmap]
  rw [hs]
  apply Finset.sum_congr rfl
  intro b hb
  change (p.map fun row => ueval row r).getD b (ueval [] r) * t ^ b = _
  rw [List.getD_map]

theorem ueval_eq_bernstein (p : Uni) (n : ℕ) (hdeg : p.length ≤ n + 1)
    (r : ℝ) :
    ueval p r = ∑ i ∈ Finset.range (n + 1),
      (bernCoeffPoly (upoly p) n i : ℝ) *
        ((Nat.choose n i : ℝ) * r ^ i * (1 - r) ^ (n - i)) := by
  change p.foldr (fun a v => (a : ℝ) + r * v) 0 = _
  rw [← upoly_eval]
  conv_lhs => rw [poly_eq_bernstein (upoly p) n (upoly_natDegree_le hdeg)]
  rw [Polynomial.eval₂_finsetSum]
  simp [bernsteinPolynomial]

theorem ueval_innerColumn_eq (p : Bi) (N i : ℕ) (hi : i ≤ N) (t : ℝ) :
    ueval (innerColumn (innerBernTable p N) i) t =
      ∑ b ∈ Finset.range (N / 2 + 1),
        (innerBernCoeff p N i b : ℝ) * t ^ b := by
  let q := innerColumn (innerBernTable p N) i
  have hlen : q.length = N / 2 + 1 := by
    simp [q, innerColumn, innerBernTable]
  change ueval q t = _
  rw [ueval_eq_sum_getD q t (N / 2 + 1) (by omega)]
  apply Finset.sum_congr rfl
  intro b hb
  have hb' : b ≤ N / 2 := by
    have := Finset.mem_range.mp hb
    omega
  have hq : q.getD b 0 = innerBernCoeff p N i b := by
    dsimp [q, innerColumn]
    change ((innerBernTable p N).map fun row => ucoeff row i).getD b
        (ucoeff [] i) = _
    rw [List.getD_map]
    exact bcoeff_innerBernTable hi hb'
  rw [hq]

theorem ueval_innerColumn_bernstein (p : Bi) (N i : ℕ) (t : ℝ) :
    ueval (innerColumn (innerBernTable p N) i) t =
      ∑ j ∈ Finset.range (N / 2 + 1),
        (outerBernCoeff (innerBernTable p N) N i j : ℝ) *
          ((Nat.choose (N / 2) j : ℝ) * t ^ j *
            (1 - t) ^ (N / 2 - j)) := by
  let q := innerColumn (innerBernTable p N) i
  have hlen : q.length = N / 2 + 1 := by
    simp [q, innerColumn, innerBernTable]
  rw [ueval_eq_bernstein q (N / 2) (by omega)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [outerBernCoeff_eq_poly]

theorem beval_eq_tensorBernstein (p : Bi) (N : ℕ)
    (houter : p.length ≤ N / 2 + 1)
    (hinner : ∀ b, b ≤ N / 2 → (p.getD b []).length ≤ N + 1)
    (r t : ℝ) :
    beval p r t =
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N / 2 + 1),
        (bernCoeffOf p N i j : ℝ) *
          ((Nat.choose N i : ℝ) * r ^ i * (1 - r) ^ (N - i)) *
          ((Nat.choose (N / 2) j : ℝ) * t ^ j *
            (1 - t) ^ (N / 2 - j)) := by
  rw [beval_eq_sum_rows p r t (N / 2 + 1) houter]
  calc
    (∑ b ∈ Finset.range (N / 2 + 1),
        ueval (p.getD b []) r * t ^ b) =
        ∑ b ∈ Finset.range (N / 2 + 1),
          ∑ i ∈ Finset.range (N + 1),
            (innerBernCoeff p N i b : ℝ) *
              ((Nat.choose N i : ℝ) * r ^ i * (1 - r) ^ (N - i)) *
              t ^ b := by
      apply Finset.sum_congr rfl
      intro b hb
      have hb' : b ≤ N / 2 := by
        have := Finset.mem_range.mp hb
        omega
      rw [ueval_eq_bernstein (p.getD b []) N (hinner b hb'), Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [innerBernCoeff_eq_poly]
    _ = ∑ i ∈ Finset.range (N + 1),
          ((Nat.choose N i : ℝ) * r ^ i * (1 - r) ^ (N - i)) *
            (∑ b ∈ Finset.range (N / 2 + 1),
              (innerBernCoeff p N i b : ℝ) * t ^ b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    _ = ∑ i ∈ Finset.range (N + 1),
          ((Nat.choose N i : ℝ) * r ^ i * (1 - r) ^ (N - i)) *
            ueval (innerColumn (innerBernTable p N) i) t := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ueval_innerColumn_eq p N i
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    _ = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N / 2 + 1),
          (bernCoeffOf p N i j : ℝ) *
            ((Nat.choose N i : ℝ) * r ^ i * (1 - r) ^ (N - i)) *
            ((Nat.choose (N / 2) j : ℝ) * t ^ j *
              (1 - t) ^ (N / 2 - j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ueval_innerColumn_bernstein p N i, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [bernCoeffOf_eq_outer
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
      ring

end SSP.K3CyclicComplex

