import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

namespace CeilingG3

-- Arithmetic part of the moment envelope; pi and the scalar coefficient are inputs.
theorem moment_guard (p C : ℝ) (hp : (157/50 : ℝ) ≤ p)
    (hC : (9/50 : ℝ) ≤ C) : (5/4 : ℝ) < 4 * p^2 * C^2 := by
  have hp2 : (157/50 : ℝ)^2 ≤ p^2 := by nlinarith
  have hC2 : (9/50 : ℝ)^2 ≤ C^2 := by nlinarith
  calc
    (5/4 : ℝ) < 4 * (157/50 : ℝ)^2 * (9/50 : ℝ)^2 := by norm_num
    _ ≤ 4 * p^2 * C^2 := by gcongr

theorem weak_coupling_guard (C l : ℝ) (hC : (9/50 : ℝ) ≤ C)
    (hl : l ≤ 1/8) : l < 4 * C^2 := by nlinarith

theorem implicit_deficit (d s a ell v : ℝ)
    (hden : 0 < s + d*ell) (h : s*a ≤ d*(v-ell*a)) :
    a ≤ d*v/(s+d*ell) := by
  apply (le_div_iff₀ hden).2
  calc
    a * (s + d*ell) = s*a + d*(ell*a) := by ring
    _ ≤ d*(v-ell*a) + d*(ell*a) := add_le_add_left h _
    _ = d*v := by ring

theorem strong_guard (K L ell b : ℝ) (hK : 0 ≤ K) (hK' : K < 4/5)
    (hL : 0 ≤ L) (hL' : L < 4/3) (he : 6 ≤ ell)
    (hb : 0 ≤ b) (hb' : b ≤ 1) :
    (2*L+K) + max 0 (b*(2*L+K)-1)*K < 1 + ell - b*K := by
  let R : ℝ := 2*L+K
  change R + max 0 (b*R-1)*K < 1+ell-b*K
  have hR : 0 ≤ R := by dsimp [R]; linarith
  have hR' : R < 52/15 := by dsimp [R]; linarith
  have hbK : b*K ≤ K := mul_le_of_le_one_left hK hb'
  have hbR : b*R ≤ R := mul_le_of_le_one_left hR hb'
  have hRK : R*(1+K) < 156/25 := by
    calc
      R*(1+K) < (52/15)*(1+K) := mul_lt_mul_of_pos_right hR' (by linarith)
      _ ≤ (156/25 : ℝ) := by linarith
  by_cases h : b*R-1 ≤ 0
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_lt (not_le.mp h))]
    have hm := mul_le_mul_of_nonneg_right (sub_le_sub_right hbR 1) hK
    calc
      R + (b*R-1)*K ≤ R + (R-1)*K := add_le_add_right hm R
      _ = R*(1+K)-K := by ring
      _ < 156/25-K := sub_lt_sub_right hRK K
      _ ≤ 1+ell-b*K := by linarith

theorem bernstein_identity (a b c t : ℝ) :
    a + (2*b-2*a)*t + (a-2*b+c)*t^2 =
      (1-t)^2*a + 2*t*(1-t)*b + t^2*c := by ring

theorem weighted_row_term (w j : ℝ) :
    (w + 2*j) + (w - 2*j) = 2*w ∧ (w + 2*j) - (2*j - w) = 2*w := by
  constructor <;> ring

theorem sum_square_bound (x y : ℝ) : (x+y)^2 ≤ 2*(x^2+y^2) := by
  nlinarith [sq_nonneg (x-y)]

theorem vacuum_binding (E1 E2 U t z : ℝ)
    (h1 : -z*t-U/2 ≤ E1) (h2 : E2 ≤ -2*U) : U-2*z*t ≤ 2*E1-E2 := by
  linarith

theorem pair_jump_coefficient (pi n m : ℝ) (hm : m ≠ 0) :
    pi * (n / 2) / (2 * m) = pi * n / (4 * m) := by
  field_simp
  ring

#print axioms moment_guard
#print axioms weak_coupling_guard
#print axioms implicit_deficit
#print axioms bernstein_identity
#print axioms strong_guard
#print axioms weighted_row_term
#print axioms sum_square_bound
#print axioms vacuum_binding
#print axioms pair_jump_coefficient

end CeilingG3
