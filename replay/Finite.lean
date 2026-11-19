import Core
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Gershgorin

open scoped BigOperators Matrix

namespace CeilingG3

/-- The order argument of G3 §1. The range of `f` is not needed for this step. -/
theorem antitone_comparison {N : ℕ} (f : ℝ → ℝ) (hf : Antitone f)
    (ell K₁ beta : ℝ) (hK : K₁ ≤ ell) (s b : Fin N → ℝ)
    (hbeta : beta = f (1 + (ell - K₁) * beta)) (hb : ∀ i, b i = f (s i))
    (hs : ∀ i, 1 + (ell - K₁) * b i ≤ s i) :
    ∀ i, 1 + (ell - K₁) * beta ≤ s i ∧ b i ≤ beta := by
  intro i
  have hsi : 1 + (ell - K₁) * beta ≤ s i := by
    by_contra! h
    have hbi : beta ≤ b i := calc
      beta = f (1 + (ell - K₁) * beta) := hbeta
      _ ≤ f (s i) := hf h.le
      _ = b i := (hb i).symm
    have hm := mul_le_mul_of_nonneg_left hbi (sub_nonneg.mpr hK)
    linarith [hs i]
  exact ⟨hsi, (hb i).le.trans ((hf hsi).trans hbeta.symm.le)⟩

section Spectral

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Eigenvalue (A : Matrix ι ι ℝ) (μ : ℝ) :=
  Module.End.HasEigenvalue (Matrix.toLin' A) μ

noncomputable def quad (A : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := x ⬝ᵥ (A *ᵥ x)
noncomputable def normSq (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2
noncomputable def gap (α : ℝ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun _ => α) - A

omit [DecidableEq ι] in
private theorem quad_sum (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    quad A x = ∑ i, ∑ j, x i * A i j * x j := by
  simp only [quad, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

omit [DecidableEq ι] in
private theorem normSq_nonneg (x : ι → ℝ) : 0 ≤ normSq x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (x i)

omit [DecidableEq ι] in
private theorem normSq_pos {x : ι → ℝ} (hx : x ≠ 0) : 0 < normSq x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  exact (sq_pos_of_ne_zero hi).trans_le
    (Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg (x i)) (Finset.mem_univ i))

omit [Fintype ι] in
private theorem gap_hermitian {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (α : ℝ) :
    (gap α A).IsHermitian := (Matrix.isHermitian_diagonal _).sub hA

private theorem gap_mulVec (A : Matrix ι ι ℝ) (α : ℝ) (x : ι → ℝ) (i : ι) :
    (gap α A *ᵥ x) i = α * x i - (A *ᵥ x) i := by
  simp [gap, Matrix.sub_mulVec]

private theorem quad_gap (A : Matrix ι ι ℝ) (α : ℝ) (x : ι → ℝ) :
    quad (gap α A) x = α * normSq x - quad A x := by
  simp only [quad, dotProduct, normSq, gap_mulVec, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem eigenvalue_of_vec {A : Matrix ι ι ℝ} {μ : ℝ} {x : ι → ℝ}
    (hx : x ≠ 0) (hAx : A *ᵥ x = μ • x) : Eigenvalue A μ :=
  Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hAx, hx⟩

omit [DecidableEq ι] in
private theorem quad_of_eigenvector {A : Matrix ι ι ℝ} {μ : ℝ} {x : ι → ℝ}
    (hAx : A *ᵥ x = μ • x) : quad A x = μ * normSq x := by
  simp only [quad, hAx, dotProduct, normSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A Rayleigh bound (for instance from head/tail square completion) caps every eigenvalue. -/
theorem eigenvalue_le_of_quad_le {A : Matrix ι ι ℝ} {α μ : ℝ}
    (hq : ∀ x, quad A x ≤ α * normSq x) (hμ : Eigenvalue A μ) : μ ≤ α := by
  obtain ⟨x, hx, hx₀⟩ := hμ.exists_hasEigenvector
  have hu := hq x
  rw [quad_of_eigenvector (Module.End.mem_eigenspace_iff.mp hx)] at hu
  exact le_of_mul_le_mul_right hu (normSq_pos hx₀)

/-- A positive definite gap is a strict upper bound on every eigenvalue. -/
theorem eigenvalue_lt_of_gap_posDef {A : Matrix ι ι ℝ} {α μ : ℝ}
    (hgap : (gap α A).PosDef) (hμ : Eigenvalue A μ) : μ < α := by
  obtain ⟨x, hx, hx₀⟩ := hμ.exists_hasEigenvector
  have hg : 0 < quad (gap α A) x := by
    simpa only [star_trivial, quad] using hgap.dotProduct_mulVec_pos hx₀
  rw [quad_gap, quad_of_eigenvector (Module.End.mem_eigenspace_iff.mp hx), sub_pos] at hg
  exact lt_of_mul_lt_mul_right hg (normSq_nonneg x)

/-- A spectral cap gives a quadratic form cap, using the spectrum of the shifted matrix. -/
theorem quad_le_of_eigenvalue_le {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {α : ℝ}
    (he : ∀ μ, Eigenvalue A μ → μ ≤ α) (x : ι → ℝ) : quad A x ≤ α * normSq x := by
  let hG := gap_hermitian hA α
  have hGpos : (gap α A).PosSemidef := hG.posSemidef_iff_eigenvalues_nonneg.mpr (fun i => by
    let z : ι → ℝ := ⇑(hG.eigenvectorBasis i)
    have hz : z ≠ 0 := by
      intro h
      apply hG.eigenvectorBasis.toBasis.ne_zero i
      exact WithLp.toLp_injective 2 (by simpa [z] using h)
    have hGz : gap α A *ᵥ z = hG.eigenvalues i • z := hG.mulVec_eigenvectorBasis i
    have hAz : A *ᵥ z = (α - hG.eigenvalues i) • z := by
      ext j
      have hj := congrFun hGz j
      rw [gap_mulVec, Pi.smul_apply, smul_eq_mul] at hj
      simp only [Pi.smul_apply, smul_eq_mul, sub_mul]
      linarith
    exact sub_nonneg.mp (by simpa using
      (sub_nonneg.mpr (he _ (eigenvalue_of_vec hz hAz)) : 0 ≤ α - (α - hG.eigenvalues i))))
  have hx : 0 ≤ quad (gap α A) x := by
    simpa only [quad, star_trivial] using hGpos.dotProduct_mulVec_nonneg x
  rwa [quad_gap, sub_nonneg] at hx

/-- Gershgorin after the diagonal similarity `xᵢ ↦ xᵢ/vᵢ`. Unlike the absolute
row test, this keeps a signed diagonal, as needed by the head witness. -/
theorem weighted_gershgorin {A : Matrix ι ι ℝ} {μ : ℝ} (hμ : Eigenvalue A μ)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ i, μ ≤ A i i + (∑ j ∈ Finset.univ.erase i, |A i j| * v j) / v i := by
  obtain ⟨x, hx, hx0⟩ := hμ.exists_hasEigenvector
  let C : Matrix ι ι ℝ := fun i j => A i j * v j / v i
  let z : ι → ℝ := fun i => x i / v i
  have hz0 : z ≠ 0 := by
    intro h
    apply hx0
    ext i
    have hi : x i / v i = 0 := congrFun h i
    exact (div_eq_zero_iff.mp hi).resolve_right (hv i).ne'
  have hCx : C *ᵥ z = μ • z := by
    ext i
    have hi : ∑ j, A i j * x j = μ * x i :=
      congrFun (Module.End.mem_eigenspace_iff.mp hx) i
    change ∑ j, C i j * z j = μ * (x i / v i)
    calc
      _ = (∑ j, A i j * x j) / v i := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by
          dsimp [C, z]
          field_simp [(hv i).ne', (hv j).ne']
      _ = _ := by rw [hi]; ring
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball (eigenvalue_of_vec hz0 hCx)
  rw [Metric.mem_closedBall, Real.dist_eq] at hi
  have hd : C i i = A i i := mul_div_cancel_right₀ _ (hv i).ne'
  have hr : ∑ j ∈ Finset.univ.erase i, ‖C i j‖ =
      (∑ j ∈ Finset.univ.erase i, |A i j| * v j) / v i := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by
      simp [C, Real.norm_eq_abs, abs_of_pos (hv i), abs_of_pos (hv j)]
  rw [hd, hr] at hi
  exact ⟨i, by linarith [le_abs_self (μ - A i i)]⟩

/-- The finite weighted absolute-row (Schur) bound, in fact without symmetry. -/
theorem weighted_schur {A : Matrix ι ι ℝ} (v : ι → ℝ) (hv : ∀ i, 0 < v i) (α : ℝ)
    (hr : ∀ i, (∑ j, |A i j| * v j) / v i ≤ α) :
    ∀ μ, Eigenvalue A μ → μ ≤ α := by
  intro μ hμ
  obtain ⟨i, hi⟩ := weighted_gershgorin hμ v hv
  have hri := hr i
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_div,
    mul_div_cancel_right₀ _ (hv i).ne'] at hri
  linarith [le_abs_self (A i i)]

omit [Fintype ι] in
private theorem gap_diag (A : Matrix ι ι ℝ) (α : ℝ) (i : ι) :
    gap α A i i = α - A i i := by simp [gap]

omit [Fintype ι] in
private theorem gap_offdiag (A : Matrix ι ι ℝ) (α : ℝ) {i j : ι} (hij : i ≠ j) :
    gap α A i j = -A i j := by simp [gap, hij]

/-- The closed head witness: weighted weak dominance of `αI − A` gives `A ≤ αI`.
The weights encode the diagonal congruence without forming the scaled matrix. -/
theorem head_witness {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (α : ℝ)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (hr : ∀ i, ∑ j ∈ Finset.univ.erase i, |gap α A i j| * v j ≤ gap α A i i * v i) :
    (gap α A).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨gap_hermitian hA α, fun x => ?_⟩
  have he : ∀ μ, Eigenvalue A μ → μ ≤ α := by
    intro μ hμ
    obtain ⟨i, hi⟩ := weighted_gershgorin hμ v hv
    have hri := (div_le_iff₀ (hv i)).mpr (hr i)
    have hs : ∑ j ∈ Finset.univ.erase i, |gap α A i j| * v j =
        ∑ j ∈ Finset.univ.erase i, |A i j| * v j := by
      exact Finset.sum_congr rfl fun j hj => by
        rw [gap_offdiag A α (Finset.ne_of_mem_erase hj).symm, abs_neg]
    rw [hs, gap_diag] at hri
    linarith
  simp only [star_trivial]
  change 0 ≤ quad (gap α A) x
  rw [quad_gap, sub_nonneg]
  exact quad_le_of_eigenvalue_le hA he x

/-- Strict row dominance gives a positive definite gap, unlike positive diagonal
with weak dominance alone. -/
theorem strict_head_witness {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (α : ℝ)
    (v : ι → ℝ) (hv : ∀ i, 0 < v i)
    (hr : ∀ i, ∑ j ∈ Finset.univ.erase i, |gap α A i j| * v j < gap α A i i * v i) :
    (gap α A).PosDef := by
  let hG := gap_hermitian hA α
  apply hG.posDef_iff_eigenvalues_pos.mpr
  intro k
  let z : ι → ℝ := ⇑(hG.eigenvectorBasis k)
  have hz : z ≠ 0 := by
    intro h
    apply hG.eigenvectorBasis.toBasis.ne_zero k
    exact WithLp.toLp_injective 2 (by simpa [z] using h)
  have hGz : gap α A *ᵥ z = hG.eigenvalues k • z := hG.mulVec_eigenvectorBasis k
  have hAz : A *ᵥ z = (α - hG.eigenvalues k) • z := by
    ext j
    have hj := congrFun hGz j
    rw [gap_mulVec, Pi.smul_apply, smul_eq_mul] at hj
    simp only [Pi.smul_apply, smul_eq_mul, sub_mul]
    linarith
  obtain ⟨i, hi⟩ := weighted_gershgorin (eigenvalue_of_vec hz hAz) v hv
  have hri := (div_lt_iff₀ (hv i)).mpr (hr i)
  have hs : ∑ j ∈ Finset.univ.erase i, |gap α A i j| * v j =
      ∑ j ∈ Finset.univ.erase i, |A i j| * v j := by
    exact Finset.sum_congr rfl fun j hj => by
      rw [gap_offdiag A α (Finset.ne_of_mem_erase hj).symm, abs_neg]
  rw [hs, gap_diag] at hri
  linarith

/-- The quadratic-form head/tail combination. The determinant condition bounds
 the square of the norm of the cross block (represented by `cross`). -/
theorem head_tail_square_completion (α B μ cross x y : ℝ)
    (hα : α < μ) (hdet : cross ^ 2 ≤ (μ - B) * (μ - α)) :
    α * x ^ 2 + 2 * cross * x * y + B * y ^ 2 ≤ μ * (x ^ 2 + y ^ 2) := by
  have h : 0 ≤ (μ - α) *
      ((μ - α) * x ^ 2 - 2 * cross * x * y + (μ - B) * y ^ 2) := by
    rw [show (μ - α) * ((μ - α) * x ^ 2 - 2 * cross * x * y + (μ - B) * y ^ 2) =
        ((μ - α) * x - cross * y) ^ 2 + ((μ - B) * (μ - α) - cross ^ 2) * y ^ 2 by ring]
    exact add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hdet) (sq_nonneg y))
  have ht := nonneg_of_mul_nonneg_right h (sub_pos.mpr hα)
  linarith only [ht, show μ * (x ^ 2 + y ^ 2) = μ * x ^ 2 + μ * y ^ 2 by ring,
    show (μ - α) * x ^ 2 = μ * x ^ 2 - α * x ^ 2 by ring,
    show (μ - B) * y ^ 2 = μ * y ^ 2 - B * y ^ 2 by ring]

end Spectral


section FiniteModel

variable {N : ℕ}

abbrev Vec (N : ℕ) := Fin N → ℝ
abbrev Mat (N : ℕ) := Matrix (Fin N) (Fin N) ℝ

def normal (w b : Vec N) (D H : Mat N) : Vec N :=
  fun i => w i + ∑ j, (D i j - H i j) * b j

noncomputable def pairing (d b : Vec N) (D H : Mat N) : Mat N :=
  fun i j => Real.sqrt (b i / d i) * (D i j + H i j) * Real.sqrt (b j / d j)

noncomputable def eliminated (w b : Vec N) (D H : Mat N) : Mat N :=
  Matrix.diagonal (fun i => 1 - normal w b D H i / w i) + pairing w b D H

private theorem pairing_hermitian (d b : Vec N) {D H : Mat N}
    (hD : D.IsHermitian) (hH : H.IsHermitian) : (pairing d b D H).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hDi : D j i = D i j := by simpa only [star_trivial] using hD.apply i j
  have hHi : H j i = H i j := by simpa only [star_trivial] using hH.apply i j
  simp only [star_trivial, pairing, hDi, hHi]
  ring

private theorem eliminated_hermitian (w b : Vec N) {D H : Mat N}
    (hD : D.IsHermitian) (hH : H.IsHermitian) : (eliminated w b D H).IsHermitian :=
  (Matrix.isHermitian_diagonal _).add (pairing_hermitian w b hD hH)

private theorem normal_split (w b : Vec N) (D H : Mat N) (i : Fin N) :
    normal w b D H i =
      w i + (∑ j ∈ Finset.univ.erase i, (D i j - H i j) * b j) +
        (D i i - H i i) * b i := by
  unfold normal
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_assoc]

/-- The corrected diagonal of Eq. (2): the `Dᵢᵢ` terms cancel, and the two `Hᵢᵢ` terms add. -/
theorem eliminated_diagonal (w b : Vec N) (D H : Mat N) (i : Fin N)
    (hw : 0 < w i) (hb : 0 ≤ b i) :
    eliminated w b D H i i =
      (2 * b i * H i i - ∑ j ∈ Finset.univ.erase i, (D i j - H i j) * b j) / w i := by
  have hs := Real.sq_sqrt (div_nonneg hb hw.le)
  simp only [eliminated, Matrix.add_apply, Matrix.diagonal_apply_eq, pairing, normal_split]
  calc
    _ = 1 - (w i + (∑ j ∈ Finset.univ.erase i, (D i j - H i j) * b j) +
          (D i i - H i i) * b i) / w i + (b i / w i) * (D i i + H i i) := by
      linear_combination (D i i + H i i) * hs
    _ = _ := by field_simp [hw.ne']; ring

private theorem eliminated_offdiag (w b : Vec N) (D H : Mat N) {i j : Fin N}
    (hij : i ≠ j) : eliminated w b D H i j = pairing w b D H i j := by
  simp [eliminated, hij]

/-- Real finite-sum uneliminated form in the original amplitudes. -/
noncomputable def physicalForm (s b : Vec N) (D H : Mat N) (y : Vec N) : ℝ :=
  (∑ i, b i * s i * y i ^ 2) - ∑ i, ∑ j, b i * b j * (D i j + H i j) * y i * y j

private theorem scaled_sqrt {w b : ℝ} (hw : 0 < w) (hb : 0 ≤ b) :
    Real.sqrt (w * b) * Real.sqrt (b / w) = b := by
  rw [← Real.sqrt_mul (mul_nonneg hw.le hb), show w * b * (b / w) = b * b by
    field_simp [hw.ne'], Real.sqrt_mul_self hb]

private theorem pairing_form (d b : Vec N) (D H : Mat N) (y : Vec N)
    (hd : ∀ i, 0 < d i) (hb : ∀ i, 0 ≤ b i) :
    quad (pairing d b D H) (fun i => Real.sqrt (d i * b i) * y i) =
      ∑ i, ∑ j, b i * b j * (D i j + H i j) * y i * y j := by
  rw [quad_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  dsimp [pairing]
  rw [show Real.sqrt (d i * b i) * y i *
      (Real.sqrt (b i / d i) * (D i j + H i j) * Real.sqrt (b j / d j)) *
      (Real.sqrt (d j * b j) * y j) =
      (Real.sqrt (d i * b i) * Real.sqrt (b i / d i)) *
      (Real.sqrt (d j * b j) * Real.sqrt (b j / d j)) * (D i j + H i j) * y i * y j by ring,
    scaled_sqrt (hd i) (hb i), scaled_sqrt (hd j) (hb j)]

/-- Expanding the finite normal and pairing sums really gives `‖x‖² − xᵀSx`
in the `xᵢ = √(wᵢbᵢ)yᵢ` coordinates, not merely agreement on diagonal tests. -/
theorem eliminated_form (w b : Vec N) (D H : Mat N) (y : Vec N)
    (hw : ∀ i, 0 < w i) (hb : ∀ i, 0 ≤ b i) :
    let x : Vec N := fun i => Real.sqrt (w i * b i) * y i
    physicalForm (normal w b D H) b D H y = normSq x - quad (eliminated w b D H) x := by
  let x : Vec N := fun i => Real.sqrt (w i * b i) * y i
  change _ = normSq x - quad (eliminated w b D H) x
  have hq : quad (eliminated w b D H) x =
      (∑ i, (1 - normal w b D H i / w i) * x i ^ 2) + quad (pairing w b D H) x := by
    rw [quad, eliminated, Matrix.add_mulVec, dotProduct_add]
    congr 1
    unfold dotProduct
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.mulVec_diagonal]; ring
  have hn : normSq x - (∑ i, (1 - normal w b D H i / w i) * x i ^ 2) =
      ∑ i, b i * normal w b D H i * y i ^ 2 := by
    rw [normSq, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [x]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg (hw i).le (hb i))]
    field_simp [(hw i).ne']
    ring
  rw [hq, ← sub_sub, hn, pairing_form w b D H y hw hb, physicalForm]

/-- The original pairing matrix `B` and the eliminated matrix `S` have congruent
level-one gaps, by the positive diagonal `sqrt(w/s)`. -/
theorem pairing_gap_congruence (w b : Vec N) (D H : Mat N)
    (hw : ∀ i, 0 < w i) (hb : ∀ i, 0 ≤ b i) (hP : ∀ i j, 0 ≤ D i j - H i j)
    (hGap : (gap 1 (eliminated w b D H)).PosDef) :
    (gap 1 (pairing (normal w b D H) b D H)).PosDef ∧
      ∀ a, Eigenvalue (pairing (normal w b D H) b D H) a → a < 1 := by
  let s := normal w b D H
  have hs (i : Fin N) : 0 < s i := by
    exact (hw i).trans_le (le_add_of_nonneg_right
      (Finset.sum_nonneg fun j _ => mul_nonneg (hP i j) (hb j)))
  let r (i : Fin N) := Real.sqrt (w i / s i)
  have hr (i : Fin N) : 0 < r i := Real.sqrt_pos.mpr (div_pos (hw i) (hs i))
  have hroot (i : Fin N) :
      Real.sqrt (b i / s i) = r i * Real.sqrt (b i / w i) := by
    dsimp only [r]
    rw [← Real.sqrt_mul (div_nonneg (hw i).le (hs i).le)]
    congr 1
    field_simp [(hw i).ne', (hs i).ne']
  let R := Matrix.diagonal r
  have hconj : gap 1 (pairing s b D H) = Rᴴ * gap 1 (eliminated w b D H) * R := by
    ext i j
    simp only [R, Matrix.diagonal_conjTranspose, star_trivial, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    by_cases hij : i = j
    · subst j
      have hd : r i * (s i / w i) * r i = 1 := by
        calc
          _ = (r i)^2 * (s i / w i) := by ring
          _ = _ := by
            rw [show (r i)^2 = w i / s i from Real.sq_sqrt (div_nonneg (hw i).le (hs i).le)]
            field_simp [(hw i).ne', (hs i).ne']
      have hDiag : gap 1 (eliminated w b D H) i i =
          1 - ((1 - s i / w i) + pairing w b D H i i) := by
        simp [gap, eliminated, s]
      rw [hDiag]
      simp only [gap, Matrix.sub_apply, Matrix.diagonal_apply_eq, pairing, hroot]
      linear_combination -hd
    · simp only [gap, eliminated, Matrix.sub_apply, Matrix.add_apply, pairing, hroot,
        Matrix.diagonal_apply_ne _ hij, zero_add, zero_sub]
      ring
  have hinj : Function.Injective R.mulVec := by
    intro x y he
    ext i
    have hi := congrFun he i
    simp only [R, Matrix.mulVec_diagonal] at hi
    exact mul_left_cancel₀ (hr i).ne' hi
  have hB : (gap 1 (pairing s b D H)).PosDef := by
    rw [hconj]
    exact hGap.conjTranspose_mul_mul_same hinj
  exact ⟨hB, fun _ ha => eigenvalue_lt_of_gap_posDef hB ha⟩

/-- A symmetric finite matrix is bounded above by a nonnegative multiple of a
comparator on absolute-value tests, plus its diagonal deficit correction. -/
private theorem quad_compare {S A : Mat N} {beta c : ℝ}
    (hdiag : ∀ i, S i i ≤ beta * A i i + c)
    (hoff : ∀ i j, i ≠ j → 0 ≤ S i j ∧ S i j ≤ beta * A i j) (x : Vec N) :
    quad S x ≤ beta * quad A (fun i => |x i|) + c * normSq x := by
  rw [quad_sum S, quad_sum A]
  calc
    _ ≤ ∑ i, ∑ j, (beta * (|x i| * A i j * |x j|) + if i = j then c * x i ^ 2 else 0) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      by_cases hij : i = j
      · subst j
        simp only [ite_eq_left, ← mul_assoc]
        have h := mul_le_mul_of_nonneg_right (hdiag i) (sq_nonneg (x i))
        calc
          _ = S i i * x i ^ 2 := by ring
          _ ≤ _ := h
          _ = _ := by
            have ha : |x i| ^ 2 = x i ^ 2 := sq_abs _
            linear_combination -(beta * A i i) * ha
      · simp only [ite_eq_right hij, add_zero]
        have ⟨h0, h1⟩ := hoff i j hij
        calc
          x i * S i j * x j = S i j * (x i * x j) := by ring
          _ ≤ S i j * (|x i| * |x j|) := by
            rw [← abs_mul]
            exact mul_le_mul_of_nonneg_left (le_abs_self _) h0
          _ ≤ (beta * A i j) * (|x i| * |x j|) :=
            mul_le_mul_of_nonneg_right h1 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = _ := by ring
    _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, normSq]

/-- The off-diagonal normal row acting on a finite vector. -/
abbrev offRow (D H : Mat N) (x : Vec N) (i : Fin N) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, (D i j - H i j) * x j

/-- Finite version of the implicit Poisson-deficit bound. The slope comparison
(3) is an input; the normal-row rearrangement and its denominator are proved. -/
private theorem finite_deficit (f : ℝ → ℝ) (hf : Antitone f)
    (ell K₁ beta R : ℝ) (w b : Vec N) (D H : Mat N)
    (hKell : K₁ ≤ ell) (hb1 : beta ≤ 1) (hw : ∀ i, 1 ≤ w i)
    (hb0 : ∀ i, 0 ≤ b i) (hb : ∀ i, b i = f (normal w b D H i))
    (hbeta : beta = f (1 + (ell - K₁) * beta))
    (hP : ∀ i j, 0 ≤ D i j - H i j)
    (hD : ∀ i, D i i = ell) (hH : ∀ i, 0 ≤ H i i) (hHK : ∀ i, H i i ≤ K₁)
    (hrow : ∀ i, offRow D H 1 i + K₁ ≤ R) (hden : 0 < 1 + ell - beta * K₁)
    (hslope : ∀ s ≥ 1 + (ell - K₁) * beta,
      (1 + (ell - K₁) * beta) * (beta - f s) ≤
        (1 - beta) * (s - (1 + (ell - K₁) * beta))) :
    ∀ i, b i ≤ beta ∧
      beta - b i ≤ (1 - beta) * (w i - 1 + beta * R) / (1 + ell - beta * K₁) := by
  have hnormal : ∀ i, 1 + (ell - K₁) * b i ≤ normal w b D H i := by
    intro i
    rw [normal_split, hD i]
    have ht : 0 ≤ offRow D H b i :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hP i j) (hb0 j)
    have hmul := mul_le_mul_of_nonneg_right (sub_le_sub_left (hHK i) ell) (hb0 i)
    linarith [hw i]
  have hcomp := antitone_comparison f hf ell K₁ beta hKell _ b hbeta hb hnormal
  intro i
  refine ⟨(hcomp i).2, ?_⟩
  have hbeta0 := (hb0 i).trans (hcomp i).2
  have hsum : offRow D H b i ≤ beta * offRow D H 1 i := by
    change _ ≤ beta * (∑ j ∈ Finset.univ.erase i, (D i j - H i j) * 1)
    simp only [mul_one, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      rw [mul_comm beta]
      exact mul_le_mul_of_nonneg_left (hcomp j).2 (hP i j)
  let anchor := 1 + (ell - K₁) * beta
  have hupper : normal w b D H i - anchor ≤ w i - 1 + beta * R - ell * (beta - b i) := by
    have hrow' := mul_le_mul_of_nonneg_left (hrow i) hbeta0
    have hdrop := mul_nonneg (hH i) (hb0 i)
    rw [normal_split, hD i]
    change w i + offRow D H b i + (ell - H i i) * b i - (1 + (ell - K₁) * beta) ≤ _
    linarith [show beta * (offRow D H 1 i + K₁) =
        beta * offRow D H 1 i + beta * K₁ by ring,
      show (ell - H i i) * b i = ell * b i - H i i * b i by ring,
      show (ell - K₁) * beta = ell * beta - beta * K₁ by ring,
      show ell * (beta - b i) = ell * beta - ell * b i by ring]
  have hs := hslope _ (hcomp i).1
  rw [← hb i] at hs
  have hmul := hs.trans (mul_le_mul_of_nonneg_left hupper (sub_nonneg.mpr hb1))
  have hidentity : anchor + (1 - beta) * ell = 1 + ell - beta * K₁ := by
    dsimp [anchor]; ring
  have h := implicit_deficit (1 - beta) anchor (beta - b i) ell (w i - 1 + beta * R)
    (by rwa [hidentity]) hmul
  rwa [hidentity] at h

/-- From the two row bounds in (4), sum the pointwise deficit against the
off-diagonal `P` row; the normalizing `wᵢ` cancels. -/
private theorem deficit_row_cap (w b : Vec N) (D H : Mat N) (beta K₁ R den : ℝ)
    (hb1 : beta ≤ 1) (hden : 0 < den) (hP : ∀ i j, 0 ≤ D i j - H i j)
    (hdef : ∀ j, beta - b j ≤ (1 - beta) * (w j - 1 + beta * R) / den)
    (hrow : ∀ i, offRow D H 1 i ≤ K₁ * w i)
    (hweight : ∀ i, offRow D H w i ≤ R * w i) (i : Fin N) :
    offRow D H (fun j => beta - b j) i ≤
      (1 - beta) * ((R + max 0 (beta * R - 1) * K₁) / den) * w i := by
  let t := max 0 (beta * R - 1)
  let d := (1 - beta) / den
  have hd : 0 ≤ d := div_nonneg (sub_nonneg.mpr hb1) hden.le
  have ht : 0 ≤ t := le_max_left _ _
  have hsum : offRow D H (fun j => beta - b j) i ≤
      d * (offRow D H w i + t * offRow D H 1 i) := by
    simp only [offRow, Pi.one_apply, mul_one, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have hu : w j - 1 + beta * R ≤ w j + t := by
      linarith [le_max_right (0 : ℝ) (beta * R - 1)]
    calc
      _ ≤ (D i j - H i j) * ((1 - beta) * (w j - 1 + beta * R) / den) :=
        mul_le_mul_of_nonneg_left (hdef j) (hP i j)
      _ = (D i j - H i j) * (d * (w j - 1 + beta * R)) := by dsimp [d]; ring
      _ ≤ (D i j - H i j) * (d * (w j + t)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu hd) (hP i j)
      _ = _ := by ring
  calc
    _ ≤ d * (offRow D H w i + t * offRow D H 1 i) := hsum
    _ ≤ d * (R * w i + t * (K₁ * w i)) := mul_le_mul_of_nonneg_left
      (add_le_add (hweight i) (mul_le_mul_of_nonneg_left (hrow i) ht)) hd
    _ = _ := by dsimp [d, t]; ring

private theorem eliminated_diag_compare (w b : Vec N) (D H : Mat N) (beta c : ℝ)
    (hw : ∀ i, 0 < w i) (hb : ∀ i, 0 ≤ b i) (hcomp : ∀ i, b i ≤ beta)
    (hH : ∀ i, 0 ≤ H i i) (hδ : ∀ i, offRow D H (fun j => beta - b j) i ≤ c * w i)
    (i : Fin N) :
    eliminated w b D H i i ≤ beta * eliminated w 1 D H i i + c := by
  have hδi := (div_le_iff₀ (hw i)).mpr (hδ i)
  have hs : offRow D H (fun j => beta - b j) i =
      beta * offRow D H 1 i - offRow D H b i := by
    simp only [offRow, Pi.one_apply, mul_one, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have heq :
      eliminated w b D H i i - beta * eliminated w 1 D H i i =
        (offRow D H (fun j => beta - b j) i - 2 * H i i * (beta - b i)) / w i := by
    rw [eliminated_diagonal w b D H i (hw i) (hb i),
      eliminated_diagonal w 1 D H i (hw i) (by norm_num), hs]
    simp only [offRow, Pi.one_apply, mul_one]
    ring
  have hdrop : 0 ≤ 2 * H i i * (beta - b i) / w i :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hH i))
      (sub_nonneg.mpr (hcomp i))) (hw i).le
  rw [sub_div] at heq
  linarith

private theorem eliminated_offdiag_compare (w b : Vec N) (D H : Mat N) (beta : ℝ)
    (hw : ∀ i, 0 < w i) (hb0 : 0 ≤ beta)
    (hcomp : ∀ i, b i ≤ beta) {i j : Fin N} (hij : i ≠ j) (hDH : 0 ≤ D i j + H i j) :
    0 ≤ eliminated w b D H i j ∧
      eliminated w b D H i j ≤ beta * eliminated w 1 D H i j := by
  rw [eliminated_offdiag w b D H hij, eliminated_offdiag w 1 D H hij]
  unfold pairing
  refine ⟨mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hDH) (Real.sqrt_nonneg _), ?_⟩
  have hroot (k : Fin N) :
      Real.sqrt (b k / w k) ≤ Real.sqrt beta * Real.sqrt (1 / w k) := by
    rw [← Real.sqrt_mul hb0, mul_one_div]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (hcomp k) (hw k).le)
  calc
    _ ≤ (Real.sqrt beta * Real.sqrt (1 / w i)) * (D i j + H i j) *
          (Real.sqrt beta * Real.sqrt (1 / w j)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hroot i) hDH) (hroot j)
        (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hDH)
    _ = _ := by
      simp only [Pi.one_apply]
      rw [show (Real.sqrt beta * Real.sqrt (1 / w i)) * (D i j + H i j) *
          (Real.sqrt beta * Real.sqrt (1 / w j)) =
          (Real.sqrt beta)^2 * (Real.sqrt (1 / w i) * (D i j + H i j) *
            Real.sqrt (1 / w j)) by ring, Real.sq_sqrt hb0]

/-- Strong-coupling finite core, G3 Eqs. (3)–(5). The DOS slope bound, the
three row bounds and the scalar (`b ≡ 1`) spectral cap come from the paper.
The strict bound for the eliminated finite matrix is a conclusion, not an input. -/
theorem finite_strong_ceiling (f : ℝ → ℝ) (hf : Antitone f)
    (ell K₁ L beta μ : ℝ) (w b : Vec N) (D H : Mat N)
    (hEll : 6 ≤ ell) (hK₀ : 0 ≤ K₁) (hK : K₁ < 4/5) (hL₀ : 0 ≤ L) (hL : L < 4/3)
    (hbeta₀ : 0 ≤ beta) (hbeta₁ : beta ≤ 1) (hw : ∀ i, 1 ≤ w i)
    (hb₀ : ∀ i, 0 ≤ b i) (hb : ∀ i, b i = f (normal w b D H i))
    (hbeta : beta = f (1 + (ell - K₁) * beta))
    (hDs : D.IsHermitian) (hHs : H.IsHermitian)
    (hP : ∀ i j, 0 ≤ D i j - H i j) (hD : ∀ i, D i i = ell)
    (hH : ∀ i j, 0 ≤ H i j) (hHK : ∀ i, H i i ≤ K₁)
    (hrow₀ : ∀ i, offRow D H 1 i + K₁ ≤ 2 * L + K₁)
    (hrow₁ : ∀ i, offRow D H 1 i ≤ K₁ * w i)
    (hrow₂ : ∀ i, offRow D H w i ≤ (2 * L + K₁) * w i)
    (hslope : ∀ s ≥ 1 + (ell - K₁) * beta,
      (1 + (ell - K₁) * beta) * (beta - f s) ≤
        (1 - beta) * (s - (1 + (ell - K₁) * beta)))
    (hμ : μ < 1) (hscalar : ∀ a, Eigenvalue (eliminated w 1 D H) a → a ≤ μ) :
    (gap 1 (eliminated w b D H)).PosDef ∧
      (∀ a, Eigenvalue (eliminated w b D H) a → a < 1) ∧
      ∀ a, Eigenvalue (pairing (normal w b D H) b D H) a → a < 1 := by
  let R := 2 * L + K₁
  let den := 1 + ell - beta * K₁
  let φ := (R + max 0 (beta * R - 1) * K₁) / den
  have hden : 0 < den := by
    dsimp [den]
    linarith [mul_le_of_le_one_left hK₀ hbeta₁]
  have hφ : φ < 1 := by
    apply (div_lt_iff₀ hden).mpr
    simpa only [one_mul, R, den] using strong_guard K₁ L ell beta hK₀ hK hL₀ hL
      hEll hbeta₀ hbeta₁
  have hdef := finite_deficit f hf ell K₁ beta R w b D H (by linarith) hbeta₁ hw hb₀ hb
    hbeta hP hD (fun i => hH i i) hHK hrow₀ hden hslope
  have hcomp i := (hdef i).1
  have hδ i := deficit_row_cap w b D H beta K₁ R den hbeta₁ hden hP
    (fun j => (hdef j).2) hrow₁ hrow₂ i
  have hw' i : 0 < w i := lt_of_lt_of_le zero_lt_one (hw i)
  have hupper (x : Vec N) :
      quad (eliminated w b D H) x ≤ (beta * μ + (1 - beta) * φ) * normSq x := by
    have hq := quad_compare (eliminated_diag_compare w b D H beta ((1 - beta) * φ)
      hw' hb₀ hcomp (fun i => hH i i) hδ)
      (fun i j hij => eliminated_offdiag_compare w b D H beta hw' hbeta₀ hcomp
        hij (by linarith [hP i j, hH i j])) x
    have hs := quad_le_of_eigenvalue_le (eliminated_hermitian w 1 hDs hHs)
      hscalar (fun i => |x i|)
    have hn : normSq (fun i => |x i|) = normSq x := by simp [normSq, sq_abs]
    rw [hn] at hs
    calc
      _ ≤ beta * quad (eliminated w 1 D H) (fun i => |x i|) + (1 - beta) * φ * normSq x := hq
      _ ≤ beta * (μ * normSq x) + (1 - beta) * φ * normSq x :=
        add_le_add_left (mul_le_mul_of_nonneg_left hs hbeta₀) _
      _ = _ := by ring
  have hcap : beta * μ + (1 - beta) * φ < 1 := by
    by_cases hbeta_eq : beta = 1
    · simpa [hbeta_eq] using hμ
    · have hp : 0 < 1 - beta := sub_pos.mpr (lt_of_le_of_ne hbeta₁ hbeta_eq)
      have h₁ := mul_le_mul_of_nonneg_left hμ.le hbeta₀
      have h₂ := mul_lt_mul_of_pos_left hφ hp
      linarith
  have hGap : (gap 1 (eliminated w b D H)).PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨gap_hermitian (eliminated_hermitian w b hDs hHs) 1, fun x hx => ?_⟩
    have hstrict := (hupper x).trans_lt
      (mul_lt_mul_of_pos_right hcap (normSq_pos hx))
    simp only [star_trivial]
    change 0 < quad (gap 1 (eliminated w b D H)) x
    rw [quad_gap, one_mul, sub_pos]
    simpa only [one_mul] using hstrict
  exact ⟨hGap, fun _ ha => eigenvalue_lt_of_gap_posDef hGap ha,
    (pairing_gap_congruence w b D H hw' hb₀ hP hGap).2⟩

#print axioms antitone_comparison
#print axioms weighted_gershgorin
#print axioms weighted_schur
#print axioms head_witness
#print axioms strict_head_witness
#print axioms head_tail_square_completion
#print axioms quad_le_of_eigenvalue_le
#print axioms eigenvalue_le_of_quad_le
#print axioms eigenvalue_lt_of_gap_posDef
#print axioms eliminated_diagonal
#print axioms eliminated_form
#print axioms pairing_gap_congruence
#print axioms finite_strong_ceiling

end FiniteModel
end CeilingG3
