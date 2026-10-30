import BC4lean.StableUnitary
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Topology.Separation.Connected

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The stable unitary K₁ group of the scalars

Every element of `K₁(ℂ)` is zero. A unitary whose spectrum is finite is joined to `1`
in the unitary group: rotate it by a scalar so that `-1` leaves the spectrum, then use
Mathlib's path for unitaries at distance less than `2` from `1`. Matrix unitaries over
`ℂ` have finite spectrum. The statements about `K₁(ℂ)` take the order on `ℂ` as an
argument (see `complexOrder_eq_spectralOrder`).
-/

noncomputable section
open Complex Metric
namespace BC4lean.OperatorKTheory

/-- A unitary whose spectrum omits `-1` is joined to `1`. -/
theorem Unitary.joined_one_of_neg_one_notMem {A : Type*} [CStarAlgebra A] (u : unitary A)
    (hu : (-1 : ℂ) ∉ spectrum ℂ (u : A)) : Joined (1 : unitary A) u := by
  apply Unitary.joined
  change ‖(u : A) - 1‖ < 2
  rw [← Unitary.spectrum_subset_slitPlane_iff_norm_lt_two u.property,
    subset_slitPlane_iff_of_subset_sphere (spectrum.subset_circle_of_unitary u.property)]
  simpa using hu

/-- A unitary with finite spectrum is joined to `1`. With `z` on the circle outside the
spectrum and `z ≠ 1`, the scalar unitary `-z` omits `-1` from its spectrum, and so does
`(-z)⋆ u`; their product is `u`. -/
theorem Unitary.joined_one_of_finite_spectrum {A : Type*} [CStarAlgebra A] (u : unitary A)
    (hfin : (spectrum ℂ (u : A)).Finite) : Joined (1 : unitary A) u := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : Subsingleton (unitary A) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    exact Subsingleton.elim (1 : unitary A) u ▸ Joined.refl _
  have hinf : (sphere (0 : ℂ) 1).Infinite :=
    (isConnected_sphere (by simp) (0 : ℂ) zero_le_one).isPreconnected.infinite_of_nontrivial
      ⟨1, by simp, -1, by simp, by norm_num⟩
  obtain ⟨z, hz, hzσ⟩ := (hinf.sdiff (hfin.union (Set.finite_singleton 1))).nonempty
  simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hzσ
  obtain ⟨hzu, hz1⟩ := hzσ
  have hzn : ‖z‖ = 1 := by simpa using hz
  have hzz : star z * z = 1 := by
    rw [star_def, ← normSq_eq_conj_mul_self, normSq_eq_norm_sq, hzn]; norm_num
  have hzz' : z * star z = 1 := by rw [mul_comm, hzz]
  let s : unitary A := ⟨algebraMap ℂ A (-z), by
    rw [Unitary.mem_iff, ← algebraMap_star_comm, ← map_mul, ← map_mul, star_neg, neg_mul_neg,
      neg_mul_neg, hzz, hzz', map_one]
    exact ⟨rfl, rfl⟩⟩
  have hs : Joined (1 : unitary A) s := by
    apply Unitary.joined_one_of_neg_one_notMem
    change (-1 : ℂ) ∉ spectrum ℂ (algebraMap ℂ A (-z))
    rw [spectrum.scalar_eq, Set.mem_singleton_iff]
    intro h; exact hz1 (neg_inj.mp h).symm
  have hw : Joined (1 : unitary A) (star s * u) := by
    apply Unitary.joined_one_of_neg_one_notMem
    have hz0 : star (-z) ≠ 0 := by
      intro h; rw [star_neg, neg_eq_zero, star_eq_zero] at h; simp [h] at hzn
    change (-1 : ℂ) ∉ spectrum ℂ (star (algebraMap ℂ A (-z)) * (u : A))
    rw [← algebraMap_star_comm, ← Algebra.smul_def,
      show star (-z) • (u : A) = (Units.mk0 _ hz0) • (u : A) from rfl,
      spectrum.unit_smul_eq_smul]
    rintro ⟨x, hx, hx1⟩
    apply hzu
    have h : star (-z) * x = -1 := hx1
    have h2 : (-z) * (star (-z) * x) = (-z) * (-1) := by rw [h]
    rw [← mul_assoc, star_neg, neg_mul_neg, hzz', one_mul, mul_neg_one, neg_neg] at h2
    exact h2 ▸ hx
  have : s * (star s * u) = u := by rw [← mul_assoc, Unitary.mul_star_self, one_mul]
  simpa [this] using hs.mul hw

/-- Every scalar matrix unitary is norm-homotopic to the identity. -/
theorem Scalar.matrixUnitary_joined_one [PartialOrder ℂ] [StarOrderedRing ℂ]
    {ι : Type} [Fintype ι] [DecidableEq ι] (u : MatrixUnitary ℂ ι) : UnitaryHomotopic 1 u :=
  -- `CStarMatrix ι ι ℂ` carries the algebra structure of `Matrix ι ι ℂ`.
  Unitary.joined_one_of_finite_spectrum u
    (Matrix.finite_spectrum (n := ι) (R := ℂ) (u : CStarMatrix ι ι ℂ))

/-- Every element of `K₁(ℂ)` is zero.

The order on `ℂ` is an argument. At an order other than the ambient one, pass both
instances explicitly or make that order a local instance. -/
theorem k1Scalar_eq_zero [PartialOrder ℂ] [StarOrderedRing ℂ] (x : K1 ℂ) : x = 0 := by
  induction x using Quotient.inductionOn with
  | h a =>
    change K1.of (FiniteUnitary.ofUnitary a.val) = 0
    rw [← K1.of_homotopic (Scalar.matrixUnitary_joined_one a.val)]
    exact K1.of_identity a.Index

instance [PartialOrder ℂ] [StarOrderedRing ℂ] : Subsingleton (K1 ℂ) :=
  ⟨fun x y => (k1Scalar_eq_zero x).trans (k1Scalar_eq_zero y).symm⟩

end BC4lean.OperatorKTheory
