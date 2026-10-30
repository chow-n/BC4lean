import BC4lean.StableProjectionMonoid
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Rank of scalar matrix projections

A complex matrix projection `P` factors as `P = v vᴴ` with `vᴴ v = 1` on an index
set of size `rank P` (spectral theorem). So every scalar matrix projection is
rectangularly equivalent to an identity block of its rank. Rank is invariant under
rectangular equivalence and additive on block sums, and so descends to an additive
map on the stable projection monoid of `ℂ`.

There is exactly one order making `ℂ` a star-ordered ring
(`complexOrder_eq_spectralOrder`), but BC4lean uses two presentations of it,
`ComplexOrder` and the spectral order, which are not definitionally equal. The
statements therefore take the order as an argument.
-/

noncomputable section
open scoped Matrix
namespace BC4lean.OperatorKTheory
open Matrix

section isometry
variable {n : Type} [Fintype n] [DecidableEq n]

/-- A complex matrix projection is `v vᴴ` for an isometry `v` whose columns are
indexed by the indices of its nonzero eigenvalues. -/
theorem Matrix.IsHermitian.exists_isometry_of_isIdempotentElem {P : Matrix n n ℂ}
    (hH : P.IsHermitian) (hI : IsIdempotentElem P) :
    ∃ v : Matrix n {i // hH.eigenvalues i ≠ 0} ℂ, v * vᴴ = P ∧ vᴴ * v = 1 := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set D : Matrix n n ℂ := diagonal (RCLike.ofReal ∘ hH.eigenvalues) with hDdef
  have hUU : Uᴴ * U = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hUU' : U * Uᴴ = 1 := by
    simpa [U, star_eq_conjTranspose] using Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hspec : P = U * D * Uᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [U, D, star_eq_conjTranspose] using h
  have hD : D = Uᴴ * P * U := by
    rw [hspec]
    calc D = (Uᴴ * U) * D * (Uᴴ * U) := by rw [hUU, one_mul, mul_one]
      _ = Uᴴ * (U * D * Uᴴ) * U := by simp only [mul_assoc]
  have hDD : D * D = D := by
    rw [hD]
    calc Uᴴ * P * U * (Uᴴ * P * U) = Uᴴ * P * (U * Uᴴ) * P * U := by simp only [mul_assoc]
      _ = Uᴴ * P * U := by rw [hUU', mul_one, mul_assoc Uᴴ P P, hI.eq]
  have h01 : ∀ i, hH.eigenvalues i ≠ 0 → (hH.eigenvalues i : ℂ) = 1 := by
    intro i hi
    have h := congrFun (congrFun hDD i) i
    simp only [D, diagonal_mul_diagonal, diagonal_apply_eq, Function.comp_apply] at h
    have hne : (hH.eigenvalues i : ℂ) ≠ 0 := by exact_mod_cast hi
    exact (mul_eq_right₀ hne).mp h
  let E : Matrix n {i // hH.eigenvalues i ≠ 0} ℂ := (1 : Matrix n n ℂ).submatrix id Subtype.val
  have hEE : E * Eᴴ = D := by
    ext i j
    simp only [E, D, mul_apply, conjTranspose_apply, submatrix_apply, id, one_apply,
      diagonal_apply, Function.comp_apply]
    by_cases hij : i = j
    · subst hij
      by_cases hi : hH.eigenvalues i = 0
      · rw [if_pos rfl]
        simp only [hi]
        apply Finset.sum_eq_zero
        intro s _
        have : ¬ i = s.1 := fun h => s.2 (h ▸ hi)
        simp [this]
      · rw [Finset.sum_eq_single_of_mem ⟨i, hi⟩ (Finset.mem_univ _)]
        · simp [h01 i hi]
        · intro s _ hs
          have : ¬ i = s.1 := fun h => hs (Subtype.ext h.symm)
          simp [this]
    · rw [if_neg hij]
      apply Finset.sum_eq_zero
      intro s _
      by_cases h : i = s.1
      · have : ¬ j = s.1 := fun h' => hij (h.trans h'.symm)
        simp [this]
      · simp [h]
  have hEE' : Eᴴ * E = 1 := by
    ext s t
    simp only [E, mul_apply, conjTranspose_apply, submatrix_apply, id, one_apply]
    rw [Finset.sum_eq_single_of_mem s.1 (Finset.mem_univ _)]
    · simp [Subtype.ext_iff]
    · intro b _ hb
      simp [hb]
  refine ⟨U * E, ?_, ?_⟩
  · rw [conjTranspose_mul]
    calc U * E * (Eᴴ * Uᴴ) = U * (E * Eᴴ) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = P := by rw [hEE, hspec]
  · rw [conjTranspose_mul]
    calc Eᴴ * Uᴴ * (U * E) = Eᴴ * (Uᴴ * U) * E := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUU, Matrix.mul_one, hEE']

end isometry

open scoped ComplexOrder in
/-- `ComplexOrder` and the spectral order on `ℂ` are the same order: a
`StarOrderedRing` structure determines the order. They are not equal by `rfl`. -/
theorem complexOrder_eq_spectralOrder :
    (inferInstance : PartialOrder ℂ) = CStarAlgebra.spectralOrder ℂ := by
  apply PartialOrder.ext
  intro a b
  rw [@StarOrderedRing.le_iff ℂ _ (inferInstance : PartialOrder ℂ) _ _,
    @StarOrderedRing.le_iff ℂ _ (CStarAlgebra.spectralOrder ℂ) _
      (CStarAlgebra.spectralOrderedRing ℂ)]

section anyOrder
variable [PartialOrder ℂ] [StarOrderedRing ℂ]
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

namespace Scalar

/-- Every scalar matrix projection is rectangularly Murray–von Neumann equivalent
to an identity block whose size is its rank. -/
theorem rectEquivalent_one_of_projection (p : MatrixProjection ℂ ι) :
    ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S),
      Fintype.card S = (projectionMatrix p).rank ∧
      RectEquivalent p (Projection.one : MatrixProjection ℂ S) := by
  have hH : (projectionMatrix p).IsHermitian := projectionMatrix_star p
  obtain ⟨v, hv, hv'⟩ := Matrix.IsHermitian.exists_isometry_of_isIdempotentElem hH
    (projectionMatrix_mul p)
  exact ⟨_, inferInstance, inferInstance, hH.rank_eq_card_non_zero_eigs.symm, v, hv, hv'⟩

/-- Rank is invariant under rectangular equivalence: `rank (v vᴴ) = rank v = rank (vᴴ v)`. -/
theorem rank_eq_of_rectEquivalent {p : MatrixProjection ℂ ι} {q : MatrixProjection ℂ κ}
    (h : RectEquivalent p q) : (projectionMatrix p).rank = (projectionMatrix q).rank := by
  obtain ⟨v, hv, hv'⟩ := h
  rw [← hv, ← hv', Matrix.rank_self_mul_conjTranspose, Matrix.rank_conjTranspose_mul_self]

/-- Identity blocks on equicardinal index types are equivalent. -/
theorem rectEquivalent_one_of_equiv {S T : Type} [Fintype S] [Fintype T] [DecidableEq S]
    [DecidableEq T] (e : T ≃ S) :
    RectEquivalent (Projection.one : MatrixProjection ℂ S) (Projection.one : MatrixProjection ℂ T) :=
  rectEquivalent_of_reindex _ _ e (Matrix.submatrix_one_equiv e).symm

/-- The block sum of two identity blocks is the identity block on the sum type. -/
theorem rectEquivalent_blockSum_one {S T : Type} [Fintype S] [Fintype T] [DecidableEq S]
    [DecidableEq T] :
    RectEquivalent (projectionBlockSum (Projection.one : MatrixProjection ℂ S)
      (Projection.one : MatrixProjection ℂ T)) (Projection.one : MatrixProjection ℂ (S ⊕ T)) := by
  refine rectEquivalent_of_reindex _ _ (Equiv.refl _) ?_
  change (1 : Matrix (S ⊕ T) (S ⊕ T) ℂ) = (Matrix.fromBlocks 1 0 0 1).submatrix id id
  rw [Matrix.fromBlocks_one, Matrix.submatrix_id_id]

/-- Rank of a finite scalar matrix projection. -/
def projectionRank (p : FiniteProjection ℂ) : ℕ := (projectionMatrix p.projection).rank

/-- Rank is additive on block sums. -/
theorem projectionRank_blockSum (p q : FiniteProjection ℂ) :
    projectionRank (FiniteProjection.blockSum p q) = projectionRank p + projectionRank q := by
  obtain ⟨S, _, _, hS, hp⟩ := rectEquivalent_one_of_projection p.projection
  obtain ⟨T, _, _, hT, hq⟩ := rectEquivalent_one_of_projection q.projection
  have h := rectEquivalent_trans (rectEquivalent_blockSum hp hq) rectEquivalent_blockSum_one
  change (projectionMatrix (projectionBlockSum p.projection q.projection)).rank = _
  rw [projectionRank, projectionRank, rank_eq_of_rectEquivalent h, ← hS, ← hT]
  change (1 : Matrix (S ⊕ T) (S ⊕ T) ℂ).rank = _
  rw [Matrix.rank_one, Fintype.card_sum]

end Scalar

open Scalar in
/-- The rank homomorphism on stable classes of scalar matrix projections. -/
def scalarRankHom : StableProjectionMonoid ℂ →+ ℤ where
  toFun := Quotient.lift (fun p => (projectionRank p : ℤ)) fun _ _ h => by
    simp only [projectionRank, rank_eq_of_rectEquivalent h]
  map_zero' := by
    change ((0 : Matrix Empty Empty ℂ).rank : ℤ) = 0
    rw [Matrix.rank_zero, Nat.cast_zero]
  map_add' x y := Quotient.inductionOn₂ x y fun p q => by
    change (projectionRank (FiniteProjection.blockSum p q) : ℤ) = projectionRank p + projectionRank q
    rw [projectionRank_blockSum, Nat.cast_add]

@[simp] theorem scalarRankHom_of (p : FiniteProjection ℂ) :
    scalarRankHom (StableProjectionMonoid.of p) = Scalar.projectionRank p := rfl

end anyOrder
end BC4lean.OperatorKTheory
