import BC4lean.ScalarProjectionRank
import BC4lean.OperatorK0

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The unital K₀ group of the scalars

`K₀(ℂ) ≃+ ℤ`: the map is the rank of a representing projection, and the class `[1]`
of the `1 × 1` identity goes to `1`. Every stable class is a multiple of `[1]`, so no
cancellation in the stable projection monoid is needed. The statements take the
order on `ℂ` as an argument (see `complexOrder_eq_spectralOrder`).
-/

noncomputable section
namespace BC4lean.OperatorKTheory

section anyOrder
variable [PartialOrder ℂ] [StarOrderedRing ℂ]
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The class `[1]` of the rank-one unit projection in `K₀(ℂ)`. -/
def k0ScalarOne : K0 ℂ :=
  k0Projection (FiniteProjection.ofProjection (Projection.one : MatrixProjection ℂ Unit))

namespace Scalar

/-- The class of an identity block is its size times the class of the unit projection. -/
theorem of_one_eq_card_nsmul (S : Type) [Fintype S] [DecidableEq S] :
    StableProjectionMonoid.of (FiniteProjection.ofProjection (Projection.one : MatrixProjection ℂ S)) =
      Fintype.card S • StableProjectionMonoid.of
        (FiniteProjection.ofProjection (Projection.one : MatrixProjection ℂ Unit)) := by
  have key : ∀ n : ℕ, StableProjectionMonoid.of
      (FiniteProjection.ofProjection (Projection.one : MatrixProjection ℂ (Fin n))) =
      n • StableProjectionMonoid.of
        (FiniteProjection.ofProjection (Projection.one : MatrixProjection ℂ Unit)) := by
    intro n
    induction n with
    | zero =>
      rw [zero_smul, ← StableProjectionMonoid.of_zeroProjection (ι := Fin 0)]
      refine StableProjectionMonoid.of_eq_of_equivalent
        (rectEquivalent_of_reindex _ _ (Equiv.refl _) ?_)
      ext i; exact i.elim0
    | succ n ih =>
      rw [succ_nsmul, ← ih, ← StableProjectionMonoid.of_blockSum]
      exact StableProjectionMonoid.of_eq_of_equivalent (rectEquivalent_trans
        (rectEquivalent_one_of_equiv (finSumFinEquiv.symm.trans
          ((Equiv.refl _).sumCongr (Equiv.ofUnique (Fin 1) Unit))).symm)
        (rectEquivalent_symm rectEquivalent_blockSum_one))
  rw [← key]
  exact StableProjectionMonoid.of_eq_of_equivalent
    (rectEquivalent_one_of_equiv (Fintype.equivFin S).symm)

/-- Every stable class of scalar projections is a multiple of the unit class. -/
theorem of_eq_rank_nsmul (p : FiniteProjection ℂ) :
    StableProjectionMonoid.of p = projectionRank p • StableProjectionMonoid.of
      (FiniteProjection.ofProjection (Projection.one : MatrixProjection ℂ Unit)) := by
  obtain ⟨S, _, _, hS, hp⟩ := rectEquivalent_one_of_projection p.projection
  rw [projectionRank, ← hS, ← of_one_eq_card_nsmul]
  exact StableProjectionMonoid.of_eq_of_equivalent hp

end Scalar

/-- The unit projection has rank one. -/
theorem scalarRankHom_one :
    scalarRankHom (StableProjectionMonoid.of
      (FiniteProjection.ofProjection (Projection.one : MatrixProjection ℂ Unit))) = 1 := by
  change ((1 : Matrix Unit Unit ℂ).rank : ℤ) = 1
  rw [Matrix.rank_one, Fintype.card_unit, Nat.cast_one]

/-- `K₀(ℂ) ≃+ ℤ`, given by the rank of a representing projection.

The order on `ℂ` is an argument. At an order other than the ambient one, pass both
instances explicitly or make that order a local instance. -/
def k0ScalarEquiv : K0 ℂ ≃+ ℤ :=
  have hinv : (zmultiplesHom (K0 ℂ) k0ScalarOne).comp (k0Universal scalarRankHom) =
      AddMonoidHom.id (K0 ℂ) := by
    have h1 : k0Universal (k0Class (A := ℂ)) = AddMonoidHom.id (K0 ℂ) :=
      k0Universal_unique _ _ (AddMonoidHom.id_comp _)
    rw [← h1]
    refine (k0Universal_unique _ _ ?_).symm
    refine AddMonoidHom.ext fun x => ?_
    induction x using Quotient.inductionOn with
    | h p =>
      change (k0Universal scalarRankHom (k0Class (StableProjectionMonoid.of p))) • k0ScalarOne =
        k0Class (StableProjectionMonoid.of p)
      rw [k0Universal_class, scalarRankHom_of, Scalar.of_eq_rank_nsmul p, map_nsmul, natCast_zsmul]
      rfl
  have hdir : (k0Universal scalarRankHom).comp (zmultiplesHom (K0 ℂ) k0ScalarOne) =
      AddMonoidHom.id ℤ := by
    ext
    simp only [AddMonoidHom.comp_apply, zmultiplesHom_apply, one_zsmul, AddMonoidHom.id_apply]
    exact (k0Universal_class scalarRankHom _).trans scalarRankHom_one
  { toFun := k0Universal scalarRankHom
    invFun := zmultiplesHom (K0 ℂ) k0ScalarOne
    left_inv := fun x => DFunLike.congr_fun hinv x
    right_inv := fun n => DFunLike.congr_fun hdir n
    map_add' := map_add _ }

/-- `k0ScalarEquiv` is the rank of a representing projection. -/
@[simp] theorem k0ScalarEquiv_projection (p : FiniteProjection ℂ) :
    k0ScalarEquiv (k0Projection p) = (Scalar.projectionRank p : ℤ) :=
  k0Universal_class scalarRankHom _

/-- `k0ScalarEquiv` sends `[1]` to `1`. -/
@[simp] theorem k0ScalarEquiv_one : k0ScalarEquiv k0ScalarOne = 1 :=
  (k0Universal_class scalarRankHom _).trans scalarRankHom_one

end anyOrder
end BC4lean.OperatorKTheory
