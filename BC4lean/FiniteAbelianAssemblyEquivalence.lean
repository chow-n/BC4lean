import BC4lean.FiniteAbelianCharacterSplit
import BC4lean.FiniteAbelianReducedEquiv
import BC4lean.FinitePointCharacterAssembly
import BC4lean.ScalarOperatorKNonunital
import BC4lean.BaumConnesProperty

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The assembly map for a finite abelian group

For a finite abelian group `Γ` the reduced assembly map is identified, in both parities, with an
explicit additive equivalence, so `Γ` has the coefficient-free reduced Baum–Connes property
(`baumConnesProperty_of_finite_commGroup`). The proof is that of `OrderTwoAssemblyEquivalence`
with the two characters of a group of order two replaced by the `|Γ|` characters of `Γ`:

* the canonical colimit is the point model (`reducedAssemblyHom_finitePoint`);
* `KK^Γ_p(C₀(pt), ℂ) ≅ ∏_{χ ∈ Γ̂} KK_p(ℂ, ℂ)` by the character parts (`finiteAbelianPointKKSplit`),
  with inverse `u ↦ ∑_χ χ ⊗ infl (u χ)`;
* on `χ ⊗ infl a` the assembly map is `(P_χ)_* [a]` in `K_p(C*_r Γ)` (`spaceAssembly_even_class`,
  `spaceAssembly_odd_class` of `FinitePointCharacterAssembly`);
* under `ℂ^Γ̂ ≅ C*_r Γ` the projection `P_χ` is the coordinate idempotent at `χ`
  (`crossedHom_comp_characterHom_dual`), so the composite is
  `∏_χ KK_p(ℂ, ℂ) ≅ ∏_χ K_p(ℂ) ≅ K_p(ℂ^Γ̂) ≅ K_p(C*_r Γ)` (`finiteAbelianAnalyticEquiv`).
-/

noncomputable section

namespace BC4lean.Chapter8Examples.FiniteAbelianAssembly
open ProperActions KKTheory OperatorKTheory FinitePointAssembly
open KKTheory.GroupUniverseParityGroup KKTheory.GroupUniverseParityFunctoriality
open KKTheory.FinitePointCompressedDescent KKTheory.FinitePointCharacterTensor KKTheory.FinitePointCutoff
open CharacterDual
open scoped ZeroAtInfty ComplexOrder KasparovDescent

variable {Γ : Type} [CommGroup Γ] [Countable Γ] [Fintype Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]

section Algebra

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- The image of `P_χ` in `C*_r(Γ)` is the image of the coordinate idempotent at `χ`. -/
theorem crossedHom_characterProjection_dual (χ : CharacterDual Γ) :
    crossedHom Γ (characterProjection Γ (toUnitary χ)) =
      finiteAbelianReducedEquiv Γ (Pi.single χ 1) := by
  rw [finiteAbelianReducedEquiv_single, characterProjection, map_sum]
  simp only [map_smul, crossedHom_regular]

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- The character homomorphism `z ↦ z P_χ` is the coordinate embedding at `χ` of
`ℂ^Γ̂ ≅ C*_r(Γ)`. -/
theorem crossedHom_comp_characterHom_dual (χ : CharacterDual Γ) :
    (crossedHom Γ).comp (characterHom Γ (toUnitary χ)) =
      (finiteAbelianReducedEquiv Γ).toNonUnitalStarAlgHom.comp
        (piSingleHom (CharacterDual Γ) χ) := by
  apply scalarHom_ext
  change crossedHom Γ ((1 : ℂ) • characterProjection Γ (toUnitary χ)) =
    finiteAbelianReducedEquiv Γ (Pi.single χ 1)
  rw [one_smul, crossedHom_characterProjection_dual]

end Algebra

section Glue

local instance pointCZero_separable'' : TopologicalSpace.SeparableSpace C₀(FiniteGroupPoint.{0}, ℂ) :=
  TopologicalKHomology.cZero_separableSpace

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
variable (Γ) in
/-- Even analytic side: `∏_χ KK₀(ℂ,ℂ) ≅ ∏_χ K₀(ℂ) ≅ K₀(ℂ^Γ̂) ≅ K₀(C*_r Γ)`. -/
def finiteAbelianK0Equiv :
    (CharacterDual Γ → KasparovHomotopyClass.{0,0,0,0} unitScalarAction unitScalarAction) ≃+ ReducedK0 Γ :=
  letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  (AddEquiv.piCongrRight fun _ => scalarKKOperatorK0AddEquiv.{0,0}).trans
    ((piOperatorK0Equiv (CharacterDual Γ)).symm.trans
      ((operatorK0MapEquiv (finiteAbelianReducedEquiv Γ)).trans
        (operatorK0UnitalEquiv (ReducedGroupCStar Γ))))

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
variable (Γ) in
/-- Odd analytic side: `∏_χ KK₁(ℂ,ℂ) ≅ ∏_χ K₁(ℂ) ≅ K₁(ℂ^Γ̂) ≅ K₁(C*_r Γ)`. -/
def finiteAbelianK1Equiv :
    (CharacterDual Γ → OddKK.{0,0,0,0} unitScalarAction unitScalarAction) ≃+ ReducedK1 Γ :=
  letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  (AddEquiv.piCongrRight fun _ => oddKKOperatorK1AllModuleUniversesAddEquiv.{0,0}).trans
    ((piOperatorK1Equiv (CharacterDual Γ)).symm.trans
      ((operatorK1MapEquiv (finiteAbelianReducedEquiv Γ)).trans
        (operatorK1UnitalEquiv (ReducedGroupCStar Γ))))

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
variable (Γ) in
/-- The analytic side for a finite abelian group in either parity. -/
def finiteAbelianAnalyticEquiv (p : Bool) :
    (CharacterDual Γ → KKParityGroup.{0,0,0,0} p unitScalarAction unitScalarAction) ≃+ Assembly.analyticGroup Γ p :=
  match p with
  | false => finiteAbelianK0Equiv Γ
  | true => finiteAbelianK1Equiv Γ

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- `finiteAbelianK0Equiv` as the sum of the character pushforwards. -/
theorem finiteAbelianK0Equiv_apply (u : CharacterDual Γ → KasparovHomotopyClass.{0,0,0,0} unitScalarAction unitScalarAction) :
    finiteAbelianK0Equiv Γ u =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      ∑ χ, operatorK0UnitalEquiv (ReducedGroupCStar Γ)
        (operatorK0Map ((crossedHom Γ).comp (characterHom Γ (toUnitary χ)))
          (scalarKKOperatorK0AddEquiv (u χ))) := by
  let : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  show operatorK0UnitalEquiv (ReducedGroupCStar Γ)
      (operatorK0Map (finiteAbelianReducedEquiv Γ).toNonUnitalStarAlgHom
        (∑ χ, operatorK0Map (piSingleHom (CharacterDual Γ) χ) (scalarKKOperatorK0AddEquiv (u χ)))) = _
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [crossedHom_comp_characterHom_dual, operatorK0Map_apply_apply]

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- `finiteAbelianK1Equiv` as the sum of the character pushforwards. -/
theorem finiteAbelianK1Equiv_apply (u : CharacterDual Γ → OddKK.{0,0,0,0} unitScalarAction unitScalarAction) :
    finiteAbelianK1Equiv Γ u =
      letI : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
      letI : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
      ∑ χ, operatorK1UnitalEquiv (ReducedGroupCStar Γ)
        (operatorK1Map ((crossedHom Γ).comp (characterHom Γ (toUnitary χ)))
          (oddKKOperatorK1AllModuleUniversesAddEquiv (u χ))) := by
  let : PartialOrder (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (ReducedGroupCStar Γ) := CStarAlgebra.spectralOrderedRing _
  show operatorK1UnitalEquiv (ReducedGroupCStar Γ)
      (operatorK1Map (finiteAbelianReducedEquiv Γ).toNonUnitalStarAlgHom
        (∑ χ, operatorK1Map (piSingleHom (CharacterDual Γ) χ)
          (oddKKOperatorK1AllModuleUniversesAddEquiv (u χ)))) = _
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [crossedHom_comp_characterHom_dual, operatorK1Map_apply_apply]

/-- On the point, the assembly map is the character split `finiteAbelianPointKKSplit` followed by
`finiteAbelianAnalyticEquiv`, in both parities and for every cutoff. -/
theorem spaceAssemblyHom_finiteAbelian (c0 : Cutoff.CutoffFunction Γ FiniteGroupPoint.{0}) (p : Bool)
    (x : TopologicalKHomology.spaceGroup p Γ FiniteGroupPoint.{0}) :
    Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} p c0 x =
      finiteAbelianAnalyticEquiv Γ p
        (finiteAbelianPointKKSplit.{0,0} (Γ := Γ) FiniteGroupPoint.{0} default p x) := by
  obtain ⟨u, rfl⟩ :=
    (finiteAbelianPointKKSplit.{0,0} (Γ := Γ) FiniteGroupPoint.{0} default p).symm.surjective x
  rw [AddEquiv.apply_symm_apply]
  cases p
  · exact (map_sum (Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} false c0) _ _).trans
      ((Finset.sum_congr rfl fun χ _ => spaceAssembly_even_class c0 (toUnitary χ) (u χ)).trans
        (finiteAbelianK0Equiv_apply u).symm)
  · exact (map_sum (Assembly.spaceAssemblyHom Γ FiniteGroupPoint.{0} true c0) _ _).trans
      ((Finset.sum_congr rfl fun χ _ => spaceAssembly_odd_class c0 (toUnitary χ) (u χ)).trans
        (finiteAbelianK1Equiv_apply u).symm)

end Glue

end BC4lean.Chapter8Examples.FiniteAbelianAssembly

namespace BC4lean.Chapter8Examples
open FiniteAbelianAssembly KKTheory

/-- The reduced assembly map of a finite abelian group, as an explicit additive equivalence. -/
def finiteAbelianAssemblyAddEquiv (Γ : Type) [CommGroup Γ] [Finite Γ] [Countable Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ] (p : Bool) :
    TopologicalKHomology.topologicalGroup p Γ ≃+ Assembly.analyticGroup Γ p :=
  letI : Fintype Γ := Fintype.ofFinite Γ
  (finiteTopologicalPointSpaceEquiv Γ p).trans
    ((finiteAbelianPointKKSplit.{0,0} (Γ := Γ) FiniteGroupPoint.{0} default p).trans
      (finiteAbelianAnalyticEquiv Γ p))

/-- Identification with Chapter 7's canonical assembly map. -/
theorem reducedAssemblyHom_finiteAbelian_eq (Γ : Type) [CommGroup Γ] [Finite Γ] [Countable Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ] (p : Bool)
    (x : TopologicalKHomology.topologicalGroup p Γ) :
    Assembly.reducedAssemblyHom Γ p x = finiteAbelianAssemblyAddEquiv Γ p x := by
  let : Fintype Γ := Fintype.ofFinite Γ
  rw [reducedAssemblyHom_finitePoint]
  exact spaceAssemblyHom_finiteAbelian (Γ := Γ) (finitePointCutoff Γ) p _

/-- The coefficient-free reduced Baum–Connes property for every countable discrete finite abelian
group. -/
theorem baumConnesProperty_of_finite_commGroup (Γ : Type) [CommGroup Γ] [Finite Γ] [Countable Γ]
    [TopologicalSpace Γ] [DiscreteTopology Γ] : Assembly.BaumConnesProperty Γ := by
  intro p
  have h : (Assembly.reducedAssemblyHom Γ p :
      TopologicalKHomology.topologicalGroup p Γ → Assembly.analyticGroup Γ p) =
      finiteAbelianAssemblyAddEquiv Γ p := funext (reducedAssemblyHom_finiteAbelian_eq Γ p)
  rw [h]
  exact (finiteAbelianAssemblyAddEquiv Γ p).bijective

open scoped ComplexOrder in
/-- `K₀(C*_r Γ) ≃+ ℤ^Γ̂` for a finite abelian group: the analytic side `finiteAbelianK0Equiv`
followed, in each coordinate, by `KK₀(ℂ, ℂ) ≅ K₀(ℂ) ≅ ℤ`. This is an explicit form of the count
`reducedK0_of_commute` of `FiniteGroupOperatorK`, with one coordinate for each character. -/
def finiteAbelianReducedK0Equiv (Γ : Type) [CommGroup Γ] [Fintype Γ] [Countable Γ] :
    ReducedK0 Γ ≃+ (CharacterDual Γ → ℤ) :=
  (finiteAbelianK0Equiv Γ).symm.trans
    (AddEquiv.piCongrRight fun _ => scalarKKOperatorK0AddEquiv.{0, 0}.trans
      OperatorKTheory.operatorK0ScalarEquiv)

/-- The order-two case as a corollary: a group of order two is cyclic, hence commutative. This
re-derives `baumConnesProperty_of_card_two` (which is kept) from the abelian theorem. -/
theorem baumConnesProperty_of_card_two' (Γ : Type) [Group Γ] [Countable Γ] [TopologicalSpace Γ]
    [DiscreteTopology Γ] (h2 : Nat.card Γ = 2) : Assembly.BaumConnesProperty Γ := by
  have : Finite Γ := Nat.finite_of_card_ne_zero (by omega)
  have : IsCyclic Γ := isCyclic_of_prime_card (p := 2) h2
  let : CommGroup Γ := IsCyclic.commGroup
  exact baumConnesProperty_of_finite_commGroup Γ

end BC4lean.Chapter8Examples
