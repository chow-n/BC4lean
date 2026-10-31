import BC4lean.BaumConnesInvariance
import BC4lean.LabeledTelescopeCW
import BC4lean.KKGroupRestriction
import BC4lean.CZeroAlgebra
import BC4lean.CocompactPieces

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # Pulled-back spaces and the classifying telescope

For `e : Γ ≃* Γ'` and a `Γ'`-space `X`, the `Γ`-space `Pull e X`; the canonical telescope of `Γ` is
equivariantly homotopy equivalent to the pulled-back telescope of `Γ'`; function algebras and
cocompact pieces of pulled-back spaces.
-/

noncomputable section

/-! ## Universal models along a group isomorphism

For `e : Γ ≃* Γ'` and a `Γ'`-space `X`, `Pull e X` is `X` with `γ • x := e γ • x`.
The canonical telescope of `Γ` and the pulled-back telescope of `Γ'` are equivariantly
homotopy equivalent as `Γ`-spaces. No CW structure is put on the pulled-back space: each
of the four homotopy-terminal premises is either proved directly for a genuine CW source
or read off from the `Γ'`-side by relabelling. Hence the canonical assembly map of `Γ` is
bijective exactly when assembly of `Γ` on the pulled-back telescope of `Γ'` is.
-/

namespace BC4lean.KKTheory.GroupIso
open ProperActions

universe u v w

section Pull
variable {Γ Γ' : Type u} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')

/-- A `Γ'`-space seen as a `Γ`-space through `e`. -/
def Pull (_ : Γ ≃* Γ') (X : Type v) : Type v := X

variable (X : Type v)

instance [TopologicalSpace X] : TopologicalSpace (Pull e X) := ‹TopologicalSpace X›

instance [MulAction Γ' X] : MulAction Γ (Pull e X) :=
  MulAction.compHom X e.toMonoidHom

theorem pull_smul [MulAction Γ' X] (g : Γ) (x : Pull e X) :
    g • x = (show X from (e g • (show X from x))) := rfl

instance [TopologicalSpace X] [MulAction Γ' X] [ContinuousConstSMul Γ' X] :
    ContinuousConstSMul Γ (Pull e X) :=
  ⟨fun g => continuous_const_smul (T := X) (e g)⟩

instance [TopologicalSpace X] [LocallyCompactSpace X] : LocallyCompactSpace (Pull e X) :=
  ‹LocallyCompactSpace X›

instance [TopologicalSpace X] [T2Space X] : T2Space (Pull e X) := ‹T2Space X›

instance [TopologicalSpace X] [SecondCountableTopology X] :
    SecondCountableTopology (Pull e X) := ‹SecondCountableTopology X›

/-- A group isomorphism between discrete groups is a homeomorphism. -/
def discreteHomeomorph [TopologicalSpace Γ] [DiscreteTopology Γ]
    [TopologicalSpace Γ'] [DiscreteTopology Γ'] : Γ ≃ₜ Γ' where
  toEquiv := e.toEquiv
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- Properness pulls back: the pair map factors through `e × id`. -/
instance [TopologicalSpace Γ] [DiscreteTopology Γ] [TopologicalSpace Γ'] [DiscreteTopology Γ']
    [TopologicalSpace X] [MulAction Γ' X] [ProperSMul Γ' X] : ProperSMul Γ (Pull e X) where
  isProperMap_smul_pair := by
    have h := (ProperSMul.isProperMap_smul_pair (G := Γ') (X := X)).comp
      ((discreteHomeomorph e).isProperMap.prodMap isProperMap_id)
    exact h

end Pull

section Transfer
variable {Γ₁ Γ₂ : Type*} [Group Γ₁] [Group Γ₂] (e : Γ₁ ≃* Γ₂)
  {X₁ Y₁ X₂ Y₂ : Type*} [TopologicalSpace X₁] [TopologicalSpace Y₁]
  [TopologicalSpace X₂] [TopologicalSpace Y₂]
  [MulAction Γ₁ X₁] [MulAction Γ₁ Y₁] [MulAction Γ₂ X₂] [MulAction Γ₂ Y₂]
  (hx : X₁ ≃ₜ X₂) (hy : Y₁ ≃ₜ Y₂)
  (hxs : ∀ (g : Γ₁) (x : X₁), hx (g • x) = e g • hx x)
  (hys : ∀ (g : Γ₁) (y : Y₁), hy (g • y) = e g • hy y)

include hys in
theorem symm_smul (g : Γ₁) (y : Y₂) : hy.symm (e g • y) = g • hy.symm y := by
  apply hy.injective
  rw [hys, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

include hxs hys in
/-- Carry a `Γ₂`-map back to a `Γ₁`-map. -/
def mapBack (f : EquivariantMap Γ₂ X₂ Y₂) : EquivariantMap Γ₁ X₁ Y₁ where
  toContinuousMap := (hy.symm : C(Y₂, Y₁)).comp (f.toContinuousMap.comp (hx : C(X₁, X₂)))
  map_smul' g x := by
    change hy.symm (f (hx (g • x))) = g • hy.symm (f (hx x))
    rw [hxs, f.map_smul, symm_smul e hy hys]

include hxs hys in
/-- Carry a `Γ₁`-map forward to a `Γ₂`-map; this uses that `e` is onto. -/
def mapForth (f : EquivariantMap Γ₁ X₁ Y₁) : EquivariantMap Γ₂ X₂ Y₂ where
  toContinuousMap := (hy : C(Y₁, Y₂)).comp (f.toContinuousMap.comp (hx.symm : C(X₂, X₁)))
  map_smul' g x := by
    change hy (f (hx.symm (g • x))) = g • hy (f (hx.symm x))
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [symm_smul e hx hxs, f.map_smul, hys]

include hxs hys in
theorem homotopic_back {f g : EquivariantMap Γ₂ X₂ Y₂} (h : EquivariantlyHomotopic f g) :
    EquivariantlyHomotopic (mapBack e hx hy hxs hys f) (mapBack e hx hy hxs hys g) := by
  obtain ⟨H⟩ := h
  refine ⟨{ toHomotopy :=
    { toFun := fun p => hy.symm (H (p.1, hx p.2))
      continuous_toFun := hy.symm.continuous.comp
        (H.continuous.comp (continuous_fst.prodMk (hx.continuous.comp continuous_snd)))
      map_zero_left := fun x => by simp [mapBack]
      map_one_left := fun x => by simp [mapBack] }, prop' := ?_ }⟩
  intro t a x
  change hy.symm (H (t, hx (a • x))) = a • hy.symm (H (t, hx x))
  rw [hxs, ← symm_smul e hy hys]
  exact congrArg hy.symm (H.prop t (e a) (hx x))

include hxs hys in
theorem back_forth (f : EquivariantMap Γ₁ X₁ Y₁) :
    mapBack e hx hy hxs hys (mapForth e hx hy hxs hys f) = f := by
  ext x
  change hy.symm (hy (f (hx.symm (hx x)))) = f x
  simp

include hxs hys in
/-- Homotopy terminality is invariant under relabelling along a group isomorphism. -/
theorem homotopyTerminalFor_transfer (h : HomotopyTerminalFor Γ₂ X₂ Y₂) :
    HomotopyTerminalFor Γ₁ X₁ Y₁ := by
  obtain ⟨⟨f⟩, hh⟩ := h
  refine ⟨⟨mapBack e hx hy hxs hys f⟩, fun f g => ?_⟩
  rw [← back_forth e hx hy hxs hys f, ← back_forth e hx hy hxs hys g]
  exact homotopic_back e hx hy hxs hys (hh _ _)

include hxs in
/-- Fixed points of `H` correspond to fixed points of its image under `e`. -/
theorem mem_fixedPoints_iff (H : Subgroup Γ₁) (x : X₁) :
    x ∈ MulAction.fixedPoints H X₁ ↔
      hx x ∈ MulAction.fixedPoints (H.map e.toMonoidHom) X₂ := by
  constructor
  · rintro hfix ⟨_, g, hg, rfl⟩
    change e g • hx x = hx x
    rw [← hxs]
    exact congrArg hx (hfix ⟨g, hg⟩)
  · intro hfix ⟨g, hg⟩
    apply hx.injective
    change hx (g • x) = hx x
    rw [hxs]
    exact hfix ⟨e g, g, hg, rfl⟩

include hxs in
/-- The fixed-point criterion transfers along relabelling. -/
theorem fixedPointCriterion_transfer (h : FixedPointCriterion Γ₂ X₂) :
    FixedPointCriterion Γ₁ X₁ := by
  have hH (H : Subgroup Γ₁) : H ≃ H.map e.toMonoidHom :=
    (H.equivMapOfInjective e.toMonoidHom e.injective).toEquiv
  have hfix (H : Subgroup Γ₁) : FixedPointSpace H X₁ ≃ₜ FixedPointSpace (H.map e.toMonoidHom) X₂ :=
    hx.subtype (mem_fixedPoints_iff e hx hxs H)
  constructor
  · intro H hfin
    have : Finite (H.map e.toMonoidHom) := Finite.of_equiv H (hH H)
    have := h.1 _ this
    exact (hfix H).contractibleSpace
  · intro H hinf
    have : Infinite (H.map e.toMonoidHom) := Infinite.of_injective (hH H) (hH H).injective
    have := h.2 _ this
    exact ⟨fun x => isEmptyElim (hfix H x)⟩

end Transfer

section Telescope
variable {Γ Γ' : Type u} [Group Γ] [Group Γ'] [Countable Γ] [Countable Γ']
  [TopologicalSpace Γ] [DiscreteTopology Γ] [TopologicalSpace Γ'] [DiscreteTopology Γ']
  (e : Γ ≃* Γ')

/-- The canonical telescope of `Γ` and the pulled-back telescope of `Γ'` are
equivariantly homotopy equivalent `Γ`-spaces. -/
theorem nonempty_homotopyEquiv_pull :
    Nonempty (EquivariantHomotopyEquiv Γ (LabeledOrbitTelescope.Model Γ) (Pull e (LabeledOrbitTelescope.Model Γ'))) := by
  have hP : FixedPointCriterion Γ (Pull e (LabeledOrbitTelescope.Model Γ')) :=
    fixedPointCriterion_transfer e (Homeomorph.refl (LabeledOrbitTelescope.Model Γ')) (fun _ _ => rfl)
      (LabeledOrbitTelescope.fixedPointCriterion Γ')
  have hQ : FixedPointCriterion Γ' (Pull e.symm (LabeledOrbitTelescope.Model Γ)) :=
    fixedPointCriterion_transfer e.symm (Homeomorph.refl (LabeledOrbitTelescope.Model Γ)) (fun _ _ => rfl)
      (LabeledOrbitTelescope.fixedPointCriterion Γ)
  have cM := LabeledOrbitTelescope.equivariantCWComplex Γ
  have cM' := LabeledOrbitTelescope.equivariantCWComplex Γ'
  apply homotopyTerminal_unique
  · exact cM.homotopyTerminal hP
  · refine homotopyTerminalFor_transfer (X₂ := LabeledOrbitTelescope.Model Γ') (Y₂ := Pull e.symm (LabeledOrbitTelescope.Model Γ)) e
      (Homeomorph.refl (LabeledOrbitTelescope.Model Γ')) (Homeomorph.refl (LabeledOrbitTelescope.Model Γ)) (fun _ _ => rfl) (fun g y => ?_)
      (cM'.homotopyTerminal hQ)
    change g • y = e.symm (e g) • y
    rw [e.symm_apply_apply]
  · exact cM.homotopyTerminal (LabeledOrbitTelescope.fixedPointCriterion Γ)
  · exact homotopyTerminalFor_transfer e (Homeomorph.refl (LabeledOrbitTelescope.Model Γ')) (Homeomorph.refl (LabeledOrbitTelescope.Model Γ'))
      (fun _ _ => rfl) (fun _ _ => rfl)
      (cM'.homotopyTerminal (LabeledOrbitTelescope.fixedPointCriterion Γ'))

/-- Canonical assembly of `Γ` is bijective exactly when assembly of `Γ` on the
pulled-back telescope of `Γ'` is. -/
theorem reducedAssemblyHom_bijective_iff_pull (p : Bool) :
    letI : ProperSMul Γ' (LabeledOrbitTelescope.Model Γ') := LabeledOrbitTelescope.proper Γ'
    Function.Bijective (Assembly.reducedAssemblyHom Γ p) ↔
      Function.Bijective (Assembly.assemblyHom Γ (Pull e (LabeledOrbitTelescope.Model Γ')) p) := by
  let : ProperSMul Γ (LabeledOrbitTelescope.Model Γ) := LabeledOrbitTelescope.proper Γ
  let : ProperSMul Γ' (LabeledOrbitTelescope.Model Γ') := LabeledOrbitTelescope.proper Γ'
  obtain ⟨h⟩ := nonempty_homotopyEquiv_pull e
  exact Assembly.assemblyHom_bijective_iff_homotopyEquiv Γ (LabeledOrbitTelescope.Model Γ) (Pull e (LabeledOrbitTelescope.Model Γ')) p h

end Telescope

end BC4lean.KKTheory.GroupIso

/-! ## Function algebras of pulled-back spaces

`C₀(e* X)` is `C₀(X)` as an algebra, and its `Γ`-action is the restriction along `e` of the
`Γ'`-action on `C₀(X)`. The two actions agree pointwise by `map_inv` (`e g⁻¹ = (e g)⁻¹`), not
definitionally, so equivariant KK classes are moved between them by `▸` along this equality.
-/

namespace BC4lean.KKTheory.GroupIso
open scoped ZeroAtInfty
universe u v
open KKTheory.GroupRestriction
open KKTheory

variable {Γ Γ' : Type u} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')
  (X : Type v) [TopologicalSpace X] [MulAction Γ' X] [ContinuousConstSMul Γ' X]

/-- The action of `Γ` on `C₀(e* X)` is the restriction of the action of `Γ'` on
`C₀(X)`. -/
theorem cZeroAction_pull :
    (CZero.action Γ (X := Pull e X) : CStarAlgebraAction Γ C₀(X, ℂ)) =
      actionComap e.toMonoidHom (CZero.action Γ' (X := X)) := by
  unfold CZero.action actionComap
  congr 1
  ext g a x
  change a (e g⁻¹ • (show X from x)) = a ((e g)⁻¹ • (show X from x))
  rw [map_inv]

end BC4lean.KKTheory.GroupIso

/-! ## Cocompact pieces of a pulled-back space

For `e : Γ ≃* Γ'` and a `Γ'`-space `X`, the orbit relations of `Γ` on `Pull e X` and of `Γ'` on
`X` are the same setoid, because `e` is onto. Hence the `Γ`-invariant subsets of `Pull e X` are
the `Γ'`-invariant subsets of `X`, with the same orbit images, and the cocompact pieces of the two
spaces correspond by an order isomorphism that keeps every carrier.
-/

namespace BC4lean.KKTheory.GroupIso
universe u v
open ProperActions

variable {Γ Γ' : Type u} [Group Γ] [Group Γ'] (e : Γ ≃* Γ')
  (X : Type v) [TopologicalSpace X] [MulAction Γ' X]

omit [TopologicalSpace X] in
/-- The orbit relations agree. -/
theorem orbitRel_pull :
    (MulAction.orbitRel Γ (Pull e X) : Setoid X) = MulAction.orbitRel Γ' X := by
  ext x y
  change (∃ g : Γ, e g • (show X from y) = x) ↔ ∃ g' : Γ', g' • (show X from y) = x
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨e g, hg⟩
  · rintro ⟨g', hg'⟩
    exact ⟨e.symm g', by rw [MulEquiv.apply_symm_apply]; exact hg'⟩

/-- Compactness of an orbit image is the same statement for both actions. -/
theorem isCompact_image_pull_iff (s : Set X) :
    IsCompact (Quotient.mk (MulAction.orbitRel Γ (Pull e X)) '' (s : Set (Pull e X))) ↔
      IsCompact (Quotient.mk (MulAction.orbitRel Γ' X) '' s) := by
  -- `Setoid X` and `Setoid (Pull e X)` differ only by `Pull`, which instance search does not unfold
  -- (stating the left side over `X` failed to find the quotient topology). Keep the
  -- left side over `Pull e X` and generalize its setoid.
  have h : (MulAction.orbitRel Γ (Pull e X) : Setoid (Pull e X)) =
      (MulAction.orbitRel Γ' X : Setoid (Pull e X)) := orbitRel_pull e X
  revert h
  generalize (MulAction.orbitRel Γ (Pull e X) : Setoid (Pull e X)) = r
  rintro rfl
  exact Iff.rfl

omit [TopologicalSpace X] in
/-- `Γ`-invariance on `Pull e X` is `Γ'`-invariance on `X`. -/
theorem smul_mem_pull_iff (s : Set X) :
    (∀ (g : Γ) {x : Pull e X}, x ∈ s → g • x ∈ s) ↔
      (∀ (g' : Γ') {x : X}, x ∈ s → g' • x ∈ s) := by
  constructor
  · intro h g' x hx
    have h' : e (e.symm g') • x ∈ s := h (e.symm g') (x := (show Pull e X from x)) hx
    rwa [MulEquiv.apply_symm_apply] at h'
  · intro h g x hx
    rw [pull_smul]
    exact h (e g) hx

/-- The cocompact pieces of `Pull e X` (for `Γ`) and of `X` (for `Γ'`) correspond, with
the same carriers. -/
def pieceRelabel : CocompactPiece Γ (Pull e X) ≃o CocompactPiece Γ' X where
  toFun S :=
    { carrier := S.carrier
      smul_mem := (smul_mem_pull_iff e X S.carrier).mp S.smul_mem
      isClosed_carrier := S.isClosed_carrier
      isCompact_image := (isCompact_image_pull_iff e X S.carrier).mp S.isCompact_image }
  invFun S :=
    { carrier := S.carrier
      smul_mem := (smul_mem_pull_iff e X S.carrier).mpr S.smul_mem
      isClosed_carrier := S.isClosed_carrier
      isCompact_image := (isCompact_image_pull_iff e X S.carrier).mpr S.isCompact_image }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

@[simp] theorem pieceRelabel_carrier (S : CocompactPiece Γ (Pull e X)) :
    (pieceRelabel e X S).carrier = S.carrier := rfl

@[simp] theorem pieceRelabel_symm_carrier (S : CocompactPiece Γ' X) :
    ((pieceRelabel e X).symm S).carrier = S.carrier := rfl

end BC4lean.KKTheory.GroupIso
