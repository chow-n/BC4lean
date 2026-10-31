import BC4lean.FinitePointCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! The coset space `Γ ⧸ F` of a finite subgroup, as a piece of the universal proper model.

Let `Γ` be a countable discrete group and `F` a finite subgroup. The discrete coset space
`Γ ⧸ F` is a proper cocompact `Γ`-space with one orbit. A point of the canonical telescope
fixed by `F` gives an equivariant map `Γ ⧸ F → E_FIN Γ`, so by naturality of assembly every
value of the cutoff/product/descent assembly of `Γ ⧸ F` is a value of the canonical reduced
assembly map. On `Γ ⧸ F` the function `|F|^(-1/2) · 1_{eF}` is a normalized cutoff, and its
cutoff projection is `|F|⁻¹ ∑_{f ∈ F} 1_{eF} δ_f`. -/

noncomputable section
namespace BC4lean.Chapter8Examples.CosetAssembly
open ProperActions KKTheory OperatorKTheory
open scoped ZeroAtInfty CompactlySupported

section Space
variable (Γ : Type) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] (F : Subgroup Γ)

instance coset_discreteTopology : DiscreteTopology (Γ ⧸ F) :=
  ⟨eq_bot_of_singletons_open fun _ => isOpen_coinduced.mpr (isOpen_discrete _)⟩

instance coset_countable [Countable Γ] : Countable (Γ ⧸ F) :=
  QuotientGroup.mk_surjective.countable

instance coset_secondCountable [Countable Γ] : SecondCountableTopology (Γ ⧸ F) :=
  DiscreteTopology.secondCountableTopology_of_countable

instance coset_continuousConstSMul : ContinuousConstSMul Γ (Γ ⧸ F) :=
  ⟨fun _ => continuous_of_discreteTopology⟩

instance coset_continuousSMul : ContinuousSMul Γ (Γ ⧸ F) :=
  ⟨continuous_of_discreteTopology⟩

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- The elements carrying the coset `aF` to the coset `bF` form the finite set `b F a⁻¹`. -/
theorem finite_setOf_smul_eq [Finite F] (a b : Γ ⧸ F) : {g : Γ | g • a = b}.Finite := by
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  refine ((Set.finite_range fun f : F => b * (f : Γ) * a⁻¹)).subset ?_
  intro g hg
  change g • (a : Γ ⧸ F) = (b : Γ ⧸ F) at hg
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq] at hg
  refine ⟨⟨(g * a)⁻¹ * b, hg⟩⁻¹, ?_⟩
  simp [mul_assoc]

/-- A finite subgroup acts properly on its discrete coset space. -/
instance coset_proper [Finite F] : ProperSMul Γ (Γ ⧸ F) := by
  refine proper_iff_finite_transporters.mpr fun {K L} hK hL => ?_
  have hK' := hK.finite_of_discrete
  have hL' := hL.finite_of_discrete
  refine ((hK'.prod hL').biUnion fun q _ => finite_setOf_smul_eq Γ F q.1 q.2).subset ?_
  rintro g ⟨_, ⟨k, hk, rfl⟩, hl⟩
  exact Set.mem_biUnion (x := (k, g • k)) ⟨hk, hl⟩ rfl

/-- The whole coset space is one closed cocompact piece: its orbit space is a point. -/
def wholePiece : CocompactPiece Γ (Γ ⧸ F) where
  carrier := Set.univ
  smul_mem _ _ _ := Set.mem_univ _
  isClosed_carrier := isClosed_univ
  isCompact_image := by
    refine Set.Subsingleton.isCompact ?_
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
    induction x using QuotientGroup.induction_on with | H a => ?_
    induction y using QuotientGroup.induction_on with | H b => ?_
    refine Quotient.sound (MulAction.orbitRel_apply.mpr ⟨a * b⁻¹, ?_⟩)
    change (a * b⁻¹) • (b : Γ ⧸ F) = (a : Γ ⧸ F)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel_right]

/-- The whole piece is the ambient coset space. -/
def wholeHomeomorph : (wholePiece Γ F).toInvariantSubset ≃ₜ Γ ⧸ F where
  toFun := Subtype.val
  invFun x := ⟨x, Set.mem_univ x⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

def wholeLift : EquivariantMap Γ (Γ ⧸ F) (wholePiece Γ F).toInvariantSubset where
  toFun x := ⟨x, Set.mem_univ x⟩
  continuous_toFun := continuous_id.subtype_mk _
  map_smul' _ _ := rfl

omit [DiscreteTopology Γ] in
theorem wholeLift_proper : IsProperMap (wholeLift Γ F) :=
  (wholeHomeomorph Γ F).symm.isProperMap

/-- The base coset `eF`. -/
abbrev base : Γ ⧸ F := ((1 : Γ) : Γ ⧸ F)

omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- `g⁻¹` fixes the base coset exactly when `g ∈ F`. -/
theorem inv_smul_base_eq_iff (g : Γ) : g⁻¹ • base Γ F = base Γ F ↔ g ∈ F := by
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
  simp

/-- A function on the discrete coset space vanishing off the base coset has compact support. -/
theorem hasCompactSupport_of_base {M : Type*} [Zero M] (φ : Γ ⧸ F → M)
    (h : ∀ x, x ≠ base Γ F → φ x = 0) : HasCompactSupport φ := by
  refine (isCompact_singleton (x := base Γ F)).of_isClosed_subset (isClosed_tsupport φ) ?_
  rw [tsupport, closure_discrete]
  intro x hx
  by_contra hne
  exact hx (h x hne)

open Classical in
/-- The indicator `δ_{eF}` of the base coset, as an element of `C₀(Γ ⧸ F)`. -/
def cosetDelta : C₀(Γ ⧸ F, ℂ) where
  toFun x := if x = base Γ F then 1 else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := HasCompactSupport.is_zero_at_infty
    (hasCompactSupport_of_base Γ F _ fun _ hx => if_neg hx)

open Classical in
theorem cosetDelta_apply (x : Γ ⧸ F) :
    cosetDelta Γ F x = if x = ((1 : Γ) : Γ ⧸ F) then 1 else 0 := rfl

end Space

section Cutoff
variable (Γ : Type) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] (F : Subgroup Γ) [Finite F]

open Classical in
/-- The cutoff `|F|^(-1/2) · 1_{eF}` as a compactly supported function. -/
def baseCutoffMap : C_c(Γ ⧸ F, ℝ) where
  toFun x := if x = base Γ F then (Real.sqrt (Nat.card F))⁻¹ else 0
  continuous_toFun := continuous_of_discreteTopology
  hasCompactSupport' := hasCompactSupport_of_base Γ F _ fun _ hx => if_neg hx

open Classical in
omit [Finite F] in
theorem baseCutoffMap_apply (x : Γ ⧸ F) :
    baseCutoffMap Γ F x = if x = base Γ F then (Real.sqrt (Nat.card F))⁻¹ else 0 := rfl

open Classical in
omit [TopologicalSpace Γ] [DiscreteTopology Γ] [Finite F] in
/-- The square of the cutoff at `g⁻¹ • eF` is `|F|⁻¹` exactly when `g ∈ F`. -/
theorem baseCutoff_sq (g : Γ) :
    ((if g⁻¹ • base Γ F = base Γ F then (Real.sqrt (Nat.card F))⁻¹ else 0) : ℝ) ^ 2 =
      if g ∈ F then (Nat.card F : ℝ)⁻¹ else 0 := by
  by_cases hg : g ∈ F
  · rw [if_pos ((inv_smul_base_eq_iff Γ F g).mpr hg), if_pos hg, inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  · rw [if_neg (mt (inv_smul_base_eq_iff Γ F g).mp hg), if_neg hg, zero_pow two_ne_zero]

open Classical in
omit [TopologicalSpace Γ] [DiscreteTopology Γ] in
/-- `∑ᶠ g, [g ∈ F] |F|⁻¹ = 1`. -/
theorem finsum_mem_inv_card :
    ∑ᶠ g : Γ, (if g ∈ F then (Nat.card F : ℝ)⁻¹ else 0) = 1 := by
  have hn : (Nat.card F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hind : (fun g : Γ => if g ∈ F then (Nat.card F : ℝ)⁻¹ else 0) =
      (F : Set Γ).indicator (fun _ => (Nat.card F : ℝ)⁻¹) := by
    funext g
    by_cases hg : g ∈ F <;> simp [hg]
  rw [hind, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite (F : Set Γ)),
    Finset.sum_const, nsmul_eq_mul, ← Nat.card_eq_card_finite_toFinset]
  exact mul_inv_cancel₀ hn

/-- The normalized cutoff `|F|^(-1/2) · 1_{eF}` on `Γ ⧸ F`. -/
def baseCutoff : Cutoff.CutoffFunction Γ (Γ ⧸ F) where
  toCompactlySupportedContinuousMap := baseCutoffMap Γ F
  nonneg x := by
    classical
    change 0 ≤ baseCutoffMap Γ F x
    rw [baseCutoffMap_apply]
    split_ifs
    · exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    · exact le_rfl
  normalized x := by
    classical
    induction x using QuotientGroup.induction_on with | H a => ?_
    rw [← finsum_mem_inv_card Γ F, ← finsum_comp_equiv (Equiv.mulLeft a)]
    refine finsum_congr fun g => ?_
    change (baseCutoffMap Γ F (((a * g)⁻¹ : Γ) • ((a : Γ) : Γ ⧸ F))) ^ 2 = _
    have h : ((a * g)⁻¹ : Γ) • ((a : Γ) : Γ ⧸ F) = g⁻¹ • base Γ F := by
      rw [MulAction.Quotient.smul_mk, MulAction.Quotient.smul_mk, mul_inv_rev, smul_eq_mul,
        smul_eq_mul, mul_one, inv_mul_cancel_right]
    rw [h, baseCutoffMap_apply, baseCutoff_sq]

@[simp] theorem baseCutoff_apply (x : Γ ⧸ F) :
    baseCutoff Γ F x = baseCutoffMap Γ F x := rfl

omit [DiscreteTopology Γ] [Finite F] in
theorem cZero_finsetSum_apply {ι : Type*} (s : Finset ι) (f : ι → C₀(Γ ⧸ F, ℂ)) (x : Γ ⧸ F) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x :=
  map_sum ({ toFun := fun a : C₀(Γ ⧸ F, ℂ) => a x, map_zero' := rfl, map_add' := fun _ _ => rfl } :
    C₀(Γ ⧸ F, ℂ) →+ ℂ) f s

/-- The coefficients of the cutoff projection: `p(g) = [g ∈ F] |F|⁻¹ δ_{eF}`, i.e.
`p = ∑_{f ∈ F} |F|⁻¹ δ_{eF} · δ_f`. -/
theorem algebraicProjection_baseCutoff [Fintype F] :
    Cutoff.algebraicProjection (baseCutoff Γ F) =
      ∑ f : F, AlgebraicCrossedProduct.single (CZero.action Γ) (f : Γ)
        ((Nat.card F : ℂ)⁻¹ • cosetDelta Γ F) := by
  classical
  apply AlgebraicCrossedProduct.ext
  intro g
  apply ZeroAtInftyContinuousMap.ext
  intro x
  rw [AlgebraicCrossedProduct.coeff_sum, Finsupp.finsetSum_apply]
  simp only [AlgebraicCrossedProduct.coeff_single, Finsupp.single_apply]
  change ((baseCutoff Γ F x * baseCutoff Γ F (g⁻¹ • x) : ℝ) : ℂ) = _
  rw [cZero_finsetSum_apply]
  by_cases hx : x = base Γ F
  · subst hx
    have hsq := baseCutoff_sq Γ F g
    simp only [baseCutoff_apply, baseCutoffMap_apply, if_true]
    by_cases hg : g ∈ F
    · rw [if_pos ((inv_smul_base_eq_iff Γ F g).mpr hg), ← sq, inv_pow,
        Real.sq_sqrt (Nat.cast_nonneg _)]
      rw [Finset.sum_eq_single ⟨g, hg⟩ (fun f _ hf => by
          rw [if_neg fun h => hf (Subtype.ext h)]; rfl) (by simp)]
      simp [cosetDelta_apply]
    · rw [if_neg (mt (inv_smul_base_eq_iff Γ F g).mp hg), mul_zero, Complex.ofReal_zero]
      refine (Finset.sum_eq_zero fun f _ => ?_).symm
      rw [if_neg fun h : (f : Γ) = g => hg (h ▸ f.2)]
      rfl
  · simp only [baseCutoff_apply, baseCutoffMap_apply, if_neg hx, zero_mul, Complex.ofReal_zero]
    refine (Finset.sum_eq_zero fun f _ => ?_).symm
    split_ifs
    · simp [cosetDelta_apply, hx]
    · rfl

end Cutoff

section Model
variable (Γ : Type) [Group Γ] [Countable Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
  (F : Subgroup Γ) [Finite F]

/-- A point of the canonical telescope fixed by `F`: the fixed set is contractible by the
fixed-point criterion, hence nonempty, and this is a point of it chosen by `Classical.choice`. -/
def fixedPoint : FixedPointSpace F (LabeledOrbitTelescope.Model Γ) := by
  letI : ContractibleSpace (FixedPointSpace F (LabeledOrbitTelescope.Model Γ)) :=
    (LabeledOrbitTelescope.fixedPointCriterion Γ).1 F inferInstance
  exact (Classical.choice (ContractibleSpace.hequiv_unit
    (FixedPointSpace F (LabeledOrbitTelescope.Model Γ)))).invFun ()

theorem smul_fixedPoint (f : Γ) (hf : f ∈ F) :
    f • (fixedPoint Γ F).val = (fixedPoint Γ F).val :=
  (fixedPoint Γ F).property ⟨f, hf⟩

/-- The orbit map `gF ↦ g • x₀` of the fixed point. -/
def toModel : EquivariantMap Γ (Γ ⧸ F) (LabeledOrbitTelescope.Model Γ) where
  toFun := Quotient.lift (fun g : Γ => g • (fixedPoint Γ F).val) (by
    intro a b h
    have h' : a⁻¹ * b ∈ F := QuotientGroup.leftRel_apply.mp h
    change a • (fixedPoint Γ F).val = b • (fixedPoint Γ F).val
    conv_lhs => rw [← smul_fixedPoint Γ F _ h']
    rw [smul_smul, mul_inv_cancel_left])
  continuous_toFun := continuous_of_discreteTopology
  map_smul' g x := by
    induction x using QuotientGroup.induction_on with | H a => ?_
    change Quotient.lift _ _ (g • (a : Γ ⧸ F)) = g • (a • (fixedPoint Γ F).val)
    rw [MulAction.Quotient.smul_mk, smul_smul]
    rfl

local instance model_proper : ProperSMul Γ (LabeledOrbitTelescope.Model Γ) :=
  LabeledOrbitTelescope.proper Γ

local instance piece_locallyCompact :
    LocallyCompactSpace (wholePiece Γ F).toInvariantSubset := (wholePiece Γ F).locallyCompact

/-- Every value of the coset-space assembly is a value of the canonical reduced assembly
map: push the class into the whole piece, then along `Γ ⧸ F → E_FIN Γ`. -/
theorem reducedAssemblyHom_toModel (p : Bool) (c : Cutoff.CutoffFunction Γ (Γ ⧸ F))
    (y : TopologicalKHomology.spaceGroup p Γ (Γ ⧸ F)) :
    Assembly.reducedAssemblyHom Γ p
        (TopologicalKHomology.pushforward p (toModel Γ F)
          (TopologicalKHomology.ofPiece p (wholePiece Γ F)
            (TopologicalKHomology.properPushforward p (wholeLift Γ F) (wholeLift_proper Γ F) y))) =
      Assembly.spaceAssemblyHom Γ (Γ ⧸ F) p c y := by
  refine (Assembly.assemblyHom_pushforward Γ (Γ ⧸ F) (LabeledOrbitTelescope.Model Γ) p
    (toModel Γ F) _).trans ?_
  rw [Assembly.assemblyHom_ofPiece]
  exact Assembly.spaceAssemblyHom_properPushforward Γ (Γ ⧸ F) (wholePiece Γ F).toInvariantSubset p
    (wholeLift Γ F) (wholeLift_proper Γ F) (Assembly.pieceCutoff Γ (Γ ⧸ F) (wholePiece Γ F)) c y

theorem spaceAssemblyHom_mem_range (p : Bool) (c : Cutoff.CutoffFunction Γ (Γ ⧸ F))
    (y : TopologicalKHomology.spaceGroup p Γ (Γ ⧸ F)) :
    Assembly.spaceAssemblyHom Γ (Γ ⧸ F) p c y ∈ (Assembly.reducedAssemblyHom Γ p).range :=
  ⟨_, reducedAssemblyHom_toModel Γ F p c y⟩

end Model

end BC4lean.Chapter8Examples.CosetAssembly
