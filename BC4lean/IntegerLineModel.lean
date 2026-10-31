import BC4lean.CompactModelColimitCalibration
import BC4lean.IntegerGroup
import BC4lean.LabeledTelescopeCW

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The real line as a proper cocompact model for the integers

The group is `Multiplicative ℤ` with its discrete topology, acting on a type synonym of `ℝ`
by translation. The line satisfies the fixed-point criterion, the action is proper with
compact orbit space, and the line is equivariantly homotopy equivalent to the canonical
telescope. No CW structure on the line is used: the telescope maps to the line by its
cellular mapping property, the line maps to the telescope through a path from a point to
its translate, and the composite on the line is the identity up to the straight-line
homotopy. Canonical assembly for the integers is then the cutoff/descent formula on the
line. This is a reduction of assembly for the integers, not a proof of assembly bijectivity.

The homotopy equivalence `intLineHomotopyEquiv` is a chosen one (a cellular map one way, a path
between chosen points the other way). The assembly formula holds for every cutoff function
(`reducedAssemblyHom_line_formula_anyCutoff`). -/

noncomputable section
namespace BC4lean.Chapter8Examples.IntegerLine
open ProperActions KKTheory
open scoped ZeroAtInfty ComplexOrder KasparovDescent

/-! ## The line with translations -/

/-- The real line, as a type synonym carrying the translation action of `Multiplicative ℤ`. -/
def IntLine : Type := ℝ
namespace IntLine
def toReal (x : IntLine) : ℝ := x
def ofReal (r : ℝ) : IntLine := r
@[simp] theorem toReal_ofReal (r : ℝ) : toReal (ofReal r) = r := rfl
@[simp] theorem ofReal_toReal (x : IntLine) : ofReal (toReal x) = x := rfl
theorem toReal_injective : Function.Injective toReal := fun _ _ h => h
end IntLine
open IntLine

instance : TopologicalSpace IntLine := inferInstanceAs (TopologicalSpace ℝ)
instance : LocallyCompactSpace IntLine := inferInstanceAs (LocallyCompactSpace ℝ)
instance : T2Space IntLine := inferInstanceAs (T2Space ℝ)
instance : SecondCountableTopology IntLine := inferInstanceAs (SecondCountableTopology ℝ)

/-- Translation: `n • x = x + n`. -/
instance intLineMulAction : MulAction (Multiplicative ℤ) IntLine where
  smul n x := ofReal (toReal x + ((Multiplicative.toAdd n : ℤ) : ℝ))
  one_smul x := toReal_injective (by
    change toReal x + ((Multiplicative.toAdd (1 : Multiplicative ℤ) : ℤ) : ℝ) = toReal x
    simp)
  mul_smul m n x := toReal_injective (by
    change toReal x + ((Multiplicative.toAdd (m * n) : ℤ) : ℝ) =
      (toReal x + ((Multiplicative.toAdd n : ℤ) : ℝ)) + ((Multiplicative.toAdd m : ℤ) : ℝ)
    rw [toAdd_mul]; push_cast; ring)

theorem toReal_smul (n : Multiplicative ℤ) (x : IntLine) :
    toReal (n • x) = toReal x + ((Multiplicative.toAdd n : ℤ) : ℝ) := rfl

theorem continuous_toReal : Continuous toReal := continuous_id
theorem continuous_ofReal : Continuous ofReal := continuous_id

instance : ContinuousConstSMul (Multiplicative ℤ) IntLine where
  continuous_const_smul _ :=
    continuous_ofReal.comp (continuous_toReal.add continuous_const)

/-! ## Fixed points -/

/-- Only the trivial subgroup fixes a point: a nonzero translation moves every point. -/
theorem intLine_fixed_iff (n : Multiplicative ℤ) (x : IntLine) : n • x = x ↔ n = 1 := by
  constructor
  · intro h
    have h' := congrArg toReal h
    rw [toReal_smul] at h'
    have : ((Multiplicative.toAdd n : ℤ) : ℝ) = 0 := by linarith
    exact Multiplicative.toAdd.injective (by exact_mod_cast this)
  · rintro rfl; exact one_smul _ _

/-- A finite subgroup of the integers is trivial. -/
theorem finite_subgroup_int_eq_bot (H : Subgroup (Multiplicative ℤ)) [Finite H] : H = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  have h1 := congrArg Subtype.val (pow_card_eq_one' (G := H) (x := ⟨g, hg⟩))
  simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h1
  have hpos : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h2 := congrArg Multiplicative.toAdd h1
  rw [toAdd_pow, toAdd_one] at h2
  exact Multiplicative.toAdd.injective
    (by simpa [hpos] using (smul_eq_zero.mp h2))

/-- Every point of a space is fixed by the trivial subgroup. -/
def botFixedHomeomorph (Γ Y : Type*) [Group Γ] [TopologicalSpace Y] [MulAction Γ Y] :
    FixedPointSpace (⊥ : Subgroup Γ) Y ≃ₜ Y where
  toFun := Subtype.val
  invFun y := ⟨y, fun g => by
    obtain ⟨g, hg⟩ := g
    rw [Subgroup.mem_bot] at hg
    subst hg; exact one_smul _ _⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

/-- The line satisfies BC4lean's fixed-point criterion for the integers. -/
theorem intLine_fixedPointCriterion : FixedPointCriterion (Multiplicative ℤ) IntLine := by
  constructor
  · intro H hH
    have hbot := finite_subgroup_int_eq_bot H
    subst hbot
    exact ((botFixedHomeomorph (Multiplicative ℤ) IntLine).trans
      (Homeomorph.refl ℝ)).contractibleSpace
  · intro H hH
    obtain ⟨g, hgH, hg1⟩ : ∃ g ∈ H, g ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : H = ⊥ := (Subgroup.eq_bot_iff_forall H).mpr hcon
      subst this
      exact not_finite (⊥ : Subgroup (Multiplicative ℤ))
    exact ⟨fun x => hg1 ((intLine_fixed_iff g x.1).mp (x.2 ⟨g, hgH⟩))⟩

/-! ## Properness and cocompactness -/

/-- Translates of a compact set meet another compact set for only finitely many integers:
if `|x| ≤ C₁` and `|x + n| ≤ C₂` then `|n| ≤ C₁ + C₂`. -/
theorem intLine_properlyDiscontinuous : ProperlyDiscontinuousSMul (Multiplicative ℤ) IntLine where
  finite_disjoint_inter_image {K L} hK hL := by
    obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn continuous_toReal.continuousOn
    obtain ⟨C₂, hC₂⟩ := hL.exists_bound_of_continuousOn continuous_toReal.continuousOn
    refine Set.Finite.subset (Set.Finite.preimage Multiplicative.toAdd.injective.injOn
      (Set.finite_Icc (-⌈C₁ + C₂⌉) ⌈C₁ + C₂⌉)) ?_
    rintro n ⟨_, ⟨x, hx, rfl⟩, hy⟩
    have h₁ := abs_le.mp (hC₁ x hx)
    have h₂ := abs_le.mp (hC₂ _ hy)
    rw [toReal_smul] at h₂
    have hc := Int.le_ceil (C₁ + C₂)
    have hu : ((Multiplicative.toAdd n : ℤ) : ℝ) ≤ ⌈C₁ + C₂⌉ := by linarith [h₁.1, h₂.2]
    have hl : -((⌈C₁ + C₂⌉ : ℤ) : ℝ) ≤ ((Multiplicative.toAdd n : ℤ) : ℝ) := by
      linarith [h₁.2, h₂.1]
    exact ⟨by exact_mod_cast hl, by exact_mod_cast hu⟩

/-- The translation action is proper, i.e. `(n, x) ↦ (x + n, x)` is a proper map. -/
instance intLine_proper : ProperSMul (Multiplicative ℤ) IntLine :=
  properlyDiscontinuousSMul_iff_properSMul.mp intLine_properlyDiscontinuous

/-- Every orbit meets `[0, 1]`: `x - ⌊x⌋` is a translate of `x`. -/
theorem intLine_quotient_image_unitInterval :
    Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) IntLine) '' (ofReal '' Set.Icc 0 1) = Set.univ := by
  refine Set.eq_univ_of_forall fun q => ?_
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective q
  refine ⟨Multiplicative.ofAdd (-⌊toReal x⌋) • x,
    ⟨Int.fract (toReal x), ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, ?_⟩, ?_⟩
  · apply toReal_injective
    rw [toReal_smul, toReal_ofReal, toAdd_ofAdd, ← Int.self_sub_floor]
    push_cast
    ring
  · exact Quotient.sound ((MulAction.orbitRel_apply).mpr (MulAction.mem_orbit _ _))

/-- The orbit space ℝ/ℤ is compact. -/
instance intLine_cocompact : CompactSpace (Quotient (MulAction.orbitRel (Multiplicative ℤ) IntLine)) where
  isCompact_univ := by
    rw [← intLine_quotient_image_unitInterval]
    exact (isCompact_Icc.image continuous_ofReal).image continuous_quotient_mk'

/-! ## The homotopy equivalence with the canonical telescope -/

/-- Any two equivariant maps into the line are homotopic through the straight-line
homotopy, which is equivariant because both ends commute with translation. -/
theorem intLine_equivariantlyHomotopic {X : Type*} [TopologicalSpace X] [MulAction (Multiplicative ℤ) X]
    (f g : EquivariantMap (Multiplicative ℤ) X IntLine) : EquivariantlyHomotopic f g :=
  ⟨{ toFun := fun p => ofReal ((1 - (p.1 : ℝ)) * toReal (f p.2) + (p.1 : ℝ) * toReal (g p.2))
     continuous_toFun := continuous_ofReal.comp
       (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          (continuous_toReal.comp (f.continuous.comp continuous_snd))).add
        ((continuous_subtype_val.comp continuous_fst).mul
          (continuous_toReal.comp (g.continuous.comp continuous_snd))))
     map_zero_left := fun x => by
       change ofReal _ = f x
       apply toReal_injective
       simp
     map_one_left := fun x => by
       change ofReal _ = g x
       apply toReal_injective
       simp
     prop' := fun t a x => by
       change ofReal ((1 - (t : ℝ)) * toReal (f (a • x)) + (t : ℝ) * toReal (g (a • x))) =
         a • ofReal ((1 - (t : ℝ)) * toReal (f x) + (t : ℝ) * toReal (g x))
       apply toReal_injective
       rw [toReal_smul, toReal_ofReal, toReal_ofReal, EquivariantMap.map_smul,
         EquivariantMap.map_smul, toReal_smul, toReal_smul]
       ring }⟩

/-- Wrap a path from `v` to its translate by the generator into the equivariant map
`x ↦ ⌊x⌋ • γ(x - ⌊x⌋)`. It is continuous because on each `[n, n + 1]` it agrees with
`x ↦ n • γ(x - n)` (at `x = n + 1` both sides are `(n + 1) • v`). -/
def intLineMap {Y : Type*} [TopologicalSpace Y] [MulAction (Multiplicative ℤ) Y] [ContinuousConstSMul (Multiplicative ℤ) Y] {v : Y}
    (γ : Path v (Multiplicative.ofAdd (1 : ℤ) • v)) : EquivariantMap (Multiplicative ℤ) IntLine Y where
  toFun x := Multiplicative.ofAdd ⌊toReal x⌋ • γ.extend (Int.fract (toReal x))
  continuous_toFun := by
    refine LocallyFinite.continuous (f := fun n : ℤ => toReal ⁻¹' Set.Icc (n : ℝ) (n + 1))
      ?_ ?_ ?_ ?_
    · intro x
      refine ⟨toReal ⁻¹' Set.Ioo (toReal x - 1) (toReal x + 1),
        continuous_toReal.continuousAt.preimage_mem_nhds
          (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
      refine (Set.finite_Icc (⌊toReal x⌋ - 2) (⌊toReal x⌋ + 2)).subset ?_
      rintro n ⟨y, ⟨hy₁, hy₂⟩, hy₃, hy₄⟩
      have hu : (n : ℝ) < ⌊toReal x⌋ + 2 := by linarith [Int.lt_floor_add_one (toReal x)]
      have hl : ((⌊toReal x⌋ : ℤ) : ℝ) - 2 < n := by linarith [Int.floor_le (toReal x)]
      have hu' : n < ⌊toReal x⌋ + 2 := by exact_mod_cast hu
      have hl' : ⌊toReal x⌋ - 2 < n := by exact_mod_cast hl
      exact ⟨hl'.le, hu'.le⟩
    · exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr
        ⟨⌊toReal x⌋, Int.floor_le _, (Int.lt_floor_add_one _).le⟩
    · exact fun n => isClosed_Icc.preimage continuous_toReal
    · intro n
      refine ((continuous_const_smul (Multiplicative.ofAdd n)).comp
        (γ.continuous_extend.comp
          (continuous_toReal.sub (continuous_const (y := (n : ℝ)))))).continuousOn.congr ?_
      intro x hx
      change Multiplicative.ofAdd ⌊toReal x⌋ • γ.extend (Int.fract (toReal x)) =
        Multiplicative.ofAdd n • γ.extend (toReal x - n)
      rcases eq_or_lt_of_le hx.2 with h | h
      · rw [h, Int.floor_add_one, Int.floor_intCast, Int.fract_add_one, Int.fract_intCast,
          add_sub_cancel_left, Path.extend_zero, Path.extend_one, ofAdd_add, mul_smul]
      · rw [← Int.self_sub_floor, Int.floor_eq_iff.mpr ⟨hx.1, h⟩]
  map_smul' g x := by
    change Multiplicative.ofAdd ⌊toReal (g • x)⌋ • γ.extend (Int.fract (toReal (g • x))) =
      g • (Multiplicative.ofAdd ⌊toReal x⌋ • γ.extend (Int.fract (toReal x)))
    rw [toReal_smul, Int.floor_add_intCast, Int.fract_add_intCast, ofAdd_add, ofAdd_toAdd,
      mul_comm, mul_smul]

/-- The canonical telescope is contractible (its trivial-subgroup fixed space is). -/
instance intTelescope_contractible : ContractibleSpace (LabeledOrbitTelescope.Model (Multiplicative ℤ)) := by
  let : ContractibleSpace (FixedPointSpace (⊥ : Subgroup (Multiplicative ℤ)) (LabeledOrbitTelescope.Model (Multiplicative ℤ))) :=
    (LabeledOrbitTelescope.fixedPointCriterion (Multiplicative ℤ)).1 ⊥ inferInstance
  exact (botFixedHomeomorph (Multiplicative ℤ) (LabeledOrbitTelescope.Model (Multiplicative ℤ))).symm.contractibleSpace

/-- A base point of the telescope. -/
def intTelescopeBasePoint : LabeledOrbitTelescope.Model (Multiplicative ℤ) := Classical.arbitrary _

/-- A path in the telescope from the base point to its translate by the generator. -/
def intTelescopePath : Path intTelescopeBasePoint
    (Multiplicative.ofAdd (1 : ℤ) • intTelescopeBasePoint) :=
  PathConnectedSpace.somePath _ _

/-- The line maps to the telescope by wrapping `intTelescopePath`. -/
def intLineToTelescope : EquivariantMap (Multiplicative ℤ) IntLine (LabeledOrbitTelescope.Model (Multiplicative ℤ)) :=
  intLineMap intTelescopePath

/-- The telescope maps to the line by its cellular mapping property and the
fixed-point criterion of the line. -/
def telescopeToIntLine : EquivariantMap (Multiplicative ℤ) (LabeledOrbitTelescope.Model (Multiplicative ℤ)) IntLine :=
  Classical.choice ((LabeledOrbitTelescope.equivariantCWComplex (Multiplicative ℤ)).homotopyTerminal
    intLine_fixedPointCriterion).1

/-- A (chosen) equivariant homotopy equivalence between the canonical telescope and the line.
Telescope → ℝ from the telescope's CW mapping property and `intLine_fixedPointCriterion`;
ℝ → telescope from a path between a free vertex and its translate; ℝ ∘ telescope ∘ ℝ ≃ id by the
straight-line homotopy; the other composite by `homotopyTerminal_unique`. No CW structure on ℝ. -/
def intLineHomotopyEquiv :
    EquivariantHomotopyEquiv (Multiplicative ℤ) (LabeledOrbitTelescope.Model (Multiplicative ℤ)) IntLine where
  toMap := telescopeToIntLine
  invMap := intLineToTelescope
  left_inv := ((LabeledOrbitTelescope.equivariantCWComplex (Multiplicative ℤ)).homotopyTerminal
    (LabeledOrbitTelescope.fixedPointCriterion (Multiplicative ℤ))).2 _ _
  right_inv := intLine_equivariantlyHomotopic _ _

/-! ## The topological side and the assembly formula -/

/-- The topological colimit on the line is full equivariant KK of `C₀(ℝ)`
(`cocompactSpaceGroupEquiv`: the orbit space is compact although the line is not). -/
def intLineSpaceGroupEquiv (p : Bool) :
    TopologicalKHomology.group (Γ := Multiplicative ℤ) (X := IntLine) p ≃+
      TopologicalKHomology.spaceGroup p (Multiplicative ℤ) IntLine :=
  Chapter8Examples.cocompactSpaceGroupEquiv (Multiplicative ℤ) IntLine p

/-- A cutoff function on the line exists (proved upstream from cocompactness). -/
def intLineCutoff : Cutoff.CutoffFunction (Multiplicative ℤ) IntLine :=
  Classical.choice (Cutoff.exists_cutoffFunction (Γ := Multiplicative ℤ) (X := IntLine))

/-- The topological side of ℤ is full equivariant KK of `C₀(ℝ)`. -/
def topologicalLineEquiv (p : Bool) :
    TopologicalKHomology.topologicalGroup p (Multiplicative ℤ) ≃+ TopologicalKHomology.spaceGroup p (Multiplicative ℤ) IntLine :=
  letI : ProperSMul (Multiplicative ℤ) (LabeledOrbitTelescope.Model (Multiplicative ℤ)) := LabeledOrbitTelescope.proper (Multiplicative ℤ)
  (TopologicalKHomology.homotopyEquiv p intLineHomotopyEquiv).trans (intLineSpaceGroupEquiv p)

/-- Canonical assembly for the integers is the cutoff/descent formula on `C₀(ℝ)` (the analogue of
`reducedAssemblyHom_finitePoint_formula`), for any cutoff function on the line. -/
theorem reducedAssemblyHom_line_formula_anyCutoff (p : Bool)
    (c : Cutoff.CutoffFunction (Multiplicative ℤ) IntLine)
    (x : TopologicalKHomology.topologicalGroup p (Multiplicative ℤ)) :
    Assembly.reducedAssemblyHom (Multiplicative ℤ) p x =
      Assembly.spaceAssemblyHom (Multiplicative ℤ) IntLine p c (topologicalLineEquiv p x) := by
  let : ProperSMul (Multiplicative ℤ) (LabeledOrbitTelescope.Model (Multiplicative ℤ)) :=
    LabeledOrbitTelescope.proper (Multiplicative ℤ)
  exact (Assembly.assemblyHom_homotopyEquiv (Multiplicative ℤ)
    (LabeledOrbitTelescope.Model (Multiplicative ℤ)) IntLine p intLineHomotopyEquiv x).symm.trans
    (Chapter8Examples.assemblyHom_eq_cocompactSpaceAssembly (Multiplicative ℤ) IntLine p c
      (TopologicalKHomology.homotopyEquiv p intLineHomotopyEquiv x))

/-- Canonical assembly for the integers is the cutoff/descent formula on `C₀(ℝ)`, with the
chosen cutoff `intLineCutoff`. -/
theorem reducedAssemblyHom_line_formula (p : Bool)
    (x : TopologicalKHomology.topologicalGroup p (Multiplicative ℤ)) :
    Assembly.reducedAssemblyHom (Multiplicative ℤ) p x =
      Assembly.spaceAssemblyHom (Multiplicative ℤ) IntLine p intLineCutoff (topologicalLineEquiv p x) :=
  reducedAssemblyHom_line_formula_anyCutoff p intLineCutoff x

/-- The same formula with the cutoff product and the descended class written out, in both
degrees. Averaging over the cutoff is not replaced by a unit. -/
theorem reducedAssemblyHom_line_descentFormula (p : Bool)
    (x : TopologicalKHomology.topologicalGroup p (Multiplicative ℤ)) :
    Assembly.reducedAssemblyHom (Multiplicative ℤ) p x =
      Assembly.reducedScalarKKToAnalyticHom (Multiplicative ℤ) p
        (Assembly.cutoffProductHom (Multiplicative ℤ) IntLine p intLineCutoff
          (KasparovDescent.classHom
            (CStarAlgebraAction.trivial : CStarAlgebraAction (Multiplicative ℤ) ℂ)
            (CZero.action (Multiplicative ℤ) (X := IntLine)) p
            (topologicalLineEquiv p x))) := by
  rw [reducedAssemblyHom_line_formula]
  rfl

end BC4lean.Chapter8Examples.IntegerLine
