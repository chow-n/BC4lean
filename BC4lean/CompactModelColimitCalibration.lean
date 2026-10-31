import BC4lean.AssemblyModelNaturality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! The topological colimit on a cocompact ambient model.
Only the orbit space is assumed compact. The whole space is then itself a closed
cocompact piece, the terminal all-space piece supplies an explicit inverse, and the
colimit assembly is the ambient cutoff/descent formula. A compact ambient space is the
special case recorded at the end. No assembly bijectivity is assumed. -/

noncomputable section
universe uI uV uΓ uX
namespace BC4lean.Chapter8Examples
open ProperActions KKTheory
open scoped ZeroAtInfty ComplexOrder KasparovDescent

section TerminalDiagram
variable {I : Type uI} [Preorder I] [Nonempty I] [IsDirectedOrder I]
  (D : DirectedAddGroupDiagram.{uI, uV} I) (t : I) (ht : ∀ i, i ≤ t)

/-- Evaluation at an actual greatest indexing object. -/
def terminalEvaluation : D.Colimit →+ D.obj t :=
  D.desc (fun i => D.map i t (ht i)) (by
    intro i j hij x
    exact D.map_comp i j t hij (ht j) x)

@[simp] theorem terminalEvaluation_of (i : I) (x : D.obj i) :
    terminalEvaluation D t ht (D.of i x) = D.map i t (ht i) x := rfl

/-- An actual terminal object computes the constructed additive colimit. -/
def terminalColimitEquiv : D.Colimit ≃+ D.obj t where
  toFun := terminalEvaluation D t ht
  invFun := D.of t
  map_add' := (terminalEvaluation D t ht).map_add
  left_inv z := by
    obtain ⟨i, x, rfl⟩ := D.exists_of z
    exact D.of_map (ht i) x
  right_inv x := by
    change D.map t t (ht t) x = x
    exact D.map_id t x

@[simp] theorem terminalColimitEquiv_of (i : I) (x : D.obj i) :
    terminalColimitEquiv D t ht (D.of i x) = D.map i t (ht i) x := rfl

end TerminalDiagram

section CocompactSpace
variable (Γ : Type uΓ) [Group Γ] (X : Type uX)
  [TopologicalSpace X] [MulAction Γ X] [CompactSpace (Quotient (MulAction.orbitRel Γ X))]

/-- With a compact orbit space, the whole ambient space is a closed cocompact piece. -/
def wholeCocompactPiece : CocompactPiece Γ X where
  carrier := Set.univ
  smul_mem _ _ _ := Set.mem_univ _
  isClosed_carrier := isClosed_univ
  isCompact_image := by
    rw [Set.image_univ_of_surjective Quotient.mk_surjective]
    exact isCompact_univ

theorem le_wholeCocompactPiece (S : CocompactPiece Γ X) :
    S ≤ wholeCocompactPiece Γ X := fun _ _ => Set.mem_univ _

/-- The all-space subtype is homeomorphic to the ambient space. -/
def wholeCocompactHomeomorph : (wholeCocompactPiece Γ X).toInvariantSubset ≃ₜ X where
  toFun := Subtype.val
  invFun x := ⟨x, Set.mem_univ x⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := continuous_id.subtype_mk _

def wholeCocompactInclusion :
    EquivariantMap Γ (wholeCocompactPiece Γ X).toInvariantSubset X :=
  (wholeCocompactPiece Γ X).toInvariantSubset.inclusion

def wholeCocompactLift :
    EquivariantMap Γ X (wholeCocompactPiece Γ X).toInvariantSubset where
  toFun x := ⟨x, Set.mem_univ x⟩
  continuous_toFun := continuous_id.subtype_mk _
  map_smul' _ _ := rfl

theorem wholeCocompactInclusion_proper : IsProperMap (wholeCocompactInclusion Γ X) :=
  (wholeCocompactHomeomorph Γ X).isProperMap

theorem wholeCocompactLift_proper : IsProperMap (wholeCocompactLift Γ X) :=
  (wholeCocompactHomeomorph Γ X).symm.isProperMap

@[simp] theorem wholeCocompactLift_comp_inclusion :
    (wholeCocompactLift Γ X).comp (wholeCocompactInclusion Γ X) = EquivariantMap.id := by
  apply EquivariantMap.ext
  intro x
  apply Subtype.ext
  rfl

@[simp] theorem wholeCocompactInclusion_comp_lift :
    (wholeCocompactInclusion Γ X).comp (wholeCocompactLift Γ X) = EquivariantMap.id := by
  apply EquivariantMap.ext
  intro x
  rfl

variable [Countable Γ] [ContinuousConstSMul Γ X]
  [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]

local instance wholeCocompactPiece_locallyCompact :
    LocallyCompactSpace (wholeCocompactPiece Γ X).toInvariantSubset :=
  (wholeCocompactPiece Γ X).locallyCompact

/-- The topological colimit collapses to its all-space piece group. -/
def cocompactWholePieceEquiv (p : Bool) :
    TopologicalKHomology.group (Γ := Γ) (X := X) p ≃+
      TopologicalKHomology.pieceGroup p (wholeCocompactPiece Γ X) :=
  terminalColimitEquiv (TopologicalKHomology.diagram (Γ := Γ) (X := X) p)
    (wholeCocompactPiece Γ X) (le_wholeCocompactPiece Γ X)

@[simp] theorem cocompactWholePieceEquiv_ofPiece (p : Bool)
    (S : CocompactPiece Γ X) (x : TopologicalKHomology.pieceGroup p S) :
    cocompactWholePieceEquiv Γ X p (TopologicalKHomology.ofPiece p S x) =
      TopologicalKHomology.transition p (le_wholeCocompactPiece Γ X S) x := rfl

/-- The all-space piece and the ambient space give the same full KK group. -/
def wholeCocompactSpaceGroupEquiv (p : Bool) :
    TopologicalKHomology.pieceGroup p (wholeCocompactPiece Γ X) ≃+
      TopologicalKHomology.spaceGroup p Γ X where
  toFun := TopologicalKHomology.properPushforward p (wholeCocompactInclusion Γ X)
    (wholeCocompactInclusion_proper Γ X)
  invFun := TopologicalKHomology.properPushforward p (wholeCocompactLift Γ X)
    (wholeCocompactLift_proper Γ X)
  map_add' := (TopologicalKHomology.properPushforward p (wholeCocompactInclusion Γ X)
    (wholeCocompactInclusion_proper Γ X)).map_add
  left_inv x := by
    have h := DFunLike.congr_fun
      (TopologicalKHomology.properPushforward_comp p
        (wholeCocompactLift Γ X) (wholeCocompactInclusion Γ X)
        (wholeCocompactLift_proper Γ X) (wholeCocompactInclusion_proper Γ X)) x
    simpa only [AddMonoidHom.comp_apply, wholeCocompactLift_comp_inclusion,
      TopologicalKHomology.properPushforward_id, AddMonoidHom.id_apply] using h
  right_inv x := by
    have h := DFunLike.congr_fun
      (TopologicalKHomology.properPushforward_comp p
        (wholeCocompactInclusion Γ X) (wholeCocompactLift Γ X)
        (wholeCocompactInclusion_proper Γ X) (wholeCocompactLift_proper Γ X)) x
    simpa only [AddMonoidHom.comp_apply, wholeCocompactInclusion_comp_lift,
      TopologicalKHomology.properPushforward_id, AddMonoidHom.id_apply] using h

/-- On a cocompact ambient model, the colimit equals the full ambient KK group. -/
def cocompactSpaceGroupEquiv (p : Bool) :
    TopologicalKHomology.group (Γ := Γ) (X := X) p ≃+
      TopologicalKHomology.spaceGroup p Γ X :=
  (cocompactWholePieceEquiv Γ X p).trans (wholeCocompactSpaceGroupEquiv Γ X p)

variable [TopologicalSpace Γ] [DiscreteTopology Γ] [ProperSMul Γ X]

/-- Assembly on the colimit evaluates on the all-space piece. -/
theorem assemblyHom_eq_wholeCocompactPiece (p : Bool)
    (x : TopologicalKHomology.group (Γ := Γ) (X := X) p) :
    Assembly.assemblyHom Γ X p x =
      Assembly.pieceAssemblyHom Γ X p (wholeCocompactPiece Γ X)
        (cocompactWholePieceEquiv Γ X p x) := by
  obtain ⟨S, y, rfl⟩ :=
    (TopologicalKHomology.diagram (Γ := Γ) (X := X) p).exists_of x
  change TopologicalKHomology.pieceGroup p S at y
  change Assembly.assemblyHom Γ X p (TopologicalKHomology.ofPiece p S y) =
    Assembly.pieceAssemblyHom Γ X p (wholeCocompactPiece Γ X)
      (cocompactWholePieceEquiv Γ X p (TopologicalKHomology.ofPiece p S y))
  rw [Assembly.assemblyHom_ofPiece, cocompactWholePieceEquiv_ofPiece]
  exact (Assembly.pieceAssemblyHom_transition Γ X p
    (le_wholeCocompactPiece Γ X S) y).symm

/-- Colimit assembly agrees with the ambient-space cutoff/descent formula, for any
cutoff (the formula is independent of the cutoff). -/
theorem assemblyHom_eq_cocompactSpaceAssembly (p : Bool)
    (c : Cutoff.CutoffFunction Γ X)
    (x : TopologicalKHomology.group (Γ := Γ) (X := X) p) :
    Assembly.assemblyHom Γ X p x =
      Assembly.spaceAssemblyHom Γ X p c (cocompactSpaceGroupEquiv Γ X p x) := by
  rw [assemblyHom_eq_wholeCocompactPiece]
  exact (Assembly.spaceAssemblyHom_properPushforward Γ
    (wholeCocompactPiece Γ X).toInvariantSubset X p
    (wholeCocompactInclusion Γ X) (wholeCocompactInclusion_proper Γ X)
    c (Assembly.pieceCutoff Γ X (wholeCocompactPiece Γ X))
    (cocompactWholePieceEquiv Γ X p x)).symm

end CocompactSpace

section CompactSpace
variable (Γ : Type uΓ) [Group Γ] (X : Type uX)
  [TopologicalSpace X] [MulAction Γ X] [CompactSpace X]

/-! A compact ambient space has a compact orbit space (`Quotient.compactSpace`), so the
compact case is the cocompact one. -/

/-- The whole compact ambient space is an actual closed cocompact piece. -/
def wholeCompactPiece : CocompactPiece Γ X := wholeCocompactPiece Γ X

theorem le_wholeCompactPiece (S : CocompactPiece Γ X) :
    S ≤ wholeCompactPiece Γ X := le_wholeCocompactPiece Γ X S

/-- The intrinsic all-space subtype really is homeomorphic to the ambient space. -/
def wholeCompactHomeomorph : (wholeCompactPiece Γ X).toInvariantSubset ≃ₜ X :=
  wholeCocompactHomeomorph Γ X

def wholeCompactInclusion :
    EquivariantMap Γ (wholeCompactPiece Γ X).toInvariantSubset X :=
  wholeCocompactInclusion Γ X

def wholeCompactLift :
    EquivariantMap Γ X (wholeCompactPiece Γ X).toInvariantSubset :=
  wholeCocompactLift Γ X

theorem wholeCompactInclusion_proper : IsProperMap (wholeCompactInclusion Γ X) :=
  wholeCocompactInclusion_proper Γ X

theorem wholeCompactLift_proper : IsProperMap (wholeCompactLift Γ X) :=
  wholeCocompactLift_proper Γ X

@[simp] theorem wholeCompactLift_comp_inclusion :
    (wholeCompactLift Γ X).comp (wholeCompactInclusion Γ X) = EquivariantMap.id :=
  wholeCocompactLift_comp_inclusion Γ X

@[simp] theorem wholeCompactInclusion_comp_lift :
    (wholeCompactInclusion Γ X).comp (wholeCompactLift Γ X) = EquivariantMap.id :=
  wholeCocompactInclusion_comp_lift Γ X

variable [Countable Γ] [ContinuousConstSMul Γ X]
  [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]

local instance wholeCompactPiece_locallyCompact :
    LocallyCompactSpace (wholeCompactPiece Γ X).toInvariantSubset :=
  (wholeCompactPiece Γ X).locallyCompact

/-- The actual topological colimit collapses to its all-space piece group. -/
def compactWholePieceEquiv (p : Bool) :
    TopologicalKHomology.group (Γ := Γ) (X := X) p ≃+
      TopologicalKHomology.pieceGroup p (wholeCompactPiece Γ X) :=
  cocompactWholePieceEquiv Γ X p

@[simp] theorem compactWholePieceEquiv_ofPiece (p : Bool)
    (S : CocompactPiece Γ X) (x : TopologicalKHomology.pieceGroup p S) :
    compactWholePieceEquiv Γ X p (TopologicalKHomology.ofPiece p S x) =
      TopologicalKHomology.transition p (le_wholeCompactPiece Γ X S) x := rfl

/-- The all-space piece and ambient space give the same actual full KK group. -/
def wholeCompactSpaceGroupEquiv (p : Bool) :
    TopologicalKHomology.pieceGroup p (wholeCompactPiece Γ X) ≃+
      TopologicalKHomology.spaceGroup p Γ X :=
  wholeCocompactSpaceGroupEquiv Γ X p

/-- On a compact ambient model, the real colimit equals the full ambient KK group. -/
def compactSpaceGroupEquiv (p : Bool) :
    TopologicalKHomology.group (Γ := Γ) (X := X) p ≃+
      TopologicalKHomology.spaceGroup p Γ X :=
  cocompactSpaceGroupEquiv Γ X p

variable [TopologicalSpace Γ] [DiscreteTopology Γ] [ProperSMul Γ X]

/-- Assembly on the colimit evaluates on the actual all-space piece. -/
theorem assemblyHom_eq_wholeCompactPiece (p : Bool)
    (x : TopologicalKHomology.group (Γ := Γ) (X := X) p) :
    Assembly.assemblyHom Γ X p x =
      Assembly.pieceAssemblyHom Γ X p (wholeCompactPiece Γ X)
        (compactWholePieceEquiv Γ X p x) :=
  assemblyHom_eq_wholeCocompactPiece Γ X p x

/-- The actual colimit assembly agrees with the actual ambient-space formula.
The only supplied datum is a legitimate cutoff, whose independence is proved. -/
theorem assemblyHom_eq_compactSpaceAssembly (p : Bool)
    (c : Cutoff.CutoffFunction Γ X)
    (x : TopologicalKHomology.group (Γ := Γ) (X := X) p) :
    Assembly.assemblyHom Γ X p x =
      Assembly.spaceAssemblyHom Γ X p c (compactSpaceGroupEquiv Γ X p x) :=
  assemblyHom_eq_cocompactSpaceAssembly Γ X p c x

end CompactSpace
end BC4lean.Chapter8Examples
