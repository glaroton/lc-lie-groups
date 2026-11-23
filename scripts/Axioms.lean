/-
Prints the axioms used by the main theorems of LocallyConvex.LieGroups.
Run with `lake env lean scripts/Axioms.lean`; every line should read
`[propext, Classical.choice, Quot.sound]` (the standard axioms of Lean and Mathlib).
-/
import LocallyConvexLieGroups

open LocallyConvex.LieGroups LocallyConvex.Manifolds

-- Lie groups (`LieGroup/Basic.lean`)
#print axioms MBLieGroup.smoothMBM_mul_left
#print axioms MBLieGroup.smoothMBM_mul_right
#print axioms MBLieGroup.smoothMBM_conj
#print axioms MBLieGroup.isTopologicalGroup
#print axioms MBLieGroup.IsHom.comp
-- The group `Diff(K)` (`Diffeomorphism/Basic.lean`)
#print axioms smooth_inv
#print axioms isVaryingLieGroup_diffeos
#print axioms Diffeo.instMBLieGroup
-- Lie groups from atlases with varying models (`LieGroup/OfVaryingAtlas.lean`)
#print axioms IsVaryingLieGroup.hasGroupoid
#print axioms IsVaryingLieGroup.mbLieGroup
-- The Lie algebra (`LieAlgebra/Local.lean`, `LieAlgebra/Basic.lean`)
#print axioms LocalGroupLaw.bracket_jacobi
#print axioms LocalGroupLaw.continuous_bracket
#print axioms LocalGroupLaw.dMB_bracket_of_hom
#print axioms LocalGroupLaw.bracket_eq_zero_of_comm
#print axioms MBLieGroup.LieAlg.instLieRing
#print axioms MBLieGroup.LieAlg.instLieAlgebraReal
#print axioms MBLieGroup.LieAlg.continuous_lie
#print axioms MBLieGroup.LieAlg.lie_eq_zero_of_comm
#print axioms MBLieGroup.IsHom.lieHom
#print axioms MBLieGroup.IsHom.continuous_lieHom
#print axioms MBLieGroup.IsHom.lieHom_comp
-- The Lie algebra of `Diff(K)` (`Diffeomorphism/LieAlgebra.lean`)
#print axioms LocalGroupLaw.clm_dMB_xl
#print axioms Diffeo.law_mul_apply
#print axioms Diffeo.evalAt_dMB_xl
#print axioms Diffeo.evalAt_lie
#print axioms Diffeo.toField_lie
-- Left invariant vector fields (`LieAlgebra/LeftInvariant.lean`)
#print axioms MBLieGroup.lieBracket_leftField
#print axioms MBLieGroup.lieBracket_leftField_one
#print axioms MBLieGroup.tangentMap_leftField
-- Taylor expansions (`LieAlgebra/Taylor.lean`)
#print axioms LocalGroupLaw.dMB_dMB_mul_one
#print axioms LocalGroupLaw.bracket_eq_b2_sub_b2
#print axioms LocalGroupLaw.LocalInverse.dMB_dMB_inv_one
#print axioms LocalGroupLaw.LocalInverse.dMB_dMB_conj_one
#print axioms LocalGroupLaw.LocalInverse.dMB_dMB_commutator_one
#print axioms MBLieGroup.LieAlg.dMB_dMB_commutator
-- Unit groups of continuous inverse algebras (`LieGroup/Units.lean`)
#print axioms UnitGroup.instMBLieGroup
#print axioms quasiLaw_bracket
#print axioms UnitGroup.lie_eq
-- Vector groups and products (`LieGroup/Vector.lean`, `LieGroup/Prod.lean`)
#print axioms VectorGroup.instMBLieGroup
#print axioms VectorGroup.lie_eq_zero
#print axioms MBLieGroup.instProd
#print axioms LocalGroupLaw.bracket_prod
#print axioms MBLieGroup.LieAlg.prodEquiv
-- Open subgroups and `Diff⁺(S¹)` (`LieGroup/OpenSubgroup.lean`, `Diffeomorphism/Circle.lean`)
#print axioms OpenSubgroup.instMBLieGroup
#print axioms OpenSubgroup.lieEquiv
#print axioms MBLieGroup.identityComponent
#print axioms DiffPlusCircle.toField_lie
-- The universal cover of `Diff⁺(S¹)` (`CircleCover/Periodic.lean`, `CircleCover/Group.lean`)
#print axioms CInfPer.smoothMBOn_precomp
#print axioms CInfPer.hasDirDerivAt_precomp
#print axioms CircleCover.coverLaw_bracket
#print axioms CircleCover.contDiffMBOn_G
#print axioms CircleCover.smoothMBOn_η
#print axioms CircleCover.CoverGroup.instMBLieGroup
#print axioms CircleCover.CoverGroup.lie_eq
#print axioms CircleCover.smoothMBOn_flow
#print axioms CircleCover.isExp_exp
-- Exponential functions (`Exponential/Basic.lean`)
#print axioms MBLieGroup.IsExp.exp_neg
#print axioms MBLieGroup.IsExp.toIdentityComponent
#print axioms MBLieGroup.IsExp.prod
#print axioms VectorGroup.isExp
#print axioms UnitGroup.isExp_exp
#print axioms MBLieGroup.IsOneParam.eq
#print axioms MBLieGroup.IsExp.unique
#print axioms MBLieGroup.IsExp.map_hom
-- Morphisms of connected Lie groups (`LieAlgebra/Morphisms.lean`)
#print axioms MBLieGroup.IsHom.eventuallyEq_of_lieHom_eq
#print axioms MBLieGroup.IsHom.eq_of_lieHom_eq
-- The adjoint representation (`LieAlgebra/Adjoint.lean`)
#print axioms MBLieGroup.Ad_mul
#print axioms MBLieGroup.Ad_eq_id_iff
#print axioms UnitGroup.Ad_apply
#print axioms MBLieGroup.dMB_Ad
#print axioms MBLieGroup.comm_iff_lie_eq_zero
#print axioms MBLieGroup.smoothMBM_AdAction
-- Semidirect products (`LieGroup/Semidirect.lean`)
#print axioms SDProd.mbLieGroup
#print axioms MBLieGroup.isSmoothAction_AdMulAut
#print axioms LocalGroupLaw.bracket_semidirect
#print axioms SDProd.bracket_eq
#print axioms MBLieGroup.TangentGroup.bracket_eq
#print axioms AffineGroup.bracket_eq
-- Regular Lie groups (`Regular/`)
#print axioms MBLieGroup.eq_of_hasLogDerivAt
#print axioms MBLieGroup.IsC0Regular.isExp
#print axioms MBLieGroup.isC0Regular_of_nhds
#print axioms MBLieGroup.isC0Regular_iff
#print axioms UnitGroup.isC0Regular
#print axioms MBLieGroup.isC0Regular_of_completeSpace
#print axioms MBLieGroup.IsC0Regular.of_hom
#print axioms VectorGroup.isC0Regular
