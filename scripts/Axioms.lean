/-
Prints the axioms used by the main theorems of LocallyConvex.LieGroups.
Run with `lake env lean scripts/Axioms.lean`; every line should read
`[propext, Classical.choice, Quot.sound]` (the standard axioms of Lean and Mathlib).
-/
import LocallyConvexLieGroups

open LocallyConvex.LieGroups

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
