module

import PlanarSeparatorSolution
import WordRAM
import Kasteleyn
import NestedDissection
import PlanarSeparator

/-!
# Axiom audit

Prints the axioms of the 8 compared theorems (stated in `PlanarSeparatorChallenge.lean`, proved by
`PlanarSeparatorSolution.lean`) and of 39 further theorems of the libraries. Every report must name only
`propext`, `Classical.choice` and `Quot.sound`. Run it with

    lake build && lake env lean Audit.lean
-/

-- The compared theorems
#print axioms PlanarSeparator.separator_theorem
#print axioms PlanarSeparator.separator_theorem_induced
#print axioms PlanarSeparator.sepTree_exists
#print axioms PlanarSeparator.square_sepTree_exists
#print axioms PlanarSeparator.fill_bound
#print axioms PlanarSeparator.planar_nested_dissection
#print axioms PlanarSeparator.square_nested_dissection
#print axioms PlanarSeparator.separator_machine

-- Further theorems of the libraries
#print axioms PlanarSeparator.planar_separator
#print axioms PlanarSeparator.planar_separator_induce
#print axioms PlanarSeparator.planar_separator_card
#print axioms PlanarSeparator.exists_sepTree
#print axioms PlanarSeparator.exists_sepTree_square
#print axioms PlanarSeparator.planar_nestedDissection_elimination
#print axioms PlanarSeparator.square_nestedDissection_elimination
#print axioms NestedDissection.card_edgeFinset_fill_le
#print axioms NestedDissection.nestedDissection_elimination
#print axioms NestedDissection.nestedDissection_det
#print axioms NestedDissection.fill_adj_iff_path
#print axioms PlanarSeparator.SepProg.sepProg_sepOut
#print axioms NestedDissection.det_eq_prod_pivots
#print axioms PlanarSeparator.CycleSearch.cycleSep_exec
#print axioms WordRAM.Machine.Exec.mono_W
#print axioms WordRAM.Machine.Exec.embed
#print axioms WordRAM.Machine.Exec.lift
#print axioms WordRAM.Machine.Exec.lift_trunc
#print axioms WordRAM.Machine.Stmt.exec_realsToNat
#print axioms WordRAM.Machine.Stmt.runsWithin_realsToNat
#print axioms WordRAM.Machine.Stmt.compile_realsToNat_noReal
#print axioms WordRAM.Program.isWord_of_all
#print axioms WordRAM.Machine.Stmt.compile_wordOnly
#print axioms WordRAM.Machine.Stmt.isWord_compile_halt
#print axioms WordRAM.Machine.Exec.det
#print axioms WordRAM.Machine.Exec.toExecI_linLoopFree
#print axioms WordRAM.Machine.Exec.toExecI_whileLtR
#print axioms WordRAM.Machine.Exec.toExecI_stepInv
#print axioms WordRAM.Machine.Exec.toExecI_arithFree
#print axioms WordRAM.Machine.Exec.toExecI_whileLtN
#print axioms WordRAM.Machine.ModNat.ExecCmp.toNat
#print axioms WordRAM.Machine.ModNat.ExecCmp.toNat_consts
#print axioms WordRAM.Machine.ModNat.CmpOK.toNat
#print axioms WordRAM.Machine.ModNat.CmpOK.whileLtN
#print axioms WordRAM.Machine.ModNat.CmpOK.whileLtR
#print axioms WordRAM.Machine.ModNat.res_cmp
#print axioms WordRAM.Machine.Exec.hoist
#print axioms WordRAM.Machine.FixIter.exit
#print axioms WordRAM.Machine.Exec.liftSame
