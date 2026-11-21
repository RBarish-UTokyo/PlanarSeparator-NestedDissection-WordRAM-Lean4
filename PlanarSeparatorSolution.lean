module

public import PlanarSeparator.Main

/-!
# Solution for `PlanarSeparatorChallenge.lean`

The eight theorems of `PlanarSeparatorChallenge.lean` are the theorems of the same names in
`PlanarSeparator/Main.lean`, about the definitions of the specification modules
`PlanarSeparator/Spec.lean`, `NestedDissection/Spec.lean`, `WordRAM/Spec.lean`,
`WordRAM/AlgebraicSpec.lean` and `Kasteleyn/Spec.lean`. This module imports
the library and never imports `PlanarSeparatorChallenge`.

* `PlanarSeparator.separator_theorem : PlanarSeparator.SeparatorTheorem`
* `PlanarSeparator.separator_theorem_induced : PlanarSeparator.SeparatorTheoremInduced`
* `PlanarSeparator.sepTree_exists : PlanarSeparator.SepTreeExists`
* `PlanarSeparator.square_sepTree_exists : PlanarSeparator.SquareSepTreeExists`
* `PlanarSeparator.fill_bound : PlanarSeparator.FillBound`
* `PlanarSeparator.planar_nested_dissection : PlanarSeparator.PlanarNestedDissection`
* `PlanarSeparator.square_nested_dissection : PlanarSeparator.SquareNestedDissection`
* `PlanarSeparator.separator_machine : PlanarSeparator.SeparatorMachine`
-/
