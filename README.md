# The planar separator theorem and nested dissection on a word RAM, in Lean 4

A Lean 4 and Mathlib formalization of the planar separator theorem, separator trees and nested
dissection (fill and operation bounds), with a linear-time separator program on an explicit word
RAM. All proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`.

Author and maintainer: Robert D. Barish ([rbarish@ims.u-tokyo.ac.jp](mailto:rbarish@ims.u-tokyo.ac.jp)).

## Submission

| Challenge | Solution | Comparator configuration | Metadata | Theorems |
|---|---|---|---|---|
| `PlanarSeparatorChallenge.lean` | `PlanarSeparatorSolution.lean` | `comparator.json` | `formalization.yaml` | 8 |

The Challenge module is the statement to audit: it is self-contained, imports only Mathlib and ends
with the compared theorems proved by `sorry`. The Solution module imports the libraries of this
repository, never the Challenge. The configuration permits exactly the axioms `propext`,
`Quot.sound` and `Classical.choice`, compares no definitions separately (`definition_names` is
empty) and enables nanoda. The definitions in the Challenge are copies of the specification modules
`WordRAM/Spec.lean`, `WordRAM/AlgebraicSpec.lean`, `Kasteleyn/Spec.lean`,
`NestedDissection/Spec.lean`, `PlanarSeparator/Spec.lean` (the declarations the statements use); the
comparator checks that every constant used by the compared statements is the same kernel constant in
the Solution's environment.

## Statement

### Common definitions

**The machine (`WordRAM`).** A program is a finite list of instructions, addressed by list position.
A configuration has a program counter, natural registers and natural memory cells (`ℕ → ℕ`), real
registers and real memory cells (`ℕ → ℝ`), and an output list. The instructions are: `halt`; reading
the number of input words and the input word at a register address (`0` past the end); natural
constants, copy, `+`, truncated `-`, `*`, `/` (`0` on division by zero) and `%` (`a % 0 = a`);
natural load and store at a register address; the same for reals with real division (division by
zero is a fault); reading a word of the random tape; jumps; branches on `<` for naturals and for
reals; and appending a natural register to the output. Every instruction costs one step.
`WordRAM.RunsWithin prog P W T out` says: started on input `P` from the all-zero configuration,
`prog` executes some number `k` of instructions without fault and then stands at a `halt`
instruction, `k + 1 ≤ T` (the final `halt` is charged one step), every configuration along the run
(the last one included) has all natural registers and all natural memory cells at most `W`, and the
output at the end is `out`. Real registers are not bounded, so a program using them is not a
word-RAM program: `Instr.isReal` marks the instructions that read, write or compare reals, and
`Program.IsWord prog` says that `prog` contains none of them. The statements below require it of
every program. All inputs in the statements below have the random tape constantly `0`.

**The arithmetic model (`WordRAM.Algebraic`).** `Counted α` is the writer monad over
`OpCount = (adds, muls)`: a value together with the number of additive operations (additions,
subtractions, negations) and of multiplications performed through the charged primitives `Op.add`,
`Op.sub`, `Op.neg`, `Op.mul` (and `NestedDissection.opInv`, an inversion charged as one
multiplication). `cost.total = adds + muls`. Moving, copying, padding and reindexing data costs
nothing. The algorithms whose costs are stated are defined explicitly in the Challenges, and their
definitions are part of the statements.

**Plane graphs as rotation systems (`Kasteleyn.RotationSystem`).** For a Mathlib simple graph `G`
(no loops, no multiple edges), a rotation system is a permutation `rot` of the darts of `G` that
keeps the initial vertex and permutes the darts leaving each vertex in a single cycle. The face
permutation sends a dart `d` to `rot (d.symm)`; the faces are its cycles, and the face of a dart is
the cycle containing it. The rotation system is *plane* (`IsPlane`) if `G` is connected and
`|V| + |F| = |E| + 2` (Euler's formula, `F` the set of faces). That such rotation systems are
exactly the combinatorial types of plane embeddings is classical and not formalized. Since faces are
cycles of darts, the one-vertex graph has no faces and is not plane in this sense: every statement
assuming `IsPlane` is about a connected graph with at least one edge.

### Planar separators and nested dissection (`PlanarSeparatorChallenge.lean`)

The statements about plane graphs assume `IsPlane`, so they are about connected graphs with at least
one edge. The theorems of Lipton, Rose and Tarjan hold for all planar graphs; the disconnected case,
which follows by joining the components with extra edges (a separation of the larger graph is one of
the original), is not formalized.

The separator theorem and its linear-time algorithm are from Lipton and Tarjan (1979); separator
trees, the fill bound and the operation count of nested dissection are from Lipton, Rose and Tarjan
(1979), generalizing George's nested dissection of the grid (1973). The explicit constants are those
of this formalization, and the case of squares of plane graphs of bounded degree is derived here
from the separator theorem (separate the closed neighbourhood of a vertex set in the graph and add
to the separator the vertices of the set adjacent to it).

Definitions: `IsSeparation G U S A B`: `S`, `A`, `B` are pairwise disjoint with union `U` and no
edge joins `A` to `B`. A separator tree (`SepTree`) is a leaf holding a vertex set or a node holding
a separator and two subtrees; `IsDissection G t`: at every node the separator and the vertex sets of
the two subtrees are pairwise disjoint and no edge joins the two subtrees; `Shrinks`: each subtree
of a node has at most two thirds of the node's vertices; `SqrtBound G α β t`: the root separator
(the whole set at a leaf) has at most `α √k` vertices and the boundary of the vertex set (outside
neighbours) at most `β √k`, `k` the number of vertices of `t`; `AllNodes P t`: `P` at every subtree.
`t.order` is the nested dissection order: first part, second part, then the separator (each set in
increasing order). `fill G r` is the filled graph of the elimination order `r`: `u ≠ w` are adjacent
iff some walk of positive length from `u` to `w` has all interior vertices of rank below both `r u`
and `r w`. `stage A k` is the matrix after the in-place elimination steps
`M i j ↦ M i j - M i k (M k k)⁻¹ M k j` (`i, j > k`) with pivots `0, …, k - 1`, where `⁻¹` is the
field's inverse, totalized by `0⁻¹ = 0`: when the pivots met are nonzero this is Gaussian
elimination without pivoting, and a step at a zero pivot leaves the matrix unchanged (ordinary
elimination without pivoting would be undefined there); `sparseCounted H A k` is the same
elimination in the counting monad restricted to positions `(i, j)` with `i`, `j` later neighbours of
the pivot in `H` (one inversion per pivot, one multiplication per multiplier, one multiplication and
one subtraction per updated entry). `square G` joins distinct vertices at distance at most 2.

* `PlanarSeparator.separator_theorem`: for every plane rotation system of `G` on `n` vertices and
  weights `w ≥ 0` with `Σ w ≤ 1`, there are `S, A, B` with `IsSeparation G V S A B`, `|S| ≤ 6 √n`,
  `w(A) ≤ 2/3` and `w(B) ≤ 2/3`.
* `PlanarSeparator.separator_theorem_induced`: the same for every vertex set `U` with `w ≥ 0` and
  `w(U) ≤ 1`: `IsSeparation G U S A B`, `|S| ≤ 6 √|U|`, `w(A), w(B) ≤ 2/3`.
* `PlanarSeparator.sepTree_exists`: every plane graph has a separator tree `t` with `t.verts = V`,
  `IsDissection G t`, `AllNodes (SqrtBound G 50000 50000) t` and `AllNodes Shrinks t`.
* `PlanarSeparator.square_sepTree_exists`: if moreover every degree is at most `Δ`, the same holds
  for `square G` with `T = 40 (1062 (Δ + 1)² + 1)` in place of `50000`.
* `PlanarSeparator.fill_bound`: for any graph `G` on `Fin n`, `α, β ≥ 0` and any separator tree `t`
  with `IsDissection G t`, `t.verts = univ`, `AllNodes (SqrtBound G α β) t` and
  `AllNodes Shrinks t`, the filled graph for the rank `x ↦ position of x in t.order` has at most
  `α (α + β) n (1 + log_{3/2} n)` edges.
* `PlanarSeparator.planar_nested_dissection`: for every plane graph `G` on `Fin n` there are a
  separator tree `t` (covering all vertices, `IsDissection G t`) and a permutation `σ` listing
  `t.order` (`t.order[k] = σ k`) such that the filled graph of `t.order` has at most
  `T (T + T) n (1 + log_{3/2} n) = 2T² n (1 + log_{3/2} n)` edges, `T = 50000`, and for every field
  `K`, with `H = fill (G.comap σ) (Fin.val)` and every matrix `A` over `K` whose off-diagonal
  nonzero entries are edges of `G`, `sparseCounted H (A.submatrix σ σ) n` returns exactly
  `stage (A.submatrix σ σ) n` (in the totalized sense above, for every such matrix) with at most
  `12 T (T + T)² n √n = 48 T³ n √n` operations.
* `PlanarSeparator.square_nested_dissection`: the same for `square G` of a plane graph `G` of
  maximum degree at most `Δ`, with `T = 40 (1062 (Δ + 1)² + 1)`.
* `PlanarSeparator.separator_machine`: there is one word program such that for every plane rotation
  system `R` of a graph on `Fin n` with `m` darts, natural vertex weights `w`, every numbering `di`
  of the darts in which darts leaving lower vertices have lower numbers, and every
  `W ≥ 16m + 12n + 3 Σ w + 22`, the program run on `sepInput R w di` halts within
  `320m + 191n + 403` steps with natural words at most `W` and prints a list `out` of words such
  that, reading `out.getD v 0` for each vertex `v`, the vertices read as `0`, `1`, `2` form a
  separation `S, A, B` of all vertices with `|S| ≤ 6 √n + 3`, `3 w(A) ≤ 2 w(V)` and
  `3 w(B) ≤ 2 w(V)`. The input is `n, m`, then `ofs 0, …, ofs n` (`ofs v` = number of darts leaving
  vertices below `v`), then `w 0, …, w (n-1)`, then for each dart number its initial vertex, the
  number of its reverse and the number of its successor in the rotation.

## Libraries

Each library root module (`WordRAM.lean`, …) imports the modules of the library present here. The
libraries contain exactly the modules needed by the Solution (60 modules).

| Library | Modules | Content |
|---|---|---|
| `WordRAM` | 13 | the machine, structured programs and their compilation, the counted-operation model |
| `Kasteleyn` | 3 | rotation systems and faces |
| `NestedDissection` | 9 | separator trees, fill, sparse elimination |
| `PlanarSeparator` | 35 | the planar separator theorem, separator trees, the separator program |

`Audit.lean` prints the axioms of the 8 compared theorems and of 39 further theorems of the
libraries.

## Checking

Toolchain `leanprover/lean4:v4.35.0-rc2`; Mathlib as pinned in `lakefile.toml` and
`lake-manifest.json`.

```bash
lake exe cache get && lake build
lake env lean Audit.lean    # every report names only propext, Classical.choice, Quot.sound
lake comparator --config comparator.json --paranoid
```

`lake comparator` needs `bwrap` and the toolchain's `bin` directory on `PATH`.

## License

Apache-2.0 (`LICENSE`).
