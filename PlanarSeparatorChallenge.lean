module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Challenge: planar separators and nested dissection

This file is the statement a mathematical reader should audit. Plane graphs are Mathlib simple
graphs with a plane rotation system (connected, with Euler's formula). Since faces are cycles of
darts, the one-vertex graph has no faces and is not plane in this sense, so every statement about
plane graphs below is about connected graphs with at least one edge. The theorems of Lipton,
Rose and Tarjan hold for all planar graphs; the disconnected case is not formalized here. It
states:

* `PlanarSeparator.separator_theorem`, `PlanarSeparator.separator_theorem_induced`: the planar
  separator theorem with constant `6`, for the whole graph and for every set of vertices;
* `PlanarSeparator.sepTree_exists`, `PlanarSeparator.square_sepTree_exists`: separator trees with
  separators and boundaries of `O(√k)` vertices at every subtree with `k` vertices, for plane
  graphs and for squares of plane graphs of bounded degree;
* `PlanarSeparator.fill_bound`: the filled graph of nested dissection along such a tree has
  `O(n log n)` edges;
* `PlanarSeparator.planar_nested_dissection`, `PlanarSeparator.square_nested_dissection`: for
  these graphs, elimination in the nested dissection order restricted to the filled graph computes
  the in-place elimination `NestedDissection.stage` of every matrix with that pattern, with
  `O(n ^ (3/2))` arithmetic operations counted in the monad `WordRAM.Algebraic.Counted`; `stage`
  is Gaussian elimination without pivoting when its pivots are nonzero, and uses the totalized
  inverse `0⁻¹ = 0` otherwise (a step at a zero pivot leaves the matrix unchanged);
* `PlanarSeparator.separator_machine`: one word program for the word RAM `WordRAM` (no real
  instruction, `WordRAM.Program.IsWord`, so every run uses only natural words, all at most the
  bound `W`) prints a separator of at most `6 √n + 3` vertices of a plane graph with `n` vertices
  and `m` darts, with both parts of weight at most `2/3`, in at most `320 m + 191 n + 403` steps.

The separator theorem and its linear-time algorithm are from

  R. J. Lipton, R. E. Tarjan, *A separator theorem for planar graphs*, SIAM J. Appl. Math. 36
  (1979), 177-189;

and separator trees, the fill bound and the operation count of nested dissection from

  R. J. Lipton, D. J. Rose, R. E. Tarjan, *Generalized nested dissection*, SIAM J. Numer. Anal.
  16 (1979), 346-358,

which generalizes nested dissection of the grid in

  A. George, *Nested dissection of a regular finite element mesh*, SIAM J. Numer. Anal. 10
  (1973), 345-363.

The explicit constants are those of this formalization. The case of squares of plane graphs of
bounded degree is derived here from the separator theorem: to separate a vertex set in the
square, separate its closed neighbourhood in the graph and add to the separator the vertices of
the set adjacent to it.

The authoritative sources of every definition below are the specification modules
`WordRAM/Spec.lean`, `WordRAM/AlgebraicSpec.lean`, `Kasteleyn/Spec.lean` (section `Map`),
`NestedDissection/Spec.lean` and `PlanarSeparator/Spec.lean`, which the proofs import. This file
is their self-contained copy, followed by the eight targets with `sorry`. The comparator checks
that every constant used by the eight statements is the same kernel constant (type and value) in
the solution's environment.
-/
@[expose] public section

namespace WordRAM

/-- The input of a run: a list of words and a random tape. -/
structure Input where
  /-- The input words. -/
  data : List ℕ
  /-- The random tape. -/
  tape : ℕ → ℕ

/-- The instruction set. `r`, `a`, `b` name registers; `k` is a literal natural; `z` a literal
integer; `l` a literal instruction address. -/
inductive Instr : Type
  /-- Stop; the run has succeeded. -/
  | halt
  /-- `nreg r := n`, the number of input words. -/
  | inputSize (r : ℕ)
  /-- `nreg r := k`. -/
  | constN (r k : ℕ)
  /-- `nreg r := nreg a`. -/
  | copyN (r a : ℕ)
  /-- `nreg r := nreg a + nreg b`. -/
  | addN (r a b : ℕ)
  /-- `nreg r := nreg a - nreg b` (truncated at zero). -/
  | subN (r a b : ℕ)
  /-- `nreg r := nreg a * nreg b`. -/
  | mulN (r a b : ℕ)
  /-- `nreg r := nreg a / nreg b` (`0` if `nreg b = 0`). -/
  | divN (r a b : ℕ)
  /-- `nreg r := nreg a % nreg b` (`nreg a` if `nreg b = 0`). -/
  | modN (r a b : ℕ)
  /-- `nreg r := nmem (nreg a)`. -/
  | loadN (r a : ℕ)
  /-- `nmem (nreg a) := nreg r`. -/
  | storeN (a r : ℕ)
  /-- `rreg r := z`. -/
  | constR (r : ℕ) (z : ℤ)
  /-- `rreg r := rreg a`. -/
  | copyR (r a : ℕ)
  /-- `rreg r := rreg a + rreg b`. -/
  | addR (r a b : ℕ)
  /-- `rreg r := rreg a - rreg b`. -/
  | subR (r a b : ℕ)
  /-- `rreg r := rreg a * rreg b`. -/
  | mulR (r a b : ℕ)
  /-- `rreg r := rreg a / rreg b`; faults if `rreg b = 0`. -/
  | divR (r a b : ℕ)
  /-- `rreg r := rmem (nreg a)`. -/
  | loadR (r a : ℕ)
  /-- `rmem (nreg a) := rreg r`. -/
  | storeR (a r : ℕ)
  /-- `nreg r :=` input word number `nreg a` (`0` past the end). -/
  | readIn (r a : ℕ)
  /-- `nreg r :=` word number `nreg a` of the random tape. -/
  | rand (r a : ℕ)
  /-- `pc := l`. -/
  | jump (l : ℕ)
  /-- If `nreg a < nreg b` then `pc := l` else continue. -/
  | brLtN (a b l : ℕ)
  /-- If `rreg a < rreg b` then `pc := l` else continue. -/
  | brLtR (a b l : ℕ)
  /-- Append `nreg a` to the output. -/
  | outN (a : ℕ)

/-- A program is a finite list of instructions; instruction addresses are list positions. -/
abbrev Program : Type := List Instr

/-- A real instruction: one that reads or writes a real register or a real memory cell, or
compares two real registers. -/
def Instr.isReal : Instr → Bool
  | .constR .. | .copyR .. | .addR .. | .subR .. | .mulR .. | .divR .. | .loadR .. | .storeR ..
  | .brLtR .. => true
  | _ => false

/-- A word program: it contains no real instruction, so its runs touch only the natural
registers and natural memory. -/
def Program.IsWord (prog : Program) : Prop := ∀ i ∈ prog, i.isReal = false

/-- A machine configuration. -/
structure Config where
  /-- The program counter. -/
  pc : ℕ
  /-- Natural registers. -/
  nreg : ℕ → ℕ
  /-- Real registers. -/
  rreg : ℕ → ℝ
  /-- Natural memory. -/
  nmem : ℕ → ℕ
  /-- Real memory. -/
  rmem : ℕ → ℝ
  /-- The words output so far, in order. -/
  output : List ℕ

/-- The initial configuration: program counter `0`, all registers and memory cells zero,
nothing output. -/
def initConfig : Config :=
  { pc := 0, nreg := fun _ => 0, rreg := fun _ => 0, nmem := fun _ => 0, rmem := fun _ => 0,
    output := [] }

/-- Update one entry of a register file or memory. -/
def upd {α : Type} (f : ℕ → α) (i : ℕ) (v : α) : ℕ → α :=
  fun j => if j = i then v else f j

/-- Execute one instruction of `prog` on input `P` from configuration `c`. Returns `none` on a
fault (program counter out of range, or real division by zero) or when the current instruction
is `halt`; otherwise the next configuration. -/
noncomputable def step (prog : Program) (P : Input) (c : Config) : Option Config :=
  match prog[c.pc]? with
  | none => none
  | some ins =>
    match ins with
    | .halt => none
    | .inputSize r => some { c with pc := c.pc + 1, nreg := upd c.nreg r P.data.length }
    | .constN r k => some { c with pc := c.pc + 1, nreg := upd c.nreg r k }
    | .copyN r a => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a) }
    | .addN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a + c.nreg b) }
    | .subN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a - c.nreg b) }
    | .mulN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a * c.nreg b) }
    | .divN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a / c.nreg b) }
    | .modN r a b => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nreg a % c.nreg b) }
    | .loadN r a => some { c with pc := c.pc + 1, nreg := upd c.nreg r (c.nmem (c.nreg a)) }
    | .storeN a r => some { c with pc := c.pc + 1, nmem := upd c.nmem (c.nreg a) (c.nreg r) }
    | .constR r z => some { c with pc := c.pc + 1, rreg := upd c.rreg r (z : ℝ) }
    | .copyR r a => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a) }
    | .addR r a b => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a + c.rreg b) }
    | .subR r a b => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a - c.rreg b) }
    | .mulR r a b => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a * c.rreg b) }
    | .divR r a b =>
        if c.rreg b = 0 then none
        else some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rreg a / c.rreg b) }
    | .loadR r a => some { c with pc := c.pc + 1, rreg := upd c.rreg r (c.rmem (c.nreg a)) }
    | .storeR a r => some { c with pc := c.pc + 1, rmem := upd c.rmem (c.nreg a) (c.rreg r) }
    | .readIn r a => some { c with pc := c.pc + 1, nreg := upd c.nreg r (P.data.getD (c.nreg a) 0) }
    | .rand r a => some { c with pc := c.pc + 1, nreg := upd c.nreg r (P.tape (c.nreg a)) }
    | .jump l => some { c with pc := l }
    | .brLtN a b l => some { c with pc := if c.nreg a < c.nreg b then l else c.pc + 1 }
    | .brLtR a b l => some { c with pc := if c.rreg a < c.rreg b then l else c.pc + 1 }
    | .outN a => some { c with pc := c.pc + 1, output := c.output ++ [c.nreg a] }

/-- Run `k` instructions, faulting if any step faults. -/
noncomputable def run (prog : Program) (P : Input) : ℕ → Config → Option Config
  | 0, c => some c
  | k + 1, c => (step prog P c).bind (run prog P k)

/-- The configuration is at a `halt` instruction. -/
def AtHalt (prog : Program) (c : Config) : Prop := prog[c.pc]? = some Instr.halt

/-- Every natural register and every natural memory cell of `c` is at most `W`. -/
def WordsBounded (W : ℕ) (c : Config) : Prop :=
  (∀ r, c.nreg r ≤ W) ∧ (∀ a, c.nmem a ≤ W)

/-- `prog`, started on input `P` in the initial configuration, executes exactly `k`
instructions without faulting and then sits at `halt`, every configuration along the way
(including the final one) has its natural words bounded by `W`, and the output at the end is
`out`. The run is charged `k + 1` steps: one for each executed instruction and one for the final
`halt`. -/
def RunsWithin (prog : Program) (P : Input) (W : ℕ) (steps : ℕ) (out : List ℕ) : Prop :=
  ∃ k : ℕ, k + 1 ≤ steps ∧
    (∀ i, i ≤ k → ∃ c, run prog P i initConfig = some c ∧ WordsBounded W c) ∧
    ∃ c, run prog P k initConfig = some c ∧ AtHalt prog c ∧ c.output = out

end WordRAM

end

@[expose] public section

namespace WordRAM.Algebraic

/-! ### Operation counts -/

/-- A count of arithmetic operations: `adds` counts additions, subtractions and negations,
`muls` counts multiplications. -/
structure OpCount where
  /-- Number of additive operations (additions, subtractions, negations). -/
  adds : ℕ
  /-- Number of multiplications. -/
  muls : ℕ

namespace OpCount

instance : Zero OpCount := ⟨⟨0, 0⟩⟩

instance : Add OpCount := ⟨fun a b => ⟨a.adds + b.adds, a.muls + b.muls⟩⟩

instance : AddCommMonoid OpCount where
  add_assoc a b c :=
    congrArg₂ OpCount.mk (Nat.add_assoc a.adds b.adds c.adds) (Nat.add_assoc a.muls b.muls c.muls)
  zero_add a := congrArg₂ OpCount.mk (Nat.zero_add a.adds) (Nat.zero_add a.muls)
  add_zero a := congrArg₂ OpCount.mk (Nat.add_zero a.adds) (Nat.add_zero a.muls)
  add_comm a b := congrArg₂ OpCount.mk (Nat.add_comm a.adds b.adds) (Nat.add_comm a.muls b.muls)
  nsmul := nsmulRec

/-- Total number of arithmetic operations. -/
def total (c : OpCount) : ℕ := c.adds + c.muls

/-- One additive operation. -/
abbrev oneAdd : OpCount := ⟨1, 0⟩

/-- One multiplication. -/
abbrev oneMul : OpCount := ⟨0, 1⟩

end OpCount

/-! ### The counting monad -/

universe u v

/-- A computation in the arithmetic cost model: a result `val` together with the number of
ring operations `cost` performed to obtain it (the writer monad over `OpCount`). -/
structure Counted (α : Type u) where
  /-- The computed value. -/
  val : α
  /-- The number of operations spent. -/
  cost : OpCount

namespace Counted

instance : Monad Counted where
  pure a := ⟨a, 0⟩
  bind x f := ⟨(f x.val).val, x.cost + (f x.val).cost⟩

/-- Run a family of independent counted computations indexed by a finite type: the value is
the family of values, the cost is the sum of the costs. -/
def pi {ι : Type v} [Fintype ι] {α : ι → Type u} (f : (i : ι) → Counted (α i)) :
    Counted ((i : ι) → α i) :=
  ⟨fun i => (f i).val, ∑ i, (f i).cost⟩

end Counted

/-! ### Primitive ring operations -/

namespace Op

variable {R : Type u}

/-- Addition, charged one additive operation. -/
def add [Add R] (a b : R) : Counted R := ⟨a + b, OpCount.oneAdd⟩

/-- Subtraction, charged one additive operation. -/
def sub [Sub R] (a b : R) : Counted R := ⟨a - b, OpCount.oneAdd⟩

/-- Negation, charged one additive operation. -/
def neg [Neg R] (a : R) : Counted R := ⟨-a, OpCount.oneAdd⟩

/-- Multiplication, charged one multiplication. -/
def mul [Mul R] (a b : R) : Counted R := ⟨a * b, OpCount.oneMul⟩

end Op

/-! ### Entrywise matrix operations -/

/-- Square matrices of size `n` over `R`. -/
abbrev SqMat (n : ℕ) (R : Type u) : Type u := Matrix (Fin n) (Fin n) R

namespace Mat

variable {R : Type u} {m : Type v} {n : Type v} [Fintype m] [Fintype n]

/-- Entrywise matrix addition, one additive operation per entry. -/
def add [Add R] (A B : Matrix m n R) : Counted (Matrix m n R) :=
  Counted.pi fun i => Counted.pi fun j => Op.add (A i j) (B i j)

/-- Entrywise matrix subtraction, one additive operation per entry. -/
def sub [Sub R] (A B : Matrix m n R) : Counted (Matrix m n R) :=
  Counted.pi fun i => Counted.pi fun j => Op.sub (A i j) (B i j)

end Mat

end WordRAM.Algebraic

end

@[expose] public section

namespace Kasteleyn

open Finset SimpleGraph

/-! ### Rotation systems and faces -/

section Map

variable {V : Type*} {G : SimpleGraph V}

/-- A rotation system on a simple graph `G`: a permutation `rot` of the darts of `G` which,
for every vertex `v`, permutes the darts leaving `v` in a single cycle. -/
structure RotationSystem (G : SimpleGraph V) where
  /-- The successor of a dart in the cyclic order of the darts leaving its initial vertex. -/
  rot : Equiv.Perm G.Dart
  fst_rot : ∀ d, (rot d).fst = d.fst
  sameCycle_of_fst_eq : ∀ d d' : G.Dart, d.fst = d'.fst → rot.SameCycle d d'

/-- The reversal of darts as a permutation. -/
def dartRev (G : SimpleGraph V) : Equiv.Perm G.Dart :=
  Function.Involutive.toPerm _ Dart.symm_involutive

namespace RotationSystem

variable (M : RotationSystem G)

/-- The face permutation: the boundary walk of a face continues a dart `d` by the successor of
`d.symm` in the rotation at the head of `d`. -/
def faceNext : Equiv.Perm G.Dart := (dartRev G).trans M.rot

/-- The faces: the cycles of the face permutation. -/
def Face : Type _ := Quotient (Equiv.Perm.SameCycle.setoid M.faceNext)

/-- The face of a dart: the face whose boundary walk traverses the dart. -/
def face (d : G.Dart) : M.Face := Quotient.mk _ d

section Fintype

variable [Fintype V] [DecidableRel G.Adj]

variable [DecidableEq V]

instance : DecidableEq M.Face :=
  @Quotient.decidableEq _ _ (Equiv.Perm.instDecidableRelSameCycle M.faceNext)

instance : Fintype M.Face :=
  @Quotient.fintype _ _ _ (Equiv.Perm.instDecidableRelSameCycle M.faceNext)

/-- A rotation system is *plane* (of genus zero) if the graph is connected and Euler's formula
`|V| + |F| = |E| + 2` holds, `F` the set of faces.

Faces are the cycles of the face permutation on the darts, so a graph without edges has no
faces here. A connected graph without edges is a single vertex; it is not plane in this sense
(`1 + 0 ≠ 0 + 2`), so statements assuming `IsPlane` leave it out. -/
structure IsPlane : Prop where
  connected : G.Connected
  euler : Fintype.card V + Fintype.card M.Face = #G.edgeFinset + 2

end Fintype

end RotationSystem

end Map

end Kasteleyn

end

@[expose] public section

namespace NestedDissection

universe u v w

/-! ### Separator trees -/

/-- A separator tree: a leaf holding a vertex set, or a node holding a separator and two
subtrees for the two parts. -/
inductive SepTree (V : Type u) : Type u
  | leaf (s : Finset V) : SepTree V
  | node (s : Finset V) (a b : SepTree V) : SepTree V

section Bdry

variable {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The boundary of `W`: the vertices outside `W` adjacent to a vertex of `W`. -/
def bdry (W : Finset V) : Finset V := {y | y ∉ W ∧ ∃ x ∈ W, G.Adj x y}

end Bdry

namespace SepTree

variable {V : Type u}

/-- The vertices numbered at the root of a subtree: the separator of a node, the whole set of a
leaf. -/
def own : SepTree V → Finset V
  | leaf s => s
  | node s _ _ => s

/-- `P` holds at every node of the tree. -/
def AllNodes (P : SepTree V → Prop) : SepTree V → Prop
  | leaf s => P (leaf s)
  | node s a b => P (node s a b) ∧ AllNodes P a ∧ AllNodes P b

variable [DecidableEq V]

/-- All vertices of a subtree. -/
def verts : SepTree V → Finset V
  | leaf s => s
  | node s a b => s ∪ a.verts ∪ b.verts

/-- `t` is a separator tree of `G`: at every node the separator and the two parts are pairwise
disjoint and no edge of `G` joins the two parts. -/
def IsDissection (G : SimpleGraph V) : SepTree V → Prop
  | leaf _ => True
  | node s a b => Disjoint s a.verts ∧ Disjoint s b.verts ∧ Disjoint a.verts b.verts ∧
      (∀ x ∈ a.verts, ∀ y ∈ b.verts, ¬ G.Adj x y) ∧ IsDissection G a ∧ IsDissection G b

/-- The parts of the root have at most two thirds of its vertices. -/
def Shrinks : SepTree V → Prop
  | leaf _ => True
  | node s a b => 3 * a.verts.card ≤ 2 * (node s a b).verts.card ∧
      3 * b.verts.card ≤ 2 * (node s a b).verts.card

/-- The separator bound `|own t| ≤ α √k` and the boundary bound `|bdry t| ≤ β √k` at the root
of `t`, where `k` is the number of vertices of `t`. -/
def SqrtBound [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (α β : ℝ) (t : SepTree V) :
    Prop :=
  (t.own.card : ℝ) ≤ α * √(t.verts.card) ∧ ((bdry G t.verts).card : ℝ) ≤ β * √(t.verts.card)

section Order

variable [LinearOrder V]

/-- The nested dissection order: recursively the first part, the second part, then the
separator (each separator and leaf set in increasing order of `V`). -/
def order : SepTree V → List V
  | leaf s => s.sort (· ≤ ·)
  | node s a b => order a ++ order b ++ s.sort (· ≤ ·)

end Order

end SepTree

/-! ### The filled graph -/

section Fill

variable {V : Type u} (G : SimpleGraph V) (r : V → ℕ)

/-- `LowWalk G r k u w`: there is a walk of positive length from `u` to `w` in `G` all of whose
interior vertices have rank `< k`. -/
inductive LowWalk (k : ℕ) : V → V → Prop
  | adj {u w : V} : G.Adj u w → LowWalk k u w
  | cons {u x w : V} : G.Adj u x → r x < k → LowWalk k x w → LowWalk k u w

namespace LowWalk

variable {G r} {k : ℕ} {u w : V}

theorem trans {x : V} (h₁ : LowWalk G r k u x) (hx : r x < k) (h₂ : LowWalk G r k x w) :
    LowWalk G r k u w := by
  induction h₁ with
  | adj h => exact .cons h hx h₂
  | cons h hy _ ih => exact .cons h hy (ih hx h₂)

theorem symm (h : LowWalk G r k u w) : LowWalk G r k w u := by
  induction h with
  | adj h => exact .adj h.symm
  | cons h hx _ ih => exact ih.trans hx (.adj h.symm)

end LowWalk

/-- The **filled graph** of `G` for the elimination order given by `r`: `u ≠ w` are adjacent
iff there is a walk from `u` to `w` whose interior vertices all have rank smaller than both
`r u` and `r w`. -/
def fill : SimpleGraph V where
  Adj u w := u ≠ w ∧ LowWalk G r (min (r u) (r w)) u w
  symm := ⟨fun u w h => ⟨h.1.symm, by rw [min_comm]; exact h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {G r}

variable (r) in
/-- The neighbours of `v` in `H` that come later in the order `r`. -/
def laterNbrs [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) : Finset V :=
  {w | H.Adj v w ∧ r v < r w}

end Fill

/-! ### Elimination -/

section Elimination

open WordRAM.Algebraic Matrix

variable {K : Type u}

/-- Inversion, charged one multiplicative operation (the cost model `OpCount` records additive
and multiplicative operations; a division or inversion is counted with the latter). -/
def opInv [Inv K] (a : K) : Counted K := ⟨a⁻¹, OpCount.oneMul⟩

/-- The leading principal `k × k` submatrix. -/
def leading {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (hk : k ≤ n) :
    Matrix (Fin k) (Fin k) K :=
  A.submatrix (Fin.castLE hk) (Fin.castLE hk)

variable [Field K]

/-- The in-place elimination step with pivot `k`: `M i j - M i k * (M k k)⁻¹ * M k j` for
`i, j > k`. The inverse is the field's, with `0⁻¹ = 0`, so at a zero pivot the step leaves `M`
unchanged. -/
def elimStep {n : ℕ} (k : Fin n) (M : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if k < i ∧ k < j then M i j - M i k * (M k k)⁻¹ * M k j else M i j

/-- `stage A k`: the matrix after the elimination steps with pivots `0, …, k - 1`; Gaussian
elimination without pivoting when these pivots are nonzero. -/
def stage {n : ℕ} (A : Matrix (Fin n) (Fin n) K) : ℕ → Matrix (Fin n) (Fin n) K
  | 0 => A
  | k + 1 => if h : k < n then elimStep ⟨k, h⟩ (stage A k) else stage A k

variable {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]

/-- The elimination step with pivot `k` restricted to the positions `(i, j)` with `i` and `j`
later neighbours of `k` in `H`, in the counting monad: one inversion, one multiplication for
each multiplier, one multiplication and one subtraction for each updated entry. -/
def sparseStepCounted (k : Fin n) (M : Matrix (Fin n) (Fin n) K) :
    Counted (Matrix (Fin n) (Fin n) K) := do
  let p ← opInv (M k k)
  let l ← Counted.pi fun i : Fin n =>
    if i ∈ laterNbrs Fin.val H k then Op.mul (M i k) p else pure 0
  let S ← Counted.pi fun i : Fin n => Counted.pi fun j : Fin n =>
    if i ∈ laterNbrs Fin.val H k ∧ j ∈ laterNbrs Fin.val H k then do
      let t ← Op.mul (l i) (M k j)
      Op.sub (M i j) t
    else pure (M i j)
  pure (Matrix.of S)

/-- Restricted elimination in the counting monad: the first `k` steps. -/
def sparseCounted (A : Matrix (Fin n) (Fin n) K) : ℕ → Counted (Matrix (Fin n) (Fin n) K)
  | 0 => pure A
  | k + 1 => do
    let M ← sparseCounted A k
    if h : k < n then sparseStepCounted H ⟨k, h⟩ M else pure M

end Elimination

end NestedDissection

/-! ### Squares of graphs -/

namespace PlanarSeparator

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- The square of a graph: distinct vertices at distance at most `2` are adjacent. -/
def square : SimpleGraph V where
  Adj i j := i ≠ j ∧ (G.Adj i j ∨ ∃ k, G.Adj i k ∧ G.Adj k j)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.elim (fun h => Or.inl h.symm)
    fun ⟨k, h1, h2⟩ => Or.inr ⟨k, h2.symm, h1.symm⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel (square G).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

end PlanarSeparator

end

@[expose] public section

namespace PlanarSeparator

open Finset

section Separation

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- `S` separates the vertex set `U` into the parts `A` and `B`: the three sets are disjoint with
union `U`, and no edge joins `A` to `B`. -/
structure IsSeparation (G : SimpleGraph V) (U S A B : Finset V) : Prop where
  union_eq : S ∪ A ∪ B = U
  disjoint_sep_left : Disjoint S A
  disjoint_sep_right : Disjoint S B
  disjoint : Disjoint A B
  not_adj : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b

end Separation

/-! ### The targets -/

open NestedDissection NestedDissection.SepTree

universe u

/-- **The planar separator theorem** (Lipton and Tarjan 1979), weighted form. Let `R` be a plane
rotation system of a graph `G` with `n` vertices, and let `w` be nonnegative weights on the
vertices with total at most `1`. Then a set `S` of at most `6 √n` vertices separates the graph
into two parts `A` and `B`, with no edge between them, each of weight at most `2/3`.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def SeparatorTheorem : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G), R.IsPlane → ∀ w : V → ℝ, (∀ v, 0 ≤ w v) → ∑ v, w v ≤ 1 →
    ∃ S A B, IsSeparation G univ S A B ∧ (#S : ℝ) ≤ 6 * √(Fintype.card V : ℝ) ∧
      ∑ v ∈ A, w v ≤ 2 / 3 ∧ ∑ v ∈ B, w v ≤ 2 / 3

/-- **The planar separator theorem for induced subgraphs.** Let `R` be a plane rotation system of
a graph `G`, let `U` be a set of `k` vertices and let `w` be nonnegative weights with total weight
on `U` at most `1`. Then `U` is separated by a set `S` of at most `6 √k` of its vertices into two
parts `A` and `B`, with no edge of `G` between them, each of weight at most `2/3`.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def SeparatorTheoremInduced : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G), R.IsPlane → ∀ (U : Finset V) (w : V → ℝ),
    (∀ v, 0 ≤ w v) → ∑ v ∈ U, w v ≤ 1 →
    ∃ S A B, IsSeparation G U S A B ∧ (#S : ℝ) ≤ 6 * √(#U : ℝ) ∧
      ∑ v ∈ A, w v ≤ 2 / 3 ∧ ∑ v ∈ B, w v ≤ 2 / 3

/-- **Separator trees of plane graphs with boundary bounds** (Lipton, Rose and Tarjan 1979). Every
plane graph has a separator tree on all its vertices in which every subtree with `k` vertices has
a separator (at a leaf: a leaf set) of at most `50000 √k` vertices and a boundary of at most
`50000 √k` vertices, and in which the two parts of every node have at most `2k/3` vertices.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def SepTreeExists : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G), R.IsPlane →
    ∃ t : SepTree V, t.verts = univ ∧ IsDissection G t ∧
      AllNodes (SqrtBound G 50000 50000) t ∧ AllNodes Shrinks t

/-- **Separator trees of squares of plane graphs of bounded degree.** If `G` is plane with
maximum degree at most `Δ`, its square has a separator tree as in `SepTreeExists`, with the
constant `T = 40 (1062 (Δ + 1)² + 1)` in place of `50000`.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def SquareSepTreeExists : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G), R.IsPlane → ∀ Δ : ℕ, (∀ v, G.degree v ≤ Δ) →
    ∃ t : SepTree V, t.verts = univ ∧ IsDissection (square G) t ∧
      AllNodes (SqrtBound (square G) (40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1))
        (40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1))) t ∧ AllNodes Shrinks t

/-- **The fill of nested dissection is `O(n log n)`** (Lipton, Rose and Tarjan 1979). Let `t` be
a separator tree of a graph `G` on `Fin n` covering all vertices, with separators of at most
`α √k` and boundaries of at most `β √k` vertices at every subtree with `k` vertices, and parts of
at most `2k/3` vertices. If the vertices are eliminated in the nested dissection order of `t`
(rank of `x` = position of `x` in `t.order`), the filled graph has at most
`α (α + β) n (1 + log_{3/2} n)` edges. -/
def FillBound : Prop :=
  ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {α β : ℝ}, 0 ≤ α → 0 ≤ β →
    ∀ t : SepTree (Fin n), IsDissection G t → t.verts = univ →
      AllNodes (SqrtBound G α β) t → AllNodes Shrinks t →
      ∀ [DecidableRel (fill G fun x => t.order.idxOf x).Adj],
        ((fill G fun x => t.order.idxOf x).edgeFinset.card : ℝ) ≤
          α * (α + β) * (n * (1 + Real.logb (3 / 2) n))

/-- **Nested dissection of plane graphs** (George 1973; Lipton, Rose and Tarjan 1979). For every
plane graph `G` on `Fin n` there is a separator tree `t` of `G`, with nested dissection order
`σ` (`σ k` is the `k`-th vertex of `t.order`), such that
* the filled graph of the nested dissection order has at most
  `T (T + T) n (1 + log_{3/2} n)` edges, `T = 50000`;
* for every matrix `A` over a field whose off-diagonal nonzero entries are edges of `G`,
  elimination of `A.submatrix σ σ` restricted to the filled graph `H` computes exactly
  `stage (A.submatrix σ σ) n`, the matrix after all `n` in-place elimination steps (Gaussian
  elimination without pivoting when its pivots are nonzero; a step at a zero pivot, totalized by
  `0⁻¹ = 0`, leaves the matrix unchanged), with at most `12 T (T + T)² n √n` operations.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def PlanarNestedDissection : Prop :=
  ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R : Kasteleyn.RotationSystem G),
    R.IsPlane →
    ∃ (t : SepTree (Fin n)) (σ : Equiv.Perm (Fin n)), t.verts = univ ∧ IsDissection G t ∧
      (∀ k : Fin n, t.order[k.val]? = some (σ k)) ∧
      (∀ [DecidableRel (fill G fun x => t.order.idxOf x).Adj],
        ((fill G fun x => t.order.idxOf x).edgeFinset.card : ℝ) ≤
          50000 * (50000 + 50000) * (n * (1 + Real.logb (3 / 2) n))) ∧
      ∀ (K : Type u) [Field K] (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
        H = fill (G.comap σ) Fin.val →
        ∀ A : Matrix (Fin n) (Fin n) K, (∀ i j, i ≠ j → A i j ≠ 0 → G.Adj i j) →
          (sparseCounted H (A.submatrix σ σ) n).val = stage (A.submatrix σ σ) n ∧
            ((sparseCounted H (A.submatrix σ σ) n).cost.total : ℝ) ≤
              12 * 50000 * (50000 + 50000) ^ 2 * (n * √n)

/-- **Nested dissection for squares of plane graphs of bounded degree.** As
`PlanarNestedDissection`, for the square of a plane graph `G` of maximum degree at most `Δ` (the
matrices whose off-diagonal nonzero entries join vertices at distance at most `2` in `G`, such
as `Kᵀ K` for a matrix `K` with pattern `G`), with `T = 40 (1062 (Δ + 1)² + 1)`.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def SquareNestedDissection : Prop :=
  ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (R : Kasteleyn.RotationSystem G),
    R.IsPlane → ∀ Δ : ℕ, (∀ v, G.degree v ≤ Δ) →
    ∃ (t : SepTree (Fin n)) (σ : Equiv.Perm (Fin n)), t.verts = univ ∧
      IsDissection (square G) t ∧ (∀ k : Fin n, t.order[k.val]? = some (σ k)) ∧
      (∀ [DecidableRel (fill (square G) fun x => t.order.idxOf x).Adj],
        ((fill (square G) fun x => t.order.idxOf x).edgeFinset.card : ℝ) ≤
          40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1) *
            (40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1) + 40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1)) *
            (n * (1 + Real.logb (3 / 2) n))) ∧
      ∀ (K : Type u) [Field K] (H : SimpleGraph (Fin n)) [DecidableRel H.Adj],
        H = fill ((square G).comap σ) Fin.val →
        ∀ A : Matrix (Fin n) (Fin n) K, (∀ i j, i ≠ j → A i j ≠ 0 → (square G).Adj i j) →
          (sparseCounted H (A.submatrix σ σ) n).val = stage (A.submatrix σ σ) n ∧
            ((sparseCounted H (A.submatrix σ σ) n).cost.total : ℝ) ≤
              12 * (40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1)) *
                (40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1) + 40 * (1062 * ((Δ : ℝ) + 1) ^ 2 + 1)) ^ 2 *
                (n * √n)

/-- The input of the separator program for a rotation system `R` of a graph on `Fin n` with
vertex weights `w` and a numbering `di` of its `m` darts: the words `n, m`, then
`ofs 0, …, ofs n` where `ofs v` is the number of darts leaving the vertices below `v`, then
`w 0, …, w (n-1)`, then for each dart number `i` the initial vertex of the dart, the number of its
reversal and the number of its successor in the rotation at its initial vertex. -/
def sepInput {n m : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G) (w : Fin n → ℕ) (di : G.Dart ≃ Fin m) : WordRAM.Input :=
  ⟨[n, m] ++ (List.range (n + 1)).map (fun v => #{d : G.Dart | (d.fst : ℕ) < v}) ++
      (List.finRange n).map w ++
      (List.finRange m).flatMap (fun i =>
        [((di.symm i).fst : ℕ), (di (di.symm i).symm : ℕ), (di (R.rot (di.symm i)) : ℕ)]),
    fun _ => 0⟩

/-- **The planar separator theorem on the machine in linear time.** One fixed word program for the
machine `WordRAM` (no real instruction, `WordRAM.Program.IsWord`), run on the input
`sepInput R w di` of a plane rotation system `R` of a graph on `Fin n` with `m` darts, vertex
weights `w` and a numbering `di` of the darts in which the darts leaving lower vertices come
first, with words of at least `16 m + 12 n + 3 Σ w + 22`, halts within `320 m + 191 n + 403` steps
and prints a list of words; reading word `v` of the list for each vertex `v` (`0` if the list is
shorter), the vertices read as `0` form a set `S` of at most `6 √n + 3` vertices separating those
read as `1` from those read as `2`, and each of these two parts weighs at most `2/3` of the
total.

As `IsPlane` requires, `G` is connected and has at least one edge. -/
def SeparatorMachine : Prop :=
  ∃ prog : WordRAM.Program, WordRAM.Program.IsWord prog ∧
    ∀ {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (R : Kasteleyn.RotationSystem G), R.IsPlane → ∀ (w : Fin n → ℕ) (di : G.Dart ≃ Fin m),
    (∀ d d' : G.Dart, d.fst < d'.fst → di d < di d') → ∀ W : ℕ,
    16 * m + 12 * n + 3 * ∑ v, w v + 22 ≤ W →
    ∃ out : List ℕ, WordRAM.RunsWithin prog (sepInput R w di) W (320 * m + 191 * n + 403) out ∧
      IsSeparation G univ {v : Fin n | out.getD v 0 = 0} {v : Fin n | out.getD v 0 = 1}
        {v : Fin n | out.getD v 0 = 2} ∧
      (#{v : Fin n | out.getD v 0 = 0} : ℝ) ≤ 6 * √(n : ℝ) + 3 ∧
      3 * ∑ v ∈ univ.filter (fun v : Fin n => out.getD v 0 = 1), w v ≤ 2 * ∑ v, w v ∧
      3 * ∑ v ∈ univ.filter (fun v : Fin n => out.getD v 0 = 2), w v ≤ 2 * ∑ v, w v

end PlanarSeparator

end

/-! ## The targets -/

public section

namespace PlanarSeparator

universe u

/-- **The planar separator theorem.** -/
theorem separator_theorem : SeparatorTheorem.{u} := by
  sorry

/-- **The planar separator theorem for induced subgraphs.** -/
theorem separator_theorem_induced : SeparatorTheoremInduced.{u} := by
  sorry

/-- **Separator trees of plane graphs.** -/
theorem sepTree_exists : SepTreeExists.{u} := by
  sorry

/-- **Separator trees of squares of plane graphs of bounded degree.** -/
theorem square_sepTree_exists : SquareSepTreeExists.{u} := by
  sorry

/-- **The fill of nested dissection.** -/
theorem fill_bound : FillBound := by
  sorry

/-- **Nested dissection of plane graphs.** -/
theorem planar_nested_dissection : PlanarNestedDissection.{u} := by
  sorry

/-- **Nested dissection for squares of plane graphs of bounded degree.** -/
theorem square_nested_dissection : SquareNestedDissection.{u} := by
  sorry

/-- **The planar separator theorem on the machine in linear time.** -/
theorem separator_machine : SeparatorMachine := by
  sorry

end PlanarSeparator

end
