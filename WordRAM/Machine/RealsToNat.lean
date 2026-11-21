module

public import WordRAM.Programs.Tactics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Real registers holding bounded integers: simulation on natural words only

The machine of `WordRAM/Spec.lean` has, besides its natural registers and memory (bounded by
the word bound `W` of `RunsWithin`, `WordsBounded`), exact real registers and real memory with
no bound. A program that keeps only **integers of absolute value at most `B`** in its real
registers and real memory is a genuine word-RAM program: this file proves it, by a program
transformation.

* `RealsIntBounded B c`: every real register and every real memory cell of `c` is an integer of
  absolute value at most `B`.
* `ExecI P Q s c c' k`: the big-step semantics `Exec` of `WordRAM/Machine/Structured.lean` with an
  arbitrary predicate `Q` on the visited configurations in place of `WordsBounded W`
  (`ExecI.toExec`, `Exec.toExecI`). With `Q = WordsBounded W ∧ RealsIntBounded B` it says that
  every configuration at which an instruction runs, and the final one, has its natural words at
  most `W` and its reals integers bounded by `B`.
* `Stmt.realsToNat`: the transformation. The natural register `r` becomes `4 r`, the real
  register `r` the pair `4 r + 1`, `4 r + 2` (sign and magnitude: `x = p - q` with `p = 0` or
  `q = 0`, `SignRep`), the registers `3`, `7`, `11` are scratch; the natural memory cell `a` becomes
  `3 a`, the real cell `a` the pair `3 a + 1`, `3 a + 2`. Every instruction becomes a block of at
  most `8` natural instructions (`Instr.toNatCode`), a real test `x < y` the natural test
  `p + q' < p' + q`. Real division is not translated (`Stmt.noDivR`); real multiplication is.
* `Stmt.exec_realsToNat` (**the simulation**): if `ExecI P (WordsBounded W ∧ RealsIntBounded B)
  s c c' k`, then from every encoding `d` of `c` bounded by `3 W + 2 B + 2` the transformed
  statement runs, with that word bound, to an encoding of `c'` within `8 k` steps.
* `Stmt.compile_realsToNat_noReal`: the compiled transformed program contains no real
  instruction at all (`Instr.isReal`).
* `Stmt.runsWithin_realsToNat` (**top level**): an `ExecI` run from the initial configuration
  gives `RunsWithin (compile s.realsToNat 0 ++ [halt]) P (3 W + 2 B + 2) (8 k + 1)` with the same
  output: the realization holds on a word RAM with natural words only, of size `O(W + B)`.

Tools to establish the hypothesis from an existing `Exec` run:

* `Exec.det`: the big-step semantics is deterministic.
* `Exec.toExecI_of_loopFree`: a loop-free statement without `mulR`/`divR` whose real constants
  are bounded by `B` and which starts with reals bounded by `B` keeps them bounded by
  `2 ^ codeSize s * B` (each instruction at most doubles the largest absolute value).
* `Exec.toExecI_whileLtN`, `Exec.toExecI_whileLtR`: the loop rules, with an invariant on the
  loop heads.
* `Exec.toExecI_stepInv`: a predicate kept by every instruction of a statement (`Stmt.instrs`)
  holds along every run, loops included; `Exec.toExecI_arithFree`: a statement without real
  arithmetic (`Stmt.ArithFree`, decidable) keeps any bound of its reals along every run.
-/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace WordRAM

/-- A real instruction: one that reads or writes a real register or real memory cell. -/
def Instr.isReal : Instr → Bool
  | .constR .. | .copyR .. | .addR .. | .subR .. | .mulR .. | .divR .. | .loadR .. | .storeR ..
  | .brLtR .. => true
  | _ => false

/-- Not a real division. -/
def Instr.noDivR : Instr → Bool
  | .divR .. => false
  | _ => true

namespace Machine

open Stmt Programs

/-- Every real register and every real memory cell of `c` is an integer of absolute value at
most `B`. -/
def RealsIntBounded (B : ℕ) (c : Config) : Prop :=
  (∀ r, ∃ z : ℤ, c.rreg r = z ∧ |z| ≤ (B : ℤ)) ∧ (∀ a, ∃ z : ℤ, c.rmem a = z ∧ |z| ≤ (B : ℤ))

theorem RealsIntBounded.mono {B B' : ℕ} {c : Config} (h : RealsIntBounded B c) (hB : B ≤ B') :
    RealsIntBounded B' c :=
  ⟨fun r => let ⟨z, hz, hb⟩ := h.1 r; ⟨z, hz, hb.trans (by exact_mod_cast hB)⟩,
    fun a => let ⟨z, hz, hb⟩ := h.2 a; ⟨z, hz, hb.trans (by exact_mod_cast hB)⟩⟩

theorem realsIntBounded_initConfig (B : ℕ) : RealsIntBounded B initConfig :=
  ⟨fun _ => ⟨0, by simp [initConfig], by simp⟩, fun _ => ⟨0, by simp [initConfig], by simp⟩⟩

/-! ### Executions with an invariant on the visited configurations -/

/-- `Exec` with the predicate `Q` in place of `WordsBounded W`. -/
inductive ExecI (P : Input) (Q : Config → Prop) : Stmt → Config → Config → ℕ → Prop
  | skip {c : Config} : Q c → ExecI P Q .skip c c 0
  | instr {ins : Instr} {c c' : Config} : ins.IsStraight → ins.effect P c = some c' →
      Q c → Q c' → ExecI P Q (.instr ins) c c' 1
  | seq {s t : Stmt} {c c₁ c₂ : Config} {k₁ k₂ : ℕ} :
      ExecI P Q s c c₁ k₁ → ExecI P Q t c₁ c₂ k₂ → ExecI P Q (.seq s t) c c₂ (k₁ + k₂)
  | ifLtN_true {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : c.nreg a < c.nreg b →
      ExecI P Q t c c' k → ExecI P Q (.ifLtN a b t e) c c' (k + 1)
  | ifLtN_false {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : ¬ c.nreg a < c.nreg b →
      ExecI P Q e c c' k → ExecI P Q (.ifLtN a b t e) c c' (k + 2)
  | ifLtR_true {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : c.rreg a < c.rreg b →
      ExecI P Q t c c' k → ExecI P Q (.ifLtR a b t e) c c' (k + 1)
  | ifLtR_false {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : ¬ c.rreg a < c.rreg b →
      ExecI P Q e c c' k → ExecI P Q (.ifLtR a b t e) c c' (k + 2)
  | whileLtN_false {a b : ℕ} {body : Stmt} {c : Config} : ¬ c.nreg a < c.nreg b →
      Q c → ExecI P Q (.whileLtN a b body) c c 2
  | whileLtN_true {a b : ℕ} {body : Stmt} {c c₁ c' : Config} {k₁ k₂ : ℕ} : c.nreg a < c.nreg b →
      ExecI P Q body c c₁ k₁ → ExecI P Q (.whileLtN a b body) c₁ c' k₂ →
      ExecI P Q (.whileLtN a b body) c c' (k₁ + 2 + k₂)
  | whileLtR_false {a b : ℕ} {body : Stmt} {c : Config} : ¬ c.rreg a < c.rreg b →
      Q c → ExecI P Q (.whileLtR a b body) c c 2
  | whileLtR_true {a b : ℕ} {body : Stmt} {c c₁ c' : Config} {k₁ k₂ : ℕ} : c.rreg a < c.rreg b →
      ExecI P Q body c c₁ k₁ → ExecI P Q (.whileLtR a b body) c₁ c' k₂ →
      ExecI P Q (.whileLtR a b body) c c' (k₁ + 2 + k₂)

namespace ExecI

variable {P : Input} {Q Q' : Config → Prop}

theorem q_left {s : Stmt} {c c' : Config} {k : ℕ} (h : ExecI P Q s c c' k) : Q c := by
  induction h with
  | skip hq => exact hq
  | instr _ _ hq _ => exact hq
  | seq _ _ ih _ => exact ih
  | ifLtN_true _ _ ih => exact ih
  | ifLtN_false _ _ ih => exact ih
  | ifLtR_true _ _ ih => exact ih
  | ifLtR_false _ _ ih => exact ih
  | whileLtN_false _ hq => exact hq
  | whileLtN_true _ _ _ ih _ => exact ih
  | whileLtR_false _ hq => exact hq
  | whileLtR_true _ _ _ ih _ => exact ih

theorem q_right {s : Stmt} {c c' : Config} {k : ℕ} (h : ExecI P Q s c c' k) : Q c' := by
  induction h with
  | skip hq => exact hq
  | instr _ _ _ hq => exact hq
  | seq _ _ _ ih => exact ih
  | ifLtN_true _ _ ih => exact ih
  | ifLtN_false _ _ ih => exact ih
  | ifLtR_true _ _ ih => exact ih
  | ifLtR_false _ _ ih => exact ih
  | whileLtN_false _ hq => exact hq
  | whileLtN_true _ _ _ _ ih => exact ih
  | whileLtR_false _ hq => exact hq
  | whileLtR_true _ _ _ _ ih => exact ih

/-- Weaken the invariant. -/
theorem mono {s : Stmt} {c c' : Config} {k : ℕ} (h : ExecI P Q s c c' k)
    (hQ : ∀ c, Q c → Q' c) : ExecI P Q' s c c' k := by
  induction h with
  | skip hq => exact .skip (hQ _ hq)
  | instr hs he hq hq' => exact .instr hs he (hQ _ hq) (hQ _ hq')
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifLtN_true ht _ ih => exact .ifLtN_true ht ih
  | ifLtN_false ht _ ih => exact .ifLtN_false ht ih
  | ifLtR_true ht _ ih => exact .ifLtR_true ht ih
  | ifLtR_false ht _ ih => exact .ifLtR_false ht ih
  | whileLtN_false ht hq => exact .whileLtN_false ht (hQ _ hq)
  | whileLtN_true ht _ _ ih₁ ih₂ => exact .whileLtN_true ht ih₁ ih₂
  | whileLtR_false ht hq => exact .whileLtR_false ht (hQ _ hq)
  | whileLtR_true ht _ _ ih₁ ih₂ => exact .whileLtR_true ht ih₁ ih₂

/-- An `ExecI` run whose invariant implies the word bound is an `Exec` run. -/
theorem toExec {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ} (h : ExecI P Q s c c' k)
    (hQ : ∀ c, Q c → WordsBounded W c) : Exec P W s c c' k := by
  induction h with
  | skip hq => exact .skip (hQ _ hq)
  | instr hs he hq hq' => exact .instr hs he (hQ _ hq) (hQ _ hq')
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifLtN_true ht _ ih => exact .ifLtN_true ht ih
  | ifLtN_false ht _ ih => exact .ifLtN_false ht ih
  | ifLtR_true ht _ ih => exact .ifLtR_true ht ih
  | ifLtR_false ht _ ih => exact .ifLtR_false ht ih
  | whileLtN_false ht hq => exact .whileLtN_false ht (hQ _ hq)
  | whileLtN_true ht _ _ ih₁ ih₂ => exact .whileLtN_true ht ih₁ ih₂
  | whileLtR_false ht hq => exact .whileLtR_false ht (hQ _ hq)
  | whileLtR_true ht _ _ ih₁ ih₂ => exact .whileLtR_true ht ih₁ ih₂

end ExecI

/-- An `Exec` run is an `ExecI` run with the word bound as invariant. -/
theorem Exec.toExecI {P : Input} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) : ExecI P (WordsBounded W) s c c' k := by
  induction h with
  | skip hq => exact .skip hq
  | instr hs he hq hq' => exact .instr hs he hq hq'
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifLtN_true ht _ ih => exact .ifLtN_true ht ih
  | ifLtN_false ht _ ih => exact .ifLtN_false ht ih
  | ifLtR_true ht _ ih => exact .ifLtR_true ht ih
  | ifLtR_false ht _ ih => exact .ifLtR_false ht ih
  | whileLtN_false ht hq => exact .whileLtN_false ht hq
  | whileLtN_true ht _ _ ih₁ ih₂ => exact .whileLtN_true ht ih₁ ih₂
  | whileLtR_false ht hq => exact .whileLtR_false ht hq
  | whileLtR_true ht _ _ ih₁ ih₂ => exact .whileLtR_true ht ih₁ ih₂

/-! ### The transformation -/

/-- The sign-and-magnitude representation: `x = p - q` with `p = 0` or `q = 0`. -/
def SignRep (p q : ℕ) (x : ℝ) : Prop := x = (p : ℝ) - q ∧ (p = 0 ∨ q = 0)

/-- The configuration `d` (natural words only) encodes `c`. -/
structure NatEnc (c d : Config) : Prop where
  nreg : ∀ r, d.nreg (4 * r) = c.nreg r
  rreg : ∀ r, SignRep (d.nreg (4 * r + 1)) (d.nreg (4 * r + 2)) (c.rreg r)
  nmem : ∀ a, d.nmem (3 * a) = c.nmem a
  rmem : ∀ a, SignRep (d.nmem (3 * a + 1)) (d.nmem (3 * a + 2)) (c.rmem a)
  out : d.output = c.output

/-- The natural block of an instruction (scratch registers `3`, `7`, `11`). -/
def _root_.WordRAM.Instr.toNatCode : Instr → List Instr
  | .inputSize r => [.inputSize (4 * r)]
  | .constN r k => [.constN (4 * r) k]
  | .copyN r a => [.copyN (4 * r) (4 * a)]
  | .addN r a b => [.addN (4 * r) (4 * a) (4 * b)]
  | .subN r a b => [.subN (4 * r) (4 * a) (4 * b)]
  | .mulN r a b => [.mulN (4 * r) (4 * a) (4 * b)]
  | .divN r a b => [.divN (4 * r) (4 * a) (4 * b)]
  | .modN r a b => [.modN (4 * r) (4 * a) (4 * b)]
  | .loadN r a => [.addN 3 (4 * a) (4 * a), .addN 3 3 (4 * a), .loadN (4 * r) 3]
  | .storeN a r => [.addN 3 (4 * a) (4 * a), .addN 3 3 (4 * a), .storeN 3 (4 * r)]
  | .constR r z => [.constN (4 * r + 1) z.toNat, .constN (4 * r + 2) (-z).toNat]
  | .copyR r a => [.copyN (4 * r + 1) (4 * a + 1), .copyN (4 * r + 2) (4 * a + 2)]
  | .addR r a b => [.addN 3 (4 * a + 1) (4 * b + 1), .addN 7 (4 * a + 2) (4 * b + 2),
      .subN (4 * r + 1) 3 7, .subN (4 * r + 2) 7 3]
  | .subR r a b => [.addN 3 (4 * a + 1) (4 * b + 2), .addN 7 (4 * a + 2) (4 * b + 1),
      .subN (4 * r + 1) 3 7, .subN (4 * r + 2) 7 3]
  | .mulR r a b => [.mulN 3 (4 * a + 1) (4 * b + 1), .mulN 7 (4 * a + 2) (4 * b + 2),
      .addN 3 3 7, .mulN 7 (4 * a + 1) (4 * b + 2), .mulN 11 (4 * a + 2) (4 * b + 1),
      .addN 7 7 11, .copyN (4 * r + 1) 3, .copyN (4 * r + 2) 7]
  | .loadR r a => [.addN 3 (4 * a) (4 * a), .addN 3 3 (4 * a), .constN 7 1, .addN 3 3 7,
      .loadN (4 * r + 1) 3, .addN 3 3 7, .loadN (4 * r + 2) 3]
  | .storeR a r => [.addN 3 (4 * a) (4 * a), .addN 3 3 (4 * a), .constN 7 1, .addN 3 3 7,
      .storeN 3 (4 * r + 1), .addN 3 3 7, .storeN 3 (4 * r + 2)]
  | .readIn r a => [.readIn (4 * r) (4 * a)]
  | .rand r a => [.rand (4 * r) (4 * a)]
  | .outN a => [.outN (4 * a)]
  | .divR _ _ _ => [.halt]
  | .halt => [.halt]
  | .jump l => [.jump l]
  | .brLtN _ _ l => [.jump l]
  | .brLtR _ _ l => [.jump l]

/-- The natural test of a real comparison `rreg a < rreg b`: `r3 := p_a + q_b`,
`r7 := p_b + q_a`. -/
def natTstR (a b : ℕ) : List Instr := [.addN 3 (4 * a + 1) (4 * b + 2), .addN 7 (4 * b + 1) (4 * a + 2)]

/-- **The transformation**: real registers and memory replaced by pairs of natural words. -/
def Stmt.realsToNat : Stmt → Stmt
  | .skip => .skip
  | .instr i => block i.toNatCode
  | .seq s t => .seq s.realsToNat t.realsToNat
  | .ifLtN a b t e => .ifLtN (4 * a) (4 * b) t.realsToNat e.realsToNat
  | .ifLtR a b t e => .seq (block (natTstR a b)) (.ifLtN 3 7 t.realsToNat e.realsToNat)
  | .whileLtN a b body => .whileLtN (4 * a) (4 * b) body.realsToNat
  | .whileLtR a b body =>
      .seq (block (natTstR a b)) (.whileLtN 3 7 (.seq body.realsToNat (block (natTstR a b))))

/-- No real division in the statement. -/
def Stmt.noDivR : Stmt → Bool
  | .skip => true
  | .instr i => i.noDivR
  | .seq s t => s.noDivR && t.noDivR
  | .ifLtN _ _ t e => t.noDivR && e.noDivR
  | .ifLtR _ _ t e => t.noDivR && e.noDivR
  | .whileLtN _ _ body => body.noDivR
  | .whileLtR _ _ body => body.noDivR

/-! ### No real instruction is left -/

theorem _root_.WordRAM.Instr.toNatCode_noReal (i : Instr) : ∀ j ∈ i.toNatCode, j.isReal = false := by
  cases i <;> simp [Instr.toNatCode, Instr.isReal]

theorem compile_block_noReal (l : List Instr) (hl : ∀ j ∈ l, j.isReal = false) (base : ℕ) :
    ∀ j ∈ compile (block l) base, j.isReal = false := by
  rw [compile_block]; exact hl

theorem Stmt.compile_realsToNat_noReal (s : Stmt) :
    ∀ base, ∀ j ∈ compile s.realsToNat base, j.isReal = false := by
  have ht : ∀ a b, ∀ j ∈ natTstR a b, j.isReal = false := by simp [natTstR, Instr.isReal]
  induction s with
  | skip => simp [Stmt.realsToNat, compile]
  | instr i => intro base; exact compile_block_noReal _ (Instr.toNatCode_noReal i) base
  | seq s t ihs iht =>
      intro base j hj
      simp only [Stmt.realsToNat, compile, List.mem_append] at hj
      rcases hj with hj | hj
      · exact ihs _ j hj
      · exact iht _ j hj
  | ifLtN a b t e iht ihe =>
      intro base j hj
      simp only [Stmt.realsToNat, compile, List.mem_append, List.mem_cons] at hj
      rcases hj with (rfl | hj) | (rfl | hj)
      · rfl
      · exact ihe _ j hj
      · rfl
      · exact iht _ j hj
  | ifLtR a b t e iht ihe =>
      intro base j hj
      simp only [Stmt.realsToNat, compile, List.mem_append, List.mem_cons] at hj
      rcases hj with hj | (rfl | hj) | (rfl | hj)
      · exact compile_block_noReal _ (ht a b) _ j hj
      · rfl
      · exact ihe _ j hj
      · rfl
      · exact iht _ j hj
  | whileLtN a b body ih =>
      intro base j hj
      simp only [Stmt.realsToNat, compile, List.mem_append, List.mem_cons] at hj
      rcases hj with (rfl | rfl | hj) | hj
      · rfl
      · rfl
      · exact ih _ j hj
      · simp at hj; subst hj; rfl
  | whileLtR a b body ih =>
      intro base j hj
      simp only [Stmt.realsToNat, compile, List.mem_append, List.mem_cons] at hj
      rcases hj with hj | (rfl | rfl | hj | hj) | hj
      · exact compile_block_noReal _ (ht a b) _ j hj
      · rfl
      · rfl
      · exact ih _ j hj
      · exact compile_block_noReal _ (ht a b) _ j hj
      · simp at hj; subst hj; rfl

/-! ### The representation -/

theorem signRep_zero : SignRep 0 0 0 := ⟨by simp, Or.inl rfl⟩

theorem signRep_int (z : ℤ) : SignRep z.toNat (-z).toNat (z : ℝ) := by
  refine ⟨?_, by omega⟩
  have h : ((z.toNat : ℤ) : ℝ) - (((-z).toNat : ℤ) : ℝ) = (z : ℝ) := by
    have : (z.toNat : ℤ) - ((-z).toNat : ℤ) = z := by omega
    exact_mod_cast this
  push_cast at h; linarith

theorem signRep_sub (s t : ℕ) : SignRep (s - t) (t - s) ((s : ℝ) - t) := by
  refine ⟨?_, by omega⟩
  rcases le_total s t with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; simp
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]; simp

theorem signRep_le {p q : ℕ} {x : ℝ} {B : ℕ} (h : SignRep p q x) (hx : ∃ z : ℤ, x = z ∧ |z| ≤ (B : ℤ)) :
    p ≤ B ∧ q ≤ B := by
  obtain ⟨z, rfl, hz⟩ := hx
  have e : z = (p : ℤ) - q := by
    have := h.1; exact_mod_cast this
  have := abs_le.1 hz
  rcases h.2 with h0 | h0 <;> subst h0 <;> omega

theorem signRep_lt {pa qa pb qb : ℕ} {xa xb : ℝ} (ha : SignRep pa qa xa) (hb : SignRep pb qb xb) :
    xa < xb ↔ pa + qb < pb + qa := by
  rw [ha.1, hb.1]
  constructor
  · intro h
    have : ((pa + qb : ℕ) : ℝ) < ((pb + qa : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · intro h
    have : ((pa + qb : ℕ) : ℝ) < ((pb + qa : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith

theorem signRep_add {pa qa pb qb : ℕ} {xa xb : ℝ} (ha : SignRep pa qa xa) (hb : SignRep pb qb xb) :
    SignRep (pa + pb - (qa + qb)) (qa + qb - (pa + pb)) (xa + xb) := by
  have := signRep_sub (pa + pb) (qa + qb)
  refine ⟨?_, this.2⟩
  have h1 := this.1
  rw [ha.1, hb.1]; push_cast at h1 ⊢; linarith

theorem signRep_sub' {pa qa pb qb : ℕ} {xa xb : ℝ} (ha : SignRep pa qa xa) (hb : SignRep pb qb xb) :
    SignRep (pa + qb - (qa + pb)) (qa + pb - (pa + qb)) (xa - xb) := by
  have := signRep_sub (pa + qb) (qa + pb)
  refine ⟨?_, this.2⟩
  have h1 := this.1
  rw [ha.1, hb.1]; push_cast at h1 ⊢; linarith

theorem signRep_mul {pa qa pb qb : ℕ} {xa xb : ℝ} (ha : SignRep pa qa xa) (hb : SignRep pb qb xb) :
    SignRep (pa * pb + qa * qb) (pa * qb + qa * pb) (xa * xb) := by
  refine ⟨by rw [ha.1, hb.1]; push_cast; ring, ?_⟩
  rcases ha.2 with h | h <;> rcases hb.2 with h' | h' <;> subst h h' <;> simp

/-! ### Index arithmetic -/

section idx
variable {a b : ℕ}
theorem rtn_i40 : 4 * a ≠ 3 := by omega
theorem rtn_i41 : 4 * a ≠ 7 := by omega
theorem rtn_i42 : 4 * a ≠ 11 := by omega
theorem rtn_i43 : 4 * a + 1 ≠ 3 := by omega
theorem rtn_i44 : 4 * a + 1 ≠ 7 := by omega
theorem rtn_i45 : 4 * a + 1 ≠ 11 := by omega
theorem rtn_i46 : 4 * a + 2 ≠ 3 := by omega
theorem rtn_i47 : 4 * a + 2 ≠ 7 := by omega
theorem rtn_i48 : 4 * a + 2 ≠ 11 := by omega
theorem rtn_i49 : 4 * a + 1 ≠ 4 * b := by omega
theorem rtn_i50 : 4 * a + 2 ≠ 4 * b := by omega
theorem rtn_i51 : 4 * a + 1 ≠ 4 * b + 2 := by omega
theorem rtn_i52 : 4 * a + 2 ≠ 4 * b + 1 := by omega
theorem rtn_i53 : 4 * a ≠ 4 * b + 1 := by omega
theorem rtn_i54 : 4 * a ≠ 4 * b + 2 := by omega
theorem rtn_i55 : 4 * a = 4 * b ↔ a = b := by omega
theorem rtn_i56 : 4 * a + 1 = 4 * b + 1 ↔ a = b := by omega
theorem rtn_i57 : 4 * a + 2 = 4 * b + 2 ↔ a = b := by omega
end idx

/-- Simplify reads of updated registers at the indices of the encoding. -/
macro "rtn_enc_simp" : tactic =>
  `(tactic| simp (config := { failIfUnchanged := false }) only [Config.nreg_mk, Config.rreg_mk,
      Config.nmem_mk, Config.rmem_mk, Config.output_mk, Config.pc_mk, Machine.upd_same,
      Machine.upd_other, Machine.upd_upd_same, Machine.upd_other _ _ _ rtn_i40, Machine.upd_other _ _ _ rtn_i41, Machine.upd_other _ _ _ rtn_i42,
      Machine.upd_other _ _ _ rtn_i43, Machine.upd_other _ _ _ rtn_i44, Machine.upd_other _ _ _ rtn_i45,
      Machine.upd_other _ _ _ rtn_i46, Machine.upd_other _ _ _ rtn_i47, Machine.upd_other _ _ _ rtn_i48,
      Machine.upd_other _ _ _ rtn_i49, Machine.upd_other _ _ _ rtn_i50, Machine.upd_other _ _ _ rtn_i51,
      Machine.upd_other _ _ _ rtn_i52, Machine.upd_other _ _ _ rtn_i53, Machine.upd_other _ _ _ rtn_i54,
      Machine.upd_other _ _ _ (Ne.symm rtn_i40), Machine.upd_other _ _ _ (Ne.symm rtn_i41),
      Machine.upd_other _ _ _ (Ne.symm rtn_i43), Machine.upd_other _ _ _ (Ne.symm rtn_i44),
      Machine.upd_other _ _ _ (Ne.symm rtn_i46), Machine.upd_other _ _ _ (Ne.symm rtn_i47),
      ne_eq, Nat.reduceEqDiff, OfNat.ofNat_ne_one, not_false_eq_true])

/-! ### One instruction -/

section sim

variable {P : Input} {W B : ℕ}

theorem NatEnc.bnd {c d : Config} (h : NatEnc c d) (hc : WordsBounded W c) (hb : RealsIntBounded B c) :
    (∀ r, d.nreg (4 * r) ≤ W) ∧ (∀ r, d.nreg (4 * r + 1) ≤ B ∧ d.nreg (4 * r + 2) ≤ B) ∧
      (∀ a, d.nmem (3 * a) ≤ W) ∧ (∀ a, d.nmem (3 * a + 1) ≤ B ∧ d.nmem (3 * a + 2) ≤ B) :=
  ⟨fun r => (h.nreg r).symm ▸ hc.1 r, fun r => signRep_le (h.rreg r) (hb.1 r),
    fun a => (h.nmem a).symm ▸ hc.2 a, fun a => signRep_le (h.rmem a) (hb.2 a)⟩

/-- Writing a scratch register keeps the encoding. -/
theorem NatEnc.scratch {c d : Config} (h : NatEnc c d) {j : ℕ} (hj : j % 4 = 3) (v : ℕ) :
    NatEnc c { d with nreg := upd d.nreg j v } :=
  ⟨fun r => by simp only [Config.nreg_mk]; rw [upd_other _ _ _ (by omega)]; exact h.nreg r,
    fun r => by
      simp only [Config.nreg_mk]
      rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact h.rreg r,
    h.nmem, h.rmem, h.out⟩

/-- The encoding after writing a natural register. -/
theorem NatEnc.setN {c d : Config} (h : NatEnc c d) (r v : ℕ) :
    NatEnc { c with nreg := upd c.nreg r v } { d with nreg := upd d.nreg (4 * r) v } :=
  ⟨fun r' => by
      simp only [Config.nreg_mk, upd_apply, rtn_i55]; split_ifs <;> [rfl; exact h.nreg r'],
    fun r' => by simp only [Config.nreg_mk, Config.rreg_mk]; rtn_enc_simp; exact h.rreg r',
    h.nmem, h.rmem, h.out⟩

/-- The encoding after writing a real register (both halves). -/
theorem NatEnc.setR {c d : Config} (h : NatEnc c d) (r : ℕ) {p q : ℕ} {x : ℝ} (hx : SignRep p q x) :
    NatEnc { c with rreg := upd c.rreg r x }
      { d with nreg := upd (upd d.nreg (4 * r + 1) p) (4 * r + 2) q } :=
  ⟨fun r' => by simp only [Config.nreg_mk]; rtn_enc_simp; exact h.nreg r',
    fun r' => by
      simp only [Config.nreg_mk, Config.rreg_mk]
      by_cases hr : r' = r
      · subst hr; rtn_enc_simp; exact hx
      · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
          upd_other _ _ _ (by omega), upd_other _ _ _ hr]
        exact h.rreg r',
    h.nmem, h.rmem, h.out⟩

/-- The encoding is kept when only scratch registers change. -/
theorem NatEnc.keep {c d : Config} (h : NatEnc c d) (d' : Config)
    (hn : ∀ j, j % 4 ≠ 3 → d'.nreg j = d.nreg j) (hm : d'.nmem = d.nmem)
    (ho : d'.output = d.output) : NatEnc c d' :=
  ⟨fun r => (hn _ (by omega)).trans (h.nreg r),
    fun r => by rw [hn _ (by omega), hn _ (by omega)]; exact h.rreg r,
    fun a => hm ▸ h.nmem a, fun a => hm ▸ h.rmem a, ho.trans h.out⟩

theorem NatEnc.setN' {c d : Config} (h : NatEnc c d) (d' : Config) (r v : ℕ) (hv : d'.nreg (4 * r) = v)
    (hn : ∀ j, j % 4 ≠ 3 → j ≠ 4 * r → d'.nreg j = d.nreg j) (hm : d'.nmem = d.nmem)
    (ho : d'.output = d.output) : NatEnc { c with nreg := upd c.nreg r v } d' :=
  ⟨fun r' => by
      by_cases hr : r' = r
      · subst hr; simpa using hv
      · rw [hn _ (by omega) (by omega)]; simp [upd_other _ _ _ hr, h.nreg r'],
    fun r' => by rw [hn _ (by omega) (by omega), hn _ (by omega) (by omega)]; exact h.rreg r',
    fun a => hm ▸ h.nmem a, fun a => hm ▸ h.rmem a, ho.trans h.out⟩

theorem NatEnc.setR' {c d : Config} (h : NatEnc c d) (d' : Config) (r : ℕ) {x : ℝ}
    (hx : SignRep (d'.nreg (4 * r + 1)) (d'.nreg (4 * r + 2)) x)
    (hn : ∀ j, j % 4 ≠ 3 → j ≠ 4 * r + 1 → j ≠ 4 * r + 2 → d'.nreg j = d.nreg j)
    (hm : d'.nmem = d.nmem) (ho : d'.output = d.output) : NatEnc { c with rreg := upd c.rreg r x } d' :=
  ⟨fun r' => (hn _ (by omega) (by omega) (by omega)).trans (h.nreg r'),
    fun r' => by
      by_cases hr : r' = r
      · subst hr; simpa using hx
      · rw [hn _ (by omega) (by omega) (by omega), hn _ (by omega) (by omega) (by omega)]
        simpa [upd_other _ _ _ hr] using h.rreg r',
    fun a => hm ▸ h.nmem a, fun a => hm ▸ h.rmem a, ho.trans h.out⟩

theorem NatEnc.setNM' {c d : Config} (h : NatEnc c d) (d' : Config) (a v : ℕ) (hv : d'.nmem (3 * a) = v)
    (hm : ∀ j, j ≠ 3 * a → d'.nmem j = d.nmem j) (hn : ∀ j, j % 4 ≠ 3 → d'.nreg j = d.nreg j)
    (ho : d'.output = d.output) : NatEnc { c with nmem := upd c.nmem a v } d' :=
  ⟨fun r => (hn _ (by omega)).trans (h.nreg r),
    fun r => by rw [hn _ (by omega), hn _ (by omega)]; exact h.rreg r,
    fun a' => by
      by_cases ha : a' = a
      · subst ha; simpa using hv
      · rw [hm _ (by omega)]; simp [upd_other _ _ _ ha, h.nmem a'],
    fun a' => by rw [hm _ (by omega), hm _ (by omega)]; exact h.rmem a', ho.trans h.out⟩

theorem NatEnc.setRM' {c d : Config} (h : NatEnc c d) (d' : Config) (a : ℕ) {x : ℝ}
    (hx : SignRep (d'.nmem (3 * a + 1)) (d'.nmem (3 * a + 2)) x)
    (hm : ∀ j, j ≠ 3 * a + 1 → j ≠ 3 * a + 2 → d'.nmem j = d.nmem j)
    (hn : ∀ j, j % 4 ≠ 3 → d'.nreg j = d.nreg j)
    (ho : d'.output = d.output) : NatEnc { c with rmem := upd c.rmem a x } d' :=
  ⟨fun r => (hn _ (by omega)).trans (h.nreg r),
    fun r => by rw [hn _ (by omega), hn _ (by omega)]; exact h.rreg r,
    fun a' => by rw [hm _ (by omega) (by omega)]; exact h.nmem a',
    fun a' => by
      by_cases ha : a' = a
      · subst ha; simpa using hx
      · rw [hm _ (by omega) (by omega), hm _ (by omega) (by omega)]
        simpa [upd_other _ _ _ ha] using h.rmem a', ho.trans h.out⟩

/-- The frame goals of the `NatEnc.set*'` lemmas. -/
macro "rtn_keep_tac" : tactic =>
  `(tactic| (intros; simp only [Config.nreg_mk, Config.nmem_mk, upd_apply]; split_ifs <;> (first | rfl | omega)))

theorem Instr.realsToNat_sim {i : Instr} {c c' d : Config} (hs : i.IsStraight) (hnd : i.noDivR = true)
    (he : i.effect P c = some c') (hc : WordsBounded W c) (hb : RealsIntBounded B c)
    (hc' : WordsBounded W c') (hb' : RealsIntBounded B c') (hE : NatEnc c d)
    (hd : WordsBounded (3 * W + 2 * B + 2) d) :
    ∃ d' k, Exec P (3 * W + 2 * B + 2) (block i.toNatCode) d d' k ∧ k ≤ 8 ∧ NatEnc c' d' := by
  obtain ⟨hN, hR, hM, hRM⟩ := hE.bnd hc hb
  have hn' := hc'.1
  cases i with
  | halt => simp at hs
  | jump => simp at hs
  | brLtN => simp at hs
  | brLtR => simp at hs
  | divR => simp [Instr.noDivR] at hnd
  | inputSize r =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    exec_block
    · have := hn' r; simp only [Config.nreg_mk, upd_same] at this; omega
    · exact ⟨by omega, hE.setN' _ r _ (by rtn_enc_simp) (by rtn_keep_tac) rfl rfl⟩
  | constN r k =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    exec_block
    · have := hn' r; simp only [Config.nreg_mk, upd_same] at this; omega
    · exact ⟨by omega, hE.setN' _ r _ (by rtn_enc_simp) (by rtn_keep_tac) rfl rfl⟩
  | copyN r a =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    exec_block
    exact ⟨by omega, hE.setN' _ r _ (by rtn_enc_simp; exact hE.nreg a) (by rtn_keep_tac) rfl rfl⟩
  | addN r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    exec_block
    · have := hn' r; simp only [Config.nreg_mk, upd_same] at this; rw [hE.nreg, hE.nreg]; omega
    · exact ⟨by omega, hE.setN' _ r _ (by rtn_enc_simp; rw [hE.nreg, hE.nreg]) (by rtn_keep_tac) rfl rfl⟩
  | subN r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    exec_block
    exact ⟨by omega, hE.setN' _ r _ (by rtn_enc_simp; rw [hE.nreg, hE.nreg]) (by rtn_keep_tac) rfl rfl⟩
  | mulN r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    exec_block
    · have := hn' r; simp only [Config.nreg_mk, upd_same] at this; rw [hE.nreg, hE.nreg]; omega
    · exact ⟨by omega, hE.setN' _ r _ (by rtn_enc_simp; rw [hE.nreg, hE.nreg]) (by rtn_keep_tac) rfl rfl⟩
  | divN r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    exec_block
    exact ⟨by omega, hE.setN' _ r _ (by rtn_enc_simp; rw [hE.nreg, hE.nreg]) (by rtn_keep_tac) rfl rfl⟩
  | modN r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    exec_block
    exact ⟨by omega, hE.setN' _ r _ (by rtn_enc_simp; rw [hE.nreg, hE.nreg]) (by rtn_keep_tac) rfl rfl⟩
  | readIn r a =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    exec_block
    · have := hn' r; simp only [Config.nreg_mk, upd_same] at this; rw [hE.nreg]; omega
    · exact ⟨by omega, hE.setN' _ r _ (by rtn_enc_simp; rw [hE.nreg]) (by rtn_keep_tac) rfl rfl⟩
  | rand r a =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    exec_block
    · have := hn' r; simp only [Config.nreg_mk, upd_same] at this; rw [hE.nreg]; omega
    · exact ⟨by omega, hE.setN' _ r _ (by rtn_enc_simp; rw [hE.nreg]) (by rtn_keep_tac) rfl rfl⟩
  | outN a =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    exec_block
    refine ⟨by omega, ⟨hE.nreg, hE.rreg, hE.nmem, hE.rmem, ?_⟩⟩
    simp [hE.out, hE.nreg]
  | loadN r a =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    have := hN a
    exec_block
    · omega
    · rtn_enc_simp; omega
    · refine ⟨by omega, hE.setN' _ r _ ?_ (by rtn_keep_tac) rfl rfl⟩
      rtn_enc_simp
      rw [hE.nreg, show c.nreg a + c.nreg a + c.nreg a = 3 * c.nreg a by ring, hE.nmem]
  | storeN a r =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    have := hN a
    exec_block
    · omega
    · rtn_enc_simp; omega
    · refine ⟨by omega, hE.setNM' _ _ _ ?_ ?_ (by rtn_keep_tac) rfl⟩
      · rtn_enc_simp
        rw [hE.nreg, show c.nreg a + c.nreg a + c.nreg a = 3 * c.nreg a by ring, upd_same,
          hE.nreg]
      · intro j hj
        rtn_enc_simp
        rw [hE.nreg, show c.nreg a + c.nreg a + c.nreg a = 3 * c.nreg a by ring,
          upd_other _ _ _ hj]
  | constR r z =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    have hz := hb'.1 r
    simp only [Config.rreg_mk, upd_same] at hz
    have := signRep_le (signRep_int z) hz
    exec_block
    · omega
    · omega
    · exact ⟨by omega, hE.setR' _ r (by rtn_enc_simp; exact signRep_int z) (by rtn_keep_tac) rfl rfl⟩
  | copyR r a =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    exec_block
    exact ⟨by omega, hE.setR' _ r (by rtn_enc_simp; exact hE.rreg a) (by rtn_keep_tac) rfl rfl⟩
  | addR r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    have := hR a; have := hR b
    exec_block
    · omega
    · rtn_enc_simp; omega
    · exact ⟨by omega, hE.setR' _ r (by rtn_enc_simp; exact signRep_add (hE.rreg a) (hE.rreg b))
        (by rtn_keep_tac) rfl rfl⟩
  | subR r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    have := hR a; have := hR b
    exec_block
    · omega
    · rtn_enc_simp; omega
    · exact ⟨by omega, hE.setR' _ r (by rtn_enc_simp; exact signRep_sub' (hE.rreg a) (hE.rreg b))
        (by rtn_keep_tac) rfl rfl⟩
  | mulR r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    have hz := hb'.1 r
    simp only [Config.rreg_mk, upd_same] at hz
    have hm := signRep_le (signRep_mul (hE.rreg a) (hE.rreg b)) hz
    exec_block
    all_goals rtn_enc_simp
    · exact (Nat.le_add_right _ _).trans (hm.1.trans (by omega))
    · exact (Nat.le_add_left _ _).trans (hm.1.trans (by omega))
    · exact hm.1.trans (by omega)
    · exact (Nat.le_add_right _ _).trans (hm.2.trans (by omega))
    · exact (Nat.le_add_left _ _).trans (hm.2.trans (by omega))
    · exact hm.2.trans (by omega)
    · exact ⟨by omega, hE.setR' _ r (by rtn_enc_simp; exact signRep_mul (hE.rreg a) (hE.rreg b)) (by rtn_keep_tac) rfl rfl⟩
  | loadR r a =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    have := hN a
    exec_block
    all_goals rtn_enc_simp
    · omega
    · omega
    · omega
    · omega
    · omega
    · refine ⟨by omega, hE.setR' _ r ?_ (by rtn_keep_tac) rfl rfl⟩
      rw [hE.nreg, show c.nreg a + c.nreg a + c.nreg a + 1 = 3 * c.nreg a + 1 by ring,
        show 3 * c.nreg a + 1 + 1 = 3 * c.nreg a + 2 by ring]
      rtn_enc_simp
      exact hE.rmem _
  | storeR a r =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he; simp only [Instr.toNatCode]
    have := hN a
    exec_block
    all_goals rtn_enc_simp
    · omega
    · omega
    · omega
    · omega
    · omega
    · refine ⟨by omega, hE.setRM' _ _ ?_ ?_ (by rtn_keep_tac) rfl⟩
      · rw [hE.nreg, show c.nreg a + c.nreg a + c.nreg a + 1 = 3 * c.nreg a + 1 by ring,
          show 3 * c.nreg a + 1 + 1 = 3 * c.nreg a + 2 by ring]
        simp only [Config.nmem_mk]
        rw [upd_other _ _ _ (by omega), upd_same, upd_same]
        exact hE.rreg r
      · intro j h1 h2
        rw [hE.nreg, show c.nreg a + c.nreg a + c.nreg a + 1 = 3 * c.nreg a + 1 by ring,
          show 3 * c.nreg a + 1 + 1 = 3 * c.nreg a + 2 by ring]
        simp only [Config.nmem_mk]
        rw [upd_other _ _ _ h2, upd_other _ _ _ h1]

/-- The test block of a real comparison. -/
theorem natTstR_exec {c d : Config} (hE : NatEnc c d) (hc : WordsBounded W c) (hb : RealsIntBounded B c)
    (hd : WordsBounded (3 * W + 2 * B + 2) d) (a b : ℕ) :
    ∃ d' k, Exec P (3 * W + 2 * B + 2) (block (natTstR a b)) d d' k ∧ k = 2 ∧ NatEnc c d' ∧
      (c.rreg a < c.rreg b ↔ d'.nreg 3 < d'.nreg 7) := by
  obtain ⟨-, hR, -, -⟩ := hE.bnd hc hb
  have := hR a; have := hR b
  simp only [natTstR]
  exec_block
  all_goals rtn_enc_simp
  · omega
  · omega
  · exact ⟨trivial, hE.keep _ (by rtn_keep_tac) rfl rfl, signRep_lt (hE.rreg a) (hE.rreg b)⟩

theorem Stmt.exec_realsToNat_aux {s : Stmt} {c c' : Config} {k : ℕ}
    (h : ExecI P (fun c => WordsBounded W c ∧ RealsIntBounded B c) s c c' k) :
    s.noDivR = true → ∀ d, NatEnc c d → WordsBounded (3 * W + 2 * B + 2) d →
      ∃ d' k', Exec P (3 * W + 2 * B + 2) s.realsToNat d d' k' ∧ k' ≤ 8 * k ∧ NatEnc c' d' := by
  induction h with
  | skip _ => intro _ d hE hd; exact ⟨d, 0, .skip hd, le_refl _, hE⟩
  | instr hst he hq hq' =>
    intro hs d hE hd
    obtain ⟨d', k', e, hk, hE'⟩ := Instr.realsToNat_sim hst hs he hq.1 hq.2 hq'.1 hq'.2 hE hd
    exact ⟨d', k', e, by omega, hE'⟩
  | seq _ _ ih₁ ih₂ =>
    intro hs d hE hd
    simp only [Stmt.noDivR, Bool.and_eq_true] at hs
    obtain ⟨d₁, k₁, e₁, hk₁, hE₁⟩ := ih₁ hs.1 d hE hd
    obtain ⟨d₂, k₂, e₂, hk₂, hE₂⟩ := ih₂ hs.2 d₁ hE₁ e₁.wb_right
    exact ⟨d₂, k₁ + k₂, .seq e₁ e₂, by omega, hE₂⟩
  | ifLtN_true ht _ ih =>
    intro hs d hE hd
    simp only [Stmt.noDivR, Bool.and_eq_true] at hs
    obtain ⟨d', k', e, hk, hE'⟩ := ih hs.1 d hE hd
    exact ⟨d', k' + 1, .ifLtN_true (by rw [hE.nreg, hE.nreg]; exact ht) e, by omega, hE'⟩
  | ifLtN_false ht _ ih =>
    intro hs d hE hd
    simp only [Stmt.noDivR, Bool.and_eq_true] at hs
    obtain ⟨d', k', e, hk, hE'⟩ := ih hs.2 d hE hd
    exact ⟨d', k' + 2, .ifLtN_false (by rw [hE.nreg, hE.nreg]; exact ht) e, by omega, hE'⟩
  | ifLtR_true ht hx ih =>
    intro hs d hE hd
    simp only [Stmt.noDivR, Bool.and_eq_true] at hs
    obtain ⟨dt, _, et, rfl, hEt, hiff⟩ := natTstR_exec hE hx.q_left.1 hx.q_left.2 hd _ _
    obtain ⟨d', k', e, hk, hE'⟩ := ih hs.1 dt hEt et.wb_right
    exact ⟨d', 2 + (k' + 1), .seq et (.ifLtN_true (hiff.1 ht) e), by omega, hE'⟩
  | ifLtR_false ht hx ih =>
    intro hs d hE hd
    simp only [Stmt.noDivR, Bool.and_eq_true] at hs
    obtain ⟨dt, _, et, rfl, hEt, hiff⟩ := natTstR_exec hE hx.q_left.1 hx.q_left.2 hd _ _
    obtain ⟨d', k', e, hk, hE'⟩ := ih hs.2 dt hEt et.wb_right
    exact ⟨d', 2 + (k' + 2), .seq et (.ifLtN_false (fun h => ht (hiff.2 h)) e), by omega, hE'⟩
  | whileLtN_false ht _ =>
    intro _ d hE hd
    exact ⟨d, 2, .whileLtN_false (by rw [hE.nreg, hE.nreg]; exact ht) hd, by omega, hE⟩
  | whileLtN_true ht _ _ ih₁ ih₂ =>
    intro hs d hE hd
    obtain ⟨d₁, k₁, e₁, hk₁, hE₁⟩ := ih₁ hs d hE hd
    obtain ⟨d₂, k₂, e₂, hk₂, hE₂⟩ := ih₂ hs d₁ hE₁ e₁.wb_right
    exact ⟨d₂, k₁ + 2 + k₂, .whileLtN_true (by rw [hE.nreg, hE.nreg]; exact ht) e₁ e₂, by omega,
      hE₂⟩
  | whileLtR_false ht hq =>
    intro _ d hE hd
    obtain ⟨dt, _, et, rfl, hEt, hiff⟩ := natTstR_exec hE hq.1 hq.2 hd _ _
    exact ⟨dt, 2 + 2, .seq et (.whileLtN_false (fun h => ht (hiff.2 h)) et.wb_right), by omega,
      hEt⟩
  | whileLtR_true ht hx _ ih₁ ih₂ =>
    intro hs d hE hd
    obtain ⟨dt, _, et, rfl, hEt, hiff⟩ := natTstR_exec hE hx.q_left.1 hx.q_left.2 hd _ _
    obtain ⟨d₁, k₁, e₁, hk₁, hE₁⟩ := ih₁ hs dt hEt et.wb_right
    obtain ⟨d₂, k₂, e₂, hk₂, hE₂⟩ := ih₂ hs d₁ hE₁ e₁.wb_right
    simp only [Stmt.realsToNat] at e₂ ⊢
    cases e₂ with
    | seq ex ey =>
      exact ⟨d₂, 2 + (_ + _ + 2 + _), .seq et (.whileLtN_true (hiff.1 ht) (.seq e₁ ex) ey),
        by omega, hE₂⟩

/-- **The simulation.** A run of `s` whose configurations have natural words at most `W` and
reals that are integers of absolute value at most `B` is simulated, from any encoding `d` of its
start bounded by `3 W + 2 B + 2`, by a run of `s.realsToNat` (natural instructions only) with
word bound `3 W + 2 B + 2` and at most `8` times the steps, ending in an encoding of its end. -/
theorem Stmt.exec_realsToNat {s : Stmt} {c c' : Config} {k : ℕ}
    (h : ExecI P (fun c => WordsBounded W c ∧ RealsIntBounded B c) s c c' k)
    (hs : s.noDivR = true) {d : Config} (hE : NatEnc c d) (hd : WordsBounded (3 * W + 2 * B + 2) d) :
    ∃ d' k', Exec P (3 * W + 2 * B + 2) s.realsToNat d d' k' ∧ k' ≤ 8 * k ∧ NatEnc c' d' :=
  Stmt.exec_realsToNat_aux h hs d hE hd

theorem enc_initConfig : NatEnc initConfig initConfig :=
  ⟨fun _ => rfl, fun _ => signRep_zero, fun _ => rfl, fun _ => signRep_zero, rfl⟩

/-- **Top level.** A run from the initial configuration with natural words at most `W` and real
values integers bounded by `B` gives a realization by a program with no real instruction
(`Stmt.compile_realsToNat_noReal`), with word bound `3 W + 2 B + 2`, within `8 k + 1` steps,
with the same output. -/
theorem Stmt.runsWithin_realsToNat {s : Stmt} {c' : Config} {k : ℕ}
    (h : ExecI P (fun c => WordsBounded W c ∧ RealsIntBounded B c) s initConfig c' k)
    (hs : s.noDivR = true) :
    RunsWithin (compile s.realsToNat 0 ++ [Instr.halt]) P (3 * W + 2 * B + 2) (8 * k + 1)
      c'.output := by
  obtain ⟨d', k', e, hk, hE⟩ :=
    s.exec_realsToNat h hs enc_initConfig ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  obtain ⟨k0, hk0, h1, h2⟩ := runsWithin_of_exec e
  exact ⟨k0, by omega, h1, by rw [← hE.out]; exact h2⟩

end sim

/-! ### Tools to establish the bounds along an existing run -/

section tools

variable {P : Input} {W : ℕ}

/-- **The big-step semantics is deterministic** (for any two word bounds). -/
theorem Exec.det {W' : ℕ} {s : Stmt} {c c₁ c₂ : Config} {k₁ k₂ : ℕ}
    (h₁ : Exec P W s c c₁ k₁) (h₂ : Exec P W' s c c₂ k₂) : c₁ = c₂ ∧ k₁ = k₂ := by
  induction h₁ generalizing c₂ k₂ with
  | skip _ => cases h₂; exact ⟨rfl, rfl⟩
  | instr _ he _ _ =>
    cases h₂ with
    | instr _ he' _ _ => rw [he] at he'; exact ⟨Option.some.inj he', rfl⟩
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq e₁ e₂ => obtain ⟨rfl, rfl⟩ := ih₁ e₁; obtain ⟨rfl, rfl⟩ := ih₂ e₂; exact ⟨rfl, rfl⟩
  | ifLtN_true ht _ ih =>
    cases h₂ with
    | ifLtN_true _ e => obtain ⟨rfl, rfl⟩ := ih e; exact ⟨rfl, rfl⟩
    | ifLtN_false hf _ => exact absurd ht hf
  | ifLtN_false ht _ ih =>
    cases h₂ with
    | ifLtN_true hf _ => exact absurd hf ht
    | ifLtN_false _ e => obtain ⟨rfl, rfl⟩ := ih e; exact ⟨rfl, rfl⟩
  | ifLtR_true ht _ ih =>
    cases h₂ with
    | ifLtR_true _ e => obtain ⟨rfl, rfl⟩ := ih e; exact ⟨rfl, rfl⟩
    | ifLtR_false hf _ => exact absurd ht hf
  | ifLtR_false ht _ ih =>
    cases h₂ with
    | ifLtR_true hf _ => exact absurd hf ht
    | ifLtR_false _ e => obtain ⟨rfl, rfl⟩ := ih e; exact ⟨rfl, rfl⟩
  | whileLtN_false ht _ =>
    cases h₂ with
    | whileLtN_false _ _ => exact ⟨rfl, rfl⟩
    | whileLtN_true hf _ _ => exact absurd hf ht
  | whileLtN_true ht _ _ ih₁ ih₂ =>
    cases h₂ with
    | whileLtN_false hf _ => exact absurd ht hf
    | whileLtN_true _ e₁ e₂ =>
      obtain ⟨rfl, rfl⟩ := ih₁ e₁; obtain ⟨rfl, rfl⟩ := ih₂ e₂; exact ⟨rfl, rfl⟩
  | whileLtR_false ht _ =>
    cases h₂ with
    | whileLtR_false _ _ => exact ⟨rfl, rfl⟩
    | whileLtR_true hf _ _ => exact absurd hf ht
  | whileLtR_true ht _ _ ih₁ ih₂ =>
    cases h₂ with
    | whileLtR_false hf _ => exact absurd ht hf
    | whileLtR_true _ e₁ e₂ =>
      obtain ⟨rfl, rfl⟩ := ih₁ e₁; obtain ⟨rfl, rfl⟩ := ih₂ e₂; exact ⟨rfl, rfl⟩

/-- The effects of a list of straight-line instructions, in order. -/
noncomputable def blockEffs (P : Input) : List Instr → Config → Option Config
  | [], c => some c
  | i :: l, c => (i.effect P c).bind (blockEffs P l)

/-- A run of a block is the composition of the effects of its instructions. -/
theorem Exec.block_effs {l : List Instr} {c c' : Config} {k : ℕ} (h : Exec P W (block l) c c' k) :
    blockEffs P l c = some c' ∧ k = l.length := by
  induction l generalizing c k with
  | nil => cases h; exact ⟨rfl, rfl⟩
  | cons i l ih =>
    cases h with
    | seq e₁ e₂ =>
      cases e₁ with
      | instr _ he _ _ =>
        obtain ⟨h1, h2⟩ := ih e₂
        exact ⟨by simp [blockEffs, he, h1], by simp [h2]; omega⟩

/-- Number of real additions and subtractions. -/
def _root_.WordRAM.Instr.addCount : Instr → ℕ
  | .addR .. | .subR .. => 1
  | _ => 0

/-- A real instruction other than a multiplication or a division, with constants bounded by
`Bc`. -/
def _root_.WordRAM.Instr.LinR (Bc : ℕ) : Instr → Prop
  | .mulR .. | .divR .. => False
  | .constR _ z => |z| ≤ (Bc : ℤ)
  | _ => True

/-- Number of real additions and subtractions of a statement. -/
def Stmt.addCount : Stmt → ℕ
  | .skip => 0
  | .instr i => i.addCount
  | .seq s t => s.addCount + t.addCount
  | .ifLtN _ _ t e => t.addCount + e.addCount
  | .ifLtR _ _ t e => t.addCount + e.addCount
  | .whileLtN _ _ body => body.addCount
  | .whileLtR _ _ body => body.addCount

/-- A loop-free statement whose instructions are `Instr.LinR Bc`. -/
def Stmt.LinLoopFree (Bc : ℕ) : Stmt → Prop
  | .skip => True
  | .instr i => i.LinR Bc
  | .seq s t => s.LinLoopFree Bc ∧ t.LinLoopFree Bc
  | .ifLtN _ _ t e => t.LinLoopFree Bc ∧ e.LinLoopFree Bc
  | .ifLtR _ _ t e => t.LinLoopFree Bc ∧ e.LinLoopFree Bc
  | .whileLtN _ _ _ => False
  | .whileLtR _ _ _ => False

theorem RealsIntBounded.updR {X : ℕ} {c : Config} (h : RealsIntBounded X c) (r : ℕ) {x : ℝ}
    (hx : ∃ z : ℤ, x = z ∧ |z| ≤ (X : ℤ)) :
    RealsIntBounded X { c with rreg := upd c.rreg r x } :=
  ⟨fun r' => by
    by_cases hr : r' = r
    · subst hr; simpa using hx
    · simpa [upd_other _ _ _ hr] using h.1 r', h.2⟩

theorem RealsIntBounded.updM {X : ℕ} {c : Config} (h : RealsIntBounded X c) (a : ℕ) {x : ℝ}
    (hx : ∃ z : ℤ, x = z ∧ |z| ≤ (X : ℤ)) :
    RealsIntBounded X { c with rmem := upd c.rmem a x } :=
  ⟨h.1, fun a' => by
    by_cases ha : a' = a
    · subst ha; simpa using hx
    · simpa [upd_other _ _ _ ha] using h.2 a'⟩

/-- One instruction at most doubles the bound (only `addR` and `subR` may). -/
theorem Instr.rib_effect {i : Instr} {c c' : Config} {X Bc : ℕ} (hi : i.LinR Bc) (hX : Bc ≤ X)
    (he : i.effect P c = some c') (h : RealsIntBounded X c) :
    RealsIntBounded (2 ^ i.addCount * X) c' := by
  have h2 : X ≤ 2 * X := by omega
  cases i <;> simp only [Instr.effect, Option.some.injEq, reduceCtorEq] at he <;>
    (try subst he) <;> simp only [Instr.addCount, pow_zero, pow_one, one_mul] <;>
    (try exact h) <;> simp only [Instr.LinR] at hi
  case constR r z => exact h.updR r ⟨z, rfl, hi.trans (by exact_mod_cast hX)⟩
  case copyR r a => exact h.updR r (h.1 a)
  case addR r a b =>
    obtain ⟨za, ha, hza⟩ := h.1 a; obtain ⟨zb, hb, hzb⟩ := h.1 b
    refine (h.mono h2).updR r ⟨za + zb, by rw [ha, hb]; push_cast; ring, ?_⟩
    have := abs_add_le za zb; push_cast; omega
  case subR r a b =>
    obtain ⟨za, ha, hza⟩ := h.1 a; obtain ⟨zb, hb, hzb⟩ := h.1 b
    refine (h.mono h2).updR r ⟨za - zb, by rw [ha, hb]; push_cast; ring, ?_⟩
    have := abs_sub za zb; push_cast; omega
  case loadR r a => exact h.updR r (h.2 _)
  case storeR a r => exact h.updM _ (h.1 r)

theorem ExecI.mono_rib {X Y : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : ExecI P (fun c => WordsBounded W c ∧ RealsIntBounded X c) s c c' k) (hXY : X ≤ Y) :
    ExecI P (fun c => WordsBounded W c ∧ RealsIntBounded Y c) s c c' k :=
  h.mono fun _ hc => ⟨hc.1, hc.2.mono hXY⟩

theorem rtn_le_two_pow_mul (n X : ℕ) : X ≤ 2 ^ n * X :=
  Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) n)

theorem rtn_two_pow_mul_le {m n : ℕ} (X : ℕ) (h : m ≤ n) : 2 ^ m * X ≤ 2 ^ n * X :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) h)

/-- **Loop-free statements.** A loop-free statement without `mulR`/`divR` and with real constants
bounded by `Bc`, started with reals bounded by `X ≥ Bc`, keeps them bounded by
`2 ^ s.addCount * X` along its run. -/
theorem Exec.toExecI_linLoopFree {s : Stmt} {c c' : Config} {k : ℕ} {Bc : ℕ}
    (h : Exec P W s c c' k) : s.LinLoopFree Bc → ∀ X, Bc ≤ X → RealsIntBounded X c →
      ExecI P (fun c => WordsBounded W c ∧ RealsIntBounded (2 ^ s.addCount * X) c) s c c' k ∧
        RealsIntBounded (2 ^ s.addCount * X) c' := by
  induction h with
  | skip hw =>
    intro _ X _ hb
    simp only [Stmt.addCount, pow_zero, one_mul]; exact ⟨.skip ⟨hw, hb⟩, hb⟩
  | instr hs he hw hw' =>
    intro hl X hX hb
    have := Instr.rib_effect hl hX he hb
    exact ⟨.instr hs he ⟨hw, hb.mono (rtn_le_two_pow_mul _ _)⟩ ⟨hw', this⟩, this⟩
  | @seq s t _ _ _ _ _ _ _ ih₁ ih₂ =>
    intro hl X hX hb
    obtain ⟨E₁, b₁⟩ := ih₁ hl.1 X hX hb
    obtain ⟨E₂, b₂⟩ := ih₂ hl.2 _ (hX.trans (rtn_le_two_pow_mul _ _)) b₁
    have e : 2 ^ t.addCount * (2 ^ s.addCount * X) = 2 ^ (s.seq t).addCount * X := by
      simp only [Stmt.addCount, pow_add]; ring
    rw [e] at E₂ b₂
    exact ⟨.seq (E₁.mono_rib (rtn_two_pow_mul_le _ (by simp [Stmt.addCount]))) E₂, b₂⟩
  | @ifLtN_true _ _ t e _ _ _ ht _ ih =>
    intro hl X hX hb
    obtain ⟨E, b⟩ := ih hl.1 X hX hb
    have hle := rtn_two_pow_mul_le X (Nat.le_add_right t.addCount e.addCount)
    exact ⟨.ifLtN_true ht (E.mono_rib hle), b.mono hle⟩
  | @ifLtN_false _ _ t e _ _ _ ht _ ih =>
    intro hl X hX hb
    obtain ⟨E, b⟩ := ih hl.2 X hX hb
    have hle := rtn_two_pow_mul_le X (Nat.le_add_left e.addCount t.addCount)
    exact ⟨.ifLtN_false ht (E.mono_rib hle), b.mono hle⟩
  | @ifLtR_true _ _ t e _ _ _ ht _ ih =>
    intro hl X hX hb
    obtain ⟨E, b⟩ := ih hl.1 X hX hb
    have hle := rtn_two_pow_mul_le X (Nat.le_add_right t.addCount e.addCount)
    exact ⟨.ifLtR_true ht (E.mono_rib hle), b.mono hle⟩
  | @ifLtR_false _ _ t e _ _ _ ht _ ih =>
    intro hl X hX hb
    obtain ⟨E, b⟩ := ih hl.2 X hX hb
    have hle := rtn_two_pow_mul_le X (Nat.le_add_left e.addCount t.addCount)
    exact ⟨.ifLtR_false ht (E.mono_rib hle), b.mono hle⟩
  | whileLtN_false => intro hl; exact hl.elim
  | whileLtN_true => intro hl; exact hl.elim
  | whileLtR_false => intro hl; exact hl.elim
  | whileLtR_true => intro hl; exact hl.elim

/-- **The loop rule.** If an invariant `I` of the loop heads implies `Q`, and every run of the
body from a loop head satisfying `I` (test true) is an `ExecI` run ending in `I`, then the run of
the loop is an `ExecI` run ending in `I` (with the test false). -/
theorem Exec.toExecI_whileLtN {Q I : Config → Prop} {a b : ℕ} {body : Stmt} {c c' : Config}
    {k : ℕ} (h : Exec P W (.whileLtN a b body) c c' k)
    (hbody : ∀ c c₁ k, I c → c.nreg a < c.nreg b → Exec P W body c c₁ k →
      ExecI P Q body c c₁ k ∧ I c₁)
    (hIQ : ∀ c, I c → Q c) (hI : I c) :
    ExecI P Q (.whileLtN a b body) c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b := by
  generalize hw : Stmt.whileLtN a b body = w at h
  induction h with
  | whileLtN_false ht _ =>
    cases hw; exact ⟨.whileLtN_false ht (hIQ _ hI), hI, ht⟩
  | whileLtN_true ht e₁ _ _ ih₂ =>
    cases hw
    obtain ⟨E₁, hI₁⟩ := hbody _ _ _ hI ht e₁
    obtain ⟨E₂, hI₂, hx⟩ := ih₂ hI₁ rfl
    exact ⟨.whileLtN_true ht E₁ E₂, hI₂, hx⟩
  | _ => cases hw

/-- **The loop rule for a real test** (`whileLtR`), as `Exec.toExecI_whileLtN`. -/
theorem Exec.toExecI_whileLtR {Q I : Config → Prop} {a b : ℕ} {body : Stmt} {c c' : Config}
    {k : ℕ} (h : Exec P W (.whileLtR a b body) c c' k)
    (hbody : ∀ c c₁ k, I c → c.rreg a < c.rreg b → Exec P W body c c₁ k →
      ExecI P Q body c c₁ k ∧ I c₁)
    (hIQ : ∀ c, I c → Q c) (hI : I c) :
    ExecI P Q (.whileLtR a b body) c c' k ∧ I c' ∧ ¬ c'.rreg a < c'.rreg b := by
  generalize hw : Stmt.whileLtR a b body = w at h
  induction h with
  | whileLtR_false ht _ =>
    cases hw; exact ⟨.whileLtR_false ht (hIQ _ hI), hI, ht⟩
  | whileLtR_true ht e₁ _ _ ih₂ =>
    cases hw
    obtain ⟨E₁, hI₁⟩ := hbody _ _ _ hI ht e₁
    obtain ⟨E₂, hI₂, hx⟩ := ih₂ hI₁ rfl
    exact ⟨.whileLtR_true ht E₁ E₂, hI₂, hx⟩
  | _ => cases hw

/-- The instructions occurring in a statement. -/
def Stmt.instrs : Stmt → List Instr
  | .skip => []
  | .instr i => [i]
  | .seq s t => s.instrs ++ t.instrs
  | .ifLtN _ _ t e => t.instrs ++ e.instrs
  | .ifLtR _ _ t e => t.instrs ++ e.instrs
  | .whileLtN _ _ body => body.instrs
  | .whileLtR _ _ body => body.instrs

/-- **A predicate kept by every instruction of the statement** holds along every run, loops
included (no loop invariant needed). -/
theorem Exec.toExecI_stepInv {R : Config → Prop} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k)
    (hR : ∀ i ∈ s.instrs, ∀ c c', R c → i.effect P c = some c' → R c') (hc : R c) :
    ExecI P (fun c => WordsBounded W c ∧ R c) s c c' k ∧ R c' := by
  induction h with
  | skip hw => exact ⟨.skip ⟨hw, hc⟩, hc⟩
  | instr hs he hw hw' =>
    have := hR _ (by simp [Stmt.instrs]) _ _ hc he
    exact ⟨.instr hs he ⟨hw, hc⟩ ⟨hw', this⟩, this⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨E₁, h₁⟩ := ih₁ (fun i hi => hR i (by simp [Stmt.instrs, hi])) hc
    obtain ⟨E₂, h₂⟩ := ih₂ (fun i hi => hR i (by simp [Stmt.instrs, hi])) h₁
    exact ⟨.seq E₁ E₂, h₂⟩
  | ifLtN_true ht _ ih =>
    obtain ⟨E, h'⟩ := ih (fun i hi => hR i (by simp [Stmt.instrs, hi])) hc
    exact ⟨.ifLtN_true ht E, h'⟩
  | ifLtN_false ht _ ih =>
    obtain ⟨E, h'⟩ := ih (fun i hi => hR i (by simp [Stmt.instrs, hi])) hc
    exact ⟨.ifLtN_false ht E, h'⟩
  | ifLtR_true ht _ ih =>
    obtain ⟨E, h'⟩ := ih (fun i hi => hR i (by simp [Stmt.instrs, hi])) hc
    exact ⟨.ifLtR_true ht E, h'⟩
  | ifLtR_false ht _ ih =>
    obtain ⟨E, h'⟩ := ih (fun i hi => hR i (by simp [Stmt.instrs, hi])) hc
    exact ⟨.ifLtR_false ht E, h'⟩
  | whileLtN_false ht hw => exact ⟨.whileLtN_false ht ⟨hw, hc⟩, hc⟩
  | whileLtN_true ht _ _ ih₁ ih₂ =>
    obtain ⟨E₁, h₁⟩ := ih₁ (fun i hi => hR i (by simpa [Stmt.instrs] using hi)) hc
    obtain ⟨E₂, h₂⟩ := ih₂ hR h₁
    exact ⟨.whileLtN_true ht E₁ E₂, h₂⟩
  | whileLtR_false ht hw => exact ⟨.whileLtR_false ht ⟨hw, hc⟩, hc⟩
  | whileLtR_true ht _ _ ih₁ ih₂ =>
    obtain ⟨E₁, h₁⟩ := ih₁ (fun i hi => hR i (by simpa [Stmt.instrs] using hi)) hc
    obtain ⟨E₂, h₂⟩ := ih₂ hR h₁
    exact ⟨.whileLtR_true ht E₁ E₂, h₂⟩

/-- An update of a function into the reals bounded by `X` with a value bounded by `X`. -/
theorem intB_upd {X : ℕ} {f : ℕ → ℝ} (hf : ∀ r, ∃ z : ℤ, f r = z ∧ |z| ≤ (X : ℤ)) (i : ℕ)
    {x : ℝ} (hx : ∃ z : ℤ, x = z ∧ |z| ≤ (X : ℤ)) :
    ∀ r, ∃ z : ℤ, upd f i x r = z ∧ |z| ≤ (X : ℤ) := fun r => by
  by_cases h : r = i
  · subst h; simpa using hx
  · rw [upd_other _ _ _ h]; exact hf r

/-- The negation of a value bounded by `X`. -/
theorem intB_neg {X : ℕ} {x : ℝ} (hx : ∃ z : ℤ, x = z ∧ |z| ≤ (X : ℤ)) :
    ∃ z : ℤ, -x = z ∧ |z| ≤ (X : ℤ) :=
  let ⟨z, hz, hb⟩ := hx; ⟨-z, by rw [hz]; push_cast; ring, by rwa [abs_neg]⟩

/-- The sum of values bounded by `X` and `Y`. -/
theorem intB_add {X Y : ℕ} {x y : ℝ} (hx : ∃ z : ℤ, x = z ∧ |z| ≤ (X : ℤ))
    (hy : ∃ z : ℤ, y = z ∧ |z| ≤ (Y : ℤ)) : ∃ z : ℤ, x + y = z ∧ |z| ≤ ((X + Y : ℕ) : ℤ) := by
  obtain ⟨a, ha, hab⟩ := hx; obtain ⟨b, hb, hbb⟩ := hy
  refine ⟨a + b, by rw [ha, hb]; push_cast; ring, ?_⟩
  have := abs_add_le a b; push_cast; linarith

/-- The difference of values bounded by `X` and `Y`. -/
theorem intB_sub {X Y : ℕ} {x y : ℝ} (hx : ∃ z : ℤ, x = z ∧ |z| ≤ (X : ℤ))
    (hy : ∃ z : ℤ, y = z ∧ |z| ≤ (Y : ℤ)) : ∃ z : ℤ, x - y = z ∧ |z| ≤ ((X + Y : ℕ) : ℤ) := by
  have := intB_add hx (intB_neg hy); rwa [← sub_eq_add_neg] at this

/-- A bound `X ≤ Y`. -/
theorem intB_mono {X Y : ℕ} {x : ℝ} (hx : ∃ z : ℤ, x = z ∧ |z| ≤ (X : ℤ)) (h : X ≤ Y) :
    ∃ z : ℤ, x = z ∧ |z| ≤ (Y : ℤ) :=
  let ⟨z, hz, hb⟩ := hx; ⟨z, hz, hb.trans (by exact_mod_cast h)⟩

/-- No real arithmetic (`addR`, `subR`, `mulR`, `divR`), real constants bounded by `Bc`. -/
def _root_.WordRAM.Instr.NoArith (Bc : ℕ) (i : Instr) : Prop := i.LinR Bc ∧ i.addCount = 0

instance (Bc : ℕ) (i : Instr) : Decidable (i.NoArith Bc) := by
  unfold Instr.NoArith Instr.LinR Instr.addCount; cases i <;> infer_instance

/-- A statement without real arithmetic, real constants bounded by `Bc` (loops allowed). -/
def Stmt.ArithFree (Bc : ℕ) (s : Stmt) : Prop := ∀ i ∈ s.instrs, i.NoArith Bc

instance (Bc : ℕ) (s : Stmt) : Decidable (s.ArithFree Bc) := by
  unfold Stmt.ArithFree; infer_instance

/-- **Statements without real arithmetic** keep any bound `X ≥ Bc` of the reals along every run,
loops included. -/
theorem Exec.toExecI_arithFree {s : Stmt} {c c' : Config} {k : ℕ} {Bc X : ℕ}
    (h : Exec P W s c c' k) (hs : s.ArithFree Bc) (hX : Bc ≤ X) (hc : RealsIntBounded X c) :
    ExecI P (fun c => WordsBounded W c ∧ RealsIntBounded X c) s c c' k ∧
      RealsIntBounded X c' :=
  h.toExecI_stepInv (fun i hi c c' hc he => by
    have := Instr.rib_effect (hs i hi).1 hX he hc
    rwa [(hs i hi).2, pow_zero, one_mul] at this) hc

end tools

end Machine

end WordRAM
