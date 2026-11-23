module

public import WordRAM.Spec
public import WordRAM.Machine.Structured
public import WordRAM.Machine.KernelRfl

/-!
# Word programs

`WordRAM.Program.IsWord prog` (`WordRAM/Spec.lean`): `prog` contains no real instruction.

* `Program.isWord_of_all`: for a concrete flat program the property is the finite check
  `prog.all (fun i => !i.isReal) = true`.
* `Stmt.wordOnly s`: the structured statement `s` has no real instruction and no real test;
  `Stmt.compile_wordOnly`: its compiled code then has no real instruction, at every base address;
  **`Stmt.isWord_compile_halt`**: `compile s 0 ++ [halt]` is a word program. For a concrete
  statement the check `s.wordOnly = true` is closed by `kernel_rfl`; it is linear in the size of
  `s`, unlike a check on the compiled code, whose addresses recompute code sizes.
-/

@[expose] public section

namespace WordRAM

/-- A program all of whose instructions pass the Boolean check is a word program. -/
theorem Program.isWord_of_all {prog : Program} (h : prog.all (fun i => !i.isReal) = true) :
    prog.IsWord := by
  intro i hi
  simpa using List.all_eq_true.mp h i hi

namespace Machine

open Stmt

/-- No real instruction and no real test. -/
def Stmt.wordOnly : Stmt → Bool
  | .skip => true
  | .instr i => !i.isReal
  | .seq s t => wordOnly s && wordOnly t
  | .ifLtN _ _ t e => wordOnly t && wordOnly e
  | .ifLtR _ _ _ _ => false
  | .whileLtN _ _ b => wordOnly b
  | .whileLtR _ _ _ => false

/-- **The compiled code of a statement without reals has no real instruction.** -/
theorem Stmt.compile_wordOnly : ∀ (s : Stmt), s.wordOnly = true →
    ∀ base, ∀ j ∈ compile s base, j.isReal = false
  | .skip, _, _, j, hj => by simp [compile] at hj
  | .instr i, h, _, j, hj => by
    simp only [compile, List.mem_singleton] at hj
    subst hj
    simpa [wordOnly] using h
  | .seq s t, h, base, j, hj => by
    simp only [wordOnly, Bool.and_eq_true] at h
    simp only [compile, List.mem_append] at hj
    rcases hj with hj | hj
    · exact compile_wordOnly s h.1 _ j hj
    · exact compile_wordOnly t h.2 _ j hj
  | .ifLtN a b t e, h, base, j, hj => by
    simp only [wordOnly, Bool.and_eq_true] at h
    simp only [compile, List.mem_append, List.mem_cons] at hj
    rcases hj with (rfl | hj) | (rfl | hj)
    · rfl
    · exact compile_wordOnly e h.2 _ j hj
    · rfl
    · exact compile_wordOnly t h.1 _ j hj
  | .ifLtR _ _ _ _, h, _, _, _ => by simp [wordOnly] at h
  | .whileLtN a b body, h, base, j, hj => by
    simp only [wordOnly] at h
    simp only [compile, List.mem_append, List.mem_cons] at hj
    rcases hj with (rfl | rfl | hj) | hj
    · rfl
    · rfl
    · exact compile_wordOnly body h _ j hj
    · simp at hj; subst hj; rfl
  | .whileLtR _ _ _, h, _, _, _ => by simp [wordOnly] at h

/-- **A compiled statement without reals, followed by `halt`, is a word program.** -/
theorem Stmt.isWord_compile_halt {s : Stmt} (h : s.wordOnly = true) :
    Program.IsWord (compile s 0 ++ [Instr.halt]) := by
  intro j hj
  rcases List.mem_append.mp hj with hj | hj
  · exact Stmt.compile_wordOnly s h 0 j hj
  · simp at hj; subst hj; rfl

end Machine

end WordRAM

end
