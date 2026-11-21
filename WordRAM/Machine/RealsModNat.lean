module

public import WordRAM.Machine.WordMono
public import WordRAM.Machine.RealsToNat

/-!
# Exact integer reals simulated by natural words modulo `M`

The machine of `WordRAM/Spec.lean` keeps reals in exact registers. A program whose real values
are all **integers** and whose real operations are `constR`, `copyR`, `addR`, `subR`, `mulR`,
`loadR`, `storeR` and the comparisons `ifLtR` / `whileLtR` (no `divR`) can be run on natural
words holding its real values **modulo `M`**: additions, subtractions and multiplications are
exact modulo `M` (`addN`/`subN`/`mulN` followed by `modN`), copies, loads and stores are
copies, and a comparison `x < y` is decided by the residue `t = (x - y) mod M`: if
`|x - y| ≤ H` and `2 H < M`, then `x < y ↔ H < t`. **The value bounds are needed only at the
comparisons**, never at the other steps: a real value may grow arbitrarily between two
comparisons, only its residue is kept.

* `ExecCmp P W H s c c' k`: `Exec` (`WordRAM/Machine/Structured.lean`) with, at every executed
  real test `rreg a < rreg b`, the bound `|rreg a - rreg b| ≤ H`. `ExecCmp.toExec` forgets it;
  `Exec.toCmp` adds it for free to a statement without real tests (`Stmt.noTestR`).
* `CmpOK P W H s c`: every execution of `s` from `c`
  is compare-bounded; the rules `CmpOK.seq`, `CmpOK.ifLtN`, `CmpOK.ifLtR`, `CmpOK.whileLtN`,
  `CmpOK.whileLtR` (with an invariant preserved along the actual runs of the body) and
  `cmpOK_of_noTestR` prove it compositionally from the existing realization lemmas, which give the
  intermediate configurations (with the determinism of executions,
  `WordRAM.Machine.Exec.det` of `WordRAM/Machine/RealsToNat.lean`). `Stmt.noDivR` is that of
  `RealsToNat.lean`; `RealsToNat.lean` simulates with value bounds at **every** visited
  configuration (sign–magnitude pairs), this file only at the comparisons.
* `toNat R M s`: the transformed statement. Natural registers `< R` are kept, the real register
  `r < R` becomes the natural register `R + r`, the real memory cell `a` becomes the natural
  memory cell `β + a`; the registers `2R`, `2R + 1`, `2R + 2` hold `M`, `H`, `β` (`Consts`, set
  by `constsS`), `2R + 3` is scratch.
* `Sim R W M β c d`: `d` simulates `c`: same natural registers `< R`, same natural memory at
  addresses `≤ W`, and the residues modulo `M` of the (integer) real registers `< R` and real
  memory cells at addresses `≤ W` (`Res`).
* **`ExecCmp.toNat`** (the simulation theorem): if `s` names only registers `< R`, has no
  `divR`, and runs compare-bounded `ExecCmp P W H s c c' k` with `2H < M`, `W < β`, then from any
  `d` with `Sim R W M β c d`, the constants in place and `WordsBounded W' d`, where
  `W ≤ W'`, `β + W ≤ W'`, `M² + M ≤ W'`, the statement `toNat R M s` runs
  `Exec P W' (toNat R M s) d d' k'` with `k' ≤ 4 k`, ending with `Sim R W M β c' d'`, and it
  changes no natural register `≥ 2R` other than the scratch `2R + 3`, no natural memory cell
  outside `[0, W] ∪ [β, β + W]`, and no real register or real memory cell (`Frame`).
-/

namespace WordRAM

namespace Machine

namespace Stmt

@[expose] public section

/-- No real test (`ifLtR`, `whileLtR`) in the statement. -/
def noTestR : Stmt → Bool
  | .skip => true
  | .instr _ => true
  | .seq s t => noTestR s && noTestR t
  | .ifLtN _ _ t e => noTestR t && noTestR e
  | .ifLtR _ _ _ _ => false
  | .whileLtN _ _ body => noTestR body
  | .whileLtR _ _ _ => false

@[simp] theorem noTestR_block (l : List Instr) : noTestR (block l) = true := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [block, noTestR, ih]

@[simp] theorem noDivR_block (l : List Instr) : noDivR (block l) = l.all Instr.noDivR := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [block, noDivR, ih]

end

end Stmt

namespace ModNat

@[expose] public section

open Stmt

/-! ### Compare-bounded executions -/

/-- `Exec P W s c c' k` with the bound `|rreg a - rreg b| ≤ H` at every executed real test. -/
inductive ExecCmp (P : Input) (W H : ℕ) : Stmt → Config → Config → ℕ → Prop
  | skip {c : Config} : WordsBounded W c → ExecCmp P W H .skip c c 0
  | instr {ins : Instr} {c c' : Config} : ins.IsStraight → ins.effect P c = some c' →
      WordsBounded W c → WordsBounded W c' → ExecCmp P W H (.instr ins) c c' 1
  | seq {s t : Stmt} {c c₁ c₂ : Config} {k₁ k₂ : ℕ} :
      ExecCmp P W H s c c₁ k₁ → ExecCmp P W H t c₁ c₂ k₂ → ExecCmp P W H (.seq s t) c c₂ (k₁ + k₂)
  | ifLtN_true {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : c.nreg a < c.nreg b →
      ExecCmp P W H t c c' k → ExecCmp P W H (.ifLtN a b t e) c c' (k + 1)
  | ifLtN_false {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : ¬ c.nreg a < c.nreg b →
      ExecCmp P W H e c c' k → ExecCmp P W H (.ifLtN a b t e) c c' (k + 2)
  | ifLtR_true {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} :
      |c.rreg a - c.rreg b| ≤ H → c.rreg a < c.rreg b →
      ExecCmp P W H t c c' k → ExecCmp P W H (.ifLtR a b t e) c c' (k + 1)
  | ifLtR_false {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} :
      |c.rreg a - c.rreg b| ≤ H → ¬ c.rreg a < c.rreg b →
      ExecCmp P W H e c c' k → ExecCmp P W H (.ifLtR a b t e) c c' (k + 2)
  | whileLtN_false {a b : ℕ} {body : Stmt} {c : Config} : ¬ c.nreg a < c.nreg b →
      WordsBounded W c → ExecCmp P W H (.whileLtN a b body) c c 2
  | whileLtN_true {a b : ℕ} {body : Stmt} {c c₁ c' : Config} {k₁ k₂ : ℕ} : c.nreg a < c.nreg b →
      ExecCmp P W H body c c₁ k₁ → ExecCmp P W H (.whileLtN a b body) c₁ c' k₂ →
      ExecCmp P W H (.whileLtN a b body) c c' (k₁ + 2 + k₂)
  | whileLtR_false {a b : ℕ} {body : Stmt} {c : Config} :
      |c.rreg a - c.rreg b| ≤ H → ¬ c.rreg a < c.rreg b →
      WordsBounded W c → ExecCmp P W H (.whileLtR a b body) c c 2
  | whileLtR_true {a b : ℕ} {body : Stmt} {c c₁ c' : Config} {k₁ k₂ : ℕ} :
      |c.rreg a - c.rreg b| ≤ H → c.rreg a < c.rreg b →
      ExecCmp P W H body c c₁ k₁ → ExecCmp P W H (.whileLtR a b body) c₁ c' k₂ →
      ExecCmp P W H (.whileLtR a b body) c c' (k₁ + 2 + k₂)

variable {P : Input} {W H : ℕ}

/-- Forget the comparison bounds. -/
theorem ExecCmp.toExec {s : Stmt} {c c' : Config} {k : ℕ} (h : ExecCmp P W H s c c' k) :
    Exec P W s c c' k := by
  induction h with
  | skip hw => exact .skip hw
  | instr hs he hw hw' => exact .instr hs he hw hw'
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifLtN_true ht _ ih => exact .ifLtN_true ht ih
  | ifLtN_false ht _ ih => exact .ifLtN_false ht ih
  | ifLtR_true _ ht _ ih => exact .ifLtR_true ht ih
  | ifLtR_false _ ht _ ih => exact .ifLtR_false ht ih
  | whileLtN_false ht hw => exact .whileLtN_false ht hw
  | whileLtN_true ht _ _ ih₁ ih₂ => exact .whileLtN_true ht ih₁ ih₂
  | whileLtR_false _ ht hw => exact .whileLtR_false ht hw
  | whileLtR_true _ ht _ _ ih₁ ih₂ => exact .whileLtR_true ht ih₁ ih₂

/-- Raise the comparison bound. -/
theorem ExecCmp.mono_H {s : Stmt} {c c' : Config} {k H' : ℕ} (h : ExecCmp P W H s c c' k)
    (hH : H ≤ H') : ExecCmp P W H' s c c' k := by
  have hH' : (H : ℝ) ≤ H' := by exact_mod_cast hH
  induction h with
  | skip hw => exact .skip hw
  | instr hs he hw hw' => exact .instr hs he hw hw'
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifLtN_true ht _ ih => exact .ifLtN_true ht ih
  | ifLtN_false ht _ ih => exact .ifLtN_false ht ih
  | ifLtR_true hb ht _ ih => exact .ifLtR_true (hb.trans hH') ht ih
  | ifLtR_false hb ht _ ih => exact .ifLtR_false (hb.trans hH') ht ih
  | whileLtN_false ht hw => exact .whileLtN_false ht hw
  | whileLtN_true ht _ _ ih₁ ih₂ => exact .whileLtN_true ht ih₁ ih₂
  | whileLtR_false hb ht hw => exact .whileLtR_false (hb.trans hH') ht hw
  | whileLtR_true hb ht _ _ ih₁ ih₂ => exact .whileLtR_true (hb.trans hH') ht ih₁ ih₂

/-- A statement without real tests: every execution is compare-bounded. -/
theorem Exec.toCmp {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k)
    (hs : s.noTestR = true) : ExecCmp P W H s c c' k := by
  induction h with
  | skip hw => exact .skip hw
  | instr hi he hw hw' => exact .instr hi he hw hw'
  | seq _ _ ih₁ ih₂ =>
    simp only [noTestR, Bool.and_eq_true] at hs
    exact .seq (ih₁ hs.1) (ih₂ hs.2)
  | ifLtN_true ht _ ih =>
    simp only [noTestR, Bool.and_eq_true] at hs
    exact .ifLtN_true ht (ih hs.1)
  | ifLtN_false ht _ ih =>
    simp only [noTestR, Bool.and_eq_true] at hs
    exact .ifLtN_false ht (ih hs.2)
  | ifLtR_true => simp [noTestR] at hs
  | ifLtR_false => simp [noTestR] at hs
  | whileLtN_false ht hw => exact .whileLtN_false ht hw
  | whileLtN_true ht _ _ ih₁ ih₂ =>
    simp only [noTestR] at hs
    exact .whileLtN_true ht (ih₁ hs) (ih₂ hs)
  | whileLtR_false => simp [noTestR] at hs
  | whileLtR_true => simp [noTestR] at hs

/-! ### Compare-boundedness of all the executions from a configuration -/

/-- Every execution of `s` from `c` is compare-bounded by `H`. -/
def CmpOK (P : Input) (W H : ℕ) (s : Stmt) (c : Config) : Prop :=
  ∀ c' k, Exec P W s c c' k → ExecCmp P W H s c c' k

theorem CmpOK.exec {s : Stmt} {c c' : Config} {k : ℕ} (h : CmpOK P W H s c)
    (e : Exec P W s c c' k) : ExecCmp P W H s c c' k := h c' k e

theorem cmpOK_of_noTestR {s : Stmt} (hs : s.noTestR = true) (c : Config) : CmpOK P W H s c :=
  fun _ _ e => Exec.toCmp e hs

theorem CmpOK.seq {s t : Stmt} {c : Config} (hs : CmpOK P W H s c)
    (ht : ∀ c₁ k₁, Exec P W s c c₁ k₁ → CmpOK P W H t c₁) : CmpOK P W H (.seq s t) c := by
  intro c' k e
  cases e with
  | seq e₁ e₂ => exact .seq (hs _ _ e₁) (ht _ _ e₁ _ _ e₂)

theorem CmpOK.ifLtN {a b : ℕ} {t e : Stmt} {c : Config}
    (ht : c.nreg a < c.nreg b → CmpOK P W H t c) (he : ¬ c.nreg a < c.nreg b → CmpOK P W H e c) :
    CmpOK P W H (.ifLtN a b t e) c := by
  intro c' k ex
  cases ex with
  | ifLtN_true h e₁ => exact .ifLtN_true h (ht h _ _ e₁)
  | ifLtN_false h e₁ => exact .ifLtN_false h (he h _ _ e₁)

theorem CmpOK.ifLtR {a b : ℕ} {t e : Stmt} {c : Config} (hb : |c.rreg a - c.rreg b| ≤ H)
    (ht : c.rreg a < c.rreg b → CmpOK P W H t c) (he : ¬ c.rreg a < c.rreg b → CmpOK P W H e c) :
    CmpOK P W H (.ifLtR a b t e) c := by
  intro c' k ex
  cases ex with
  | ifLtR_true h e₁ => exact .ifLtR_true hb h (ht h _ _ e₁)
  | ifLtR_false h e₁ => exact .ifLtR_false hb h (he h _ _ e₁)

/-- The loop rule: an invariant `I` such that, from a state of `I` with the test true, the body
is compare-bounded and every execution of the body ends in a state of `I`. -/
theorem CmpOK.whileLtN {a b : ℕ} {body : Stmt} (I : Config → Prop)
    (hI : ∀ c, I c → c.nreg a < c.nreg b →
      CmpOK P W H body c ∧ ∀ c₁ k, Exec P W body c c₁ k → I c₁)
    {c : Config} (hc : I c) : CmpOK P W H (.whileLtN a b body) c := by
  intro c' k ex
  generalize hs : Stmt.whileLtN a b body = s at ex
  induction ex with
  | whileLtN_false h hw =>
    cases hs; exact .whileLtN_false h hw
  | whileLtN_true h e₁ _ _ ih₂ =>
    cases hs
    obtain ⟨hb, hp⟩ := hI _ hc h
    exact .whileLtN_true h (hb _ _ e₁) (ih₂ (hp _ _ e₁) rfl)
  | _ => cases hs

/-- The loop rule for a real test: in addition, the test is bounded in every state of `I`. -/
theorem CmpOK.whileLtR {a b : ℕ} {body : Stmt} (I : Config → Prop)
    (hB : ∀ c, I c → |c.rreg a - c.rreg b| ≤ H)
    (hI : ∀ c, I c → c.rreg a < c.rreg b →
      CmpOK P W H body c ∧ ∀ c₁ k, Exec P W body c c₁ k → I c₁)
    {c : Config} (hc : I c) : CmpOK P W H (.whileLtR a b body) c := by
  intro c' k ex
  generalize hs : Stmt.whileLtR a b body = s at ex
  induction ex with
  | whileLtR_false h hw =>
    cases hs; exact .whileLtR_false (hB _ hc) h hw
  | whileLtR_true h e₁ _ _ ih₂ =>
    cases hs
    obtain ⟨hb, hp⟩ := hI _ hc h
    exact .whileLtR_true (hB _ hc) h (hb _ _ e₁) (ih₂ (hp _ _ e₁) rfl)
  | _ => cases hs

/-- A compare-bounded run from a realization lemma and `CmpOK`. -/
theorem CmpOK.of_exists {s : Stmt} {c : Config} {Q : Config → ℕ → Prop}
    (h : ∃ c' k, Exec P W s c c' k ∧ Q c' k) (hc : CmpOK P W H s c) :
    ∃ c' k, ExecCmp P W H s c c' k ∧ Q c' k := by
  obtain ⟨c', k, e, hq⟩ := h
  exact ⟨c', k, hc _ _ e, hq⟩

/-! ### Residues -/

/-- `v` is the residue modulo `M` of the real `x`, which is an integer. -/
def Res (M : ℕ) (x : ℝ) (v : ℕ) : Prop := ∃ z : ℤ, x = z ∧ (v : ℤ) = z % (M : ℤ)

theorem Res.lt {M : ℕ} {x : ℝ} {v : ℕ} (hM : 0 < M) (h : Res M x v) : v < M := by
  obtain ⟨z, -, hv⟩ := h
  have h1 := Int.emod_lt_of_pos z (show (0 : ℤ) < M by exact_mod_cast hM)
  have h2 : (v : ℤ) < M := hv ▸ h1
  exact_mod_cast h2

theorem res_const {M : ℕ} (hM : 0 < M) (z : ℤ) : Res M (z : ℝ) (z % (M : ℤ)).toNat :=
  ⟨z, rfl, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hM.ne'))⟩

theorem res_add {M : ℕ} {x y : ℝ} {A B : ℕ} (hx : Res M x A) (hy : Res M y B) :
    Res M (x + y) ((A + B) % M) := by
  obtain ⟨z₁, rfl, h₁⟩ := hx
  obtain ⟨z₂, rfl, h₂⟩ := hy
  refine ⟨z₁ + z₂, by push_cast; rfl, ?_⟩
  push_cast
  rw [h₁, h₂, ← Int.add_emod]

theorem res_mul {M : ℕ} {x y : ℝ} {A B : ℕ} (hx : Res M x A) (hy : Res M y B) :
    Res M (x * y) ((A * B) % M) := by
  obtain ⟨z₁, rfl, h₁⟩ := hx
  obtain ⟨z₂, rfl, h₂⟩ := hy
  refine ⟨z₁ * z₂, by push_cast; rfl, ?_⟩
  push_cast
  rw [h₁, h₂, ← Int.mul_emod]

theorem res_sub {M : ℕ} (hM : 0 < M) {x y : ℝ} {A B : ℕ} (hx : Res M x A) (hy : Res M y B) :
    Res M (x - y) ((A + (M - B)) % M) := by
  have hB := hy.lt hM
  obtain ⟨z₁, rfl, h₁⟩ := hx
  obtain ⟨z₂, rfl, h₂⟩ := hy
  refine ⟨z₁ - z₂, by push_cast; rfl, ?_⟩
  have e : ((A + (M - B) : ℕ) : ℤ) = ((A : ℤ) - B) + M := by
    rw [Nat.cast_add, Nat.cast_sub hB.le]; omega
  rw [Int.natCast_mod, e, Int.add_emod_right, h₁, h₂, ← Int.sub_emod]

/-- **The comparison by residues**: if `|x - y| ≤ H < M - H`, then `x < y` iff the residue of
`x - y` exceeds `H`. -/
theorem res_cmp {M H : ℕ} (hM : 2 * H < M) {x y : ℝ} {A B : ℕ} (hx : Res M x A)
    (hy : Res M y B) (hb : |x - y| ≤ H) : x < y ↔ H < (A + (M - B)) % M := by
  have hM0 : 0 < M := by omega
  obtain ⟨z, hz, ht⟩ := res_sub hM0 hx hy
  rw [hz] at hb
  have hb' : |z| ≤ (H : ℤ) := by exact_mod_cast hb
  have hlt : x < y ↔ z < 0 := by
    rw [← sub_neg, hz]
    exact_mod_cast Iff.rfl
  rw [hlt]
  rw [abs_le] at hb'
  have hMz : (0 : ℤ) < M := by exact_mod_cast hM0
  have hHM : (2 * H : ℤ) < M := by exact_mod_cast hM
  constructor
  · intro hz0
    have e : z % (M : ℤ) = z + M := by
      rw [← Int.add_emod_right]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    have : ((H : ℕ) : ℤ) < (((A + (M - B)) % M : ℕ) : ℤ) := by rw [ht, e]; omega
    exact_mod_cast this
  · intro hH
    by_contra hz0
    have e : z % (M : ℤ) = z := Int.emod_eq_of_lt (by omega) (by omega)
    have : (((A + (M - B)) % M : ℕ) : ℤ) ≤ ((H : ℕ) : ℤ) := by rw [ht, e]; omega
    have : (A + (M - B)) % M ≤ H := by exact_mod_cast this
    omega

/-! ### The transformation -/

/-- One instruction on natural words: the real register `r` is the natural register `R + r`,
the real memory cell `a` the natural memory cell `β + a` (`β` in the register `2R + 2`), the
modulus `M` in the register `2R`; `2R + 3` is scratch. -/
def trI (R M : ℕ) : Instr → Stmt
  | .constR r z => .instr (.constN (R + r) (z % (M : ℤ)).toNat)
  | .copyR r a => .instr (.copyN (R + r) (R + a))
  | .addR r a b => block [.addN (2 * R + 3) (R + a) (R + b), .modN (R + r) (2 * R + 3) (2 * R)]
  | .subR r a b => block [.subN (2 * R + 3) (2 * R) (R + b),
      .addN (2 * R + 3) (R + a) (2 * R + 3), .modN (R + r) (2 * R + 3) (2 * R)]
  | .mulR r a b => block [.mulN (2 * R + 3) (R + a) (R + b), .modN (R + r) (2 * R + 3) (2 * R)]
  | .loadR r a => block [.addN (2 * R + 3) a (2 * R + 2), .loadN (R + r) (2 * R + 3)]
  | .storeR a r => block [.addN (2 * R + 3) a (2 * R + 2), .storeN (2 * R + 3) (R + r)]
  | i => .instr i

/-- `r(2R+3) := (r(R+a) - r(R+b)) mod M`, the residue compared with `H` (in `2R + 1`). -/
def cmpS (R a b : ℕ) : Stmt :=
  block [.subN (2 * R + 3) (2 * R) (R + b), .addN (2 * R + 3) (R + a) (2 * R + 3),
    .modN (2 * R + 3) (2 * R + 3) (2 * R)]

/-- **The statement on natural words.** A real test `rreg a < rreg b` becomes `cmpS` followed by
the natural test `H < r(2R+3)`; a real loop recomputes the residue at the end of its body. -/
def toNat (R M : ℕ) : Stmt → Stmt
  | .skip => .skip
  | .instr i => trI R M i
  | .seq s t => .seq (toNat R M s) (toNat R M t)
  | .ifLtN a b t e => .ifLtN a b (toNat R M t) (toNat R M e)
  | .ifLtR a b t e => .seq (cmpS R a b) (.ifLtN (2 * R + 1) (2 * R + 3) (toNat R M t) (toNat R M e))
  | .whileLtN a b body => .whileLtN a b (toNat R M body)
  | .whileLtR a b body => .seq (cmpS R a b)
      (.whileLtN (2 * R + 1) (2 * R + 3) (.seq (toNat R M body) (cmpS R a b)))

/-- The constants `M`, `H`, `β` into the registers `2R`, `2R + 1`, `2R + 2`. -/
def constsS (R M H β : ℕ) : Stmt :=
  block [.constN (2 * R) M, .constN (2 * R + 1) H, .constN (2 * R + 2) β]

/-! ### The simulation relation -/

/-- `d` simulates `c`: the natural registers `< R` and the natural memory at addresses `≤ W`
agree, and `d` holds the residues modulo `M` of the integer real registers `< R` (at `R + r`) and
real memory cells at addresses `≤ W` (at `β + a`); the outputs agree. -/
structure Sim (R W M β : ℕ) (c d : Config) : Prop where
  nreg : ∀ r, r < R → d.nreg r = c.nreg r
  rreg : ∀ r, r < R → Res M (c.rreg r) (d.nreg (R + r))
  nmem : ∀ a, a ≤ W → d.nmem a = c.nmem a
  rmem : ∀ a, a ≤ W → Res M (c.rmem a) (d.nmem (β + a))
  output : d.output = c.output

/-- The constants in their registers. -/
structure Consts (R M H β : ℕ) (d : Config) : Prop where
  m : d.nreg (2 * R) = M
  h : d.nreg (2 * R + 1) = H
  b : d.nreg (2 * R + 2) = β

/-- What the simulating run keeps: the natural registers `≥ 2R` other than the scratch
`2R + 3`, the natural memory outside `[0, W] ∪ [β, β + W]`, the real registers and memory. -/
structure Frame (R W β : ℕ) (d d' : Config) : Prop where
  nreg : ∀ r, 2 * R ≤ r → r ≠ 2 * R + 3 → d'.nreg r = d.nreg r
  nmem : ∀ a, W < a → (a < β ∨ β + W < a) → d'.nmem a = d.nmem a
  rreg : d'.rreg = d.rreg
  rmem : d'.rmem = d.rmem

theorem Frame.refl (R W β : ℕ) (d : Config) : Frame R W β d d :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl⟩

theorem Frame.trans {R W β : ℕ} {d₁ d₂ d₃ : Config} (h₁ : Frame R W β d₁ d₂)
    (h₂ : Frame R W β d₂ d₃) : Frame R W β d₁ d₃ :=
  ⟨fun r h h' => (h₂.nreg r h h').trans (h₁.nreg r h h'),
    fun a h h' => (h₂.nmem a h h').trans (h₁.nmem a h h'), h₂.rreg.trans h₁.rreg,
    h₂.rmem.trans h₁.rmem⟩

theorem Frame.consts {R W β M H : ℕ} {d d' : Config} (hf : Frame R W β d d')
    (hK : Consts R M H β d) : Consts R M H β d' :=
  ⟨(hf.nreg _ le_rfl (by omega)).trans hK.m, (hf.nreg _ (by omega) (by omega)).trans hK.h,
    (hf.nreg _ (by omega) (by omega)).trans hK.b⟩

theorem Frame.updN {R W β : ℕ} (d : Config) {r : ℕ} (hr : r < 2 * R ∨ r = 2 * R + 3) (v : ℕ) :
    Frame R W β d { d with nreg := upd d.nreg r v } :=
  ⟨fun r' h h' => upd_other _ _ _ (by omega), fun _ _ _ => rfl, rfl, rfl⟩

theorem Frame.storeN {R W β : ℕ} (d : Config) {a : ℕ} (ha : a ≤ W ∨ (β ≤ a ∧ a ≤ β + W))
    (v : ℕ) : Frame R W β d { d with nmem := upd d.nmem a v } :=
  ⟨fun _ _ _ => rfl, fun a' h h' => upd_other _ _ _ (by omega), rfl, rfl⟩

theorem Frame.out {R W β : ℕ} (d : Config) (l : List ℕ) :
    Frame R W β d { d with output := l } :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl⟩

section SimUpd

variable {R W M β : ℕ} {c d : Config}

theorem Sim.updN (hS : Sim R W M β c d) {r : ℕ} (hr : r < R) {v v' : ℕ} (hv : v' = v) :
    Sim R W M β { c with nreg := upd c.nreg r v } { d with nreg := upd d.nreg r v' } := by
  refine ⟨fun r' hr' => ?_, fun r' hr' => ?_, hS.nmem, hS.rmem, hS.output⟩
  · by_cases h : r' = r
    · subst h; simp only [upd_same]; exact hv
    · simp only [upd_other _ _ _ h]; exact hS.nreg r' hr'
  · simp only [upd_other _ _ _ (show R + r' ≠ r by omega)]; exact hS.rreg r' hr'

theorem Sim.storeN (hS : Sim R W M β c d) (hβ : W < β) {a : ℕ} (ha : a ≤ W) {v v' : ℕ}
    (hv : v' = v) :
    Sim R W M β { c with nmem := upd c.nmem a v } { d with nmem := upd d.nmem a v' } := by
  refine ⟨hS.nreg, hS.rreg, fun a' ha' => ?_, fun a' ha' => ?_, hS.output⟩
  · by_cases h : a' = a
    · subst h; simp only [upd_same]; exact hv
    · simp only [upd_other _ _ _ h]; exact hS.nmem a' ha'
  · simp only [upd_other _ _ _ (show β + a' ≠ a by omega)]; exact hS.rmem a' ha'

theorem Sim.updR (hS : Sim R W M β c d) {r : ℕ} (hr : r < R) {x : ℝ} {v : ℕ} (hx : Res M x v) :
    Sim R W M β { c with rreg := upd c.rreg r x } { d with nreg := upd d.nreg (R + r) v } := by
  refine ⟨fun r' hr' => ?_, fun r' hr' => ?_, hS.nmem, hS.rmem, hS.output⟩
  · simp only [upd_other _ _ _ (show r' ≠ R + r by omega)]; exact hS.nreg r' hr'
  · by_cases h : r' = r
    · subst h; simp only [upd_same]; exact hx
    · simp only [upd_other _ _ _ h, upd_other _ _ _ (show R + r' ≠ R + r by omega)]
      exact hS.rreg r' hr'

theorem Sim.storeR (hS : Sim R W M β c d) (hβ : W < β) {a : ℕ} (ha : a ≤ W) {x : ℝ} {v : ℕ}
    (hx : Res M x v) {a' : ℕ} (ha' : a' = β + a) :
    Sim R W M β { c with rmem := upd c.rmem a x } { d with nmem := upd d.nmem a' v } := by
  subst ha'
  refine ⟨hS.nreg, hS.rreg, fun b hb => ?_, fun b hb => ?_, hS.output⟩
  · simp only [upd_other _ _ _ (show b ≠ β + a by omega)]; exact hS.nmem b hb
  · by_cases h : b = a
    · subst h; simp only [upd_same]; exact hx
    · simp only [upd_other _ _ _ h, upd_other _ _ _ (show β + b ≠ β + a by omega)]
      exact hS.rmem b hb

theorem Sim.updT (hS : Sim R W M β c d) {t : ℕ} (ht : 2 * R ≤ t) (v : ℕ) :
    Sim R W M β c { d with nreg := upd d.nreg t v } :=
  ⟨fun r hr => by simp only [upd_other _ _ _ (show r ≠ t by omega)]; exact hS.nreg r hr,
    fun r hr => by simp only [upd_other _ _ _ (show R + r ≠ t by omega)]; exact hS.rreg r hr,
    hS.nmem, hS.rmem, hS.output⟩

theorem Sim.out (hS : Sim R W M β c d) {x y : ℕ} (hxy : y = x) :
    Sim R W M β { c with output := c.output ++ [x] } { d with output := d.output ++ [y] } :=
  ⟨hS.nreg, hS.rreg, hS.nmem, hS.rmem, by simp only [hS.output, hxy]⟩

end SimUpd

/-! ### One instruction -/

section OneInstr

lemma add_le_sq {M A B : ℕ} (hA : A < M) (hB : B ≤ M) : A + B ≤ M * M + M := by
  have h := Nat.le_mul_self M
  generalize M * M = m at *
  omega

variable {P : Input} {W H W' R M β : ℕ} {c c' d : Config}

/-- **One straight-line instruction on natural words**, at most `3` instructions. -/
theorem sim_instr {ins : Instr} (hs : ins.IsStraight) (he : ins.effect P c = some c')
    (hwc : WordsBounded W c) (hwc' : WordsBounded W c')
    (hok : ins.regsOK (fun r => decide (r < R)) = true) (hD : ins.noDivR = true)
    (hM : 0 < M) (hβ : W < β) (hW1 : W ≤ W') (hW2 : β + W ≤ W') (hW3 : M * M + M ≤ W')
    (hS : Sim R W M β c d) (hK : Consts R M H β d) (hd : WordsBounded W' d) :
    ∃ d' k', Exec P W' (trI R M ins) d d' k' ∧ k' ≤ 3 ∧ Sim R W M β c' d' ∧
      Frame R W β d d' := by
  have hT : 2 * R ≤ 2 * R + 3 := by omega
  cases ins with
  | halt => simp [Instr.IsStraight, Instr.isControl] at hs
  | jump => simp [Instr.IsStraight, Instr.isControl] at hs
  | brLtN => simp [Instr.IsStraight, Instr.isControl] at hs
  | brLtR => simp [Instr.IsStraight, Instr.isControl] at hs
  | divR => simp [Instr.noDivR] at hD
  | inputSize r =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      decide_eq_true_eq] at hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have hv : P.data.length ≤ W := by simpa using hwc'.1 r
    exact ⟨_, _, Exec.inputSize hd r (hv.trans hW1), le_of_lt (by omega), hS.updN hok rfl,
      Frame.updN d (Or.inl (by omega)) _⟩
  | constN r k =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      decide_eq_true_eq] at hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have hv : k ≤ W := by simpa using hwc'.1 r
    exact ⟨_, _, Exec.constN hd r k (hv.trans hW1), le_of_lt (by omega), hS.updN hok rfl,
      Frame.updN d (Or.inl (by omega)) _⟩
  | copyN r a =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    exact ⟨_, _, Exec.copyN hd r a, le_of_lt (by omega), hS.updN hok.1 (hS.nreg a hok.2),
      Frame.updN d (Or.inl (by omega)) _⟩
  | addN r a b =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hr, ha, hb⟩ := hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have hv : c.nreg a + c.nreg b ≤ W := by simpa using hwc'.1 r
    have e := Exec.addN (P := P) hd r a b (by rw [hS.nreg a ha, hS.nreg b hb]; omega)
    exact ⟨_, _, e, le_of_lt (by omega), hS.updN hr (by rw [hS.nreg a ha, hS.nreg b hb]),
      Frame.updN d (Or.inl (by omega)) _⟩
  | subN r a b =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hr, ha, hb⟩ := hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    exact ⟨_, _, Exec.subN hd r a b, le_of_lt (by omega),
      hS.updN hr (by rw [hS.nreg a ha, hS.nreg b hb]), Frame.updN d (Or.inl (by omega)) _⟩
  | mulN r a b =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hr, ha, hb⟩ := hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have hv : c.nreg a * c.nreg b ≤ W := by simpa using hwc'.1 r
    have e := Exec.mulN (P := P) hd r a b (by rw [hS.nreg a ha, hS.nreg b hb]; omega)
    exact ⟨_, _, e, le_of_lt (by omega), hS.updN hr (by rw [hS.nreg a ha, hS.nreg b hb]),
      Frame.updN d (Or.inl (by omega)) _⟩
  | divN r a b =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hr, ha, hb⟩ := hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    exact ⟨_, _, Exec.divN hd r a b, le_of_lt (by omega),
      hS.updN hr (by rw [hS.nreg a ha, hS.nreg b hb]), Frame.updN d (Or.inl (by omega)) _⟩
  | modN r a b =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hr, ha, hb⟩ := hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    exact ⟨_, _, Exec.modN hd r a b, le_of_lt (by omega),
      hS.updN hr (by rw [hS.nreg a ha, hS.nreg b hb]), Frame.updN d (Or.inl (by omega)) _⟩
  | loadN r a =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    exact ⟨_, _, Exec.loadN hd r a, le_of_lt (by omega),
      hS.updN hok.1 (by rw [hS.nreg a hok.2, hS.nmem _ (hwc.1 a)]),
      Frame.updN d (Or.inl (by omega)) _⟩
  | storeN a r =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have e := Exec.storeN (P := P) hd a r
    rw [hS.nreg a hok.1] at e
    exact ⟨_, _, e, le_of_lt (by omega), hS.storeN hβ (hwc.1 a) (hS.nreg r hok.2),
      Frame.storeN d (Or.inl (hwc.1 a)) _⟩
  | readIn r a =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have hv : P.data.getD (c.nreg a) 0 ≤ W := by simpa using hwc'.1 r
    have e := Exec.readIn (P := P) hd r a (by rw [hS.nreg a hok.2]; omega)
    exact ⟨_, _, e, le_of_lt (by omega), hS.updN hok.1 (by rw [hS.nreg a hok.2]),
      Frame.updN d (Or.inl (by omega)) _⟩
  | rand r a =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have hv : P.tape (c.nreg a) ≤ W := by simpa using hwc'.1 r
    have e := Exec.rand (P := P) hd r a (by rw [hS.nreg a hok.2]; omega)
    exact ⟨_, _, e, le_of_lt (by omega), hS.updN hok.1 (by rw [hS.nreg a hok.2]),
      Frame.updN d (Or.inl (by omega)) _⟩
  | outN a =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      decide_eq_true_eq] at hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    exact ⟨_, _, Exec.outN hd a, le_of_lt (by omega), hS.out (hS.nreg a hok),
      Frame.out d _⟩
  | constR r z =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      decide_eq_true_eq] at hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have hv := (res_const hM z).lt hM
    have e := Exec.constN (P := P) hd (R + r) (z % (M : ℤ)).toNat
      ((add_le_sq hv (Nat.zero_le M)).trans hW3)
    exact ⟨_, _, e, le_of_lt (by omega), hS.updR hok (res_const hM z),
      Frame.updN d (Or.inl (by omega)) _⟩
  | copyR r a =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    exact ⟨_, _, Exec.copyN hd (R + r) (R + a), le_of_lt (by omega),
      hS.updR hok.1 (hS.rreg a hok.2), Frame.updN d (Or.inl (by omega)) _⟩
  | addR r a b =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hr, ha, hb⟩ := hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have hA := (hS.rreg a ha).lt hM
    have hB := (hS.rreg b hb).lt hM
    have e1 := Exec.addN (P := P) hd (2 * R + 3) (R + a) (R + b)
      ((add_le_sq hA hB.le).trans hW3)
    have e2 := Exec.modN (P := P) e1.wb_right (R + r) (2 * R + 3) (2 * R)
    refine ⟨_, _, Exec.block_cons e1 (Exec.block_cons e2 (Exec.block_nil e2.wb_right)),
      le_of_lt (by omega), (hS.updT hT _).updR hr ?_,
      (Frame.updN d (Or.inr rfl) _).trans (Frame.updN _ (Or.inl (by omega)) _)⟩
    simp only [upd_same, upd_other _ _ _ (show 2 * R ≠ 2 * R + 3 by omega), hK.m]
    exact res_add (hS.rreg a ha) (hS.rreg b hb)
  | subR r a b =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hr, ha, hb⟩ := hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have hA := (hS.rreg a ha).lt hM
    have e1 := Exec.subN (P := P) hd (2 * R + 3) (2 * R) (R + b)
    have e2 := Exec.addN (P := P) e1.wb_right (2 * R + 3) (R + a) (2 * R + 3) (by
      simp only [upd_same, upd_other _ _ _ (show R + a ≠ 2 * R + 3 by omega), hK.m]
      exact (add_le_sq hA (Nat.sub_le _ _)).trans hW3)
    have e3 := Exec.modN (P := P) e2.wb_right (R + r) (2 * R + 3) (2 * R)
    refine ⟨_, _, Exec.block_cons e1 (Exec.block_cons e2 (Exec.block_cons e3
      (Exec.block_nil e3.wb_right))), le_rfl, ((hS.updT hT _).updT hT _).updR hr ?_,
      ((Frame.updN d (Or.inr rfl) _).trans (Frame.updN _ (Or.inr rfl) _)).trans
        (Frame.updN _ (Or.inl (by omega)) _)⟩
    simp only [upd_same, upd_other _ _ _ (show 2 * R ≠ 2 * R + 3 by omega),
      upd_other _ _ _ (show R + a ≠ 2 * R + 3 by omega), hK.m]
    exact res_sub hM (hS.rreg a ha) (hS.rreg b hb)
  | mulR r a b =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hr, ha, hb⟩ := hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have hA := (hS.rreg a ha).lt hM
    have hB := (hS.rreg b hb).lt hM
    have hAB : d.nreg (R + a) * d.nreg (R + b) ≤ M * M :=
      Nat.mul_le_mul hA.le hB.le
    have e1 := Exec.mulN (P := P) hd (2 * R + 3) (R + a) (R + b)
      (hAB.trans ((Nat.le_add_right _ _).trans hW3))
    have e2 := Exec.modN (P := P) e1.wb_right (R + r) (2 * R + 3) (2 * R)
    refine ⟨_, _, Exec.block_cons e1 (Exec.block_cons e2 (Exec.block_nil e2.wb_right)),
      le_of_lt (by omega), (hS.updT hT _).updR hr ?_,
      (Frame.updN d (Or.inr rfl) _).trans (Frame.updN _ (Or.inl (by omega)) _)⟩
    simp only [upd_same, upd_other _ _ _ (show 2 * R ≠ 2 * R + 3 by omega), hK.m]
    exact res_mul (hS.rreg a ha) (hS.rreg b hb)
  | loadR r a =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨hr, ha⟩ := hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have hca := hwc.1 a
    have e1 := Exec.addN (P := P) hd (2 * R + 3) a (2 * R + 2) (by
      rw [hS.nreg a ha, hK.b]; omega)
    have e2 := Exec.loadN (P := P) e1.wb_right (R + r) (2 * R + 3)
    refine ⟨_, _, Exec.block_cons e1 (Exec.block_cons e2 (Exec.block_nil e2.wb_right)),
      le_of_lt (by omega), (hS.updT hT _).updR hr ?_,
      (Frame.updN d (Or.inr rfl) _).trans (Frame.updN _ (Or.inl (by omega)) _)⟩
    simp only [upd_same]
    rw [hS.nreg a ha, hK.b, Nat.add_comm]
    exact hS.rmem _ hca
  | storeR a r =>
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨ha, hr⟩ := hok
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have hca := hwc.1 a
    have e1 := Exec.addN (P := P) hd (2 * R + 3) a (2 * R + 2) (by
      rw [hS.nreg a ha, hK.b]; omega)
    have e2 := Exec.storeN (P := P) e1.wb_right (2 * R + 3) (R + r)
    have hadr : (upd d.nreg (2 * R + 3) (d.nreg a + d.nreg (2 * R + 2))) (2 * R + 3) =
        β + c.nreg a := by
      rw [upd_same, hS.nreg a ha, hK.b, Nat.add_comm]
    refine ⟨_, _, Exec.block_cons e1 (Exec.block_cons e2 (Exec.block_nil e2.wb_right)),
      le_of_lt (by omega), (hS.updT hT _).storeR hβ hca ?_ hadr,
      (Frame.updN d (Or.inr rfl) _).trans (Frame.storeN _ (Or.inr ?_) _)⟩
    · simp only [upd_other _ _ _ (show R + r ≠ 2 * R + 3 by omega)]
      exact hS.rreg r hr
    · simp only [hadr]; omega

end OneInstr

/-! ### The comparison -/

section Cmp

variable {P : Input} {W H W' R M β : ℕ} {c d : Config}

/-- The residue of `rreg a - rreg b` into the scratch register, `3` instructions. -/
theorem cmpS_exec (hS : Sim R W M β c d) (hK : Consts R M H β d) (hd : WordsBounded W' d)
    (hM : 0 < M) (hW3 : M * M + M ≤ W') {a b : ℕ} (ha : a < R) :
    ∃ e, Exec P W' (cmpS R a b) d e 3 ∧ Sim R W M β c e ∧ Frame R W β d e ∧
      Consts R M H β e ∧ e.nreg (2 * R + 3) = (d.nreg (R + a) + (M - d.nreg (R + b))) % M := by
  have hA := (hS.rreg a ha).lt hM
  have hT : 2 * R ≤ 2 * R + 3 := by omega
  have e1 := Exec.subN (P := P) hd (2 * R + 3) (2 * R) (R + b)
  have e2 := Exec.addN (P := P) e1.wb_right (2 * R + 3) (R + a) (2 * R + 3) (by
    simp only [upd_same, upd_other _ _ _ (show R + a ≠ 2 * R + 3 by omega), hK.m]
    exact (add_le_sq hA (Nat.sub_le _ _)).trans hW3)
  have e3 := Exec.modN (P := P) e2.wb_right (2 * R + 3) (2 * R + 3) (2 * R)
  refine ⟨_, Exec.block_cons e1 (Exec.block_cons e2 (Exec.block_cons e3
    (Exec.block_nil e3.wb_right))), ((hS.updT hT _).updT hT _).updT hT _,
    ((Frame.updN d (Or.inr rfl) _).trans (Frame.updN _ (Or.inr rfl) _)).trans
      (Frame.updN _ (Or.inr rfl) _),
    (((Frame.updN (W := W) d (Or.inr rfl) _).trans (Frame.updN _ (Or.inr rfl) _)).trans
      (Frame.updN _ (Or.inr rfl) _)).consts hK, ?_⟩
  simp only [upd_same, upd_other _ _ _ (show 2 * R ≠ 2 * R + 3 by omega),
    upd_other _ _ _ (show R + a ≠ 2 * R + 3 by omega), hK.m]

/-- The natural test after `cmpS` decides the real test. -/
theorem cmp_test (hS : Sim R W M β c d) (hM : 2 * H < M) {a b : ℕ} (ha : a < R) (hb : b < R)
    (hbd : |c.rreg a - c.rreg b| ≤ H) {e : Config} (hK : Consts R M H β e)
    (he : e.nreg (2 * R + 3) = (d.nreg (R + a) + (M - d.nreg (R + b))) % M) :
    e.nreg (2 * R + 1) < e.nreg (2 * R + 3) ↔ c.rreg a < c.rreg b := by
  rw [hK.h, he]
  exact (res_cmp hM (hS.rreg a ha) (hS.rreg b hb) hbd).symm

end Cmp

/-! ### The simulation theorem -/

/-- **Exact integer reals on natural words modulo `M`.** Let `s` name only registers `< R` and
contain no `divR`, and run compare-bounded (`|x - y| ≤ H` at every real test) from `c` to `c'`
in `k` steps with word bound `W`. Let `2H < M`, `W < β`, and `W'` with `W ≤ W'`,
`β + W ≤ W'`, `M² + M ≤ W'`. Then from every `d` simulating `c` (`Sim R W M β c d`: the
residues modulo `M` of the integer reals of `c`), with `M`, `H`, `β` in the registers `2R`,
`2R + 1`, `2R + 2` and `WordsBounded W' d`, the statement `toNat R M s` (natural instructions
only) runs to a `d'` simulating `c'` within `4 k` steps, with word bound `W'`, and keeps the
frame `Frame R W β d d'` (in particular all real registers and memory, the constants, and the
natural registers `≥ 2R + 4`). -/
theorem ExecCmp.toNat {P : Input} {W H W' R M β : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : ExecCmp P W H s c c' k) (hR : s.regsOK (fun r => decide (r < R)) = true)
    (hD : s.noDivR = true) (hM : 2 * H < M) (hβ : W < β) (hW1 : W ≤ W') (hW2 : β + W ≤ W')
    (hW3 : M * M + M ≤ W') {d : Config} (hS : Sim R W M β c d) (hK : Consts R M H β d)
    (hd : WordsBounded W' d) :
    ∃ d' k', Exec P W' (toNat R M s) d d' k' ∧ k' ≤ 4 * k ∧ Sim R W M β c' d' ∧
      Frame R W β d d' := by
  have hM0 : 0 < M := by omega
  induction h generalizing d with
  | skip _ => exact ⟨d, 0, .skip hd, le_rfl, hS, Frame.refl _ _ _ _⟩
  | instr hs he hwc hwc' =>
    simp only [Stmt.regsOK] at hR
    simp only [Stmt.noDivR] at hD
    obtain ⟨d', k', e, hk, hS', hF⟩ :=
      sim_instr hs he hwc hwc' hR hD hM0 hβ hW1 hW2 hW3 hS hK hd
    exact ⟨d', k', e, by omega, hS', hF⟩
  | seq _ _ ih₁ ih₂ =>
    simp only [Stmt.regsOK, Stmt.noDivR, Bool.and_eq_true] at hR hD
    obtain ⟨d₁, k₁', e₁, hk₁, hS₁, hF₁⟩ := ih₁ hR.1 hD.1 hS hK hd
    obtain ⟨d₂, k₂', e₂, hk₂, hS₂, hF₂⟩ := ih₂ hR.2 hD.2 hS₁ (hF₁.consts hK) e₁.wb_right
    exact ⟨d₂, k₁' + k₂', .seq e₁ e₂, by omega, hS₂, hF₁.trans hF₂⟩
  | @ifLtN_true a b t e c c' k ht _ ih =>
    simp only [Stmt.regsOK, Stmt.noDivR, Bool.and_eq_true, decide_eq_true_eq] at hR hD
    obtain ⟨⟨⟨ha, hb⟩, hRt⟩, -⟩ := hR
    obtain ⟨d', k', e', hk, hS', hF⟩ := ih hRt hD.1 hS hK hd
    have ht' : d.nreg a < d.nreg b := by rw [hS.nreg a ha, hS.nreg b hb]; exact ht
    exact ⟨d', k' + 1, .ifLtN_true ht' e', by omega, hS', hF⟩
  | @ifLtN_false a b t e c c' k ht _ ih =>
    simp only [Stmt.regsOK, Stmt.noDivR, Bool.and_eq_true, decide_eq_true_eq] at hR hD
    obtain ⟨⟨⟨ha, hb⟩, -⟩, hRe⟩ := hR
    obtain ⟨d', k', e', hk, hS', hF⟩ := ih hRe hD.2 hS hK hd
    have ht' : ¬ d.nreg a < d.nreg b := by rw [hS.nreg a ha, hS.nreg b hb]; exact ht
    exact ⟨d', k' + 2, .ifLtN_false ht' e', by omega, hS', hF⟩
  | @ifLtR_true a b t e c c' k hbd ht _ ih =>
    simp only [Stmt.regsOK, Stmt.noDivR, Bool.and_eq_true, decide_eq_true_eq] at hR hD
    obtain ⟨⟨⟨ha, hb⟩, hRt⟩, -⟩ := hR
    obtain ⟨e₀, ec, hS₀, hF₀, hK₀, ht₀⟩ := cmpS_exec (P := P) (b := b) hS hK hd hM0 hW3 ha
    obtain ⟨d', k', e', hk, hS', hF⟩ := ih hRt hD.1 hS₀ hK₀ ec.wb_right
    have ht' := (cmp_test hS hM ha hb hbd hK₀ ht₀).2 ht
    exact ⟨d', 3 + (k' + 1), .seq ec (.ifLtN_true ht' e'), by omega, hS', hF₀.trans hF⟩
  | @ifLtR_false a b t e c c' k hbd ht _ ih =>
    simp only [Stmt.regsOK, Stmt.noDivR, Bool.and_eq_true, decide_eq_true_eq] at hR hD
    obtain ⟨⟨⟨ha, hb⟩, -⟩, hRe⟩ := hR
    obtain ⟨e₀, ec, hS₀, hF₀, hK₀, ht₀⟩ := cmpS_exec (P := P) (b := b) hS hK hd hM0 hW3 ha
    obtain ⟨d', k', e', hk, hS', hF⟩ := ih hRe hD.2 hS₀ hK₀ ec.wb_right
    have ht' : ¬ _ := mt (cmp_test hS hM ha hb hbd hK₀ ht₀).1 ht
    exact ⟨d', 3 + (k' + 2), .seq ec (.ifLtN_false ht' e'), by omega, hS', hF₀.trans hF⟩
  | @whileLtN_false a b body c ht _ =>
    simp only [Stmt.regsOK, Bool.and_eq_true, decide_eq_true_eq] at hR
    obtain ⟨⟨ha, hb⟩, -⟩ := hR
    have ht' : ¬ d.nreg a < d.nreg b := by rw [hS.nreg a ha, hS.nreg b hb]; exact ht
    exact ⟨d, 2, .whileLtN_false ht' hd, by omega, hS, Frame.refl _ _ _ _⟩
  | @whileLtN_true a b body c c₁ c' k₁ k₂ ht _ _ ih₁ ih₂ =>
    have hR' := hR
    have hD' := hD
    simp only [Stmt.regsOK, Stmt.noDivR, Bool.and_eq_true, decide_eq_true_eq] at hR hD
    obtain ⟨⟨ha, hb⟩, hRb⟩ := hR
    have ht' : d.nreg a < d.nreg b := by rw [hS.nreg a ha, hS.nreg b hb]; exact ht
    obtain ⟨d₁, k₁', e₁, hk₁, hS₁, hF₁⟩ := ih₁ hRb hD hS hK hd
    obtain ⟨d', k₂', e₂, hk₂, hS', hF₂⟩ := ih₂ hR' hD' hS₁ (hF₁.consts hK) e₁.wb_right
    exact ⟨d', k₁' + 2 + k₂', .whileLtN_true ht' e₁ e₂, by omega, hS', hF₁.trans hF₂⟩
  | @whileLtR_false a b body c hbd ht _ =>
    simp only [Stmt.regsOK, Bool.and_eq_true, decide_eq_true_eq] at hR
    obtain ⟨⟨ha, hb⟩, -⟩ := hR
    obtain ⟨e₀, ec, hS₀, hF₀, hK₀, ht₀⟩ := cmpS_exec (P := P) (b := b) hS hK hd hM0 hW3 ha
    have ht' : ¬ _ := mt (cmp_test hS hM ha hb hbd hK₀ ht₀).1 ht
    exact ⟨e₀, 3 + 2, .seq ec (.whileLtN_false ht' ec.wb_right), by omega, hS₀, hF₀⟩
  | @whileLtR_true a b body c c₁ c' k₁ k₂ hbd ht _ _ ih₁ ih₂ =>
    have hR' := hR
    have hD' := hD
    simp only [Stmt.regsOK, Stmt.noDivR, Bool.and_eq_true, decide_eq_true_eq] at hR hD
    obtain ⟨⟨ha, hb⟩, hRb⟩ := hR
    obtain ⟨e₀, ec, hS₀, hF₀, hK₀, ht₀⟩ := cmpS_exec (P := P) (b := b) hS hK hd hM0 hW3 ha
    have ht' := (cmp_test hS hM ha hb hbd hK₀ ht₀).2 ht
    obtain ⟨d₁, k₁', e₁, hk₁, hS₁, hF₁⟩ := ih₁ hRb hD hS₀ hK₀ ec.wb_right
    obtain ⟨d', k₂', e₂, hk₂, hS', hF₂⟩ :=
      ih₂ hR' hD' hS₁ (hF₁.consts hK₀) e₁.wb_right
    simp only [ModNat.toNat] at e₂
    cases e₂ with
    | @seq _ _ _ e₁' _ ka kb ec' el =>
      exact ⟨d', 3 + (k₁' + ka + 2 + kb),
        .seq ec (.whileLtN_true ht' (.seq e₁ ec') el), by omega, hS',
        hF₀.trans (hF₁.trans hF₂)⟩

/-- The constants into their registers (`3` instructions): from `d` simulating `c`, a
configuration simulating `c` with the constants in place and the same frame outside `2R`,
`2R + 1`, `2R + 2`. -/
theorem constsS_exec {P : Input} {W' R M H β : ℕ} {W : ℕ} {c d : Config}
    (hS : Sim R W M β c d) (hd : WordsBounded W' d) (hMW : M ≤ W') (hHW : H ≤ W')
    (hβW : β ≤ W') :
    ∃ e, Exec P W' (constsS R M H β) d e 3 ∧ Sim R W M β c e ∧ Consts R M H β e ∧
      (∀ r, r ≠ 2 * R → r ≠ 2 * R + 1 → r ≠ 2 * R + 2 → e.nreg r = d.nreg r) ∧
      e.nmem = d.nmem ∧ e.rreg = d.rreg ∧ e.rmem = d.rmem ∧ e.output = d.output := by
  have e1 := Exec.constN (P := P) hd (2 * R) M hMW
  have e2 := Exec.constN (P := P) e1.wb_right (2 * R + 1) H hHW
  have e3 := Exec.constN (P := P) e2.wb_right (2 * R + 2) β hβW
  refine ⟨_, Exec.block_cons e1 (Exec.block_cons e2 (Exec.block_cons e3
    (Exec.block_nil e3.wb_right))), ((hS.updT le_rfl _).updT (by omega) _).updT (by omega) _,
    ⟨?_, ?_, ?_⟩, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [upd_same, upd_other _ _ _ (show 2 * R ≠ 2 * R + 1 by omega),
      upd_other _ _ _ (show 2 * R ≠ 2 * R + 2 by omega)]
  · simp only [upd_same, upd_other _ _ _ (show 2 * R + 1 ≠ 2 * R + 2 by omega)]
  · simp only [upd_same]
  · simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3]

/-- **The simulation with the constants set first**: `constsS R M H β` then `toNat R M s`, from
any `d` simulating `c` and bounded by `W'`, within `4 k + 3` steps; the natural registers
`≥ 2R + 4`, the natural memory outside `[0, W] ∪ [β, β + W]`, the real registers and memory are
kept, and the constants are left in their registers. -/
theorem ExecCmp.toNat_consts {P : Input} {W H W' R M β : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : ExecCmp P W H s c c' k) (hR : s.regsOK (fun r => decide (r < R)) = true)
    (hD : s.noDivR = true) (hM : 2 * H < M) (hβ : W < β) (hW1 : W ≤ W') (hW2 : β + W ≤ W')
    (hW3 : M * M + M ≤ W') {d : Config} (hS : Sim R W M β c d) (hd : WordsBounded W' d) :
    ∃ d' k', Exec P W' (.seq (constsS R M H β) (ModNat.toNat R M s)) d d' k' ∧ k' ≤ 4 * k + 3 ∧
      Sim R W M β c' d' ∧ Consts R M H β d' ∧
      (∀ r, 2 * R + 4 ≤ r → d'.nreg r = d.nreg r) ∧
      (∀ a, W < a → (a < β ∨ β + W < a) → d'.nmem a = d.nmem a) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem := by
  have hMM : M ≤ W' := (Nat.le_add_left M (M * M)).trans hW3
  obtain ⟨e, ec, hSe, hKe, hre, hme, hRe, hMe, -⟩ :=
    constsS_exec (P := P) (H := H) hS hd hMM (by omega) (by omega)
  obtain ⟨d', k', ex, hk, hS', hF⟩ := h.toNat hR hD hM hβ hW1 hW2 hW3 hSe hKe ec.wb_right
  refine ⟨d', 3 + k', .seq ec ex, by omega, hS', hF.consts hKe, fun r hr => ?_,
    fun a h1 h2 => ?_, hF.rreg.trans hRe, hF.rmem.trans hMe⟩
  · rw [hF.nreg r (by omega) (by omega), hre r (by omega) (by omega) (by omega)]
  · rw [hF.nmem a h1 h2, hme]

/-- The simulation from an ordinary execution whose real tests are bounded (`CmpOK`). -/
theorem CmpOK.toNat {P : Input} {W H W' R M β : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (hc : CmpOK P W H s c) (h : Exec P W s c c' k)
    (hR : s.regsOK (fun r => decide (r < R)) = true) (hD : s.noDivR = true) (hM : 2 * H < M)
    (hβ : W < β) (hW1 : W ≤ W') (hW2 : β + W ≤ W') (hW3 : M * M + M ≤ W') {d : Config}
    (hS : Sim R W M β c d) (hK : Consts R M H β d) (hd : WordsBounded W' d) :
    ∃ d' k', Exec P W' (ModNat.toNat R M s) d d' k' ∧ k' ≤ 4 * k ∧ Sim R W M β c' d' ∧
      Frame R W β d d' :=
  (hc.exec h).toNat hR hD hM hβ hW1 hW2 hW3 hS hK hd

/-- A residue of a nonnegative integer below `M` is the integer itself. -/
theorem Res.eq_of_lt {M : ℕ} {x : ℝ} {v : ℕ} (h : Res M x v) {z : ℕ} (hz : x = z)
    (hzM : z < M) : v = z := by
  obtain ⟨z', hx, hv⟩ := h
  have : z' = (z : ℤ) := by exact_mod_cast hx.symm.trans hz
  subst this
  have : ((z : ℤ) % (M : ℤ)) = z := Int.emod_eq_of_lt (by omega) (by exact_mod_cast hzM)
  exact_mod_cast hv.trans this

/-- The residue of a natural number below `M`. -/
theorem res_nat {M z : ℕ} (hz : z < M) : Res M (z : ℝ) z :=
  ⟨z, by norm_cast, by rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast hz)]⟩

end

end ModNat

end Machine

end WordRAM
