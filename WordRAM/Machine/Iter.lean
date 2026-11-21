module

public import WordRAM.Machine.WordMono
public import WordRAM.Machine.RealsToNat

/-!
# Partial iterations of a loop, inversion of runs, transport of hoisted blocks

Tools for fixed programs that simulate a *family* of structured programs (a program indexed by
data, e.g. unrolled along a tree) by a `while` loop over an explicit stack of frames, with the
correctness *transported* from the runs of the family members (`Exec.lift`) rather than proved
again.

* `WordRAM.Machine.FixIter`: finitely many iterations of the body of `whileLtN a b body`, each
  started with the test true; `FixIter.trans`, `FixIter.single`, `FixIter.exit` (a partial
  iteration followed by a false test is a run of the loop).
* `WordRAM.Machine.Exec.seq_inv`, `Exec.block_inv`: inversion of runs of a sequence and of a
  block (`blockEffs`).
* `WordRAM.Machine.Agree.of_regs`: agreement after two register-only blocks whose results agree
  on the registers in `U` (the transport of a block of constants by a *hoisted* block computing
  the same values from parameter registers).
-/

@[expose] public section

namespace WordRAM

namespace Machine

open Stmt

variable {P : Input} {W : ℕ}

/-- Finitely many iterations of the body of `whileLtN a b body`, each started with the test
true, costing two steps more than the body each (the test and the jump back). -/
inductive FixIter (P : Input) (W : ℕ) (a b : ℕ) (body : Stmt) : Config → Config → ℕ → Prop
  | refl {c : Config} : FixIter P W a b body c c 0
  | step {c c₁ c₂ : Config} {k₁ k₂ : ℕ} : c.nreg a < c.nreg b → Exec P W body c c₁ k₁ →
      FixIter P W a b body c₁ c₂ k₂ → FixIter P W a b body c c₂ (k₁ + 2 + k₂)

namespace FixIter

variable {a b : ℕ} {body : Stmt}

theorem cast {c c' : Config} {k k' : ℕ} (h : FixIter P W a b body c c' k) (hk : k = k') :
    FixIter P W a b body c c' k' := hk ▸ h

theorem trans {c c₁ c₂ : Config} {k₁ k₂ : ℕ} (h₁ : FixIter P W a b body c c₁ k₁)
    (h₂ : FixIter P W a b body c₁ c₂ k₂) : FixIter P W a b body c c₂ (k₁ + k₂) := by
  induction h₁ with
  | refl => simpa using h₂
  | step ht e _ ih => exact (FixIter.step ht e (ih h₂)).cast (by omega)

/-- One iteration. -/
theorem single {c c₁ : Config} {k : ℕ} (ht : c.nreg a < c.nreg b) (e : Exec P W body c c₁ k) :
    FixIter P W a b body c c₁ (k + 2) :=
  (FixIter.step ht e FixIter.refl).cast (by omega)

/-- Iterations followed by a run of the loop are a run of the loop. -/
theorem exec_loop {c c₁ c₂ : Config} {k₁ k₂ : ℕ} (h : FixIter P W a b body c c₁ k₁)
    (hl : Exec P W (.whileLtN a b body) c₁ c₂ k₂) :
    Exec P W (.whileLtN a b body) c c₂ (k₁ + k₂) := by
  induction h with
  | refl => simpa using hl
  | step ht e _ ih => exact (Exec.whileLtN_true ht e (ih hl)).cast (by omega)

/-- **Exit**: iterations ending with the test false are a run of the loop. -/
theorem exit {c c₁ : Config} {k : ℕ} (h : FixIter P W a b body c c₁ k)
    (ht : ¬ c₁.nreg a < c₁.nreg b) (hw : WordsBounded W c₁) :
    Exec P W (.whileLtN a b body) c c₁ (k + 2) :=
  h.exec_loop (Exec.whileLtN_false ht hw)

end FixIter

/-! ### Inversion -/

theorem Exec.seq_inv {s t : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W (.seq s t) c c' k) :
    ∃ c₁ k₁ k₂, Exec P W s c c₁ k₁ ∧ Exec P W t c₁ c' k₂ ∧ k = k₁ + k₂ := by
  cases h with
  | seq e₁ e₂ => exact ⟨_, _, _, e₁, e₂, rfl⟩

theorem Exec.block_inv {l : List Instr} {c c' : Config} {k : ℕ}
    (h : Exec P W (block l) c c' k) : blockEffs P l c = some c' ∧ k = l.length :=
  Exec.block_effs h

/-! ### Agreement after register-only blocks -/

/-- Two configurations agreeing on `U`/`W`, each changed in its natural registers only, agree if
the new natural registers agree on `U`. -/
theorem Agree.of_regs {U : ℕ → Bool} {c d c' d' : Config} (hA : Agree U W c d)
    (hc : c' = { c with nreg := c'.nreg }) (hd : d' = { d with nreg := d'.nreg })
    (hr : ∀ r, U r = true → d'.nreg r = c'.nreg r) : Agree U W c' d' := by
  refine ⟨hr, fun r hr' => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · rw [hc, hd]; exact hA.rreg r hr'
  · rw [hc, hd]; exact hA.nmem a ha
  · rw [hc, hd]; exact hA.rmem a ha


/-! ### Hoisting: constants read from parameter registers -/

/-- `HoistS U ρ s s'`: the statement `s'` is `s` with some instructions `constN r k` (`r` in `U`)
replaced by `copyN r F` from a parameter register `F` outside `U` holding `ρ F = k`; the parts
kept verbatim name only registers in `U` and read neither input nor tape. -/
inductive HoistS (U : ℕ → Bool) (ρ : ℕ → ℕ) : Stmt → Stmt → Prop
  | same {s : Stmt} : s.regsOK U = true → s.noInp = true → s.noRand = true → HoistS U ρ s s
  | cst {r k F : ℕ} : U r = true → U F = false → ρ F = k →
      HoistS U ρ (.instr (.constN r k)) (.instr (.copyN r F))
  | seq {s t s' t' : Stmt} : HoistS U ρ s s' → HoistS U ρ t t' → HoistS U ρ (.seq s t) (.seq s' t')
  | ifLtN {a b : ℕ} {t e t' e' : Stmt} : U a = true → U b = true → HoistS U ρ t t' →
      HoistS U ρ e e' → HoistS U ρ (.ifLtN a b t e) (.ifLtN a b t' e')
  | whileLtN {a b : ℕ} {body body' : Stmt} : U a = true → U b = true → HoistS U ρ body body' →
      HoistS U ρ (.whileLtN a b body) (.whileLtN a b body')

namespace HoistS

variable {U : ℕ → Bool}

theorem congr {ρ ρ' : ℕ → ℕ} (e : ∀ F, U F = false → ρ' F = ρ F) {s s' : Stmt}
    (h : HoistS U ρ s s') : HoistS U ρ' s s' := by
  induction h with
  | same h1 h2 h3 => exact .same h1 h2 h3
  | cst hr hF hk => exact .cst hr hF (by rw [e _ hF, hk])
  | seq _ _ ih1 ih2 => exact .seq ih1 ih2
  | ifLtN ha hb _ _ ih1 ih2 => exact .ifLtN ha hb ih1 ih2
  | whileLtN ha hb _ ih => exact .whileLtN ha hb ih

/-- A block hoisted instruction by instruction. -/
theorem block_cons {ρ : ℕ → ℕ} {i i' : Instr} {l l' : List Instr}
    (hi : HoistS U ρ (.instr i) (.instr i')) (hl : HoistS U ρ (block l) (block l')) :
    HoistS U ρ (block (i :: l)) (block (i' :: l')) := .seq hi hl

theorem block_nil {ρ : ℕ → ℕ} : HoistS U ρ (block []) (block []) := .same rfl rfl rfl

/-- A verbatim instruction. -/
theorem instr {ρ : ℕ → ℕ} {i : Instr} (h1 : i.regsOK U = true) (h2 : i.notInp = true)
    (h3 : i.noRand = true) : HoistS U ρ (.instr i) (.instr i) := .same h1 h2 h3

end HoistS

/-- **Transport of a hoisted statement.** If `s` runs from `c` to `c'` (word bound `W`) and `s'`
is `s` hoisted with the parameter values `ρ = d.nreg` of a configuration `d` agreeing with `c`
(registers in `U`, memory `≤ W`), then `s'` runs from `d` (any input, word bound `W' ≥ W`) in
the same number of steps to a configuration agreeing with `c'`, keeping the registers outside
`U` and the memory above `W`, and appending to the output what `s` appends. -/
theorem Exec.hoist {P' : Input} {U : ℕ → Bool} {W' : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hW : W ≤ W') :
    ∀ {s' : Stmt} {d : Config}, HoistS U d.nreg s s' → Agree U W c d → WordsBounded W' d →
      ∃ d', Exec P' W' s' d d' k ∧ Agree U W c' d' ∧ Keep U W d d' ∧
        ∃ L, c'.output = c.output ++ L ∧ d'.output = d.output ++ L := by
  induction h with
  | skip hw =>
    intro s' d hH hA hd
    cases hH with
    | same h1 h2 h3 => exact Exec.lift (P := P) (P' := P') (.skip hw) h1 h2 h3 hW hA hd
  | @instr ins c c' hst he hw hw' =>
    intro s' d hH hA hd
    cases hH with
    | same h1 h2 h3 => exact Exec.lift (P := P) (P' := P') (.instr hst he hw hw') h1 h2 h3 hW hA hd
    | @cst r kk F hr hF hk =>
      simp only [Instr.effect_constN, Option.some.injEq] at he
      subst he
      refine ⟨{ d with nreg := upd d.nreg r kk }, ?_, ?_, ?_, [], by simp, by simp⟩
      · have e := Exec.copyN (P := P') (W := W') (c := d) hd r F
        rw [hk] at e
        exact e
      · refine ⟨fun x hx => ?_, hA.rreg, hA.nmem, hA.rmem⟩
        simp only [upd_apply]
        split_ifs
        · rfl
        · exact hA.nreg x hx
      · refine ⟨fun x hx => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
        have : x ≠ r := fun e => by rw [e, hr] at hx; cases hx
        simp only [upd_other _ _ _ this]
  | seq e₁ e₂ ih₁ ih₂ =>
    intro s' d hH hA hd
    cases hH with
    | same h1 h2 h3 =>
      exact Exec.lift (P := P) (P' := P') (.seq e₁ e₂) h1 h2 h3 hW hA hd
    | seq hs ht =>
      obtain ⟨d₁, x₁, hA₁, hK₁, L₁, o₁, o₁'⟩ := ih₁ hs hA hd
      have hd₁ : WordsBounded W' d₁ := x₁.wb_right
      obtain ⟨d₂, x₂, hA₂, hK₂, L₂, o₂, o₂'⟩ :=
        ih₂ (ht.congr fun F hF => hK₁.nreg F hF) hA₁ hd₁
      exact ⟨d₂, .seq x₁ x₂, hA₂, hK₁.trans hK₂, L₁ ++ L₂, by rw [o₂, o₁, List.append_assoc],
        by rw [o₂', o₁', List.append_assoc]⟩
  | ifLtN_true ht e ih =>
    intro s' d hH hA hd
    cases hH with
    | same h1 h2 h3 => exact Exec.lift (P := P) (P' := P') (.ifLtN_true ht e) h1 h2 h3 hW hA hd
    | ifLtN ha hb htt _ =>
      obtain ⟨d', x, hA', hK, L, o, o'⟩ := ih htt hA hd
      exact ⟨d', .ifLtN_true (by rw [hA.nreg _ ha, hA.nreg _ hb]; exact ht) x, hA', hK, L, o, o'⟩
  | ifLtN_false ht e ih =>
    intro s' d hH hA hd
    cases hH with
    | same h1 h2 h3 => exact Exec.lift (P := P) (P' := P') (.ifLtN_false ht e) h1 h2 h3 hW hA hd
    | ifLtN ha hb _ hee =>
      obtain ⟨d', x, hA', hK, L, o, o'⟩ := ih hee hA hd
      exact ⟨d', .ifLtN_false (by rw [hA.nreg _ ha, hA.nreg _ hb]; exact ht) x, hA', hK, L, o, o'⟩
  | ifLtR_true ht e ih =>
    intro s' d hH hA hd
    cases hH with
    | same h1 h2 h3 => exact Exec.lift (P := P) (P' := P') (.ifLtR_true ht e) h1 h2 h3 hW hA hd
  | ifLtR_false ht e ih =>
    intro s' d hH hA hd
    cases hH with
    | same h1 h2 h3 => exact Exec.lift (P := P) (P' := P') (.ifLtR_false ht e) h1 h2 h3 hW hA hd
  | whileLtN_false ht hw =>
    intro s' d hH hA hd
    cases hH with
    | same h1 h2 h3 => exact Exec.lift (P := P) (P' := P') (.whileLtN_false ht hw) h1 h2 h3 hW hA hd
    | whileLtN ha hb _ =>
      exact ⟨d, .whileLtN_false (by rw [hA.nreg _ ha, hA.nreg _ hb]; exact ht) hd, hA,
        Keep.refl _ _ _, [], by simp, by simp⟩
  | whileLtN_true ht e₁ e₂ ih₁ ih₂ =>
    intro s' d hH hA hd
    cases hH with
    | same h1 h2 h3 => exact Exec.lift (P := P) (P' := P') (.whileLtN_true ht e₁ e₂) h1 h2 h3 hW hA hd
    | whileLtN ha hb hbody =>
      obtain ⟨d₁, x₁, hA₁, hK₁, L₁, o₁, o₁'⟩ := ih₁ hbody hA hd
      have hd₁ : WordsBounded W' d₁ := x₁.wb_right
      obtain ⟨d₂, x₂, hA₂, hK₂, L₂, o₂, o₂'⟩ :=
        ih₂ ((HoistS.whileLtN ha hb hbody).congr fun F hF => hK₁.nreg F hF) hA₁ hd₁
      exact ⟨d₂, .whileLtN_true (by rw [hA.nreg _ ha, hA.nreg _ hb]; exact ht) x₁ x₂, hA₂,
        hK₁.trans hK₂, L₁ ++ L₂, by rw [o₂, o₁, List.append_assoc],
        by rw [o₂', o₁', List.append_assoc]⟩
  | whileLtR_false ht hw =>
    intro s' d hH hA hd
    cases hH with
    | same h1 h2 h3 => exact Exec.lift (P := P) (P' := P') (.whileLtR_false ht hw) h1 h2 h3 hW hA hd
  | whileLtR_true ht e₁ e₂ =>
    intro s' d hH hA hd
    cases hH with
    | same h1 h2 h3 => exact Exec.lift (P := P) (P' := P') (.whileLtR_true ht e₁ e₂) h1 h2 h3 hW hA hd


/-! ### Lifting a run on the same input (input instructions allowed) -/

/-- One `readIn` or `inputSize` on the same input, from an agreeing configuration. -/
theorem effect_lift_inp {U : ℕ → Bool} {ins : Instr} {c c' d : Config}
    (hok : ins.regsOK U = true) (hri : ins.notInp = false)
    (he : ins.effect P c = some c') (hA : Agree U W c d) :
    ∃ d', ins.effect P d = some d' ∧ Agree U W c' d' ∧ Keep U W d d' ∧
      c'.output = c.output ∧ d'.output = d.output := by
  have hl : ∀ r ∈ ins.regs, U r = true := fun r hr => List.all_eq_true.1 hok r hr
  cases ins with
  | readIn r a =>
    have hr : U r = true := hl r (by simp [Instr.regs])
    have ha : U a = true := hl a (by simp [Instr.regs])
    simp only [Instr.effect, Option.some.injEq] at he
    subst he
    refine ⟨{ d with nreg := upd d.nreg r (P.data.getD (d.nreg a) 0) }, rfl,
      ⟨fun x hx => ?_, hA.rreg, hA.nmem, hA.rmem⟩,
      ⟨fun x hx => upd_other _ _ _ (fun e => by rw [e, hr] at hx; cases hx), fun _ _ => rfl,
        fun _ _ => rfl, fun _ _ => rfl⟩, rfl, rfl⟩
    simp only [upd_apply, hA.nreg a ha]
    split
    · rfl
    · exact hA.nreg x hx
  | inputSize r =>
    have hr : U r = true := hl r (by simp [Instr.regs])
    simp only [Instr.effect, Option.some.injEq] at he
    subst he
    refine ⟨{ d with nreg := upd d.nreg r P.data.length }, rfl,
      ⟨fun x hx => ?_, hA.rreg, hA.nmem, hA.rmem⟩,
      ⟨fun x hx => upd_other _ _ _ (fun e => by rw [e, hr] at hx; cases hx), fun _ _ => rfl,
        fun _ _ => rfl, fun _ _ => rfl⟩, rfl, rfl⟩
    simp only [upd_apply]
    split
    · rfl
    · exact hA.nreg x hx
  | _ => simp [Instr.notInp] at hri

/-- **Lifting a run on the same input.** As `Exec.lift`, but the statement may read the input
(`readIn`, `inputSize`): the outer run reads the same input. -/
theorem Exec.liftSame {U : ℕ → Bool} {V : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : s.regsOK U = true) (hr : s.noRand = true) (hW : W ≤ V) :
    ∀ {d : Config}, Agree U W c d → WordsBounded V d →
      ∃ d', Exec P V s d d' k ∧ Agree U W c' d' ∧ Keep U W d d' ∧
        ∃ L, c'.output = c.output ++ L ∧ d'.output = d.output ++ L := by
  induction h with
  | skip hw =>
    intro d hA hd
    exact ⟨d, .skip hd, hA, Keep.refl _ _ _, [], by simp, by simp⟩
  | @instr ins c c' hst he hw hw' =>
    intro d hA hd
    have hok : ins.regsOK U = true := hs
    obtain ⟨d', he', hA', hK, hout⟩ : ∃ d', ins.effect P d = some d' ∧ Agree U W c' d' ∧
        Keep U W d d' ∧ ∃ L, c'.output = c.output ++ L ∧ d'.output = d.output ++ L := by
      cases hri : ins.notInp
      · obtain ⟨d', a, b, e, o1, o2⟩ := effect_lift_inp hok hri he hA
        exact ⟨d', a, b, e, [], by simp [o1], by simp [o2]⟩
      · exact effect_embed (P' := P) hok hri (Or.inr rfl) he hw hA
    have hd' : WordsBounded V d' := wordsBounded_of_agree hA' hw' hW
      (fun r hr' => by rw [hK.nreg r hr']; exact WordsBounded.nreg hd r)
      (fun a ha => by rw [hK.nmem a ha]; exact WordsBounded.nmem hd a)
    exact ⟨d', .instr hst he' hd hd', hA', hK, hout⟩
  | seq e₁ e₂ ih₁ ih₂ =>
    intro d hA hd
    simp only [Stmt.regsOK, Stmt.noRand, Bool.and_eq_true] at hs hr
    obtain ⟨d₁, x₁, hA₁, hK₁, L₁, o₁, o₁'⟩ := ih₁ hs.1 hr.1 hA hd
    obtain ⟨d₂, x₂, hA₂, hK₂, L₂, o₂, o₂'⟩ := ih₂ hs.2 hr.2 hA₁ x₁.wb_right
    exact ⟨d₂, .seq x₁ x₂, hA₂, hK₁.trans hK₂, L₁ ++ L₂, by rw [o₂, o₁, List.append_assoc],
      by rw [o₂', o₁', List.append_assoc]⟩
  | ifLtN_true ht e ih =>
    intro d hA hd
    simp only [Stmt.regsOK, Stmt.noRand, Bool.and_eq_true] at hs hr
    obtain ⟨d', x, hA', hK, L, o, o'⟩ := ih hs.1.2 hr.1 hA hd
    exact ⟨d', .ifLtN_true (by rw [hA.nreg _ hs.1.1.1, hA.nreg _ hs.1.1.2]; exact ht) x, hA', hK,
      L, o, o'⟩
  | ifLtN_false ht e ih =>
    intro d hA hd
    simp only [Stmt.regsOK, Stmt.noRand, Bool.and_eq_true] at hs hr
    obtain ⟨d', x, hA', hK, L, o, o'⟩ := ih hs.2 hr.2 hA hd
    exact ⟨d', .ifLtN_false (by rw [hA.nreg _ hs.1.1.1, hA.nreg _ hs.1.1.2]; exact ht) x, hA', hK,
      L, o, o'⟩
  | ifLtR_true ht e ih =>
    intro d hA hd
    simp only [Stmt.regsOK, Stmt.noRand, Bool.and_eq_true] at hs hr
    obtain ⟨d', x, hA', hK, L, o, o'⟩ := ih hs.1.2 hr.1 hA hd
    exact ⟨d', .ifLtR_true (by rw [hA.rreg _ hs.1.1.1, hA.rreg _ hs.1.1.2]; exact ht) x, hA', hK,
      L, o, o'⟩
  | ifLtR_false ht e ih =>
    intro d hA hd
    simp only [Stmt.regsOK, Stmt.noRand, Bool.and_eq_true] at hs hr
    obtain ⟨d', x, hA', hK, L, o, o'⟩ := ih hs.2 hr.2 hA hd
    exact ⟨d', .ifLtR_false (by rw [hA.rreg _ hs.1.1.1, hA.rreg _ hs.1.1.2]; exact ht) x, hA', hK,
      L, o, o'⟩
  | whileLtN_false ht hw =>
    intro d hA hd
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    exact ⟨d, .whileLtN_false (by rw [hA.nreg _ hs.1.1, hA.nreg _ hs.1.2]; exact ht) hd, hA,
      Keep.refl _ _ _, [], by simp, by simp⟩
  | whileLtN_true ht e₁ e₂ ih₁ ih₂ =>
    intro d hA hd
    have hs' := hs; have hr' := hr
    simp only [Stmt.regsOK, Stmt.noRand, Bool.and_eq_true] at hs hr
    obtain ⟨d₁, x₁, hA₁, hK₁, L₁, o₁, o₁'⟩ := ih₁ hs.2 hr hA hd
    obtain ⟨d₂, x₂, hA₂, hK₂, L₂, o₂, o₂'⟩ := ih₂ hs' hr' hA₁ x₁.wb_right
    exact ⟨d₂, .whileLtN_true (by rw [hA.nreg _ hs.1.1, hA.nreg _ hs.1.2]; exact ht) x₁ x₂, hA₂,
      hK₁.trans hK₂, L₁ ++ L₂, by rw [o₂, o₁, List.append_assoc],
      by rw [o₂', o₁', List.append_assoc]⟩
  | whileLtR_false ht hw =>
    intro d hA hd
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    exact ⟨d, .whileLtR_false (by rw [hA.rreg _ hs.1.1, hA.rreg _ hs.1.2]; exact ht) hd, hA,
      Keep.refl _ _ _, [], by simp, by simp⟩
  | whileLtR_true ht e₁ e₂ ih₁ ih₂ =>
    intro d hA hd
    have hs' := hs; have hr' := hr
    simp only [Stmt.regsOK, Stmt.noRand, Bool.and_eq_true] at hs hr
    obtain ⟨d₁, x₁, hA₁, hK₁, L₁, o₁, o₁'⟩ := ih₁ hs.2 hr hA hd
    obtain ⟨d₂, x₂, hA₂, hK₂, L₂, o₂, o₂'⟩ := ih₂ hs' hr' hA₁ x₁.wb_right
    exact ⟨d₂, .whileLtR_true (by rw [hA.rreg _ hs.1.1, hA.rreg _ hs.1.2]; exact ht) x₁ x₂, hA₂,
      hK₁.trans hK₂, L₁ ++ L₂, by rw [o₂, o₁, List.append_assoc],
      by rw [o₂', o₁', List.append_assoc]⟩

/-- Agreement on the registers below `R`. -/
abbrev below (R : ℕ) : ℕ → Bool := fun r => decide (r < R)

end Machine

end WordRAM
