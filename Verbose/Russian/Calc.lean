import Verbose.Tactics.Calc
import Verbose.Russian.Common
import Verbose.Russian.We
import Verbose.Russian.By
import Verbose.Russian.TokenSupport

section widget

open ProofWidgets
open Lean Meta

implement_endpoint (lang := ru) getSince? : MetaM String := pure "поскольку?"
implement_endpoint (lang := ru) createOneStepMsg : MetaM String := pure "Создать новый шаг"
implement_endpoint (lang := ru) createTwoStepsMsg : MetaM String := pure "Создать два новых шага"

/-- Rpc function for the calc widget. -/
@[server_rpc_method]
def VerboseCalcPanelRU.rpc := mkSelectionPanelRPC' verboseSuggestSteps
  "Пожалуйста, выделите некоторые подвыражения в цели, используя shift-клик."
  "Создание нового шага вычисления"
  (extraCss := some "#suggestions {display:none}")

/-- The calc widget. -/
@[widget_module]
def WidgetCalcPanelRU : Component CalcParams :=
  mk_rpc_widget% VerboseCalcPanelRU.rpc

implement_endpoint (lang := ru) mkComputeCalcTac : MetaM String := pure "вычислением"
implement_endpoint (lang := ru) mkComputeCalcDescr : MetaM String := pure "Обосновать вычислением"
implement_endpoint (lang := ru) mkComputeAssptTac : MetaM String := pure "по предположению"
implement_endpoint (lang := ru) mkComputeAssptDescr : MetaM String := pure "Обосновать предположением"
implement_endpoint (lang := ru) mkSinceCalcTac : MetaM String := pure "поскольку"
implement_endpoint (lang := ru) mkSinceCalcHeader : MetaM String := pure "Обосновать, используя"
implement_endpoint (lang := ru) mkSinceCalcArgs (args : Array Format) : MetaM String := do
  return match args with
  | #[] => ""
  | #[x] => s!"{x}"
  | a => ", ".intercalate ((a[:a.size-1]).toArray.toList.map (toString)) ++ s!" и {a[a.size-1]!}"

configureCalcSuggestionProvider verboseSelectSince

implement_endpoint (lang := ru) theSelectedSubExpr : MetaM String :=
  pure "Выделенное подвыражение"
implement_endpoint (lang := ru) allSelectedSubExpr : MetaM String :=
  pure "Все выделенные подвыражения"
implement_endpoint (lang := ru) inMainGoal : MetaM String :=
  pure "в основной цели."
implement_endpoint (lang := ru) inMainGoalOrCtx : MetaM String :=
  pure "в основной цели или её контексте."
implement_endpoint (lang := ru) shouldBe : MetaM String :=
  pure "должно быть"
implement_endpoint (lang := ru) shouldBePl : MetaM String :=
  pure "должны быть"
implement_endpoint (lang := ru) selectOnlyOne : MetaM String :=
  pure "Нужно выделить только одно подвыражение."
implement_endpoint (lang := ru) factCannotJustifyStep : CoreM String :=
  return  "Этот факт не позволяет напрямую обосновать этот шаг."
implement_endpoint (lang := ru) factsCannotJustifyStep : CoreM String :=
  return  "Перечисленные факты не позволяют напрямую обосновать этот шаг."

/-- Rpc function for the calc justification widget. -/
@[server_rpc_method]
def VerboseCalcSincePanelRU.rpc := mkSelectionPanelRPC' (onlyGoal := false) getCalcSuggestion
  "Можно выбрать локальное предположение."
  "Обоснование"
  verboseGetDefaultCalcSuggestions
  (extraCss := some "#suggestions {display:none}")

/-- The calc justification widget. -/
@[widget_module]
def WidgetCalcSincePanelRU : Component CalcParams :=
  mk_rpc_widget% VerboseCalcSincePanelRU.rpc
end widget

namespace Lean.Elab.Tactic
open Meta Verbose Russian

declare_ru_tokens "Вычислим" "Вычислим?"

declare_syntax_cat CalcFirstStepRU
syntax ppIndent(colGe term (" из "  sepBy(maybeAppliedRU, " и из "))?) : CalcFirstStepRU
syntax ppIndent(colGe term (" по предположению")?) : CalcFirstStepRU
syntax ppIndent(colGe term (" вычислением")?) : CalcFirstStepRU
syntax ppIndent(colGe term (" поскольку " factsRU)?) : CalcFirstStepRU
syntax ppIndent(colGe term (" поскольку?")?) : CalcFirstStepRU
syntax ppIndent(colGe term (" по " tacticSeq)?) : CalcFirstStepRU

-- enforce indentation of calc steps so we know when to stop parsing them
declare_syntax_cat CalcStepRU
syntax ppIndent(colGe term " из " sepBy(maybeAppliedRU, " и из ")) : CalcStepRU
syntax ppIndent(colGe term " по предположению") : CalcStepRU
syntax ppIndent(colGe term " вычислением") : CalcStepRU
syntax ppIndent(colGe term " поскольку " factsRU) : CalcStepRU
syntax ppIndent(colGe term " поскольку?") : CalcStepRU
syntax ppIndent(colGe term " по " tacticSeq) : CalcStepRU
syntax CalcStepRUs := ppLine withPosition(CalcFirstStepRU) withPosition((ppLine linebreak CalcStepRU)*)

syntax (name := calcTacticRU) "Вычислим" CalcStepRUs : tactic

elab tk:"sinceCalcTacRU" facts:factsRU : tactic => withRef tk <| sinceCalcTac (factsRUToArray facts)

def convertFirstCalcStepRU (step : TSyntax `CalcFirstStepRU) : TermElabM (TSyntax ``calcFirstStep × Option Syntax) := do
  match step with
  | `(CalcFirstStepRU|$t:term) => pure (← `(calcFirstStep|$t:term), none)
  | `(CalcFirstStepRU|$t:term по%$btk предположению%$ctk) =>
    pure (← run t btk ctk `(tacticSeq| strong_assumption), none)
  | `(CalcFirstStepRU|$t:term вычислением%$ctk) =>
    pure (← run t ctk ctk `(tacticSeq| computeCalcTac), none)
  | `(CalcFirstStepRU|$t:term из%$tk $prfs и из*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedRUToTerm
    pure (← run t tk none `(tacticSeq| fromCalcTac $prfTs,*), none)
  | `(CalcFirstStepRU|$t:term поскольку%$tk $facts:factsRU) =>
    pure (← run t tk none `(tacticSeq|sinceCalcTacRU%$tk $facts), none)
  | `(CalcFirstStepRU|$t:term поскольку?%$tk) =>
    pure (← run t tk none `(tacticSeq|sorry%$tk), some tk)
  | `(CalcFirstStepRU|$t:term по%$tk $prf:tacticSeq) =>
    pure (← run t tk none `(tacticSeq|tacSeqCalcTac $prf), none)
  | _ => throwUnsupportedSyntax
where
  run (t : Term) (btk : Syntax) (ctk? : Option Syntax)
      (tac : TermElabM (TSyntax `Lean.Parser.Tactic.tacticSeq)) :
      TermElabM (TSyntax `Lean.calcFirstStep) := do
    let ctk := ctk?.getD btk
    let tacs ← withRef ctk tac
    let pf ← withRef step.raw[1] `(term| by%$btk $tacs)
    let pf := pf.mkInfoCanonical
    withRef step <| `(calcFirstStep|$t:term := $pf)

def convertCalcStepRU (step : TSyntax `CalcStepRU) : TermElabM (TSyntax ``calcStep × Option Syntax) := do
  match step with
  | `(CalcStepRU|$t:term по%$btk предположению%$ctk) =>
    pure (← run t btk ctk `(tacticSeq| strong_assumption), none)
  | `(CalcStepRU|$t:term вычислением%$ctk) =>
    pure (← run t ctk ctk `(tacticSeq| computeCalcTac), none)
  | `(CalcStepRU|$t:term из%$tk $prfs и из*) => do
    let prfTs ← liftMetaM <| prfs.getElems.mapM maybeAppliedRUToTerm
    pure (← run t tk none `(tacticSeq| fromCalcTac $prfTs,*), none)
  | `(CalcStepRU|$t:term поскольку%$tk $facts:factsRU) =>
    pure (← run t tk none `(tacticSeq|sinceCalcTacRU%$tk $facts), none)
  | `(CalcStepRU|$t:term поскольку?%$tk) =>
    pure (← run t tk none `(tacticSeq|sorry%$tk), some tk)
  | `(CalcStepRU|$t:term по%$tk $prf:tacticSeq) =>
    pure (← run t tk none `(tacticSeq|tacSeqCalcTac $prf), none)
  | _ => throwUnsupportedSyntax
where
  run (t : Term) (btk : Syntax) (ctk? : Option Syntax)
      (tac : TermElabM (TSyntax `Lean.Parser.Tactic.tacticSeq)) :
      TermElabM (TSyntax `Lean.calcStep) := do
    let ctk := ctk?.getD btk
    let tacs ← withRef ctk tac
    let pf ← withRef step.raw[1] `(term| by%$btk $tacs)
    let pf := pf.mkInfoCanonical
    withRef step <| `(calcStep|$t:term := $pf)

def convertCalcStepsRU (steps : TSyntax ``CalcStepRUs) : TermElabM (TSyntax ``calcSteps × Array (Option Syntax)) := do
  match steps with
  | `(CalcStepRUs| $first:CalcFirstStepRU
       $steps:CalcStepRU*) => do
         let (first, tk?) ← convertFirstCalcStepRU first
         let mut newsteps := #[]
         let mut tks? := #[tk?]
         for step in steps do
           let (newstep, tk?) ← convertCalcStepRU step
           newsteps := newsteps.push newstep
           tks? := tks?.push tk?
         pure (← `(calcSteps|$first
           $newsteps*), tks?)
  | _ => throwUnsupportedSyntax

elab_rules : tactic
| `(tactic|Вычислим%$calcstx $stx) => do
  let steps : TSyntax ``CalcStepRUs := ⟨stx⟩
  let (steps, tks?) ← convertCalcStepsRU steps
  let views ← Lean.Elab.Term.mkCalcStepViews steps
  if (← verboseConfigurationExt.get).useCalcWidget then
    if let some calcRange := (← getFileMap).lspRangeOfStx? calcstx then
    let indent := calcRange.start.character + 2
    let mut isFirst := true
    for (step, tk?) in views.zip tks? do
      if let some replaceRange := (← getFileMap).lspRangeOfStx? step.ref then
        let json := json% {"replaceRange": $(replaceRange),
                           "isFirst": $(isFirst),
                           "indent": $(indent)}
        Lean.Widget.savePanelWidgetInfo WidgetCalcPanelRU.javascriptHash (pure json) step.proof
      if let some tk := tk? then
        if let some replaceRange := (← getFileMap).lspRangeOfStx? tk then
          let json := json% {"replaceRange": $(replaceRange),
                             "isFirst": $(isFirst),
                             "indent": $(indent)}
          Lean.Widget.savePanelWidgetInfo WidgetCalcSincePanelRU.javascriptHash (pure json) tk
      isFirst := false
  evalVerboseCalc (← `(tactic|calc%$calcstx $steps))

syntax (name := Calc?RU) "Вычислим?" : tactic

elab "Вычислим?" : tactic =>
  mkCalc?Tac "Создать вычисление" "Вычислим" "поскольку?"

setLang ru

example (a b : ℕ) : (a + b)^ 2 = 2*a*b + (a^2 + b^2) := by
  success_if_fail_with_msg "Unknown identifier `x`"
    Вычислим (x+b)^2 = a^2 + b^2 + 2*a*b вычислением
    _ = 2*a*b + (a^2 + b^2) вычислением
  Вычислим (a+b)^2 = a^2 + b^2 + 2*a*b   вычислением
    _           = 2*a*b + (a^2 + b^2) вычислением

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Вычислим a + c    ≤ b + c из h
  _              ≤ b + d из h'

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Вычислим a + 0 + c = a + c вычислением
  _              ≤ b + c из h
  _              ≤ b + d из h'

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Вычислим a + 0 + c = a + c вычислением
  _              ≤ b + c поскольку a ≤ b
  _              ≤ b + d поскольку c ≤ d

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Вычислим a + 0 + c = a + c вычислением
  _              ≤ b + d поскольку a ≤ b и c ≤ d

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Вычислим a + 0 + c = a + c вычислением
  _              ≤ b + d из h и из h'

example (a b c d : ℕ) (h : a ≤ b) (h' : c ≤ d) : a + 0 + c ≤ b + d := by
  Вычислим a + 0 + c = a + c вычислением
  _              ≤ b + d из h и из h'

def even_fun  (f : ℝ → ℝ) := ∀ x, f (-x) = f x

example (f g : ℝ → ℝ) : even_fun f → even_fun g →  even_fun (f + g) := by
  intro hf hg
  show ∀ x, (f+g) (-x) = (f+g) x
  intro x₀
  Вычислим (f + g) (-x₀) = f (-x₀) + g (-x₀) вычислением
  _                  = f x₀ + g (-x₀)    поскольку f (-x₀) = f x₀
  _                  = f x₀ + g x₀       поскольку g (-x₀) = g x₀
  _                  = (f + g) x₀        вычислением

example (f g : ℝ → ℝ) : even_fun f →  even_fun (g ∘ f) := by
  intro hf x
  Вычислим (g ∘ f) (-x) = g (f (-x)) вычислением
                _   = g (f x)    поскольку f (-x) = f x

example (f : ℝ → ℝ) (x : ℝ) (hx : f (-x) = f x ∧ 1 = 1) : f (-x) + 0 = f x := by
  Вычислим f (-x) + 0 = f (-x) вычислением
                _   = f x  поскольку f (-x) = f x

example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) (x) :  (f+g) (-x) = (f+g) x := by
  Вычислим (f + g) (-x) = f (-x) + g (-x) вычислением
  _                 = f x + g (-x)    поскольку even_fun f
  _                 = f x + g x       поскольку even_fun g
  _                 = (f + g) x       вычислением

example (ε : ℝ) (h : ε > 1) : 0 ≤ ε := by
  Вычислим
    (0 : ℝ) ≤ 1 по norm_num
    _       < ε из h

example (ε : ℝ) (h : ε > 1) : ε ≥ 0 := by
  Вычислим
    (0 : ℝ) ≤ 1 по norm_num
    _       < ε из h

example (ε : ℝ) (h : ε > 1) : ε ≥ 0 := by
  Вычислим
    ε > 1 из h
    _ > 0 по norm_num

example (ε : ℝ) (h : ε = 1) : ε+1 ≥ 2 := by
  Вычислим
    ε + 1 = 1 + 1 по rw [h]
    _     = 2 по norm_num

example (ε : ℝ) (h : ε = 1) : ε+1 ≤ 2 := by
  Вычислим
    ε + 1 = 1 + 1 по rw [h]
    _     = 2 по norm_num

example (f : ℝ → ℝ) (h : ∀ x, f (f x) = x) : f (f 0) + 0 = 0 := by
  Вычислим f (f 0) + 0 = f (f 0) вычислением
       _           = 0       по предположению

example (f : ℝ → ℝ) (h : ∀ x, f (f x) = x) : f (f 0) = 0 + 0 := by
  Вычислим f (f 0) = 0      по предположению
       _       = 0  + 0 вычислением

example (u : ℕ → ℝ) (y) (hy : ∀ n, u n = y) (n m) : u n = u m := by
  Вычислим
    u n = y поскольку ∀ n, u n = y
    _   = u m поскольку ∀ n, u n = y

-- Next two examples check casting capabilities

example (ε : ℝ) (ε_pos : 1/ε > 0) (N : ℕ) (hN : N ≥ 1 / ε) : N > 0 := by
  success_if_fail_with_msg "'calc' expression has type
  3 > 0
but is expected to have type
  N > 0"
    Вычислим
      3 ≥ 1/ε поскольку?
      _ > 0 из ε_pos
  Вычислим
    N ≥ 1/ε из hN
    _ > 0 из ε_pos

-- Combine with relaxed calc now
example (ε : ℝ) (ε_pos : 1/ε > 0) (N : ℕ) (hN : N ≥ 1 / ε) : N ≥ 0 := by
  success_if_fail_with_msg "'calc' expression has type
  3 > 0
but is expected to have type
  N ≥ 0"
    Вычислим
      3 ≥ 1/ε поскольку?
      _ > 0 из ε_pos
  Вычислим
    N ≥ 1/ε из hN
    _ > 0 из ε_pos

-- A case where the conclusion has an extra cast
example (N : ℕ) (hN : N ≥ 3) : N > (1 : ℝ) := by
  Вычислим
    N ≥ 3 из hN
    _ > 1 вычислением

-- Combine with relaxed calc now
example (N : ℕ) (hN : N ≥ 3) : N ≥ (1 : ℝ) := by
  Вычислим
    N ≥ 3 из hN
    _ > 1 вычислением

example (x : ℝ) (p : ℕ) (h : x ≤ p) : x < (p + 1 : ℕ) := by
  Вычислим x ≤ p по assumption
    _ < p + 1 вычислением

-- Regression test for bug where simp reached max recursion depth
example (a b : ℝ) (h : a = a*b) : a - a* b = 0 := by
  Вычислим a - a*b = 0 поскольку a = a*b

example (u : Nat → Nat) (h : ∀ n, u n = u 0)
  : ∀ n, ∀ m, u m = u n := by
  intro m n
  success_if_fail_with_msg "invalid 'calc' step, left-hand side is
  u m : ℕ
but is expected to be
  u n : ℕ"
    Вычислим
      u m = u 0 поскольку ∀ n, u n = u 0
      _   = u n поскольку ∀ n, u n = u 0
  success_if_fail_with_msg "invalid 'calc' step, right-hand side is
  u n : ℕ
but is expected to be
  u m : ℕ"
    Вычислим
      u n = u 0 поскольку ∀ n, u n = u 0
      _   = u n поскольку ∀ n, u n = u 0
  Вычислим
    u n = u 0 поскольку ∀ n, u n = u 0
    _   = u m поскольку ∀ n, u n = u 0
