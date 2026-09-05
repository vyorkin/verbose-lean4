import Verbose.Tactics.Lets
import Verbose.Russian.TokenSupport
import Mathlib.Tactic.Linarith

open Lean

-- NB: multi-word literal atoms are internally split into individual whitespace-separated
-- word tokens by the `syntax`/`macro`/`elab` sugar, so each word (with its attached
-- punctuation) must be registered on its own, not as a combined phrase.
declare_ru_tokens "Докажем" "Докажем," "по" "индукции" "индукции," "что" "сначала,"
  "теперь," "подходит" "противоречие" "контрапозицию:"

namespace Verbose.Named
scoped elab "Докажем по индукции " name:ident " : " stmt:term : tactic =>
letsInduct name.getId stmt
end Verbose.Named

namespace Verbose.NameLess
scoped elab "Докажем по индукции, что " stmt:term : tactic =>
letsInduct none stmt
end Verbose.NameLess

open Lean Elab Tactic in
macro "Докажем, что " stmt:term : tactic =>
`(tactic| first | show $stmt | apply Or.inl; show $stmt | apply Or.inr; show $stmt | fail "Это не то, что нужно доказать. Возможно, вы имели в виду «Докажем сначала, что»?")

declare_syntax_cat explicitStmtRU
syntax " : " term : explicitStmtRU

def toStmt (e : Lean.TSyntax `explicitStmtRU) : Lean.Term := ⟨e.raw[1]!⟩

elab "Докажем, что " witness:term " подходит" stmt:(explicitStmtRU)? : tactic => do
  useTac witness (stmt.map toStmt)

elab "Докажем сначала, что " stmt:term : tactic =>
  anonymousSplitLemmaTac stmt

elab "Докажем теперь, что " stmt:term : tactic =>
  unblockTac stmt

syntax "Нужно объявить: Докажем теперь, что " term : term

open Lean Parser Term PrettyPrinter Delaborator in
@[delab app.goalBlocker]
def goalBlocker_delab : Delab := whenPPOption Lean.getPPNotation do
  let stx ← SubExpr.withAppArg delab
  `(Нужно объявить: Докажем теперь, что $stx)

macro "Докажем противоречие" : tactic => `(tactic|exfalso)

implement_endpoint (lang := ru) wrongContraposition : CoreM String :=
pure "Это не контрапозиция текущей цели."

elab "Докажем контрапозицию: " stmt:term : tactic =>
  showContraposeTac stmt

implement_endpoint (lang := ru) inductionError : CoreM String :=
pure "Утверждение должно начинаться с квантора всеобщности по натуральному числу."

implement_endpoint (lang := ru) notWhatIsNeeded : CoreM String :=
pure "Это не то, что нужно доказать."

implement_endpoint (lang := ru) notWhatIsRequired : CoreM String :=
pure "Это не то, что требуется сейчас."

setLang ru

example : 1 + 1 = 2 := by
  Докажем, что 2 = 2
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Докажем, что 2 подходит
  rfl

example : ∃ k : ℕ, 4 = 2*k := by
  Докажем, что 2 подходит: 4 = 2*2
  rfl

example : True ∧ True := by
  Докажем сначала, что True
  trivial
  Докажем теперь, что True
  trivial

example (P Q : Prop) (h : P) : P ∨ Q := by
  Докажем, что P
  exact h

example (P Q : Prop) (h : Q) : P ∨ Q := by
  Докажем, что Q
  exact h

example : 0 = 0 ∧ 1 = 1 := by
  Докажем сначала, что 0 = 0
  trivial
  Докажем теперь, что 1 = 1
  trivial

example : (0 : ℤ) = 0 ∧ 1 = 1 := by
  Докажем сначала, что 0 = 0
  trivial
  Докажем теперь, что 1 = 1
  trivial

example : 0 = 0 ∧ 1 = 1 := by
  Докажем сначала, что 1 = 1
  trivial
  Докажем теперь, что 0 = 0
  trivial

example : True ↔ True := by
  Докажем сначала, что True → True
  exact id
  Докажем теперь, что True → True
  exact id

example (h : False) : 2 = 1 := by
  Докажем противоречие
  exact h

section
open Verbose.NameLess

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 4 := by
  Докажем по индукции, что ∀ k, P k
  . exact h₀
  . intro k hyp_rec
    exact h k hyp_rec

set_option linter.unusedVariables false in
example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : True := by
  Докажем по индукции, что ∀ k, P k
  exacts [h₀, h, trivial]

end

section
open Verbose.Named

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 4 := by
  Докажем по индукции H : ∀ k, P k
  . exact h₀
  . intro k hyp_rec
    exact h k hyp_rec

example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : ∀ k, P k := by
  Докажем по индукции H : ∀ k, P k
  . exact h₀
  . intro k hyp_rec
    exact h k hyp_rec

example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : P 3 := by
  success_if_fail_with_msg "Утверждение должно начинаться с квантора всеобщности по натуральному числу."
    Докажем по индукции H : true
  Докажем по индукции H : ∀ n, P n
  exact h₀
  exact h

set_option linter.unusedVariables false in
example (P : ℕ → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) : True := by
  Докажем по индукции H : ∀ k, P k
  exacts [h₀, h, trivial]

example : True := by
  Докажем по индукции H : ∀ l, l < l + 1
  decide
  intro l
  intros hl
  linarith
  trivial

-- Check free variable is cleared when main goal is the statement proven
-- by induction applied to a free variable.
set_option linter.unusedTactic false in
example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) (N : ℕ) : P N := by
  Докажем по индукции H : ∀ k, P k
  . fail_if_success let x : Nat := N
    exact h₀
  . fail_if_success let x : Nat := N
    intro k hyp_rec
    exact h k hyp_rec

-- Same with an assumption depending on it
set_option linter.unusedTactic false in
set_option linter.unusedVariables false in
example (P : Nat → Prop) (h₀ : P 0) (h : ∀ n, P n → P (n+1)) (N : ℕ) (hN : Odd N) : P N := by
  Докажем по индукции H : ∀ k, P k
  . fail_if_success let x : Nat := N
    exact h₀
  . fail_if_success let x : Nat := N
    intro k hyp_rec
    exact h k hyp_rec

set_option linter.unusedVariables false in
example : True := by
  success_if_fail_with_msg "Утверждение должно начинаться с квантора всеобщности по натуральному числу."
    Докажем по индукции H : true
  success_if_fail_with_msg "Утверждение должно начинаться с квантора всеобщности по натуральному числу."
    Докажем по индукции H : ∀ n : ℤ, true
  trivial

end

example (P Q : Prop) (h : P ∧ Q) : P ∧ Q := by
  constructor
  Докажем сначала, что P
  exact h.1
  Докажем теперь, что Q
  exact h.2

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  Докажем контрапозицию: ¬ Q → ¬ P
  exact h

example (P Q : Nat → Prop) (h : (∀ x, ¬ Q x) → ∃ x, ¬ P x) : (∀ x, P x) → (∃ x, Q x)  := by
  Докажем контрапозицию: (∀ x, ¬ Q x) → ∃ x, ¬ P x
  exact h

example (P Q : Nat → Prop) (h : (∀ x, ¬ Q x) → ¬ ∀ x, P x) : (∀ x, P x) → (∃ x, Q x)  := by
  Докажем контрапозицию: (∀ x, ¬ Q x) → ¬ (∀ x, P x)
  exact h

private def foo (P : Nat → Prop) := ∀ x, P x
configureUnfoldableDefs foo

example (P Q : Nat → Prop) (h : (∀ x, ¬ Q x) → ¬ ∀ x, P x) : foo P → (∃ x, Q x)  := by
  Докажем контрапозицию: (∀ x, ¬ Q x) → ¬ (∀ x, P x)
  exact h

example (P Q : Nat → Prop) (h : (∀ x, ¬ Q x) → ∃ x, ¬ P x) : foo P → (∃ x, Q x)  := by
  Докажем контрапозицию: (∀ x, ¬ Q x) → ∃ x, ¬ P x
  exact h
