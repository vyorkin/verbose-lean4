import Verbose.Tactics.Claim
import Verbose.Russian.Common
import Verbose.Russian.We
import Verbose.Russian.Since
import Verbose.Russian.TokenSupport

open Lean Verbose.Russian

declare_ru_tokens "Факт" "Утверждение" "доказательство" "из" "вычислением" "поскольку"
  "Заметим," "Получим," "что" "Получаем" "Берём"

namespace Verbose.Named
scoped macro ("Факт" <|> "Утверждение") name:ident " : " stmt:term " доказательство" colGt prf:tacticSeq: tactic =>
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by $prf))

scoped macro ("Факт" <|> "Утверждение") name:ident " : " stmt:term " из " prf:maybeAppliedRU : tactic => do
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by Заключаем по $prf))

scoped macro ("Факт" <|> "Утверждение") name:ident " : " stmt:term " вычислением" : tactic => do
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by Вычисляем))

scoped macro ("Факт" <|> "Утверждение") name:ident " : " stmt:term " поскольку " facts:factsRU : tactic =>
 withRef name  `(tactic|(checkName $name; have $name : $stmt := by Поскольку $facts заключаем, что $stmt))
end Verbose.Named

namespace Verbose.NameLess
scoped elab ("Факт" <|> "Утверждение") ":" stmt:term " доказательство" colGt prf:tacticSeq : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by $prf)

scoped elab ("Заметим, что " <|> "Получим, что ") stmt:term : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by strongAssumption)

scoped elab ("Получаем " <|> "Берём ") news:newObjectNameLessRU : tactic => do
  let newsT ← newObjectNameLessRUToTerm news
  let news_patt := newObjectNameLessRUToRCasesPatt news
  sinceObtainTac newsT news_patt #[]

scoped elab ("Факт" <|> "Утверждение") " : " stmt:term " из " prf:maybeAppliedRU : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by Заключаем по $prf)

scoped elab ("Факт" <|> "Утверждение") " : " stmt:term " вычислением" : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by Вычисляем)

scoped elab ("Факт" <|> "Утверждение") " : " stmt:term " поскольку " facts:factsRU : tactic =>
  mkClaim stmt fun name ↦ `(tactic|have $name : $stmt := by Поскольку $facts заключаем, что $stmt)

end Verbose.NameLess

setLang ru

section
open Verbose.Named
example : 1 = 1 := by
  Утверждение H : 1 = 1 доказательство
    rfl
  exact H

example : 1 + 1 = 2 := by
  Факт H : 1 + 1 = 2 вычислением
  exact H

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Утверждение H : ε ≥ 0 из ε_pos
  rfl

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Факт H : ε ≥ 0 поскольку ε > 0
  rfl

set_option linter.unusedVariables false

example (n : ℕ) : n + n + n = 3*n := by
  Факт key : n + n = 2*n доказательство
    ring
  ring

example (n : ℤ) (h : 0 < n) : True := by
  Факт key : 0 < 2*n доказательство
    linarith only [h]
  Факт keybis : 0 < 2*n из mul_pos применённый к zero_lt_two и h
  trivial
end

section
open Verbose.NameLess
example : 1 = 1 := by
  Утверждение: 1 = 1 доказательство
    rfl
  exact h

example : 1 + 1 = 2 := by
  Факт: 1 + 1 = 2 вычислением
  exact h

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Утверждение: ε ≥ 0 из ε_pos
  rfl

example (ε : ℝ) (ε_pos : 0 < ε) : 1 = 1 := by
  Факт: ε ≥ 0 поскольку ε > 0
  rfl

set_option linter.unusedVariables false

example (n : ℕ) : n + n + n = 3*n := by
  Факт: n + n = 2*n доказательство
    ring
  ring

example (n : ℤ) (h : 0 < n) : True := by
  Факт: 0 < 2*n доказательство
    linarith only [h]
  Факт: 0 < 2*n из mul_pos применённый к zero_lt_two и h
  trivial

lemma foo_ex : ∃ N : Nat, True := by simp

addAnonymousFactSplittingLemma foo_ex

example (A : ℝ) : True := by
  Получаем N : ℕ такой, что True
  trivial
end
