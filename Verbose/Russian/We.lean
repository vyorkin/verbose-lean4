import Verbose.Tactics.Since
import Verbose.Tactics.We
import Verbose.Russian.Common
import Verbose.Russian.TokenSupport

open Lean Elab Parser Tactic Verbose.Russian

declare_ru_tokens "Переписываем," "используя" "везде" "Продолжаем," "Продолжаем" "в"
  "зависимости" "от" "Заключаем" "по" "Комбинируем" "и" "Вычисляем" "Применяем" "к"
  "Забываем" "Переформулируем" "как" "Переименовываем" "предположении" "Раскрываем"
  "Переходим" "контрапозиции" "просто" "Вносим" "отрицание" "Приходим" "противоречию" "с"

syntax locationRU := withPosition(" в предположении " (locationWildcard <|> locationHyp))

def locationRU_to_location : TSyntax `locationRU → TacticM (TSyntax `Lean.Parser.Tactic.location)
| `(locationRU|в предположении $x) => `(location|at $x)
| _ => `(location|at *) -- should not happen

declare_syntax_cat becomesRU
syntax colGt " что даёт " term : becomesRU

def extractBecomesRU (e : Lean.TSyntax `becomesRU) : Lean.Term := ⟨e.raw[1]!⟩

elab rw:"Переписываем, используя " s:myRwRuleSeq l:(locationRU)? new:(becomesRU)? : tactic => do
  let loc ← l.mapM locationRU_to_location
  rewriteTac rw s (loc.map expandLocation) (new.map extractBecomesRU)

elab rw:"Переписываем, используя " s:myRwRuleSeq " везде" : tactic => do
  rewriteTac rw s (some Location.wildcard) none

elab "Продолжаем, используя " exp:term : tactic =>
  discussOr exp

elab "Продолжаем в зависимости от " exp:term : tactic =>
  discussEm exp

implement_endpoint (lang := ru) cannotConclude : CoreM String :=
pure "Это не завершает доказательство."

elab "Заключаем по " e:maybeAppliedRU : tactic => do
  concludeTac (← maybeAppliedRUToTerm e)

elab "Комбинируем " prfs:sepBy(term, " и ") : tactic => do
  combineTac prfs.getElems

implement_endpoint (lang := ru) computeFailed (goal : MessageData) : TacticM MessageData :=
  pure m!"Похоже, что цель {goal} не следует из вычисления без использования локального предположения."

elab "Вычисляем" loc:(locationRU)? : tactic => do
  let loc ← loc.mapM locationRU_to_location
  computeTac loc

elab "Применяем " exp:term : tactic => do
  evalApply (← `(tactic|apply $exp))

elab "Применяем " exp:term " к " e:term : tactic => do
  evalTactic (← `(tactic|specialize $exp $e))

macro "Забываем " args:(ppSpace colGt term:max)+ : tactic => `(tactic|clear $args*)

macro "Переформулируем " h:ident " как " new:term : tactic => `(tactic|change $new at $h:ident)

implement_endpoint (lang := ru) renameResultSeveralLoc : CoreM String :=
pure "Результат переименования можно указать только при переименовании в одном месте."

elab "Переименовываем" old:ident " в " new:ident loc:(locationRU)? become?:(becomesRU)? : tactic => do
  let loc? ← loc.mapM locationRU_to_location
  renameTac old new loc? (become?.map extractBecomesRU)

implement_endpoint (lang := ru) unfoldResultSeveralLoc : CoreM String :=
pure "Результат раскрытия можно указать только при раскрытии в одном месте."

elab "Раскрываем " tgt:ident loc:(locationRU)? new:(becomesRU)? : tactic => do
  let loc? ← loc.mapM locationRU_to_location
  let new? := new.map extractBecomesRU
  unfoldTac tgt loc? new?

elab "Переходим к контрапозиции" : tactic => contraposeTac true

elab "Переходим к контрапозиции" " просто": tactic => contraposeTac false

elab "Вносим отрицание " l:(locationRU)? new:(becomesRU)? : tactic => do
  let loc ← l.mapM locationRU_to_location
  pushNegTac (loc.map expandLocation) (new.map extractBecomesRU)

implement_endpoint (lang := ru) rwResultWithoutGoal : CoreM String :=
pure "Результат переписывания можно указать, только если ещё есть что доказывать."

implement_endpoint (lang := ru) rwResultSeveralLoc : CoreM String :=
pure "Результат переписывания можно указать только при переписывании в одном месте."

implement_endpoint (lang := ru) cannotContrapose : CoreM String :=
pure "Невозможно перейти к контрапозиции: текущая цель не является импликацией."

namespace Verbose.Contradicting

scoped elab "Приходим к противоречию с " facts:factsRU : tactic => do
  let factsT := factsRUToArray facts
  sinceConcludeTac (← `(term| False)) factsT

end Verbose.Contradicting

setLang ru

example (P Q : Prop) (h : P ∨ Q) : True := by
  Продолжаем, используя h
  . intro _hP
    trivial
  . intro _hQ
    trivial


example (P : Prop) : True := by
  Продолжаем в зависимости от P
  . intro _hP
    trivial
  . intro _hnP
    trivial

set_option linter.unusedVariables false in
example (P Q R : Prop) (hRP : R → P) (hR : R) (hQ : Q) : P := by
  success_if_fail_with_msg "Application type mismatch: The argument
  hQ
has type
  Q
but is expected to have type
  R
in the application
  hRP hQ"
    Заключаем по hRP применённый к hQ
  Заключаем по hRP применённый к hR

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  Заключаем по h применённый к _

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  Заключаем по h

example {a b : ℕ}: a + b = b + a := by
  Вычисляем

example {a : ℕ}: 2*a + 1 ≥ a + 1 := by
  Вычисляем

example {a b : ℕ} (h : a + b - a = 0) : b = 0 := by
  Вычисляем в предположении h
  Заключаем по h

addAnonymousComputeLemma abs_sub_le
addAnonymousComputeLemma abs_sub_comm

example {x y : ℝ} : |x - y| = |y - x| := by
  Вычисляем

example {x y z : ℝ} : |x - y| ≤ |x - z| + |z - y| := by
  Вычисляем

example {x y z : ℝ} : 2*|x - y| + 3 ≤ 2*(|x - z| + |z - y|) + 3 := by
  Вычисляем

example (a : ℝ) (h : a ≤ 3) : a + 5 ≤ 3 + 5 := by
  success_if_fail_with_msg "Похоже, что цель a + 5 ≤ 3 + 5 не следует из вычисления без использования локального предположения."
    Вычисляем
  rel [h]

variable (k : Nat)

example (h : True) : True := by
  Заключаем по h

example (h : ∀ _n : ℕ, True) : True := by
  Заключаем по h применённый к 0

example (h : True → True) : True := by
  Применяем h
  trivial

example (h : ∀ _n _k : ℕ, True) : True := by
  Заключаем по h применённый к 0 и 1

example (a b : ℕ) (h : a < b) : a ≤ b := by
  Заключаем по h

example (a b c : ℕ) (h : a < b ∧ a < c) : a ≤ b := by
  Заключаем по h

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  Комбинируем h и h'

example (a b c : ℤ) (h : a = b + c) (h' : b - a = c) : c = 0 := by
  Комбинируем h и h'

example (a b c : ℕ) (h : a ≤ b) (h' : b ≤ c ∧ a+b ≤ a+c) : a ≤ c := by
  Комбинируем h и h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  Переписываем, используя ← h
  Заключаем по h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  Переписываем, используя h в предположении h'
  Заключаем по h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  Переписываем, используя ← h в предположении h' что даёт a = 0
  exact h'

example (a b : Nat) (h : a = b) (h' : b = 0): a = 0 := by
  Переписываем, используя ← h в предположении h'
  clear h
  exact h'

example (f : ℕ → ℕ) (n : ℕ) (h : n > 0 → f n = 0) (hn : n > 0): f n = 0 := by
  Переписываем, используя h
  exact hn

example (f : ℕ → ℕ) (h : ∀ n > 0, f n = 0) : f 1 = 0 := by
  Переписываем, используя h
  norm_num

example (a b c : ℕ) (h : a = b) (h' : a = c) : b = c := by
  success_if_fail_with_msg "Данный терм
  a = c
не равен по определению ожидаемому
  b = c"
    Переписываем, используя [h] в предположении h' что даёт a = c
  Переписываем, используя [h] в предположении h' что даёт b = c
  Заключаем по h'

example (a b c : ℕ) (h : a = b) (h' : a = c) : a = c := by
  Переписываем, используя h везде
  Заключаем по h'

example (P Q : Prop) (h : P → Q) (h' : P) : Q := by
  Применяем h к h'
  Заключаем по h

example (P Q R : Prop) (h : P → Q → R) (hP : P) (hQ : Q) : R := by
  Заключаем по h применённый к hP и hQ

example (P : ℕ → Prop) (h : ∀ n, P n) : P 0 := by
  Применяем h к 0
  Заключаем по h


example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  Переходим к контрапозиции
  intro h
  use x/2
  constructor
  Заключаем по h
  Заключаем по h

example (ε : ℝ) (h : ε > 0) : ε ≥ 0 := by Заключаем по h
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by Заключаем по h
example (ε : ℝ) (h : ε > 0) : ε ≥ -1 := by Заключаем по h
example (ε : ℝ) (h : ε > 0) : ε/2 ≥ -3 := by Заключаем по h

example (x : ℝ) (h : x = 3) : 2*x = 6 := by Заключаем по h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  Переходим к контрапозиции просто
  intro h
  Вносим отрицание
  Вносим отрицание в предположении h
  use x/2
  constructor
  · Заключаем по h
  · Заключаем по h

example (x : ℝ) : (∀ ε > 0, x ≤ ε) → x ≤ 0 := by
  Переходим к контрапозиции просто
  intro h
  success_if_fail_with_msg "Данный терм
  0 < x
не равен по определению ожидаемому
  ∃ ε > 0, ε < x"
    Вносим отрицание что даёт 0 < x
  Вносим отрицание что даёт ∃ ε > 0, ε < x
  success_if_fail_with_msg "Данный терм
  ∃ ε > 0, ε < x
не равен по определению ожидаемому
  0 < x"
    Вносим отрицание в предположении h что даёт ∃ ε > 0, ε < x
  Вносим отрицание в предположении h что даёт 0 < x
  use x/2
  constructor
  · Заключаем по h
  · Заключаем по h

def test_ub (A : Set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x
def test_sup (A : Set ℝ) (x : ℝ) := test_ub A x ∧ ∀ y, test_ub A y → x ≤ y

example {A : Set ℝ} {x : ℝ} (hx : test_sup A x) :
∀ y, y < x → ∃ a ∈ A, y < a := by
  intro y
  Переходим к контрапозиции
  rcases hx with ⟨hx₁, hx₂⟩
  exact hx₂ y

set_option linter.unusedVariables false in
example : (∀ n : ℕ, False) → 0 = 1 := by
  Переходим к контрапозиции
  intro h
  use 1

example (P Q : Prop) (h : P ∨ Q) : True := by
  Продолжаем, используя h
  all_goals
    intro
    trivial

example (P : Prop) (hP₁ : P → True) (hP₂ : ¬ P → True): True := by
  Продолжаем в зависимости от P
  intro h
  exact hP₁ h
  intro h
  exact hP₂ h

set_option linter.unusedVariables false

namespace Verbose.Russian

def f (n : ℕ) := 2*n

example : f 2 = 4 := by
  Раскрываем f
  rfl

example (h : f 2 = 4) : True → True := by
  Раскрываем f в предположении h
  guard_hyp h :ₛ 2*2 = 4
  exact id

example (h : f 2 = 4) : True → True := by
  success_if_fail_with_msg "hypothesis h has type
  2 * 2 = 4
not
  2 * 2 = 5"
    Раскрываем f в предположении h что даёт 2*2 = 5
  success_if_fail_with_msg "hypothesis h has type
  2 * 2 = 4
not
  Verbose.Russian.f 2 = 4"
    Раскрываем f в предположении h что даёт f 2 = 4
  Раскрываем f в предположении h что даёт 2*2 = 4
  exact id

set_option linter.unusedTactic false

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  Переименовываем n в p в предположении h
  Переименовываем k в l в предположении h
  guard_hyp_strict h : ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) (h : ∀ n : ℕ, ∃ k, P n k) : True := by
  Переименовываем n в p в предположении h что даёт ∀ p, ∃ k, P p k
  success_if_fail_with_msg "hypothesis h has type
  ∀ (p : ℕ), ∃ l, P p l
not
  ∀ (p : ℕ), ∃ j, P p j"
    Переименовываем k в l в предположении h что даёт ∀ p, ∃ j, P p j
  Переименовываем k в l в предположении h что даёт ∀ p, ∃ l, P p l
  guard_hyp_strict h :  ∀ p, ∃ l, P p l
  trivial

example (P : ℕ → ℕ → Prop) : (∀ n : ℕ, ∃ k, P n k) ∨ True := by
  Переименовываем n в p
  Переименовываем k в l
  guard_target_strict (∀ p, ∃ l, P p l) ∨ True
  right
  trivial

example (a b c : ℤ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  rcases h1 with ⟨k, hk⟩
  rcases h2 with ⟨l, hl⟩
  show ∃ k, c = a * k
  Переименовываем k в m
  guard_target_strict ∃ m, c = a * m
  use k*l
  rw [hl, hk]
  ring

example (a b c : ℕ) : True := by
  Забываем a
  Забываем b c
  trivial

example (h : 1 + 1 = 2) : True := by
  success_if_fail_with_msg "
'change' tactic failed, pattern
  2 = 3
is not definitionally equal to target
  1 + 1 = 2"
    Переформулируем h как 2 = 3
  Переформулируем h как 2 = 2
  trivial

open Verbose.Contradicting in
example (p : Prop) (_ : p) (_ : ¬ p) : False := by
  Приходим к противоречию с p и ¬ p

end Verbose.Russian
