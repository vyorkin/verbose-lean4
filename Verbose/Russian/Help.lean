import Verbose.Tactics.Help
import Verbose.Russian.Tactics
import Verbose.Russian.TokenSupport

open Lean Meta Elab Tactic Term Verbose

namespace Verbose.Russian

declare_ru_tokens "помощь"

implement_endpoint (lang := ru) try_this : CoreM String := pure "Попробуйте: "

implement_endpoint (lang := ru) apply_suggestion : CoreM String := pure "Применить предложение"

open Lean.Parser.Tactic in
elab "помощь" h:(colGt ident)? : tactic => do
unless (← verboseConfigurationExt.get).useHelpTactic do
  throwError "Тактика помощи не включена."
match h with
| some h => do
    let (s, msg) ← gatherSuggestions (helpAtHyp (← getMainGoal) h.getId)
    if s.isEmpty then
      logInfo (msg.getD "Нет предложений")
    else
      addSuggestions (← getRef) s (header := "Помощь")
| none => do
    let (s, msg) ← gatherSuggestions (helpAtGoal (← getMainGoal))
    if s.isEmpty then
      logInfo (msg.getD "Нет предложений")
    else
      addSuggestions (← getRef) s (header := "Помощь")

def describe (t : Format) : String :=
match toString t with
| "ℝ" => "вещественное число"
| "ℕ" => "натуральное число"
| "ℤ" => "целое число"
| t => "выражение типа " ++ t

def describe_pl (t : Format) : String :=
match toString t with
| "ℝ" => "некоторые вещественные числа"
| "ℕ" => "некоторые натуральные числа"
| "ℤ" => "некоторые целые числа"
| t => "некоторые выражения типа " ++ t

def libre (s : Ident) : String := s!"Имя {s.getId} можно выбрать свободно среди доступных имён."

def printIdentList (l : List Ident) : String := commaSep (l.toArray.map (toString ·.getId)) "и"

def libres (ls : List Ident) : String :=
s!"Имена {printIdentList ls} можно выбрать свободно среди доступных имён."

def describeHypShape (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "Предположение {hyp} имеет вид «{headDescr}»"

def describeHypStart (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "Предположение {hyp} начинается с «{headDescr}»"

implement_endpoint (lang := ru) helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|По $hyp.ident:term получаем $nameS:ident такой, что ($ineqIdent : $ineqS) и ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

implement_endpoint (lang := ru) helpSinceExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (hypS ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|Поскольку $hypS:term получаем $nameS:ident такой, что ($ineqIdent : $ineqS) и ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

implement_endpoint (lang := ru) helpConjunctionSuggestion (hyp : Name) (h₁I h₂I : Ident) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... и ..."
  describeHypShape hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|По $hyp.ident:term получаем ($h₁I : $p₁S) ($h₂I : $p₂S))
  pushComment <| libres [h₁I, h₂I]

implement_endpoint (lang := ru) helpSinceConjunctionSuggestion (hyp : Name) (p₁S p₂S : Term) :
    SuggestionM Unit := do
  let headDescr := "... и ..."
  describeHypShape hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|Поскольку $p₁S:term ∧ $p₂S получаем, что $p₁S:term и $p₂S)

implement_endpoint (lang := ru) helpDisjunctionSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "Предположение {hyp} имеет вид « ... или ... »"
  pushCom "Можно использовать его так:"
  pushTac `(tactic|Продолжаем, используя $hyp.ident:term)

implement_endpoint (lang := ru) helpSinceDisjunctionSuggestion (hyp : Name) (p₁S p₂S : Term) : SuggestionM Unit := do
  describeHypShape hyp "... или ..."
  pushCom "Можно использовать его так:"
  pushTac `(tactic|Различаем случаи $p₁S:term или $p₂S)

implement_endpoint (lang := ru) helpImplicationSuggestion (hyp HN H'N : Name) (closes : Bool)
    (le re : Expr) : SuggestionM Unit := do
  pushCom "Предположение {hyp} — импликация"
  if closes then do
    pushCom "Заключение этой импликации — текущая цель"
    pushCom "Поэтому можно использовать это предположение так:"
    pushTac `(tactic| По $hyp.ident:term достаточно доказать, что $(← le.stx))
    flush
    pushCom "Если уже есть доказательство {HN} утверждения {← le.fmt}, можно использовать:"
    pushTac `(tactic|Заключаем по $hyp.ident:term применённый к $HN.ident)
  else do
    pushCom "Посылка этой импликации — {← le.fmt}"
    pushCom "Если есть доказательство {HN} утверждения {← le.fmt},"
    pushCom "можно использовать это предположение так:"
    pushTac `(tactic|По $hyp.ident:term применённый к $HN.ident:term получаем $H'N.ident:ident : $(← re.stx):term)
    pushComment <| libre H'N.ident

implement_endpoint (lang := ru) helpSinceImplicationSuggestion (stmt goalS leS : Term) (hyp : Name) (closes : Bool)
    (le re : Expr) : SuggestionM Unit := do
  pushCom "Предположение {hyp} — импликация"
  if closes then do
    pushCom "Заключение этой импликации — текущая цель"
    pushCom "Поэтому можно использовать это предположение так:"
    pushTac `(tactic| Поскольку $stmt:term достаточно доказать, что $(← le.stx):term)
    flush
    pushCom "Если уже есть доказательство утверждения {← le.fmt}, можно использовать:"
    pushTac `(tactic|Поскольку $stmt:term и $(← le.stx):term заключаем, что $goalS)
  else do
    pushCom "Посылка этой импликации — {← le.fmt}"
    pushCom "Если есть доказательство утверждения {← le.fmt},"
    pushCom "можно использовать это предположение так:"
    pushTac `(tactic|Поскольку $stmt:term и $leS:term получаем, что $(← re.stx):term)

implement_endpoint (lang := ru) helpEquivalenceSuggestion (hyp hyp'N : Name) (l r : Expr) : SuggestionM Unit := do
  pushCom "Предположение {hyp} — эквивалентность"
  pushCom "Можно заменить левую часть (а именно {← l.fmt}) на правую (а именно {← r.fmt}) в цели так:"
  pushTac `(tactic|Переписываем, используя $hyp.ident:term)
  flush
  pushCom "Можно заменить правую часть на левую в цели так:"
  pushTac `(tactic|Переписываем, используя ← $hyp.ident)
  flush
  pushCom "Такую замену можно также выполнить в предположении {hyp'N} так:"
  pushTac `(tactic|Переписываем, используя $hyp.ident:term в предположении $hyp'N.ident:ident)
  flush
  pushCom "или"
  pushTac `(tactic|Переписываем, используя ← $hyp.ident:term в предположении $hyp'N.ident:ident)

implement_endpoint (lang := ru) helpSinceEquivalenceSuggestion
    (hyp : Name) (stmt : Term) (l r : Expr) : SuggestionM Unit := do
  pushCom "Предположение {hyp} — эквивалентность"
  pushCom "Можно заменить левую часть (а именно {← l.fmt}) на правую (а именно {← r.fmt}) или наоборот в цели так:"
  pushTac `(tactic|Поскольку $stmt:term достаточно доказать, что ?_)
  pushCom "заменив вопросительный знак на новую цель."
  flush
  pushCom "Такую замену можно также выполнить в утверждении, следующем из одного из текущих предположений, так:"
  pushTac `(tactic|Поскольку $stmt:term и ?_ получаем, что ?_)
  pushCom "заменив первый вопросительный знак на факт, в котором нужна замена, а второй — на новый полученный факт."

implement_endpoint (lang := ru) helpEqualSuggestion (hyp hyp' : Name) (closes : Bool) (l r : String) :
    SuggestionM Unit := do
  pushCom "Предположение {hyp} — равенство"
  if closes then
    pushComment <| s!"Текущая цель следует из него непосредственно"
    pushComment   "Можно использовать его так:"
    pushTac `(tactic|Заключаем по $hyp.ident:ident)
  else do
    pushCom "Можно заменить левую часть (а именно {l}) на правую (а именно {r}) в цели так:"
    pushTac `(tactic|Переписываем, используя $hyp.ident:ident)
    flush
    pushCom "Можно заменить правую часть на левую в цели так:"
    pushTac `(tactic|Переписываем, используя ← $hyp.ident:ident)
    flush
    pushCom "Такую замену можно также выполнить в предположении {hyp'} так:"
    pushTac `(tactic|Переписываем, используя $hyp.ident:ident в предположении $hyp'.ident:ident)
    flush
    pushCom "или"
    pushTac `(tactic|Переписываем, используя ← $hyp.ident:ident в предположении $hyp'.ident:ident)
    flush
    pushCom "Также можно использовать его в шаге вычисления или линейно скомбинировать с другими так:"
    pushTac `(tactic|Комбинируем [$hyp.ident:term, ?_])
    pushCom "заменив вопросительный знак на один или несколько термов, доказывающих равенства."

implement_endpoint (lang := ru) helpSinceEqualSuggestion (hyp : Name)
    (closes : Bool) (l r : String) (leS reS goalS : Term) : SuggestionM Unit := do
  pushCom "Предположение {hyp} — равенство"
  let eq ← `($leS = $reS)
  if closes then
    pushComment <| s!"Текущая цель следует из него непосредственно"
    pushComment   "Можно использовать его так:"
    pushTac `(tactic|Поскольку $eq:term заключаем, что $goalS)
  else do
    pushCom "Можно заменить левую часть (а именно {l}) на правую (а именно {r}) или наоборот в цели так:"
    pushTac `(tactic|Поскольку $eq:term достаточно доказать, что ?_)
    pushCom "заменив вопросительный знак на новую цель."
    flush
    pushCom "Такую замену можно также выполнить в утверждении, следующем из одного из текущих предположений, так:"
    pushTac `(tactic|Поскольку $eq:term и ?_ получаем, что ?_)
    pushCom "заменив первый вопросительный знак на факт, в котором нужна замена, а второй — на новый полученный факт."

implement_endpoint (lang := ru) helpIneqSuggestion (hyp : Name) (closes : Bool) : SuggestionM Unit := do
  pushCom "Предположение {hyp} — неравенство"
  if closes then
    pushCom "Оно непосредственно влечёт текущую цель."
    pushCom "Можно использовать его так:"
    pushTac `(tactic|Заключаем по $hyp.ident:ident)
  else do
    pushCom "Также можно использовать его в шаге вычисления или линейно скомбинировать с другими так:"
    pushTac `(tactic|Комбинируем [$hyp.ident:term, ?_])
    pushCom "заменив вопросительный знак на один или несколько термов, доказывающих равенства или неравенства."

implement_endpoint (lang := ru) helpSinceIneqSuggestion (hyp : Name) (stmt goal : Term) (closes : Bool) : SuggestionM Unit := do
  pushCom "Предположение {hyp} — неравенство"
  if closes then
    pushCom "Оно непосредственно влечёт текущую цель."
    pushCom "Можно использовать его так:"
    pushTac `(tactic|Поскольку $stmt:term заключаем, что $goal)
  else do
    flush
    pushCom "Также можно использовать его в шаге вычисления или линейно скомбинировать с другими так:"
    pushTac `(tactic| Поскольку $stmt:term и ?_ заключаем, что $goal)
    pushCom "заменив вопросительный знак на один или несколько термов, доказывающих равенства или неравенства."

implement_endpoint (lang := ru) helpMemInterSuggestion (hyp h₁ h₂ : Name) (elemS p₁S p₂S : Term) :
    SuggestionM Unit := do
  pushCom "Предположение {hyp} утверждает принадлежность пересечению"
  pushCom "Можно использовать его так:"
  pushTac `(tactic|По $hyp.ident:term получаем ($h₁.ident : $elemS ∈ $p₁S) ($h₂.ident : $elemS ∈ $p₂S))
  pushComment <| libres [h₁.ident, h₂.ident]

implement_endpoint (lang := ru) helpSinceMemInterSuggestion (stmt : Term) (hyp : Name) (mem₁ mem₂ : Term) :
    SuggestionM Unit := do
  pushCom "Предположение {hyp} утверждает принадлежность пересечению"
  pushCom "Можно использовать его так:"
  pushTac `(tactic|Поскольку $stmt:term получаем, что $mem₁:term и $mem₂)

implement_endpoint (lang := ru) helpMemUnionSuggestion (hyp : Name) :
    SuggestionM Unit := do
  pushCom "Предположение {hyp} утверждает принадлежность объединению"
  pushCom "Можно использовать его так:"
  pushTac `(tactic|Продолжаем, используя $hyp.ident)

implement_endpoint (lang := ru) helpSinceMemUnionSuggestion (elemS leS reS : Term) (hyp : Name) :
    SuggestionM Unit := do
  pushCom "Предположение {hyp} утверждает принадлежность объединению"
  pushCom "Можно использовать его так:"
  pushTac `(tactic|Различаем случаи $elemS ∈ $leS или $elemS ∈ $reS)

implement_endpoint (lang := ru) helpGenericMemSuggestion (hyp : Name) : SuggestionM Unit := do
  pushCom "Предположение {hyp} — утверждение о принадлежности"

implement_endpoint (lang := ru) helpContradictionSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushComment <| "Это предположение — противоречие."
  pushCom "Из него можно вывести что угодно так:"
  pushTac `(tactic|(Докажем противоречие
                    Заключаем по $hypId:ident))

implement_endpoint (lang := ru) helpSinceContradictionSuggestion
     (stmt goal : Term) : SuggestionM Unit := do
  pushComment <| "Это предположение — противоречие."
  pushCom "Из него можно вывести цель так:"
  pushTac `(tactic|Поскольку $stmt:term заключаем, что $goal)

implement_endpoint (lang := ru) helpSubsetSuggestion (hyp x hx hx' : Name)
    (r : Expr) (l ambientTypePP : Format) : SuggestionM Unit := do
  pushCom "Предположение {hyp} обеспечивает включение {l} в {← r.fmt}."
  pushCom "Можно использовать его так:"
  pushTac `(tactic| По $hyp.ident:ident применённый к $x.ident используя $hx.ident получаем $hx'.ident:ident : $x.ident ∈ $(← r.stx))
  pushCom "где {x} — {describe ambientTypePP}, а {hx} доказывает, что {x} ∈ {l}"
  pushComment <| libre hx'.ident

implement_endpoint (lang := ru) helpSinceSubsetSuggestion (hyp x : Name) (stmt new : Term)
    (l r : Expr) (ambientTypePP : Format) : SuggestionM Unit := do
  pushCom "Предположение {hyp} обеспечивает включение {← l.fmt} в {← r.fmt}."
  pushCom "Можно использовать его так:"
  pushTac `(tactic| Поскольку $stmt:term и $x.ident ∈ $(← l.stx) получаем, что $new:term)
  pushCom "где {x} — {describe ambientTypePP}"

implement_endpoint (lang := ru) assumptionClosesSuggestion (hypId : Ident) : SuggestionM Unit := do
  pushCom "Это предположение — как раз то, что нужно доказать"
  pushCom "Можно использовать его так:"
  pushTac `(tactic|Заключаем по $hypId:ident)

implement_endpoint (lang := ru) assumptionUnfoldingSuggestion (hypId : Ident) (expandedHypTypeS : Term) :
    SuggestionM Unit := do
  pushCom "Это предположение начинается с применения определения."
  pushCom "Можно сделать это явным так:"
  pushTac `(tactic|Переформулируем $hypId:ident как $expandedHypTypeS)
  flush

implement_endpoint (lang := ru) helpForAllRelExistsRelSuggestion (hyp var_name' n₀ hn₀ : Name)
    (headDescr hypDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|По $hyp.ident:term применённый к $n₀.ident используя $hn₀.ident получаем $var_name'.ident:ident такой, что ($ineqIdent : $ineqS) и ($hn'S : $p'S))
  pushCom "где {n₀} — {describe t}, а {hn₀} — доказательство того, что {hypDescr}."
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := ru) helpSinceForAllRelExistsRelSuggestion (stmt :
    Term) (hyp var_name' n₀ : Name) (stmtn₀ : Term)
    (stmtn₀Str headDescr : String) (t : Format) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|Поскольку $stmt:term и $stmtn₀ получаем $var_name'.ident:ident такой, что $ineqS и $p'S)
  pushCom "где {n₀} — {describe t}, а отношение {stmtn₀Str} должно следовать непосредственно из предположения."
  pushComment <| libre var_name'.ident

implement_endpoint (lang := ru) helpForAllRelExistsSimpleSuggestion (hyp n' hn' n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|По $hyp.ident:term применённый к $n₀.ident используя $hn₀.ident получаем $n'.ident:ident такой, что ($hn'.ident : $p'S))
  pushCom "где {n₀} — {describe t}, а {hn₀} — доказательство того, что {n₀rel}"
  pushComment <| libres [n'.ident, hn'.ident]

implement_endpoint (lang := ru) helpSinceForAllRelExistsSimpleSuggestion (stmt : Term)
  (hyp n' n₀ : Name)
  (stmtn₀ : Term) (stmtn₀Str headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|Поскольку $stmt:term и $stmtn₀ получаем $n'.ident:ident такой, что $p'S)
  pushCom "где {n₀} — {describe t}, а отношение {stmtn₀Str} должно следовать непосредственно из предположения."
  pushComment <| libre n'.ident

implement_endpoint (lang := ru) helpForAllRelGenericSuggestion (hyp n₀ hn₀ : Name)
    (headDescr n₀rel : String) (t : Format) (newsI : Ident) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|По $hyp.ident:term применённый к $n₀.ident используя $hn₀.ident получаем ($newsI : $pS))
  pushCom "где {n₀} — {describe t}, а {hn₀} — доказательство того, что {n₀rel}"
  pushComment <| libre newsI

implement_endpoint (lang := ru) helpSinceForAllRelGenericSuggestion (stmt : Term) (hyp n₀ : Name)
  (stmtn₀ : Term)
  (stmtn₀Str headDescr : String) (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|Поскольку $stmt:term и $stmtn₀ получаем, что $pS:term)
  pushCom "где {n₀} — {describe t}, а {stmtn₀Str} следует непосредственно из предположения."

implement_endpoint (lang := ru) helpForAllSimpleExistsRelSuggestion (hyp var_name' nn₀ : Name)
    (headDescr : String) (t : Format) (hn'S ineqIdent : Ident) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|По $hyp.ident:term применённый к $nn₀.ident получаем $var_name'.ident:ident такой, что ($ineqIdent : $ineqS) и ($hn'S : $p'S))
  pushCom "где {nn₀} — {describe t}"
  pushComment <| libres [var_name'.ident, ineqIdent, hn'S]

implement_endpoint (lang := ru) helpSinceForAllSimpleExistsRelSuggestion (stmt : Term) (hyp var_name' nn₀ : Name)
    (headDescr : String) (t : Format) (ineqS p'S : Term) :
    SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|Поскольку $stmt:term получаем $var_name'.ident:ident такой, что $ineqS и $p'S)
  pushCom "где {nn₀} — {describe t}"
  pushComment <| libre var_name'.ident

implement_endpoint (lang := ru) helpForAllSimpleExistsSimpleSuggestion (hyp var_name' hn' nn₀  : Name)
    (headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|По $hyp.ident:term применённый к $nn₀.ident получаем $var_name'.ident:ident такой, что ($hn'.ident : $p'S))
  pushCom "где {nn₀} — {describe t}"
  pushComment <| libres [var_name'.ident, hn'.ident]

implement_endpoint (lang := ru) helpSinceForAllSimpleExistsSimpleSuggestion (stmt : Term) (hyp var_name' nn₀  : Name)
    (headDescr : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|Поскольку $stmt:term получаем $var_name'.ident:ident такой, что $p'S)
  pushCom "где {nn₀} — {describe t}"
  pushComment <| libre var_name'.ident

implement_endpoint (lang := ru) helpForAllSimpleForAllRelSuggestion (hyp nn₀ var_name'₀ H h : Name)
    (headDescr rel₀ : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  pushCom "Предположение {hyp} начинается с «{headDescr}"
  pushCom "Можно использовать его так:"
  pushTac `(tactic|По $hyp.ident:term применённый к $nn₀.ident и $var_name'₀.ident используя $H.ident получаем ($h.ident : $p'S))
  pushCom "где {nn₀} и {var_name'₀} — {describe_pl t}, а {H} — доказательство {rel₀}"
  pushComment <| libre h.ident

implement_endpoint (lang := ru) helpSinceForAllSimpleForAllRelSuggestion (stmt rel₀S : Term) (hyp nn₀ var_name'₀ : Name)
    (headDescr rel₀ : String) (t : Format) (p'S : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Можно использовать его так:"
  let facts ← arrayToFactsRU #[stmt, rel₀S]
  pushTac `(tactic|Поскольку $facts:factsRU получаем, что $p'S:term)
  pushCom "где {nn₀} и {var_name'₀} — {describe_pl t}, а {rel₀} следует непосредственно из предположения."

implement_endpoint (lang := ru) helpForAllSimpleGenericSuggestion (hyp nn₀ hn₀ : Name) (headDescr : String)
    (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|По $hyp.ident:term применённый к $nn₀.ident получаем ($hn₀.ident : $pS))
  pushCom "где {nn₀} — {describe t}"
  pushComment <| libre hn₀.ident
  flush
  pushCom "Если это предположение больше не понадобится в общем виде, можно также конкретизировать {hyp} так:"
  pushTac `(tactic|Применяем $hyp.ident:ident к $nn₀.ident)

implement_endpoint (lang := ru) helpSinceForAllSimpleGenericSuggestion (stmt : Term) (hyp nn₀ : Name) (headDescr : String)
    (t : Format) (pS : Term) : SuggestionM Unit := do
  describeHypStart hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|Поскольку $stmt:term получаем, что $pS:term)
  pushCom "где {nn₀} — {describe t}"
  flush
  pushCom "Если это предположение больше не понадобится в общем виде, можно также конкретизировать {hyp} так:"
  pushTac `(tactic|Применяем $hyp.ident:ident к $nn₀.ident)

implement_endpoint (lang := ru) helpForAllSimpleGenericApplySuggestion (prf : Expr) (but : Format) :
    SuggestionM Unit := do
  let prfS ← prf.toMaybeAppliedRU
  pushCom "Поскольку цель — {but}, можно использовать:"
  pushTac `(tactic|Заключаем по $prfS)

implement_endpoint (lang := ru) helpExistsSimpleSuggestion (hyp n hn : Name) (headDescr : String)
    (pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic|По $hyp.ident:term получаем $n.ident:ident такой, что ($hn.ident : $pS))
  pushComment <| libres [n.ident, hn.ident]

implement_endpoint (lang := ru) helpSinceExistsSimpleSuggestion (stmt : Term) (hyp n : Name) (headDescr : String)
    (pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "Можно использовать его так:"
  pushTac `(tactic| Поскольку $stmt:term получаем $n.ident:ident такой, что $pS)
  pushComment <| libre n.ident

implement_endpoint (lang := ru) helpDataSuggestion (hyp : Name) (t : Format) : SuggestionM Unit := do
  pushComment <| s!"Объект {hyp}" ++ match t with
    | "ℝ" => " — фиксированное вещественное число."
    | "ℕ" => " — фиксированное натуральное число."
    | "ℤ" => " — фиксированное целое число."
    | s => s!" : {s} фиксирован."

implement_endpoint (lang := ru) helpNothingSuggestion : SuggestionM Unit := do
  pushCom "Мне нечего сказать об этом предположении."
  flush

implement_endpoint (lang := ru) helpNothingGoalSuggestion : SuggestionM Unit := do
  pushCom "Мне нечего сказать об этой цели."
  flush

def descrGoalHead (headDescr : String) : SuggestionM Unit :=
 pushCom "Цель начинается с «{headDescr}»"

def descrGoalShape (headDescr : String) : SuggestionM Unit :=
 pushCom "Цель имеет вид «{headDescr}»"

def descrDirectProof : SuggestionM Unit :=
 pushCom "Поэтому прямое доказательство начинается так:"

implement_endpoint (lang := ru) helpUnfoldableGoalSuggestion (expandedGoalTypeS : Term) :
    SuggestionM Unit := do
  pushCom "Цель начинается с применения определения."
  pushCom "Можно сделать это явным так:"
  pushTac `(tactic|Докажем, что $expandedGoalTypeS)
  flush

implement_endpoint (lang := ru) helpAnnounceGoalSuggestion (actualGoalS : Term) : SuggestionM Unit := do
  pushCom "Следующий шаг — объявить:"
  pushTac `(tactic| Докажем теперь, что $actualGoalS)

implement_endpoint (lang := ru) helpFixSuggestion (headDescr : String) (ineqS : TSyntax `fixDecl) :
    SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Пусть $ineqS)

implement_endpoint (lang := ru) helpExistsRelGoalSuggestion (headDescr : String) (n₀ : Name) (t : Format)
    (fullTgtS : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Докажем, что $n₀.ident подходит: $fullTgtS)
  pushCom "заменив {n₀} на {describe t}"

implement_endpoint (lang := ru) helpExistsGoalSuggestion (headDescr : String) (nn₀ : Name) (t : Format)
    (tgt : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic|Докажем, что $nn₀.ident подходит: $tgt)
  pushCom "заменив {nn₀} на {describe t}"

implement_endpoint (lang := ru) helpConjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... и ..."
  descrDirectProof
  pushTac `(tactic|Докажем сначала, что $p)
  pushCom "После завершения этого первого доказательства останется доказать, что {← p'.fmt}"
  flush
  pushCom "Можно также начать с"
  pushTac `(tactic|Докажем сначала, что $p')
  pushCom "тогда после завершения этого первого доказательства останется доказать, что {← p.fmt}"

implement_endpoint (lang := ru) helpDisjunctionGoalSuggestion (p p' : Term) : SuggestionM Unit := do
  descrGoalShape "... или ..."
  pushCom "Поэтому прямое доказательство начинается с объявления того, какая из альтернатив будет доказана:"
  pushTac `(tactic|Докажем, что $p)
  flush
  pushCom "или:"
  pushTac `(tactic|Докажем, что $p')

open Verbose.Named in
implement_endpoint (lang := ru) helpImplicationGoalSuggestion (headDescr : String) (Hyp : Name)
    (leStx : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic| Предположим $Hyp.ident:ident : $leStx)
  pushComment <| libre Hyp.ident

open Verbose.NameLess in
implement_endpoint (lang := ru) helpImplicationGoalNLSuggestion (headDescr : String) (leStx : Term) : SuggestionM Unit := do
  descrGoalHead headDescr
  descrDirectProof
  pushTac `(tactic| Предположим, что $leStx)

implement_endpoint (lang := ru) helpEquivalenceGoalSuggestion (mpF mrF : Format) (mpS mrS : Term) :
    SuggestionM Unit := do
  pushCom "Цель — эквивалентность. Можно объявить доказательство импликации слева направо так:"
  pushTac `(tactic|Докажем сначала, что $mpS)
  pushCom "После доказательства этого первого утверждения останется доказать, что {mrF}"
  flush
  pushCom "Можно также начать с"
  pushTac `(tactic|Докажем сначала, что $mrS)
  pushCom "тогда после завершения этого первого доказательства останется доказать, что {mpF}"

implement_endpoint (lang := ru) helpSetEqSuggestion (lS rS : Term) : SuggestionM Unit := do
  pushCom "Цель — равенство множеств"
  pushCom "Можно доказать это переписыванием так:"
  pushTac `(tactic|Переписываем, используя ?_)
  flush
  pushCom "или начать вычисление так:"
  pushTac `(tactic|Calc $lS:term = $rS поскольку?)
  flush
  pushCom "Можно также доказать это через двойное включение."
  pushCom "В этом случае доказательство начинается так:"
  pushTac `(tactic|Докажем сначала, что $lS ⊆ $rS)

implement_endpoint (lang := ru) helpSinceSetEqSuggestion (lS rS : Term) : SuggestionM Unit := do
  pushCom "Цель — равенство множеств"
  pushCom "Можно доказать это переписыванием так:"
  pushTac `(tactic|Поскольку ?_ достаточно доказать, что ?_)
  flush
  pushCom "или начать вычисление так:"
  pushTac `(tactic|Calc $lS:term = $rS поскольку?)
  flush
  pushCom "Можно также доказать это через двойное включение."
  pushCom "В этом случае доказательство начинается так:"
  pushTac `(tactic|Докажем сначала, что $lS ⊆ $rS)

implement_endpoint (lang := ru) helpEqGoalSuggestion (lS rS : Term) : SuggestionM Unit := do
  pushCom "Цель — равенство"
  pushCom "Можно доказать это переписыванием так:"
  pushTac `(tactic|Переписываем, используя ?_)
  flush
  pushCom "или начать вычисление так:"
  pushTac `(tactic|Calc $lS:term = $rS поскольку?)
  flush
  pushCom "Можно также составить линейную комбинацию предположений так:"
  pushTac `(tactic|Комбинируем [?_, ?_])

implement_endpoint (lang := ru) helpSinceEqGoalSuggestion (goal : Term) : SuggestionM Unit := do
  pushCom "Цель — равенство"
  pushCom "Можно доказать это переписыванием так:"
  pushTac `(tactic|Поскольку ?_ заключаем, что $goal)
  flush
  pushCom "или начать вычисление так:"
  pushTac `(tactic|Calc $goal:term поскольку?)

implement_endpoint (lang := ru) helpIneqGoalSuggestion (goal : Term) (rel : String) : SuggestionM Unit := do
  pushCom "Цель — неравенство"
  pushCom "Можно начать вычисление так:"
  pushTac `(tactic|Calc $goal:term поскольку?)
  pushCom "Последняя строка вычисления не обязательно равенство, она может быть неравенством."
  pushCom "Аналогично первая строка может быть равенством. В целом символы отношений"
  pushCom "должны образовать цепочку, дающую {rel}"
  flush
  pushCom "Можно также составить линейную комбинацию предположений так:"
  pushTac `(tactic| Комбинируем [?_, ?_])

implement_endpoint (lang := ru) helpSinceIneqGoalSuggestion (goal : Term) (rel : String) : SuggestionM Unit := do
  pushCom "Цель — неравенство"
  pushCom "Можно начать вычисление так:"
  pushTac `(tactic|Calc $goal:term поскольку?)
  pushCom "Последняя строка вычисления не обязательно равенство, она может быть неравенством."
  pushCom "Аналогично первая строка может быть равенством. В целом символы отношений"
  pushCom "должны образовать цепочку, дающую {rel}"
  flush
  pushCom "Если это неравенство следует непосредственно из предположения, можно использовать:"
  pushTac `(tactic|Поскольку ?_ заключаем, что $goal)
  pushCom "заменив вопросительный знак на утверждение предположения."

implement_endpoint (lang := ru) helpMemInterGoalSuggestion (elem le : Expr) : SuggestionM Unit := do
  pushCom "Цель — доказать, что {← elem.fmt} принадлежит пересечению {← le.fmt} с другим множеством."
  pushCom "Поэтому прямое доказательство начинается так:"
  pushTac `(tactic|Докажем сначала, что $(← elem.stx) ∈ $(← le.stx))

implement_endpoint (lang := ru) helpMemUnionGoalSuggestion (elem le re : Expr) : SuggestionM Unit := do
  pushCom "Цель — доказать, что {← elem.fmt} принадлежит объединению {← le.fmt} и {← re.fmt}."
  descrDirectProof
  pushTac `(tactic|Докажем, что $(← elem.stx) ∈ $(← le.stx))
  flush
  pushCom "или:"
  pushTac `(tactic|Докажем, что $(← elem.stx) ∈ $(← re.stx))

implement_endpoint (lang := ru) helpNoIdeaGoalSuggestion : SuggestionM Unit := do
  pushCom "Нет идей."

implement_endpoint (lang := ru) helpSubsetGoalSuggestion (l r : Format) (xN : Name) (lT : Term) :
    SuggestionM Unit := do
  pushCom "Цель — включение {l} ⊆ {r}"
  descrDirectProof
  pushTac `(tactic| Пусть $xN.ident:ident ∈ $lT)
  pushComment <| libre xN.ident

implement_endpoint (lang := ru) helpFalseGoalSuggestion : SuggestionM Unit := do
  pushCom "Цель — доказать противоречие."
  pushCom "Можно применить предположение, являющееся отрицанием,"
  pushCom "то есть, по определению, имеющее вид P → false."

implement_endpoint (lang := ru) helpSinceFalseGoalSuggestion (goal : Term) : SuggestionM Unit := do
  pushCom "Цель — доказать противоречие."
  pushCom "Можно применить предположение, являющееся отрицанием,"
  pushCom "то есть, по определению, имеющее вид P → false."
  pushCom "Можно также скомбинировать два факта, явно противоречащих друг другу, так:"
  pushTac `(tactic|Поскольку ?_ и ?_ заключаем, что $goal)
  pushCom "заменив вопросительные знаки на эти два факта, непосредственно следующих из предположений."
  flush
  pushCom "Можно также сослаться на явно ложный факт (например, `0 = 1`), непосредственно следующий из предположения."
  pushTac `(tactic|Поскольку ?_ заключаем, что $goal)
  pushCom "заменив вопросительный знак на этот явно ложный факт."

implement_endpoint (lang := ru) helpContraposeGoalSuggestion : SuggestionM Unit := do
  pushCom "Цель — импликация."
  pushCom "Можно начать доказательство контрапозицией так:"
  pushTac `(tactic| Переходим к контрапозиции)

implement_endpoint (lang := ru) helpShowContrapositiveGoalSuggestion (stmt : Term) :
    SuggestionM Unit := do
  pushCom "Цель — импликация."
  pushCom "Можно начать доказательство контрапозицией так:"
  pushTac `(tactic| Докажем контрапозицию: $stmt)

open Verbose.Named in
implement_endpoint (lang := ru) helpByContradictionSuggestion (hyp : Ident) (assum : Term) : SuggestionM Unit := do
  pushCom "Можно начать доказательство от противного так:"
  pushTac `(tactic| Предположим от противного $hyp:ident : $assum)

open Verbose.NameLess in
implement_endpoint (lang := ru) helpByContradictionNLSuggestion (assum : Term) : SuggestionM Unit := do
  pushCom "Можно начать доказательство от противного так:"
  pushTac `(tactic| Предположим от противного, что $assum)

open Verbose.Named in
implement_endpoint (lang := ru) helpNegationGoalSuggestion (hyp : Ident) (p : Format) (assum : Term) :
    SuggestionM Unit := do
  pushCom "Цель — отрицание {p}, то есть {p} влечёт противоречие."
  pushCom "Поэтому прямое доказательство начинается так:"
  pushTac `(tactic| Предположим $hyp:ident : $assum)
  pushCom "И тогда останется доказать противоречие."

open Verbose.NameLess in
implement_endpoint (lang := ru) helpNegationNLGoalSuggestion (p : Format) (assum : Term) :
    SuggestionM Unit := do
  pushCom "Цель — отрицание {p}, то есть {p} влечёт противоречие."
  pushCom "Поэтому прямое доказательство начинается так:"
  pushTac `(tactic| Предположим, что $assum)
  pushCom "И тогда останется доказать противоречие."

open Verbose.Named in
implement_endpoint (lang := ru) helpNeGoalSuggestion (l r : Format) (lS rS : Term) (Hyp : Ident):
    SuggestionM Unit := do
  pushCom "Цель — отрицание {l} = {r}, то есть {l} = {r} влечёт противоречие."
  pushCom "Поэтому прямое доказательство начинается так:"
  pushTac `(tactic| Предположим $Hyp:ident : $lS = $rS)
  pushCom "И тогда останется доказать противоречие."

open Verbose.NameLess in
implement_endpoint (lang := ru) helpNeGoalNLSuggestion (l r : Format) (lS rS : Term) :
    SuggestionM Unit := do
  pushCom "Цель — отрицание {l} = {r}, то есть {l} = {r} влечёт противоречие."
  pushCom "Поэтому прямое доказательство начинается так:"
  pushTac `(tactic| Предположим, что $lS = $rS)
  pushCom "И тогда останется доказать противоречие."

set_option linter.unusedVariables false

configureAnonymousGoalSplittingLemmas Iff.intro Iff.intro' And.intro And.intro' abs_le_of_le_le abs_le_of_le_le'

configureHelpProviders DefaultHypHelp DefaultGoalHelp

set_option linter.unusedTactic false

/--
info: Помощь
  • Предположение h начинается с «∀ n > 0, ...»
    Можно использовать его так:
    По h применённый к n₀ используя hn₀ получаем (hyp : P n₀)
    где n₀ — натуральное число, а hn₀ — доказательство того, что n₀ > 0
    Имя hyp можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  помощь h
  apply h
  norm_num

/--
info: Помощь
  • Предположение h имеет вид «∃ n > 0, ...»
    Можно использовать его так:
    По h получаем n такой, что (n_pos : n > 0) и (hn : P n)
    Имена n, n_pos и hn можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h имеет вид «∃ ε > 0, ...»
    Можно использовать его так:
    По h получаем ε такой, что (ε_pos : ε > 0) и (hε : P ε)
    Имена ε, ε_pos и hε можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h начинается с «∀ n, ...»
    Можно использовать его так:
    По h применённый к n₀ получаем (hn₀ : P n₀ ⇒ Q n₀)
    где n₀ — натуральное число
    Имя hn₀ можно выбрать свободно среди доступных имён.
  • Если это предположение больше не понадобится в общем виде, можно также конкретизировать h так:
    Применяем h к n₀
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  помощь h
  exact h 2 h'

/--
info: Помощь
  • Предположение h начинается с «∀ n, ...»
    Можно использовать его так:
    По h применённый к n₀ получаем (hn₀ : P n₀)
    где n₀ — натуральное число
    Имя hn₀ можно выбрать свободно среди доступных имён.
  • Если это предположение больше не понадобится в общем виде, можно также конкретизировать h так:
    Применяем h к n₀
  • Поскольку цель — P 2, можно использовать:
    Заключаем по h применённый к 2
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  помощь h
  exact h 2

/--
info: Помощь
  • Предположение h — импликация
    Заключение этой импликации — текущая цель
    Поэтому можно использовать это предположение так:
    По h достаточно доказать, что P 1
  • Если уже есть доказательство H утверждения P 1, можно использовать:
    Заключаем по h применённый к H
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  помощь h
  exact h h'

/--
info: Помощь
  • Предположение h — импликация
    Посылка этой импликации — P 1
    Если есть доказательство H утверждения P 1,
    можно использовать это предположение так:
    По h применённый к H получаем H' : Q 2
    Имя H' можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h имеет вид «... и ...»
    Можно использовать его так:
    По h получаем (h_1 : P 1) (h' : Q 2)
    Имена h_1 и h' можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h — эквивалентность
    Можно заменить левую часть (а именно ∀ n ≥ 2, P n) на правую (а именно ∀ (l : ℕ), Q l) в цели так:
    Переписываем, используя h
  • Можно заменить правую часть на левую в цели так:
    Переписываем, используя ← h
  • Такую замену можно также выполнить в предположении hyp так:
    Переписываем, используя h в предположении hyp
  • или
    Переписываем, используя ← h в предположении hyp
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Цель имеет вид «... и ...»
    Поэтому прямое доказательство начинается так:
    Докажем сначала, что True
    После завершения этого первого доказательства останется доказать, что 1 = 1
  • Можно также начать с
    Докажем сначала, что 1 = 1
    тогда после завершения этого первого доказательства останется доказать, что True
-/
#guard_msgs in
example : True ∧ 1 = 1 := by
  помощь
  exact ⟨trivial, rfl⟩

/--
info: Помощь
  • Предположение h имеет вид « ... или ... »
    Можно использовать его так:
    Продолжаем, используя h
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Цель имеет вид «... или ...»
    Поэтому прямое доказательство начинается с объявления того, какая из альтернатив будет доказана:
    Докажем, что True
  • или:
    Докажем, что False
-/
#guard_msgs in
example : True ∨ False := by
  помощь
  left
  trivial

/-- info: Мне нечего сказать об этом предположении. -/
#guard_msgs in
example (P : Prop) (h : P) : True := by
  помощь h
  trivial

-- TODO: Improve this help message (low priority since it is very rare)
/--
info: Помощь
  • Это предположение — противоречие.
    Из него можно вывести что угодно так:
    ( Докажем противоречие
        Заключаем по h)
-/
#guard_msgs in
example (h : False) : 0 = 1 := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h — импликация
    Посылка этой импликации — l - n = 0
    Если есть доказательство H утверждения l - n = 0,
    можно использовать это предположение так:
    По h применённый к H получаем H' : P l k
    Имя H' можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h начинается с «∀ k ≥ 2, ∃ n ≥ 3, ...»
    Можно использовать его так:
    По h применённый к k₀ используя hk₀ получаем
        n такой, что (n_sup : n ≥ 3) и (hn : ∀ (l : ℕ), l - n = 0 ⇒ P l k₀)
    где k₀ — натуральное число, а hk₀ — доказательство того, что k₀ ≥ 2.
    Имена n, n_sup и hn можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h начинается с «∀ k n, k ≥ n ⇒ ...
    Можно использовать его так:
    По h применённый к k₀ и n₀ используя H получаем (h_1 : ∀ (l : ℕ), l - n₀ = 0 ⇒ P l k₀)
    где k₀ и n₀ — некоторые натуральные числа, а H — доказательство k₀ ≥ n₀
    Имя h_1 можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h начинается с «∀ k ≥ 2, ∃ n_1 ≥ 3, ...»
    Можно использовать его так:
    По h применённый к k₀ используя hk₀ получаем
        n_1 такой, что (n_1_sup : n_1 ≥ 3) и (hn_1 : ∀ (l : ℕ), l - n = 0 ⇒ P l k₀)
    где k₀ — натуральное число, а hk₀ — доказательство того, что k₀ ≥ 2.
    Имена n_1, n_1_sup и hn_1 можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h имеет вид «∃ n ≥ 5, ...»
    Можно использовать его так:
    По h получаем n такой, что (n_sup : n ≥ 5) и (hn : P n)
    Имена n, n_sup и hn можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h начинается с «∀ k ≥ 2, ∃ n ≥ 3, ...»
    Можно использовать его так:
    По h применённый к k₀ используя hk₀ получаем n такой, что (n_sup : n ≥ 3) и (hn : P n k₀)
    где k₀ — натуральное число, а hk₀ — доказательство того, что k₀ ≥ 2.
    Имена n, n_sup и hn можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h имеет вид «∃ n, ...»
    Можно использовать его так:
    По h получаем n такой, что (hn : P n)
    Имена n и hn можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h начинается с «∀ k, ∃ n, ...»
    Можно использовать его так:
    По h применённый к k₀ получаем n такой, что (hn : P n k₀)
    где k₀ — натуральное число
    Имена n и hn можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h начинается с «∀ k ≥ 2, ∃ n, ...»
    Можно использовать его так:
    По h применённый к k₀ используя hk₀ получаем n такой, что (hn : P n k₀)
    где k₀ — натуральное число, а hk₀ — доказательство того, что k₀ ≥ 2
    Имена n и hn можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n : ℕ, P n k) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Цель начинается с «∃ n, ...»
    Поэтому прямое доказательство начинается так:
    Докажем, что n₀ подходит : P n₀ ⇒ True
    заменив n₀ на натуральное число
-/
#guard_msgs in
example (P : ℕ → Prop): ∃ n : ℕ, P n → True := by
  помощь
  use 0
  tauto

/--
info: Помощь
  • Цель начинается с «P ⇒ ...»
    Поэтому прямое доказательство начинается так:
    Предположим hyp : P
    Имя hyp можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P Q : Prop) (h : Q) : P → Q := by
  помощь
  exact fun _ ↦ h

/--
info: Помощь
  • Цель начинается с «∀ n ≥ 0»
    Поэтому прямое доказательство начинается так:
    Пусть n ≥ 0
-/
#guard_msgs in
example : ∀ n ≥ 0, True := by
  помощь
  intros
  trivial

/--
info: Помощь
  • Цель начинается с «∀ n : ℕ,»
    Поэтому прямое доказательство начинается так:
    Пусть n : ℕ
-/
#guard_msgs in
example : ∀ n : ℕ, 0 ≤ n := by
  помощь
  exact Nat.zero_le

/--
info: Помощь
  • Цель начинается с «∃ n, ...»
    Поэтому прямое доказательство начинается так:
    Докажем, что n₀ подходит : 0 ≤ n₀
    заменив n₀ на натуральное число
-/
#guard_msgs in
example : ∃ n : ℕ, 0 ≤ n := by
  помощь
  use 1
  exact Nat.zero_le 1

/--
info: Помощь
  • Цель начинается с «∃ n ≥ 1, ...»
    Поэтому прямое доказательство начинается так:
    Докажем, что n₀ подходит : n₀ ≥ 1 ∧ True
    заменив n₀ на натуральное число
-/
#guard_msgs in
example : ∃ n ≥ 1, True := by
  помощь
  use 1

/-- info: Мне нечего сказать об этом предположении. -/
#guard_msgs in
example (h : Odd 3) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Цель — включение s ⊆ t
    Поэтому прямое доказательство начинается так:
    Пусть x ∈ s
    Имя x можно выбрать свободно среди доступных имён.
---
info: Помощь
  • Предположение h обеспечивает включение s в t.
    Можно использовать его так:
    По h применённый к x_1 используя hx получаем hx' : x_1 ∈ t
    где x_1 — натуральное число, а hx доказывает, что x_1 ∈ s
    Имя hx' можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (s t : Set ℕ) (h : s ⊆ t) : s ⊆ t := by
  помощь
  Пусть x ∈ s
  помощь h
  exact h x_mem

/--
info: Помощь
  • Предположение h утверждает принадлежность пересечению
    Можно использовать его так:
    По h получаем (h_1 : x ∈ s) (h' : x ∈ t)
    Имена h_1 и h' можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  помощь h
  По h получаем (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Помощь
  • Предположение h утверждает принадлежность пересечению
    Можно использовать его так:
    По h получаем (h_1 : x ∈ s) (h' : x ∈ t)
    Имена h_1 и h' можно выбрать свободно среди доступных имён.
---
info: Помощь
  • Цель — доказать, что x принадлежит пересечению t с другим множеством.
    Поэтому прямое доказательство начинается так:
    Докажем сначала, что x ∈ t
---
info: Помощь
  • Следующий шаг — объявить:
    Докажем теперь, что x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ t ∩ s := by
  помощь h
  По h получаем (h_1 : x ∈ s) (h' : x ∈ t)
  помощь
  Докажем сначала, что x ∈ t
  exact h'
  помощь
  Докажем теперь, что x ∈ s
  exact h_1

open Verbose.Named in
/--
info: Помощь
  • Предположение h утверждает принадлежность объединению
    Можно использовать его так:
    Продолжаем, используя h
---
info: Помощь
  • Цель — доказать, что x принадлежит объединению t и s.
    Поэтому прямое доказательство начинается так:
    Докажем, что x ∈ t
  • или:
    Докажем, что x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∪ t) : x ∈ t ∪ s := by
  помощь h
  Продолжаем, используя h
  Предположим hyp : x ∈ s
  помощь
  Докажем, что x ∈ s
  exact hyp
  Предположим hyp : x ∈ t
  Докажем, что x ∈ t
  exact  hyp

/--
info: Помощь
  • Цель начинается с «False ⇒ ...»
    Поэтому прямое доказательство начинается так:
    Предположим hyp : False
    Имя hyp можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example : False → True := by
  помощь
  simp

/-- info: Мне нечего сказать об этой цели. -/
#guard_msgs in
example : True := by
  помощь
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpContraposeGoal

/--
info: Помощь
  • Цель начинается с «False ⇒ ...»
    Поэтому прямое доказательство начинается так:
    Предположим hyp : False
    Имя hyp можно выбрать свободно среди доступных имён.
  • Цель — импликация.
    Можно начать доказательство контрапозицией так:
    Переходим к контрапозиции
-/
#guard_msgs in
example : False → True := by
  помощь
  Переходим к контрапозиции
  simp

/-- info: Мне нечего сказать об этой цели. -/
#guard_msgs in
example : True := by
  помощь
  trivial

configureHelpProviders DefaultHypHelp DefaultGoalHelp helpByContradictionGoal

/--
info: Помощь
  • Можно начать доказательство от противного так:
    Предположим от противного hyp : False
-/
#guard_msgs in
example : True := by
  помощь
  trivial

/--
info: Помощь
  • Предположение h имеет вид «∃ x, ...»
    Можно использовать его так:
    По h получаем x_1 такой, что (hx_1 : f x_1 = y)
    Имена x_1 и hx_1 можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example {X Y} (f : X → Y) (x : X) (y : Y) (h : ∃ x, f x = y) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h имеет вид «∃ x ∈ s, ...»
    Можно использовать его так:
    По h получаем x_1 такой, что (x_1_dans : x_1 ∈ s) и (hx_1 : f x_1 = y)
    Имена x_1, x_1_dans и hx_1 можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example {X Y} (f : X → Y) (s : Set X) (x : X) (y : Y) (h : ∃ x ∈ s, f x = y) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Цель — отрицание P, то есть P влечёт противоречие.
    Поэтому прямое доказательство начинается так:
    Предположим hyp : P
    И тогда останется доказать противоречие.
-/
#guard_msgs in
example (P : Prop) (h : ¬ P) : ¬ P := by
  помощь
  exact h

/--
info: Помощь
  • Цель — отрицание x = y, то есть x = y влечёт противоречие.
    Поэтому прямое доказательство начинается так:
    Предположим hyp : x = y
    И тогда останется доказать противоречие.
-/
#guard_msgs in
example (x y : ℕ) (h : x ≠ y) : x ≠ y := by
  помощь
  exact h

allowProvingNegationsByContradiction

/--
info: Помощь
  • Можно начать доказательство от противного так:
    Предположим от противного hyp : P
  • Цель — отрицание P, то есть P влечёт противоречие.
    Поэтому прямое доказательство начинается так:
    Предположим hyp : P
    И тогда останется доказать противоречие.
-/
#guard_msgs in
example (P : Prop) (h : ¬ P) : ¬ P := by
  помощь
  exact h

/--
info: Помощь
  • Можно начать доказательство от противного так:
    Предположим от противного hyp : x = y
  • Цель — отрицание x = y, то есть x = y влечёт противоречие.
    Поэтому прямое доказательство начинается так:
    Предположим hyp : x = y
    И тогда останется доказать противоречие.
-/
#guard_msgs in
example (x y : ℕ) (h : x ≠ y) : x ≠ y := by
  помощь
  exact h

configureHelpProviders SinceHypHelp SinceGoalHelp helpShowContrapositiveGoal
/--
info: Помощь
  • Предположение h начинается с «∀ n > 0, ...»
    Можно использовать его так:
    Поскольку ∀ n > 0, P n и n₀ > 0 получаем, что P n₀
    где n₀ — натуральное число, а n₀ > 0 следует непосредственно из предположения.
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∀ n > 0, P n) : P 2 := by
  помощь h
  apply h
  norm_num

/--
info: Помощь
  • Предположение h имеет вид «∃ n > 0, ...»
    Можно использовать его так:
    Поскольку ∃ n > 0, P n получаем n такой, что (n_pos : n > 0) и (hn : P n)
    Имена n, n_pos и hn можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example {P : ℕ → Prop} (h : ∃ n > 0, P n) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h имеет вид «∃ ε > 0, ...»
    Можно использовать его так:
    Поскольку ∃ ε > 0, P ε получаем ε такой, что (ε_pos : ε > 0) и (hε : P ε)
    Имена ε, ε_pos и hε можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example {P : ℝ → Prop} (h : ∃ ε > 0, P ε) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h начинается с «∀ n, ...»
    Можно использовать его так:
    Поскольку ∀ (n : ℕ), P n ⇒ Q n получаем, что P n₀ ⇒ Q n₀
    где n₀ — натуральное число
  • Если это предположение больше не понадобится в общем виде, можно также конкретизировать h так:
    Применяем h к n₀
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : ∀ n, P n → Q n) (h' : P 2) : Q 2 := by
  помощь h
  exact h 2 h'

/--
info: Помощь
  • Предположение h начинается с «∀ n, ...»
    Можно использовать его так:
    Поскольку ∀ (n : ℕ), P n получаем, что P n₀
    где n₀ — натуральное число
  • Если это предположение больше не понадобится в общем виде, можно также конкретизировать h так:
    Применяем h к n₀
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∀ n, P n) : P 2 := by
  помощь h
  exact h 2

/--
info: Помощь
  • Предположение h — импликация
    Заключение этой импликации — текущая цель
    Поэтому можно использовать это предположение так:
    Поскольку P 1 ⇒ Q 2 достаточно доказать, что P 1
  • Если уже есть доказательство утверждения P 1, можно использовать:
    Поскольку P 1 ⇒ Q 2 и P 1 заключаем, что Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) (h' : P 1) : Q 2 := by
  помощь h
  exact h h'

/--
info: Помощь
  • Предположение h — импликация
    Посылка этой импликации — P 1
    Если есть доказательство утверждения P 1,
    можно использовать это предположение так:
    Поскольку P 1 ⇒ Q 2 и P 1 получаем, что Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 → Q 2) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h имеет вид «... и ...»
    Можно использовать его так:
    Поскольку P 1 ∧ Q 2 получаем, что P 1 и Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∧ Q 2) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h — эквивалентность
    Можно заменить левую часть (а именно ∀ n ≥ 2, P n) на правую (а именно ∀ (l : ℕ), Q l) или наоборот в цели так:
    Поскольку (∀ n ≥ 2, P n) ⇔ ∀ (l : ℕ), Q l достаточно доказать, что ?_
    заменив вопросительный знак на новую цель.
  • Такую замену можно также выполнить в утверждении, следующем из одного из текущих предположений, так:
    Поскольку (∀ n ≥ 2, P n) ⇔ ∀ (l : ℕ), Q l и ?_ получаем, что ?_
    заменив первый вопросительный знак на факт, в котором нужна замена, а второй — на новый полученный факт.
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : (∀ n ≥ 2, P n) ↔  ∀ l, Q l) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h начинается с «∀ x, ...»
    Можно использовать его так:
    Поскольку ∀ (x y : ℝ), x ≤ y ⇒ f x ≤ f y получаем, что ∀ (y : ℝ), x₀ ≤ y ⇒ f x₀ ≤ f y
    где x₀ — вещественное число
  • Если это предположение больше не понадобится в общем виде, можно также конкретизировать h так:
    Применяем h к x₀
-/
#guard_msgs in
example (f : ℝ → ℝ) (h : ∀ x y, x ≤ y → f x ≤ f y) (a b : ℝ) (h' : a ≤ b) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h начинается с «∀ x > 0, ...»
    Можно использовать его так:
    Поскольку ∀ x > 0, x = 1 ⇒ f x ≤ 0 и x₀ > 0 получаем, что x₀ = 1 ⇒ f x₀ ≤ 0
    где x₀ — вещественное число, а x₀ > 0 следует непосредственно из предположения.
-/
#guard_msgs in
example (f : ℝ → ℝ) (h : ∀ x > 0, x = 1 → f x ≤ 0) (a b : ℝ) (h' : a ≤ b) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h — импликация
    Посылка этой импликации — l - n = 0
    Если есть доказательство утверждения l - n = 0,
    можно использовать это предположение так:
    Поскольку l - n = 0 ⇒ P l k и l - n = 0 получаем, что P l k
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (k l n : ℕ) (h : l - n = 0 → P l k) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h начинается с «∀ k ≥ 2, ∃ n ≥ 3, ...»
    Можно использовать его так:
    Поскольку ∀ k ≥ 2, ∃ n ≥ 3, ∀ (l : ℕ), l - n = 0 ⇒ P l k и k₀ ≥ 2 получаем
        n такой, что n ≥ 3 и ∀ (l : ℕ), l - n = 0 ⇒ P l k₀
    где k₀ — натуральное число, а отношение k₀ ≥ 2 должно следовать непосредственно из предположения.
    Имя n можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  помощь h
  trivial

-- FIXME: completely broken case
/-- info: Помощь -/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∀ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  помощь h
  trivial

-- FIXME: completely broken case
/-- info: Помощь -/
#guard_msgs in
example (f : ℕ → ℕ) (h : ∀ k n, n ≤ k → f n ≤ f k) : True := by
  помощь h
  trivial

-- FIXME: in hn_1, n is not replaced by n_1. This is an issue in
-- helpSinceForAllRelExistsRelSuggestion (or rather the function calling it)
/--
info: Помощь
  • Предположение h начинается с «∀ k ≥ 2, ∃ n_1 ≥ 3, ...»
    Можно использовать его так:
    Поскольку ∀ k ≥ 2, ∃ n ≥ 3, ∀ (l : ℕ), l - n = 0 ⇒ P l k и k₀ ≥ 2 получаем
        n_1 такой, что n_1 ≥ 3 и ∀ (l : ℕ), l - n = 0 ⇒ P l k₀
    где k₀ — натуральное число, а отношение k₀ ≥ 2 должно следовать непосредственно из предположения.
    Имя n_1 можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (n : ℕ) (h : ∀ k ≥ 2, ∃ n ≥ 3, ∀ l, l - n = 0 → P l k) : True := by
  помощь h
  По h применённый к 2 используя le_rfl получаем n' такой, что (n_sup : n' ≥ 3) и (hn : ∀ (l : ℕ), l - n' = 0 → P l 2)
  trivial

/--
info: Помощь
  • Предположение h имеет вид «∃ n ≥ 5, ...»
    Можно использовать его так:
    Поскольку ∃ n ≥ 5, P n получаем n такой, что (n_sup : n ≥ 5) и (hn : P n)
    Имена n, n_sup и hn можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n ≥ 5, P n) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h начинается с «∀ k ≥ 2, ∃ n ≥ 3, ...»
    Можно использовать его так:
    Поскольку ∀ k ≥ 2, ∃ n ≥ 3, P n k и k₀ ≥ 2 получаем n такой, что n ≥ 3 и P n k₀
    где k₀ — натуральное число, а отношение k₀ ≥ 2 должно следовать непосредственно из предположения.
    Имя n можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k ≥ 2, ∃ n ≥ 3, P n k) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h имеет вид «∃ n, ...»
    Можно использовать его так:
    Поскольку ∃ n, P n получаем n такой, что P n
    Имя n можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P : ℕ → Prop) (h : ∃ n : ℕ, P n) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h начинается с «∀ k, ∃ n, ...»
    Можно использовать его так:
    Поскольку ∀ (k : ℕ), ∃ n, P n k получаем n такой, что P n k₀
    где k₀ — натуральное число
    Имя n можно выбрать свободно среди доступных имён.
-/
#guard_msgs in
example (P : ℕ → ℕ → Prop) (h : ∀ k, ∃ n : ℕ, P n k) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h имеет вид «... или ...»
    Можно использовать его так:
    Различаем случаи P 1 или Q 2
-/
#guard_msgs in
example (P Q : ℕ → Prop) (h : P 1 ∨ Q 2) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Предположение h утверждает принадлежность пересечению
    Можно использовать его так:
    Поскольку x ∈ s ∩ t получаем, что x ∈ s и x ∈ t
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ s := by
  помощь h
  По h получаем (h_1 : x ∈ s) (h' : x ∈ t)
  exact h_1

/--
info: Помощь
  • Предположение h утверждает принадлежность пересечению
    Можно использовать его так:
    Поскольку x ∈ s ∩ t получаем, что x ∈ s и x ∈ t
---
info: Помощь
  • Цель — доказать, что x принадлежит пересечению t с другим множеством.
    Поэтому прямое доказательство начинается так:
    Докажем сначала, что x ∈ t
---
info: Помощь
  • Следующий шаг — объявить:
    Докажем теперь, что x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∩ t) : x ∈ t ∩ s := by
  помощь h
  По h получаем (h_1 : x ∈ s) (h' : x ∈ t)
  помощь
  Докажем сначала, что x ∈ t
  exact h'
  помощь
  Докажем теперь, что x ∈ s
  exact h_1

open Verbose.Named in
/--
info: Помощь
  • Предположение h утверждает принадлежность объединению
    Можно использовать его так:
    Различаем случаи x ∈ s или x ∈ t
---
info: Помощь
  • Цель — доказать, что x принадлежит объединению t и s.
    Поэтому прямое доказательство начинается так:
    Докажем, что x ∈ t
  • или:
    Докажем, что x ∈ s
-/
#guard_msgs in
example (s t : Set ℕ) (x : ℕ) (h : x ∈ s ∪ t) : x ∈ t ∪ s := by
  помощь h
  Продолжаем, используя h
  Предположим hyp : x ∈ s
  помощь
  Докажем, что x ∈ s
  exact hyp
  Предположим hyp : x ∈ t
  Докажем, что x ∈ t
  exact  hyp

/--
info: Помощь
  • Предположение h — неравенство
    Оно непосредственно влечёт текущую цель.
    Можно использовать его так:
    Поскольку ε > 0 заключаем, что ε / 2 > 0
-/
#guard_msgs in
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by
  помощь h
  linarith

/--
info: Помощь
  • Цель — неравенство
    Можно начать вычисление так:
    Calc
        ε / 2 > 0 поскольку?
    Последняя строка вычисления не обязательно равенство, она может быть неравенством.
    Аналогично первая строка может быть равенством. В целом символы отношений
    должны образовать цепочку, дающую  > ⏎
  • Если это неравенство следует непосредственно из предположения, можно использовать:
    Поскольку ?_ заключаем, что ε / 2 > 0
    заменив вопросительный знак на утверждение предположения.
-/
#guard_msgs in
example (ε : ℝ) (h : ε > 0) : ε/2 > 0 := by
  помощь
  Поскольку ε > 0 заключаем, что ε / 2 > 0

/--
info: Помощь
  • Предположение h — эквивалентность
    Можно заменить левую часть (а именно P) на правую (а именно Q) или наоборот в цели так:
    Поскольку P ⇔ Q достаточно доказать, что ?_
    заменив вопросительный знак на новую цель.
  • Такую замену можно также выполнить в утверждении, следующем из одного из текущих предположений, так:
    Поскольку P ⇔ Q и ?_ получаем, что ?_
    заменив первый вопросительный знак на факт, в котором нужна замена, а второй — на новый полученный факт.
-/
#guard_msgs in
example (P Q : Prop) (h : P ↔ Q) (h' : P) : Q := by
  помощь h
  Поскольку P ↔ Q достаточно доказать, что P
  exact h'

/--
info: Помощь
  • Предположение h обеспечивает включение A в B.
    Можно использовать его так:
    Поскольку A ⊆ B и x ∈ A получаем, что x ∈ B
    где x — натуральное число
-/
#guard_msgs in
example (A B : Set ℕ) (h : A ⊆ B) : True := by
  помощь h
  trivial

/--
info: Помощь
  • Это предположение — противоречие.
    Из него можно вывести цель так:
    Поскольку False заключаем, что 0 = 1
-/
#guard_msgs in
example (h : False) : 0 = 1 := by
  помощь h
  Поскольку False заключаем, что 0 = 1

/--
info: Помощь
  • Цель — доказать противоречие.
    Можно применить предположение, являющееся отрицанием,
    то есть, по определению, имеющее вид P → false.
    Можно также скомбинировать два факта, явно противоречащих друг другу, так:
    Поскольку ?_ и ?_ заключаем, что False
    заменив вопросительные знаки на эти два факта, непосредственно следующих из предположений.
  • Можно также сослаться на явно ложный факт (например, `0 = 1`), непосредственно следующий из предположения.
    Поскольку ?_ заключаем, что False
    заменив вопросительный знак на этот явно ложный факт.
-/
#guard_msgs in
example (h : 0 = 1) : False := by
  помощь
  Поскольку 0 = 1 заключаем, что False

/--
info: Помощь
  • Цель — неравенство
    Можно начать вычисление так:
    Calc
        a ≤ c поскольку?
    Последняя строка вычисления не обязательно равенство, она может быть неравенством.
    Аналогично первая строка может быть равенством. В целом символы отношений
    должны образовать цепочку, дающую  ≤ ⏎
  • Если это неравенство следует непосредственно из предположения, можно использовать:
    Поскольку ?_ заключаем, что a ≤ c
    заменив вопросительный знак на утверждение предположения.
-/
#guard_msgs in
example (a b c : ℤ) (h : a ≤ b) (h' : b ≤ c) : a ≤ c := by
  помощь
  exact le_trans h h'

/--
info: Помощь
  • Цель начинается с «False ⇒ ...»
    Поэтому прямое доказательство начинается так:
    Предположим, что False
  • Цель — импликация.
    Можно начать доказательство контрапозицией так:
    Докажем контрапозицию: ¬True ⇒ ¬False
-/
#guard_msgs in
example : False → True := by
  помощь
  Докажем контрапозицию: ¬True → ¬False
  tauto

end Verbose.Russian
