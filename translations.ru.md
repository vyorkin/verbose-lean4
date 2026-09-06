# Перевод на другие языки

Сейчас у Verbose Lean есть французская и английская версии.
Надеюсь, добавить другие языки в отдельных библиотеках несложно (хотя и
несколько утомительно) — я не хочу поддерживать версии на языках, которые я
не понимаю, поэтому я не буду принимать pull request'ы с таким
предложением.

Вам нужно всего лишь скопировать содержимое папки `English` из этого
репозитория и заменить английские слова.
Если сомневаетесь, что именно нужно сделать, посмотрите на различия между
папками `French` и `English`.

Чтобы показать, какая работа здесь предстоит, вот несколько примеров.
Самые простые части — это функции вроде:
```lean
def describeHypShape (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "The assumption {hyp} has shape “{headDescr}”"

def describeHypStart (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "The assumption {hyp} starts with “{headDescr}”"


implement_endpoint (lang := en) helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "One can use it with:"
  pushTac `(tactic|By $hyp.ident:term we get $nameS:ident such that ($ineqIdent : $ineqS) and ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]
```
чей французский вариант:
```lean
def describeHypShape (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "L'hypothèse {hyp} est de la forme « {headDescr} »"

def describeHypStart (hyp : Name) (headDescr : String) : SuggestionM Unit :=
  pushCom "L'hypothèse {hyp} commence par « {headDescr} »"

implement_endpoint (lang := fr) helpExistRelSuggestion (hyp : Name) (headDescr : String)
    (nameS ineqIdent hS : Ident) (ineqS pS : Term) : SuggestionM Unit := do
  describeHypShape hyp headDescr
  pushCom "On peut l'utiliser avec :"
  pushTac `(tactic|Par $hyp.ident:term on obtient $nameS:ident tel que ($ineqIdent : $ineqS) et ($hS : $pS))
  pushComment <| libres [nameS, ineqIdent, hS]

```
Иногда окружающий Lean-код выглядит немного пугающе, но принцип тот же:
ищите английские слова, которые выглядят обращёнными к пользователю, и
сверяйтесь с французской версией, чтобы убедиться в этом.
Например, в английской версии одного из файлов мы видим:
```lean
declare_syntax_cat maybeApplied
syntax term : maybeApplied
syntax term "applied to " term : maybeApplied
syntax term "applied to " term " using " term : maybeApplied
syntax term "applied to " term " using that " term : maybeApplied

def maybeAppliedToTerm : TSyntax `maybeApplied → MetaM (TSyntax `term)
| `(maybeApplied| $e:term) => pure e
| `(maybeApplied| $e:term applied to $x:term) => `($e $x)
| `(maybeApplied| $e:term applied to $x:term using $y) => `($e $x $y)
| `(maybeApplied| $e:term applied to $x:term using that $y) => 
    `($e $x (strongAssumption% $y))
| _ => pure default 

elab "We" " conclude by " e:maybeApplied : tactic => do
  concludeTac (← maybeAppliedToTerm e)
```
а соответствующий французский код:
```lean
declare_syntax_cat maybeAppliedFR
syntax term : maybeAppliedFR
syntax term "appliqué à " term : maybeAppliedFR
syntax term "appliqué à " term " en utilisant " term : maybeAppliedFR
syntax term "appliqué à " term " en utilisant que " term : maybeAppliedFR

def maybeAppliedFRToTerm : TSyntax `maybeAppliedFR → MetaM Term
| `(maybeAppliedFR| $e:term) => pure e
| `(maybeAppliedFR| $e:term appliqué à $x:term) => `($e $x)
| `(maybeAppliedFR| $e:term appliqué à $x:term en utilisant $y) => `($e $x $y)
| `(maybeAppliedFR| $e:term appliqué à $x:term en utilisant que $y) => 
    `($e $x (strongAssumption% $y))
| _ => pure default 

elab "On" " conclut par " e:maybeAppliedFR : tactic => do
  concludeTac (← maybeAppliedFRToTerm e)
```
Замечание об именах: причина, по которой имя категории синтаксиса
`maybeApplied` тоже переведено, хотя оно не обращено к пользователю, в том,
что разработчику библиотеки удобнее иметь возможность одновременно
импортировать оба языка.
Если вы делаете собственный перевод, это менее критично. Но я всё равно
рекомендую так поступать, потому что никогда не знаешь, не захочешь ли ты
когда-нибудь создать многоязычный документ.

## Заметка о нелатинских алфавитах (русский перевод в этом форке)

Этот форк добавляет неофициальный русский перевод (`Verbose/Russian`, не
влитый в основной репозиторий, см. начало этого файла). Чтобы кириллические
ключевые слова вообще начали парситься, потребовалась дополнительная
работа, которую стоит здесь задокументировать — на случай, если кто-то ещё
возьмётся переводить на нелатинский алфавит (греческий, ханьские
иероглифы, арабский, иврит, грузинский, …).

Токенизатор Lean принимает только определённый список Unicode-диапазонов
«похожих на буквы» символов для голых идентификаторов и атомов ключевых
слов (`Lean.isLetterLike` в `Init/Meta/Defs.lean`): туда входят греческий,
коптский, математические буквоподобные символы и акцентированная/
расширенная латиница, но не кириллица (`'П'.isAlpha` возвращает `false`).
Одно это уже заблокировало бы прямолинейный перевод на русский, но реальная
проблема, с которой мы столкнулись, оказалась уже и её было легче упустить:
кириллическое ключевое слово, объявленное через `syntax "…" : term` или
`: command`, парсится и сразу же работает, а та же самая строка, объявленная
через `syntax "…" : tactic` (или `macro "…" : tactic => …`), молча не
регистрирует свой токен — после этого любое её использование выдаёт ошибку
`expected token`, хотя само объявление компилируется без единого замечания.
`term` и `command` эта проблема не затрагивает; баг специфичен именно для
категории `tactic`.

Обходной путь лежит в `Verbose/Russian/TokenSupport.lean`: там определена
команда `declare_ru_tokens`, которая явно добавляет каждое ключевое слово в
таблицу токенов Lean через `Lean.Parser.addToken` (тот же самый примитив,
который внутри используют `syntax`/`notation`), и каждый файл с русскими
тактиками вызывает её для своих собственных ключевых слов перед тем, как их
объявить. Ещё один нюанс: *составной* литерал из нескольких слов, например
`"Докажем по индукции, что "`, — это не один атом: синтаксический сахар
`syntax` разбивает его по пробелам на отдельные последовательные атомы
(«Докажем», «по», «индукции,», «что» — каждый сохраняет любую пунктуацию,
приклеенную к нему без предшествующего пробела) — поэтому регистрировать
нужно каждое получившееся *слово* по отдельности, а не составную фразу
целиком.

Ничего из этого не требуется для ключевых слов, живущих в собственной
категории `declare_syntax_cat` (в отличие от встроенной категории
`tactic`) — такие регистрируются нормально для любого алфавита, поэтому,
например, категориям в духе «такой, что»/«применённый к» в
`Verbose/Russian/Common.lean` подобный обходной путь не нужен.

Перевод `Help.lean` (тактика `help` и виджет с подсказками, чья задача —
заново «красиво распечатать» уже элаборированные деревья `Syntax` в виде
предлагаемого кода) выявил ещё две особенности, связанные с `isIdFirst`,
обе обойдены централизованно в
`Verbose/Infrastructure/HelpInfrastructure.lean` и
`Verbose/Tactics/Widget.lean` (независимо от языка, для английского/
французского это безвредные no-op'ы):

- При повторной сериализации дерева `Syntax` тактики может незаметно
  пропасть пробел между идентификатором и соседним кириллическим атомом
  ключевого слова («h применённый» превращается в «hприменённый»), потому
  что проверка pretty-printer'а «не будет ли конкатенация этих токенов
  неоднозначной» тоже основана на `isIdFirst`, а кириллица не проходит её в
  любом случае. `Verbose.fixCyrillicSpacing` восстанавливает пробел, сканируя
  отрендеренную строку на предмет границ идентификатор/кириллица.
- Несколько генераторов подсказок по форме гипотезы, которые *уже* были
  помечены как «полностью сломанные» для английского/французского (паттерн
  с двойным квантором `∀ x, ∀ y rel x, …`), для кириллицы ломаются ещё
  сильнее: parenthesizer выбрасывает исключение `uncaught backtrack
  exception` вместо того, чтобы просто отрендерить неверный текст.
  `mkSuggestionsMessage` теперь пропускает подсказку, чей `Syntax` не
  удаётся заново сериализовать, вместо того чтобы дать ей обрушить весь
  вывод `help`.
