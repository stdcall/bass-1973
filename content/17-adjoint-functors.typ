#import "main-defs.typ": idx, name-idx, symbol-idx
#import "main-defs.typ": source
#import "statements.typ": (
  condition-item, condition-list, corollary, proof, proposition,
)
#import "diagrams/category-algebra-adjoint.typ": (
  adjoint-pair, adjunction-naturality,
)

== Сопряженные функторы <sec:adjoint-functors>

Пусть даны два функтора
$ #adjoint-pair() $
и естественный изоморфизм
$ gamma = gamma_(A, B): bold(A)(A, S B) -> bold(B)(T A, B) $
<eq:adjunction-isomorphism>
функторов из $bold(A)^degree times bold(B)$ в $italic("Sets")$. Мы говорим в
этом случае, что функтор $S$ является #idx("сопряженный функтор")#idx(
  "функтор сопряженный",
)_сопряженным_ к $T$, а функтор $T$~— #idx("косопряженный функтор")#idx(
  "функтор косопряженный",
)_косопряженным_ к $S$. Нетрудно заметить, что любой из этих функторов
определяет #source(49) (посредством изоморфизма~@eq:adjunction-isomorphism)
другой с точностью до однозначно определенного изоморфизма. Назовем $(T, S)$
#idx("сопряженная пара")_сопряженной парой_.

Эта ситуация часто возникает в действительности. Например, #idx(
  "забывающий функтор",
)#idx("функтор забывающий")«забывающий» функтор из групп в множества обладает
косопряженным, сопоставляющим множеству свободную группу с этим множеством в
качестве множества свободных образующих. Аналогично забывающий функтор из
$k$-алгебр в $k$-модули ($k$~— коммутативное кольцо) обладает косопряженным
функтором перехода к тензорной алгебре.

#proposition[
  Пусть $(T, S)$~— сопряженная пара функторов. Тогда:

  #condition-list[
    #condition-item[функтор $S$ сохраняет произведения, пределы, финальные
      объекты, ядра, …;] <cond:right-adjoint-preserves-limits>

    #condition-item[функтор $T$ сохраняет копроизведения, копределы, начальные
      объекты, коядра, … .] <cond:left-adjoint-preserves-colimits>
  ]
] <prop:adjoints-preserve-limits>

#proof[
  Утверждение @cond:left-adjoint-preserves-colimits двойственно
  @cond:right-adjoint-preserves-limits. Утверждение
  @cond:right-adjoint-preserves-limits немедленно следует из определений и
  естественности отождествления $bold(A)(A, S B) =
  bold(B)(T A, B)$. Иллюстрируем последнее заявление, показав, что функтор $S$
  сохраняет пределы (кстати, вопрос о сохранении произведений является частным
  случаем этого). Предположим, что $B = lim F$ для некоторого функтора
  $F: bold(L) -> bold(B)$. Утверждаем, что $S B = lim S F$. Нам надо показать,
  что они представляют один и тот же функтор $bold(A)^degree -> italic("Sets")$.
  В силу определения $bold(A)(A, lim S F) = bold(A)^bold(L)(c(A), S F)$, где
  $c(A): bold(L) -> bold(A)$~— постоянный функтор со значением $A$. Из тождества
  сопряженности следует, что
  $
    bold(A)^bold(L)(c(A), S F) = bold(B)^bold(L)(c(T A), F)
    = bold(B)(T A, lim F) = bold(A)(A, S lim F).
  $
]

#corollary[
  Если рассмотренные выше категории $bold(A)$ и $bold(B)$ аддитивны, то функторы
  $S$ и $T$ аддитивны.
] <cor:additive-adjoints>

#proof[
  Из предложения~@prop:adjoints-preserve-limits следует, что оба функтора
  сохраняют нулевые объекты и прямые суммы. Эти два свойства влекут за собой
  аддитивность функтора.
]

Пусть $(T, S)$~— сопряженная пара с изоморфизмом $gamma$ (см.
@eq:adjunction-isomorphism). Тогда для $A in bold(A)$ и $B in bold(B)$
$ alpha_A = gamma_(A, T A)^(-1)(1_(T A)): A -> S T A $
и
$ beta_B = gamma_(S B, B)(1_(S B)): T S B -> B. $
#source(50)Если заданы морфизмы $a: A' -> A$ в $bold(A)$ и $b: B -> B'$ в
$bold(B)$, то квадрат
$ #adjunction-naturality() $
коммутативен ввиду естественности изоморфизма $gamma$. Таким образом,
$
  b gamma_(A, B)(c)(T a) = gamma_(A', B')((S b) c a) quad (c in bold(A)(A, S
      B)).
$
Если применим это к $a = alpha_A: A -> S T A$, $b = 1_(T A)$ и $c = 1_(S T A)$,
то получим
$
  b gamma_(S T A, T A)(c)(T a) = 1_(T A) beta_(T A) T alpha_A = beta_(T A) T
  alpha_A
$
и
$ gamma_(A, T A)((S b) c a) = gamma_(A, T A)(alpha_A) = 1_(T A). $
Таким образом, композиция морфизмов
$ T A arrow.r^(T alpha_A) T S T A arrow.r^(beta_(T A)) T A $
тождественна на $T A$. Аналогично проверяется, что композиция морфизмов
$ S B arrow.r^(alpha_(S B)) S T S B arrow.r^(S beta_B) S B $
тождественна на $S B$ для $B in bold(B)$.

#proposition[
  Пусть $(T, S)$~— сопряженная пара функторов между аддитивными категориями.
  Если объект $A in bold(A)$ таков, что морфизм $alpha_A: A -> S T A$ является
  изоморфизмом, то $beta_B: T S B -> B$~— изоморфизм для любого прямого
  слагаемого $B$ объекта $T A$.
] <prop:adjunction-counit-summands>

#proof[
  Так как $beta: T S -> 1_(bold(B))$ является естественным преобразованием
  аддитивных функторов, то достаточно показать, что $beta_(T A)$~— изоморфизм.
  Но из приведенного выше рассуждения следует, что
  $beta_(T A) T alpha_A = 1_(T A)$. Из нашего предположения относительно объекта
  $A$ вытекает, что $T alpha_A$~— изоморфизм. Следовательно,
  $beta_(T A) = T alpha_A^(-1)$~— также изоморфизм.
]

#corollary[
  Пусть $(T, S)$~— сопряженная пара функторов между аддитивными категориями,
  такая, что естественное преобразование $alpha: 1_(bold(A)) -> S T$ является
  изоморфизмом. Предположим, далее, что каждый объект категории $bold(B)$
  изоморфен прямому слагаемому объекта $T A$ для некоторого $A in bold(A)$.
  Тогда морфизм $beta: T S -> 1_(bold(B))$ также является изоморфизмом, и
  поэтому $S$ и $T$~— взаимно обратные эквивалентности категорий.
] <cor:adjunction-equivalence>
