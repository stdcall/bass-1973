#import "main-defs.typ": Aut, idx, source
#import "statements.typ": (
  condition-item, condition-list, definition, proof, proposition,
)
#import "diagrams/exact-k-sequences-squares.typ": (
  category-fiber-square, fiber-functor-cospan, fiber-morphism-square,
  universal-fiber-square,
)

== Категории расслоенных произведений <sec:fiber-product-categories>

#definition(upright: true)[
  Для данной диаграммы функторов
  $ #fiber-functor-cospan() $
  <eq:fiber-product-functor-cospan>
  определим #idx("категория: расслоенных произведений")_категорию расслоенных
  произведений_
  $
    bold(A) = bold(A)_1 times_(bold(A)') bold(A)_2
    = italic("co")(F_1, F_2)
  $
  следующим образом: объектами являются тройки $(A_1, alpha, A_2)$, где
  $A_i in bold(A)_i$ и $alpha: F_1 A_1 -> F_2 A_2$~— изоморфизм в категории
  $bold(A)'$. Морфизм $(A_1, alpha, A_2) -> (B_1, beta, B_2)$ в $bold(A)$
  является парой морфизмов $A_i -> B_i$ в $bold(A)_i$ ($i = 1, 2$), для которых
  диаграмма
  #fiber-morphism-square()
  коммутативна. Рассмотрим канонические функторы
  $
    G_i: bold(A) -> bold(A)_i; quad
    (A_1, alpha, A_2) |-> A_i, quad (f_1, f_2) |-> f_i quad (i = 1, 2).
  $
  Диаграмма
  $ #category-fiber-square() $
  <eq:fiber-product-cartesian-square>
  коммутативна с точностью до естественного изоморфизма
  $ alpha: F_1 G_1 -> F_2 G_2, $
  #source(289)отображающего $F_1 G_1 (A_1, alpha, A_2) = F_1 A_1$ в
  $F_2 G_2 (A_1, alpha, A_2) = F_2 A_2$ с помощью $alpha$.

  Эта конструкция дает решение следующей универсальной задачи: для данных
  $
    #universal-fiber-square() quad beta: F_1 H_1 arrow.r.tilde F_2 H_2
  $ <eq:fiber-product-universal-square>
  существует единственный (а не единственный с точностью до изоморфизма) функтор
  $T: bold(B) -> bold(A)$, для которого $G_i T = H_i$ (равенство, а не
  изоморфизм) ($i = 1, 2$) и
  $ beta = alpha dot.op T: F_1 H_1 = F_1 G_1 T -> F_2 H_2 = F_2 G_2 T. $
  Именно должны иметь место равенства
  $ T(B) = (H_1 B, beta_B, H_2 B), $
  $ T(f) = (H_1 f, H_2 f), $
  и такой функтор $T$, очевидно, годится для нашей цели.
] <def:fiber-product-category>

Рассмотренную выше диаграмму
#category-fiber-square()
$ alpha: F_1 G_1 -> F_2 G_2, $
будем называть #idx("декартов квадрат")_декартовым квадратом_. Если
$A in bold(A)$, то, как тройка, $A = (G_1 A, alpha_A, G_2 A)$.

Предположим, что рассмотренная диаграмма~@eq:fiber-product-functor-cospan
является диаграммой сохраняющих произведение функторов между категориями с
произведением. Тогда можно ввести произведение на категории
$bold(A) = bold(A)_1 times_(bold(A)') bold(A)_2$:
$
  (A_1, alpha, A_2) perp (B_1, beta, B_2)
  = (A_1 perp B_1, alpha perp beta, A_2 perp B_2),
$
$ (f_1, f_2) perp (g_1, g_2) = (f_1 perp g_1, f_2 perp g_2). $
В этом определении содержатся неявные отождествления:
$F_i (A_i perp B_i) = F_i A_i perp F_i B_i$ ($i = 1, 2$). Очевидно, что функторы
$G_i$ в @eq:fiber-product-cartesian-square сохраняют это произведение. Наконец,
если @eq:fiber-product-universal-square~— диаграмма сохраняющих произведение
функторов, то построенный выше функтор $T: bold(B) -> bold(A)$ также сохраняет
произведение. Рассмотрим теперь условия, гарантирующие то, что функторы $G_i$ и
$T$ кофинальны. Приводимые ниже результаты являются подготовительными для
некоторых рассуждений, которые будут использованы в
§~@sec:mayer-vietoris-sequence.

#definition(upright: true)[
  #source(290)Пусть @eq:fiber-product-functor-cospan~— диаграмма функторов,
  сохраняющих произведение. Будем говорить, что функтор $F_1$ #idx(
    "функтор относительно функторов",
  )_кофинален относительно $F_2$_, если для данного объекта $A_2 in bold(A)_2$
  можно найти $A'_2 in bold(A)_2$ и $A_1 in bold(A)_1$, для которых
  $F_2 (A_2 perp A'_2) tilde.eq F_1 A_1$. Назовем $(F_1, F_2)$ #idx(
    "кофинальная пара",
  )_кофинальной парой_, если каждый функтор $F_i$ кофинальный и если каждый из
  них кофинален относительно другого.
] <def:cofinal-functor-pair>

Пусть $A = (A_1, alpha, A_2) in bold(A)$, $beta in Aut_(bold(A)') (F_1 A_1)$ и
$gamma in Aut_(bold(A)') (F_2 A_2)$. Тогда введем такое обозначение:
$ gamma A beta = (A_1, gamma alpha beta, A_2). $

#definition(upright: true)[
  Диаграмма~@eq:fiber-product-universal-square сохраняющих произведение
  функторов называется #idx("E-сюръективная диаграмма")_Е-сюръективной_, если
  выполнены следующие условия: для данных $B in bold(B)$ и $epsilon$ из
  коммутанта группы $Aut_(bold(A)') (F_1 H_1 B)$ существуют $B' in bold(B)$ и
  $epsilon_i$ из коммутанта группы $Aut_(bold(A)_i) (H_i (B perp B'))$
  ($i = 1, 2$), для которых
  $ (epsilon_1, epsilon_2): (T B)epsilon perp T B' -> T B perp T B' $
  является изоморфизмом в категории $bold(A)$.
] <def:e-surjective-functor-square>

#proposition[
  Пусть @eq:fiber-product-universal-square~— диаграмма функторов, сохраняющих
  произведение. Тогда:
  #condition-list[
    #condition-item(format: "cyrillic")[Если функторы $H_1$ и $H_2$ кофинальны,
      то объекты $(T B)alpha$ ($B in bold(B)$,
      $alpha in Aut_(bold(A)') (F_1 H_1 B)$) кофинальны в
      $bold(A)$.] <cond:fiber-square-twisted-cofinality>

    #condition-item(format: "cyrillic")[Если, кроме того, диаграмма
      @eq:fiber-product-universal-square Е-сюръективна (см.
      @def:e-surjective-functor-square), то функтор $T: bold(B) -> bold(A)$
      кофинален.]
    <cond:fiber-square-cofinality>

    #condition-item(format: "cyrillic")[Если функтор $F_2$ кофинален
      относительно $F_1$ (см. @def:cofinal-functor-pair) и если функтор $F_1$
      Е-сюръективен (см. @def:e-surjective-functor), то декартов
      квадрат~@eq:fiber-product-cartesian-square Е-сюръективен в смысле
      определения~@def:e-surjective-functor-square.]
    <cond:fiber-square-e-surjectivity>

    #condition-item(format: "cyrillic")[Предположим, что $(F_1, F_2)$~—
      кофинальная пара (см. @def:cofinal-functor-pair); тогда для данных
      объектов $A_i in bold(A)_i$ ($i = 1, 2$) найдутся $B in bold(A)$ и
      $A'_i in bold(A)_i$ ($i = 1, 2$), такие, что
      $G_i B tilde.eq A_i perp A'_i$ ($i = 1, 2$). В частности, функторы $G_i$,
      а следовательно, и $F_i G_i$ кофинальны.]
    <cond:fiber-square-projection-cofinality>
  ]
] <prop:fiber-square-cofinality>

Заметим, что в силу симметрии в части @cond:fiber-square-e-surjectivity можно
переставить $F_1$ с $F_2$.

#proof[
  @cond:fiber-square-twisted-cofinality. Если $A = (A_1, alpha, A_2)$, то
  достаточно найти $B in bold(B)$ и $A' = (A'_1, alpha', A'_2) in bold(A)$, для
  которых $A_i perp A'_i tilde.eq H_i B$ ($i = 1, 2$). Действительно, тогда
  $A perp A' tilde.eq (H_1 B, gamma, H_2 B)$ для некоторого $gamma$ и
  $(H_1 B, gamma, H_2 B) = (T B)beta$, где $beta = beta_B^(-1) gamma$.

  Так как функтор $H_i$ кофинален, то можно найти $C_i in bold(A)_i$ и
  $B_i in bold(B)$, такие, что $A_i perp C_i tilde.eq H_i B_i$ ($i = 1, 2$).
  Положим теперь $A'_1 = C_1 perp H_1 B_2$ и $A'_2 = C_2 perp H_2 B_1$. Тогда
  #source(291)$F_1 A'_1 = F_1 C_1 perp F_1 H_1 B_2
  tilde.eq F_1 C_1 perp F_2 H_2 B_2
  tilde.eq F_1 C_1 perp F_2 A_2 perp F_2 C_2
  tilde.eq F_1 C_1 perp F_1 A_1 perp F_2 C_2$ (используем $alpha$)
  $tilde.eq F_1 H_1 B_1 perp F_2 C_2
  tilde.eq F_2 H_2 B_1 perp F_2 C_2 tilde.eq F_2 A'_2$. Таким образом,
  существует изоморфизм $alpha': F_1 A'_1 -> F_2 A'_2$. Кроме того,
  $A_i perp A'_i tilde.eq H_i B$ ($i = 1, 2$), где $B = B_1 perp B_2$. Это
  завершает построение.

  @cond:fiber-square-cofinality. В силу части
  @cond:fiber-square-twisted-cofinality достаточно для данного объекта
  $(T B)alpha$ из утверждения~@cond:fiber-square-twisted-cofinality найти
  $A in bold(A)$ и $B' in bold(B)$, для которых
  $(T B)alpha perp A tilde.eq T B'$.

  Сначала образуем $(T B)alpha perp (T B)alpha^(-1) = T(B perp B)epsilon$, где
  $epsilon = alpha perp alpha^(-1)$. Так как в силу
  @lem:whitehead-diagonal-commutator $epsilon$~— коммутатор, то из определения
  Е-сюръективности~@def:e-surjective-functor-square следует, что
  $T(B perp B)epsilon perp T B' tilde.eq T(B perp B) perp T B'$ для некоторого
  $B' in bold(B)$, что и требовалось доказать.

  @cond:fiber-square-e-surjectivity. Как только нам даны
  $A = (A_1, alpha, A_2) in bold(A)$ и $epsilon$ из коммутанта группы
  $Aut_(bold(A)') (F_1 A_1)$, нам надо найти $B = (B_1, beta, B_2) in bold(A)$ и
  $epsilon_i$ из коммутанта группы $Aut_(bold(A)_i) (A_i perp B_i)$
  ($i = 1, 2$), для которых пара
  $ (epsilon_1, epsilon_2): (A_1, alpha epsilon, A_2) perp B -> A perp B $
  является изоморфизмом в $bold(A)$.

  Так как функтор $F_1$ Е-сюръективен, найдутся $B_1 in bold(A)_1$ и $delta$ из
  коммутанта группы $Aut_(bold(A)_1) (A_1 perp B_1)$, такие, что
  $F_1 delta = epsilon perp 1_(F_1 B_1)$. Поскольку функтор $F_2$ кофинален
  относительно $F_1$, можно (увеличивая $B_1$ и $delta$, если это необходимо)
  считать, что существуют $B_2 in bold(A)_2$ и изоморфизм
  $beta: F_1 B_1 -> F_2 B_2$. Таким образом, построена тройка
  $B = (B_1, beta, B_2)$. Кроме того,
  $
    (delta, 1_(A_2 perp B_2)): (A_1, alpha epsilon, A_2) perp B
    -> (A_1 perp B_1, (alpha epsilon perp beta)(F delta)^(-1), A_2 perp B_2).
  $
  Так как $alpha epsilon perp beta = (alpha perp beta)(epsilon perp 1_(F_1 B_1))
  = (alpha perp beta)(F_1 delta)$, то правая часть указанного выше изоморфизма
  совпадает с $A perp B$, что и требуется доказать.

  @cond:fiber-square-projection-cofinality. Нам даны $A_i in bold(A)_i$
  ($i = 1, 2$). Так как каждый функтор $F_i$ кофинален относительно другого, то
  можно найти $A'_i, A''_i in bold(A)_i$ ($i = 1, 2$), такие, что
  $F_1 (A_1 perp A'_1) tilde.eq F_2 A''_2$ и
  $F_2 (A_2 perp A'_2) tilde.eq F_1 A''_1$. Положим
  $B_i = A_i perp A'_i perp A''_i$. Тогда очевидно, что
  $F_1 B_1 tilde.eq F_2 B_2$, и поэтому существует тройка
  $B = (B_1, beta, B_2)$. Это доказывает первую часть утверждения
  @cond:fiber-square-projection-cofinality. Кофинальность функтора $G_i$
  является ее непосредственным следствием. Так как в силу предположения функторы
  $F_i$ кофинальны, то также кофинальны и функторы $F_i G_i$.
]
