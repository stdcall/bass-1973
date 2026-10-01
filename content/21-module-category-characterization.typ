#import "main-defs.typ": (
  Coker, Hom, Im, Int, idx, moduleCategory, name-idx, ob, source,
)
#import "statements.typ": (
  condition-item, condition-list, exercise, proof, proposition, theorem,
)
#import "diagrams/module-categories-diagrams.typ": (
  left-exact-comparison, map-arrow,
)

== Характеризация категорий модулей <sec:module-category-characterization>

Функтор на абелевых категориях будем называть _строго точным_, #idx(
  "строго точный функтор",
)#idx("функтор", "строго точный")если он строгий и точный и если к тому же он
сохраняет произвольные копроизведения. Из этого следует, что он сохраняет
копределы.

Пусть $bold(A)$~— абелева категория, и пусть объект $P in bold(A)$ представляет
функтор $h = bold(A)(P, dot): bold(A) -> Int hyph moduleCategory$. Напомним, что
объект $P$ проективен, если функтор $h$ точен. Объект $P$ называется
_образующим_#idx("образующий") категории $bold(A)$, если функтор $h$ строгий.
Назовем объект $P$ _строго проективным_,#idx("объект", "строго проективный")
#idx("строго проективный объект")если функтор $h$ строго точен. Заметим, что это
несколько больше, чем то, что $P$ является проективным образующим, так как в
целом неверно, что функторы вида $bold(A)(P, dot)$ сохраняют копроизведения. Как
мы убедимся, это условие связано с условием конечнопорожденности в случае
модулей. Если $A$~— кольцо, то модуль $A$ строго проективен в
$moduleCategory hyph A$.

#source(57)
#proposition[
  Пусть $bold(A)$~— абелева категория с копроизведениями.

  #condition-list[
    #condition-item(format: "cyrillic")[Объект $P in bold(A)$ является
      образующим в $bold(A)$ тогда и только тогда, когда каждый объект в
      категории $bold(A)$ является факторобъектом объекта $P^((I))$ для
      некоторого множества $I$.] <cond:generator-coproduct-quotients>

    #condition-item(format: "cyrillic")[Пусть $C$~— класс объектов категории
      $bold(A)$, такой, что: #condition-list[
        #condition-item[$C$ содержит образующий категории $bold(A)$;]
        <cond:generator-class-contains-generator>
        #condition-item[копроизведения объектов из $C$ принадлежат $C$;]
        <cond:generator-class-coproducts>
        #condition-item[коядра морфизмов объектов из $C$ принадлежат $C$.]
        <cond:generator-class-cokernels>
      ] Тогда $C = ob bold(A)$.] <cond:generator-closure-characterization>
  ]
] <prop:generator-coproduct-quotients>

#proof[
  @cond:generator-coproduct-quotients Предположим, что $P$~— образующий в
  $bold(A)$ и $A in bold(A)$. Тогда $H = bold(A)(P, A)$ определяет морфизм
  $a: P^((H)) -> A$, и мы утверждаем, что он является эпиморфизмом. Пусть
  $b: A -> B$~— его коядро. Если $p in H = h(A)$, где $h = bold(A)(P, dot)$, то
  $h(b)(p) = b p$. Так как $Im(p) subset Im(a)$ и $b a = 0$, то $b p = 0$ и,
  следовательно, $h(b) = 0$. Но функтор $h$~— строгий, и поэтому $b = 0$, т. е.
  $a$~— эпиморфизм.

  Обратно, если существует эпиморфизм $(p_i)_(i in I): P^((I)) -> A$, то мы
  покажем, что $bold(A)(A, B) -> Hom_Int (h A, h B)$~— мономорфизм при любом
  $B in bold(A)$. Действительно, если $b: A -> B$~— морфизм и $h(b) = 0$, то
  $h(b)(p_i) = b p_i = 0$ для всех $i in I$, и, следовательно, $b(p_i) = 0$. Но
  $(p_i)_(i in I)$~— эпиморфизм, и поэтому $b = 0$.

  @cond:generator-closure-characterization Если $P in C$~— образующий в
  $bold(A)$, то из пункта @cond:generator-coproduct-quotients следует, что для
  любого объекта $A$ из $bold(A)$ найдется точная последовательность
  $P^((J)) -> P^((I)) -> A -> 0$.

  Следовательно, из условий @cond:generator-class-contains-generator,
  @cond:generator-class-coproducts и @cond:generator-class-cokernels следует,
  что $C = ob bold(A)$, что и требовалось доказать.
]

#proposition[
  Пусть $A$~— кольцо и $P in moduleCategory hyph A$.

  #condition-list[
    #condition-item(format: "cyrillic")[Модуль $P$ конечно порожден и проективен
      тогда и только тогда, когда $P$ является прямым слагаемым модуля $A^((n))$
      для некоторого $n >= 0$.] <cond:projective-finite-free-summand>

    #condition-item(format: "cyrillic")[Модуль $P$ является образующим в
      категории $moduleCategory hyph A$ тогда и только тогда, когда $A$~— прямое
      слагаемое модуля $P^((n))$ для некоторого
      $n >= 0$.] <cond:generator-finite-coproduct-summand>

    #condition-item(format: "cyrillic")[Модуль $P$ строго проективен тогда и
      только тогда, когда $P$ является конечно порожденным проективным
      образующим в
      $moduleCategory hyph A$.] <cond:strict-projective-characterization>
  ]
] <prop:strict-projective-modules>

#proof[
  @cond:projective-finite-free-summand Функтор $Hom_A (A, dot)$ изоморфен
  тождественному функтору, и поэтому $A$~— проективный модуль, и, следовательно,
  аналогичное рассуждение применимо к модулю $A^((n))$ и его прямым слагаемым.
  Если $P$~— конечно порожденный модуль, то существует эпиморфизм
  $A^((n)) -> P$, который расщепляется, если $P$~— проективный модуль.

  @cond:generator-finite-coproduct-summand Каждый модуль является фактормодулем
  модуля $A^((I))$ для некоторого $I$, и поэтому $A$ является образующим в
  $moduleCategory hyph A$. Если $A$~— #source(58)прямое слагаемое модуля
  $P^((n))$, то очевидно, что $P$ также является образующим. Обратно, если $P$~—
  образующий, то $A$ является фактормодулем и, следовательно, прямым слагаемым
  копроизведения некоторого множества экземпляров модуля $P$. Так как $A$~—
  конечно порожденный модуль, то достаточно взять копроизведение конечного числа
  экземпляров.

  @cond:strict-projective-characterization В силу определения функтор
  $Hom_A (P, dot)$ строгий и точный в том и только в том случае, когда $P$~—
  проективный образующий. Следовательно, достаточно показать, что проективный
  модуль $P$ конечно порожден тогда и только тогда, когда функтор
  $h = Hom_A (P, dot)$ сохраняет копроизведения. Последнее условие
  $Hom_A (P, product.co M_i) = product.co Hom_A (P, M_i)$ означает как раз, что
  образ любого морфизма $f: P -> product.co M_i$ лежит в подмодуле, порожденном
  конечным числом модулей $M_i$. Очевидно, что любой конечно порожденный модуль
  $P$ обладает этим свойством. Обратно, если $P$~— проективный модуль, то
  существует расщепляющийся мономорфизм $f: P -> A^((I))$ для некоторого $I$.
  Приведенное выше условие влечет за собой, что $P tilde.eq f(P)$ является
  прямым слагаемым модуля $A^((J))$ для некоторого конечного подмножества $J$ в
  $I$, и, следовательно, модуль $P$ конечно порожден.
]

#exercise[
  #condition-list[
    #condition-item(format: "cyrillic")[Покажите, что модуль $P$ конечно
      порожден тогда и только тогда, когда объединение линейно упорядоченного
      семейства собственных подмодулей модуля $P$ является собственным
      подмодулем.] <cond:finite-generation-chain-condition>

    #condition-item(format: "cyrillic")[Покажите, что функтор $Hom_A (P, dot)$
      сохраняет копроизведения тогда и только тогда, когда объединение каждой
      (счетной) цепи собственных подмодулей является собственным
      подмодулем.] <cond:small-module-chain-condition>

    #condition-item(format: "cyrillic")[Покажите, что условия в
      @cond:finite-generation-chain-condition и
      @cond:small-module-chain-condition не равносильны. (Не так просто найти
      примеры.)] <cond:chain-conditions-nonequivalent>
  ]
] <exc:finite-generation-coproducts>

Кажется, что модуль $A$ играет в категории $moduleCategory hyph A$ в каком-то
смысле особую роль. Это не совсем так. Любой другой строго проективный модуль
может играть ту же роль. Выделение модуля $A$ в $moduleCategory hyph A$ также
произвольно, как и выбор базиса векторного пространства. Более того, этот
принцип может быть применен в обратном направлении: общие теоремы о строго
проективных модулях иногда нужно доказывать лишь для $A$ (см. предложение
@prop:picard-stabilizer ниже в качестве примера).

#theorem(title: [Габриель, Митчел])[
  #name-idx("Габриель (Gabriel P.)")#name-idx("Митчелл (Mitchell B.)") #idx(
    "теорема",
    "Габриэля — Митчелла",
  )Пусть $bold(A)$~— абелева категория с копроизведениями и со строго
  проективным объектом $P$. Положим $A = bold(A)(P, P)$. Тогда функтор
  $
    h = bold(A)(P, dot): bold(A) -> moduleCategory hyph A
  $
  является эквивалентностью категорий и $h(P) = A$~— свободный модуль с одним
  образующим.
] <th:gabriel-mitchell>

#proof[
  #source(59)Учитывая критерий эквивалентности @prop:equivalence-criterion, нам
  надо установить следующие свойства @cond:gabriel-fully-faithful и
  @cond:gabriel-essentially-surjective:

  #condition-list[
    #condition-item(format: "cyrillic")[
      $h_(X, Y): bold(A)(X, Y) -> Hom_A (h X, h Y)$~— изоморфизм для всех
      $X, Y in bold(A)$;
    ] <cond:gabriel-fully-faithful>

    #condition-item(format: "cyrillic")[каждый модуль
      $M in moduleCategory hyph A$ изоморфен некоторому модулю $h X$.]
    <cond:gabriel-essentially-surjective>
  ]

  Зафиксируем $Y in bold(A)$. Будем рассматривать $h_(X, Y)$ как естественное
  преобразование $alpha_X: T X -> S X$, где $T$ и $S$~— указанные функторы из
  $bold(A)^degree$ в $Int hyph moduleCategory$.

  Докажем свойство @cond:gabriel-fully-faithful, показав, что класс $C$ объектов
  $X$, для которых $alpha_X$ является изоморфизмом, #condition-list[
    #condition-item[содержит образующий;] <cond:gabriel-class-generator>
    #condition-item[выдерживает копроизведения;] <cond:gabriel-class-coproducts>
    #condition-item[«замкнут относительно
      коядер».] <cond:gabriel-class-cokernels>
  ] Действительно, тогда в силу предложения @prop:generator-coproduct-quotients
  @cond:generator-closure-characterization следует, что $C = ob bold(A)$.

  Так как функтор $h$ строгий, то $P$~— образующий. Кроме того, как легко
  видеть,
  $alpha_P: bold(A)(P, Y) -> Hom_A (h P, h Y) = Hom_A (A, bold(A)(P, Y))$
  является стандартным изоморфизмом, и это доказывает
  @cond:gabriel-class-generator.

  Условие @cond:gabriel-class-coproducts следует из того, что оба функтора $S$ и
  $T$ переводят копроизведения в произведения. Для $T$ это очевидно, а для $S$
  это вытекает из нашего предположения о том, что функтор $h$ сохраняет
  копроизведения.

  Условие @cond:gabriel-class-cokernels означает, что если последовательность
  $X -> Y -> Z -> 0$ точна в $bold(A)$, то $X, Y in C => Z in C$. Но функтор $T$
  точен слева. Так как функтор $h$ точен, то функтор $S$ также точен слева.
  Следовательно, получаем коммутативную диаграмму с точными строками
  $ #left-exact-comparison() $
  Наше утверждение следует из леммы @prop:five-lemma.

  Для доказательства пункта @cond:gabriel-essentially-surjective пусть
  $M = Coker(A^((I)) #map-arrow($f$) A^((J)))$. Тогда
  $
    f in Hom_A ((h P)^((I)), (h P)^((J)))
    = Hom_A (h(P^((I))), h(P^((J)))),
  $
  и поэтому $f = h(g)$ для некоторого $g: P^((I)) -> P^((J))$ (благодаря части
  @cond:gabriel-fully-faithful утверждения). В силу точности
  $
    M tilde.eq Coker(f) = Coker(h(g)) tilde.eq h(Coker g),
  $
  что и требовалось доказать.
]

#exercise(title: [Лэм])[
  #name-idx("Лэм (Lam T.-Y.)")#idx("теорема", "Лэма")Пусть $bold(A)$~— абелева
  категория, в которой все объекты нётеровы (т. е. выполняется условие обрыва
  возрастающих цепей подобъектов). Допустим, что $P$~— проективный образующий в
  $bold(A)$. Положим $A = bold(A)(P, P)$. Покажите, что #source(60)$A$~—
  нётерово справа кольцо и что функтор $bold(A)(P, dot)$ определяет
  эквивалентность из категории $bold(A)$ в категорию конечно порожденных правых
  $A$-модулей.
] <exc:lam-noetherian-module-category>
