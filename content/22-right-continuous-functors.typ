#import "main-defs.typ": (
  Center, End, Hom, Id, Int, idx, moduleCategory, name-idx, ob, source,
  symbol-idx, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, proof, proposition, theorem,
)
#import "diagrams/module-categories-diagrams.typ": (
  homothety-square, map-arrow, tensor-natural-square,
)

== $R$-категории: непрерывные справа функторы <sec:right-continuous-functors>

Если элемент $c$ лежит в центре кольца $A$, то эндоморфизмы $x arrow.r.bar x c$
на $A$-модулях определяют эндоморфизм $h(c)$ тождественного функтора на
категории $moduleCategory hyph A$. И других эндоморфизмов нет. Более подробно:

#proposition[
  Отображение «гомотетии»#idx("гомотетия") #symbol-idx(
    $Center$,
    sort: "center",
    group: "operators",
    order: 33,
  )#symbol-idx($Id$, sort: "Id", group: "operators", order: 54)
  $
    h: Center A -> End(Id_(moduleCategory hyph A))
  $
  является изоморфизмом коммутативных колец.
] <prop:center-module-category>

#proof[
  Так как $h(c)_A (1) = 1 dot c = c$, то отображение $h$ инъективно. Очевидно,
  что это гомоморфизм колец. Наконец, пусть
  $t in End(Id_(moduleCategory hyph A))$. Положим $c = t_A (1)$. Если
  $x in M in moduleCategory hyph A$, то определим $f: A -> M$, положив
  $f(a) = x a$. Так как $t$~— естественное преобразование, то диаграмма
  $ #homothety-square() $
  коммутативна, и поэтому
  $t_M (x) = t_M (f(1)) = f(t_A (1)) = f(c) = x c = h(c)_M (x)$. Таким образом,
  $t = h(c)$, и, следовательно, отображение $h$ сюръективно.
]

Это предложение делает естественным следующее определение, где $bold(A)$~— любая
категория:
$
  Center bold(A) = End(Id_(bold(A)))
  #footnote[Легко убедиться, что это кольцо коммутативно.~— _Прим. ред._].
$

Пусть $R$~— коммутативное кольцо, и пусть $bold(A)$~— абелева категория. Легко
видеть, что задание кольцевого гомоморфизма $R -> Center bold(A)$ равносильно
заданию на всех абелевых группах $bold(A)(X, Y)$ структуры $R$-модулей таким
образом, что композиция является $R$-билинейным отображением. Категория
$bold(A)$ с этой дополнительной структурой называется _$R$-категорией_. #idx(
  "R-категория",
)Функтор $T: bold(A) -> bold(B)$, где $bold(A)$ и $bold(B)$~— две $R$-категории,
называется _$R$-функтором_,#idx("R-функтор") если отображения
$bold(A)(X, Y) -> bold(B)(T X, T Y)$ являются $R$-линейными. В том случае, когда
$R = Int$, мы получаем понятия абелевой категории и аддитивного функтора.

#source(61)_$R$-алгеброй_#idx("R-алгебра") называется кольцо $A$ с заданным
гомоморфизмом $R -> A$, образ которого лежит в центре кольца $A$. Из предложения
@prop:center-module-category следует, таким образом, что задание структуры
$R$-алгебры на $A$ равносильно заданию структуры $R$-категории на
$moduleCategory hyph A$.

Пусть $A$ и $B$~— две $R$-алгебры. Обозначим через
$A hyph moduleCategory hyph B$ категорию левых $A$- и правых $B$-бимодулей $M$ и
их гомоморфизмов. Напомним, что согласованность структур $A$- и $B$-модулей
требует, чтобы
$
  (a x) b = a(x b) quad (a in A, x in M, b in B).
$
Если $r in R$, то $r x$ и $x r$ определены, но, возможно, не совпадают.
Действительно, равенство $r x = x r$ для всех $x in M$ и $r in R$ равносильно
тому, что структура бимодуля на $M$ превращает $M$ в левый
$A tensor_R B^degree$-модуль. Кроме того, это эквивалентно также и тому, что
функтор $tensor_A M: moduleCategory hyph A -> moduleCategory hyph B$ является
$R$-функтором.

#proposition[
  Пусть $A$ и $B$~— две $R$-алгебры, и пусть функтор $h$ из категории
  $(A tensor_R B^degree) hyph moduleCategory$ в категорию $R$-функторов
  $moduleCategory hyph A -> moduleCategory hyph B$ определен следующим образом:
  $h(M) = tensor_A M$. Тогда функтор $h$ вполне строгий#footnote[
    То есть полный и строгий.~— _Прим. ред._
  ]. В частности, $[M tilde.eq N$ (как бимодули)$]
  <=> [tensor_A M tilde.eq tensor_A N$ (как функторы из $moduleCategory hyph A$
  в $moduleCategory hyph B$)$]$.
] <prop:tensor-functors-fully-faithful>

#proof[
  Если $f: M -> N$~— гомоморфизм бимодулей, то $h(f) = tensor_A f$. Если
  $h(f) = 0$, то из обращения в нуль $A tensor_A f$ следует, что $f = 0$, и
  поэтому функтор $h$ строгий.

  Предположим, что $t: h M -> h N$~— естественное преобразование. Пусть
  $f: M -> N$~— гомоморфизм, для которого диаграмма
  $ #tensor-natural-square() $
  коммутативна. Левые умножения в $A$ являются $A$-линейными справа
  отображениями, и в силу естественности $t_A$ обязано сохранить их. Таким
  образом, $t_A$, как и отображения, обозначенные вертикальными стрелками,
  являются гомоморфизмами бимодулей, и, следовательно, это верно и для $f$.
  Показав, что $t = h(f)$, мы докажем, что функтор $h$ полон. Пусть
  $s = t - h(f)$, и пусть $C$~— класс таких модулей
  $N in moduleCategory hyph A$, что $s_N = 0$. В силу определения класс $C$
  содержит $A$. Так как функторы $h M$ и $h N$ точны справа и сохраняют
  копроизведения, то $C$ удовлетворяет предположению предложения
  @prop:generator-coproduct-quotients @cond:generator-closure-characterization
  и, следовательно, $C = ob(moduleCategory hyph A)$, что и требовалось доказать.
]

Функторы $h M = tensor_A M$ из предложения @prop:tensor-functors-fully-faithful
обладают следующими свойствами: #condition-list[
  #condition-item[сохраняют коядра;] <cond:right-continuous-cokernels>
  #condition-item[сохраняют копро#source(62)изведения.]
  <cond:right-continuous-coproducts>
] Функтор, удовлетворяющий условиям @cond:right-continuous-cokernels и
@cond:right-continuous-coproducts, назовем _непрерывным справа_.#idx(
  "непрерывный справа функтор",
) #idx(
  "функтор",
  "непрерывный справа",
)Терминология оправдывается тем, что такой функтор обязан сохранять прямые
пределы. Непрерывные справа функторы в категориях модулей являются тензорными
произведениями. Более детально:

#theorem(title: [Эйленберг, Уотс])[
  #name-idx("Эйленберг (Eilenberg S.)")#name-idx("Уотс (Watts)") #idx(
    "теорема",
    "Эйленберга — Уотса",
  )#symbol-idx($tensor$, sort: "⊗", group: "symbols", order: 137)Пусть $A$, $B$
  и $C$~— три $R$-алгебры. Сопоставление $M arrow.r.bar h M = tensor_A M$ левому
  $A tensor_R B^degree$-модулю непрерывного справа $R$-функтора из
  $moduleCategory hyph A$ в $moduleCategory hyph B$ индуцирует биекцию на
  классах изоморфных объектов. Если $N$~— левый $B tensor_R C^degree$-модуль, то
  $
    h(M tensor_B N) = h(N) compose h(M).
  $
] <th:eilenberg-watts>

*Замечание.* Напрашивается желание сформулировать этот результат, используя
эквивалентность категорий, следующим образом. Пусть $bold(A)$ и $bold(B)$~—
категории, объектами которых в обоих случаях являются $R$-алгебры, а морфизмы
$
  bold(A)(A, B) = {"левые " A tensor_R B^degree "-модули"},
$
$
  bold(B)(A, B) = {"непрерывные справа функторы "
    moduleCategory hyph A -> moduleCategory hyph B}
$
соответственно. Категория $bold(B)$ вполне приемлема с композицией функторов в
качестве произведения. В категории $bold(A)$ хотелось бы использовать $tensor$ в
качестве произведения. Но тогда у нас нет ни тождественных морфизмов, ни
ассоциативности. Действительно, хотя модули $A tensor_A M$ и $M$ (канонически)
изоморфны, они не совпадают. Аналогично обстоит с ассоциативностью для $tensor$.
Таким образом, мы вынуждены перейти к рассмотрению классов изоморфных объектов.

#proof[
  Если $X in moduleCategory hyph A$, то
  $
    h(N) compose h(M)(X) &= h(N)(X tensor_A M) \
    &= (X tensor_A M) tensor_B N tilde.eq X tensor_A (M tensor_B N),
  $
  причем этот изоморфизм естественный, что доказывает последнее утверждение.

  Утверждение о том, что отображение $h$ инъективно на классах изоморфных
  объектов, содержится в предложении @prop:tensor-functors-fully-faithful.
  Остается лишь доказать, что непрерывный справа $R$-функтор
  $t: moduleCategory hyph A -> moduleCategory hyph B$ имеет вид $h M$. Положим
  $M = t A$ (вначале это лишь $B$-модуль). Гомоморфизм $R$-алгебр
  $
    A tilde.eq Hom_A (A, A) #map-arrow($t$) Hom_B (M, M)
  $
  превращает $M$ в левый $A tensor_R B^degree$-модуль.

  Для $X in moduleCategory hyph A$ рассмотрим отображения
  $
    X tilde.eq Hom_A (A, X) #map-arrow($t$) Hom_B (M, t X),
  $
  #source(63)композиция $f_X$ которых является $A$-линейным отображением
  относительно введенной структуры $A$-модуля на $M$. При каноническом
  изоморфизме
  $
    Hom_A (X, Hom_B (M, t X)) tilde.eq Hom_B (X tensor_A M, t X)
  $
  пусть элементу $f_X$ слева соответствует элемент $g_X$ справа. Так как
  отображения $f_X$ естественны по $X$, то $g_X$ также естественны по $X$:
  $g: h M -> t$. Поскольку функторы $h M$ и $t$ непрерывны справа, класс $C$
  объектов $X$, для которых $g_X$ является изоморфизмом, замкнут относительно
  копроизведений и коядер. Из утверждения @prop:generator-coproduct-quotients
  @cond:generator-closure-characterization следует тогда, что если $g_A$~—
  изоморфизм, то $g$~— изоморфизм, так как $A$~— образующий в
  $moduleCategory hyph A$. Но $g_A: A tensor_A M -> t A = M$ является
  стандартным изоморфизмом.
]

#corollary(word: [Следствие и определение])[
  Назовем левый $A tensor_R B^degree$-модуль _обратимым_, #idx(
    "обратимый модуль",
  )если выполнены следующие эквивалентные условия:

  #condition-list[
    #condition-item(
      format: "cyrillic",
    )[$tensor_A M: moduleCategory hyph A -> moduleCategory hyph B$~—
      эквивалентность;] <cond:invertible-right-tensor-equivalence>

    #condition-item(format: "cyrillic")[существует левый
      $B tensor_R A^degree$-модуль $N$, такой, что $M tensor_B N tilde.eq A$ и
      $N tensor_A M tilde.eq B$ (как
      бимодули);] <cond:invertible-bimodule-inverse>

    #condition-item(
      format: "cyrillic",
    )[$M tensor_B: B hyph moduleCategory -> A hyph moduleCategory$~—
      эквивалентность.] <cond:invertible-left-tensor-equivalence>
  ]
] <cor:invertible-bimodule>

#proof[
  Так как эквивалентность непрерывна справа, то импликации
  @cond:invertible-right-tensor-equivalence $<=>$
  @cond:invertible-bimodule-inverse следуют немедленно из теоремы
  @th:eilenberg-watts. Лево-правое отражение теоремы @th:eilenberg-watts
  показывает, что @cond:invertible-bimodule-inverse $<=>$
  @cond:invertible-left-tensor-equivalence.
]
