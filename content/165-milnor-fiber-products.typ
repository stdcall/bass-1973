#import "main-defs.typ": (
  AzCat, ContMaps, E, G, GFunctor, GL, H, HFunctor, Hom, Im, K, Ker, Pic,
  PicCat, Quad, Rk, SK, U, coker, det, ed-note, idx, moduleCategory, source,
  spec, symbol-idx, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, example, numbered-condition, proof,
  proposition, remark, theorem,
)
#import "diagrams/projective-k-theory-milnor.typ": (
  milnor-adjoint-square, milnor-category-square, milnor-conductor-square,
  milnor-determinant-square, milnor-intersection-square,
  milnor-product-induction-square, milnor-quotient-square,
  milnor-reduced-determinant-sequences, milnor-ring-square,
  milnor-spectrum-square, milnor-two-squares,
)

== Расслоенные произведения; теорема Милнора <sec:milnor-fiber-products>

Пусть диаграмма #numbered-condition[$ #milnor-ring-square() $]
<eq:milnor-ring-pullback-square>
является декартовым квадратом гомоморфизмов колец. Таким образом,
$ A = {(a_1, a_2) in A_1 times A_2 | f_1 a_1 = f_2 a_2}, $
#source(372)и отображения $h_i$ индуцированы координатными проекциями. Полагая
$bold(P)' = bold(P)(A')$ и $bold(P)_i = bold(P)(A_i)$ ($i = 1, 2$), получаем
диаграмму функторов #numbered-condition[
  $ #milnor-category-square() quad beta: F_1 HFunctor_1 -> F_2 HFunctor_2 $
] <eq:milnor-projective-functor-square>
где $F_i = tensor_(A_i) A'$, $HFunctor_i = tensor_A A_i$ ($i = 1, 2$), а $beta$
— естественный изоморфизм, возникающий в связи с изоморфизмами
$(P tensor_A A_i) tensor_(A_i) A' approx P tensor_A A'$ ($i = 1, 2$).

Мы получаем также категорию расслоенного произведения
$bold(P) = bold(P)_1 times_(bold(P)') bold(P)_2$
(см. гл.~@ch:exact-k-sequences, §~@sec:fiber-product-categories) и декартов
квадрат #numbered-condition[
  $
    #milnor-category-square(fiber: true) quad alpha: F_1 GFunctor_1 -> F_2
    GFunctor_2
  $
] <eq:milnor-projective-fiber-square>
Из универсального свойства диаграммы @eq:milnor-projective-fiber-square следует
существование единственного функтора
$ T: bold(P)(A) -> bold(P), $
$ T(P) = (HFunctor_1 P, beta_P, HFunctor_2 P), $
для которого $HFunctor_i = GFunctor_i T$ ($i = 1, 2$) и $beta = alpha T$.

#theorem(title: [Милнор])[
  #idx("теорема Милнора")Если отображение $f_1$ или $f_2$ сюръективно, то
  функтор
  $
    T: bold(P)(A_1 times_(A') A_2) ->
    bold(P)(A_1) times_(bold(P)(A')) bold(P)(A_2)
  $
  является эквивалентностью.
] <th:milnor-projective-patching>

#proof[
  Положим $bold(M)' = moduleCategory-A'$, $bold(M)_i = moduleCategory-A_i$
  ($i = 1, 2$) и $bold(M) = bold(M)_1 times_(bold(M)') bold(M)_2$. Эти категории
  содержат в себе соответствующие из категорий, рассмотренных выше. Члены
  диаграмм @eq:milnor-projective-functor-square и
  @eq:milnor-projective-fiber-square можно вложить в соответствующие члены
  диаграмм
  $
    #milnor-category-square(modules: true) quad "и" quad
    #milnor-category-square(fiber: true, modules: true)
  $
  #source(373)Мы не будем различать функторы $F$, $GFunctor$, $HFunctor$ и
  функторы, которые они индуцируют на меньших категориях. Как и выше, получаем
  функтор $T: moduleCategory-A -> bold(M)$, индуцирующий приведенный выше.
  Построим теперь функтор, ему сопряженный, $S: bold(M) -> moduleCategory-A$.
  Если $M = (M_1, alpha_M, M_2) in bold(M)$, то образуем следующую диаграмму:
  $ #milnor-adjoint-square() $
  Именно,
  $
    S M = {(x_1, x_2) in M_1 times M_2 | alpha_M (x_1 tensor 1) = x_2 tensor 1}.
  $
  Ясно, что в $S M$ существует естественная структура правого $A$-модуля и что
  соответствие $M |-> S M$ определяет аддитивный функтор из $bold(M)$ в
  $moduleCategory-A$. Желая показать, что $S$ является сопряженным для $T$, мы
  должны указать естественное отождествление
  $ Hom_A (N, S M) = Hom_bold(M) (T N, M) $
  для $N in moduleCategory-A$ и $M in bold(M)$. По самому построению $S M$ как
  расслоенного произведения
  $ Hom_A (N, S M) = Hom_A (N, M_1) times_(Hom_A (N, F_2 M_2)) Hom_A (N, M_2). $
  Но существует стандартное отождествление
  $
    Hom_A (N, M_i) = Hom_(A_i) (N tensor_A A_i, M_i) =
    Hom_(A_i) (HFunctor_i N, M_i)
  $
  и т. д., так что можно записать
  $
    Hom_A (N, S M)
    = Hom_(A_1) (HFunctor_1 N, M_1)
    times_(Hom_(A') (F_1 HFunctor_1 N, F_2 M_2)) Hom_(A_2) (HFunctor_2 N, M_2)
    = {(h_1, h_2) | h_i in Hom_(A_i) (HFunctor_i N, M_i) quad (i = 1, 2)
      "и" alpha_M (h_1 tensor A') = (h_2 tensor A')}
    = Hom_bold(M) (T N, M).
  $
  Естественное преобразование $phi_N: N -> S T N$, очевидно, является
  изоморфизмом для $N = A$. В силу аддитивности, _$phi_P$ — изоморфизм для всех
  $P in bold(P)(A)$_.

  До сих пор мы не использовали дополнительных предположений. Покажем теперь,
  что если отображение $f_1$ (или $f_2$) сюръективно, то функтор
  $T: bold(P)(A) -> bold(P)$ кофинален (относительно $plus.o$). Это означает,
  что как только нам дан модуль $U in bold(P)$, то найдутся модули
  $V in bold(P)$ и $P in bold(P)(A)$, для которых $U plus.o V approx T P$. Тогда
  мы получим, что $S U plus.o S V approx S T P approx P$ (используя $phi$), и
  поэтому $S U in bold(P)(A)$. Таким образом, $S$ индуцирует сопряженный функтор
  $S: bold(P) -> bold(P)(A)$ для функтора $T: bold(P)(A) -> bold(P)$. Кроме
  того, из @cor:adjunction-equivalence #source(374)будет следовать, что эти
  функторы являются взаимно обратными эквивалентностями. Таким образом, теорема
  будет доказана, как только мы убедимся, что функтор $T$ кофинален.

  Если отображение $f_1$ сюръективно, то, как мы видели в доказательстве
  @th:ideal-relative-k-exact-sequences, функтор $F_1: bold(P)_1 -> bold(P)'$
  является $E$-сюръективным. Следовательно, диаграмма
  @eq:milnor-projective-fiber-square $E$-сюръективна в смысле
  гл.~@ch:exact-k-sequences, §~@sec:fiber-product-categories. Тогда из
  @prop:fiber-square-cofinality @cond:fiber-square-cofinality следует, что
  функтор $T$ кофинален. Это завершает доказательство теоремы.
]

#remark[
  Эта теорема утверждает, что декартов квадрат @eq:milnor-ring-pullback-square,
  в котором отображение $f_1$ (или $f_2$) сюръективно, приводит нас к квадрату
  @eq:milnor-projective-functor-square, который с точностью до эквивалентности
  также является декартовым. Если все рассматриваемые кольца коммутативны, то
  можно получить другие такие эквивалентности. Например, квадраты, аналогичные
  квадрату @eq:milnor-projective-functor-square, для категорий $PicCat$, $Quad$
  или $AzCat$ вместо $bold(P)$ (см. @exm:product-categories) также являются по
  существу декартовыми. Это же рассуждение применимо к различным другим
  категориям «проективных модулей со структурами». В каждом случае основная
  эквивалентность может быть легко получена из теоремы Милнора. Важность этого
  замечания в том, что по существу все результаты, которые мы получим для
  категории $bold(P)$, обладают аналогами для указанных категорий.
] <rem:milnor-structured-projective-patching>

#theorem(title: [Милнор])[
  #idx("теорема Милнора")Пусть диаграмма
  $ #milnor-ring-square() $
  является декартовым квадратом гомоморфизмов колец, в котором отображение $f_1$
  (или $f_2$) сюръективно. Тогда имеет место точная последовательность Майера —
  Вьеториса #numbered-condition[
    $
      K_1 (A) -> K_1 (A_1) plus.o K_1 (A_2) -> K_1 (A') ->
      K_0 (A) -> K_0 (A_1) plus.o K_0 (A_2) -> K_0 (A').
    $
  ] <eq:projective-k-mayer-vietoris>
  Если все рассматриваемые кольца коммутативны, то также имеет место следующая
  последовательность Майера — Вьеториса: #numbered-condition[
    $
      0 -> U(A) -> U(A_1) plus.o U(A_2) -> U(A') ->
      Pic(A) -> Pic(A_1) plus.o Pic(A_2) -> Pic(A'),
    $
  ] <eq:picard-mayer-vietoris>
  при этом $det: #[@eq:projective-k-mayer-vietoris] ->
  #[@eq:picard-mayer-vietoris]$ является эпиморфизмом точных
  последовательностей.
] <th:projective-k-mayer-vietoris>

#proof[
  #source(375)Эти последовательности в точности совпадают с последовательностями
  из гл.~@ch:exact-k-sequences, §~@sec:mayer-vietoris-sequence. Для их получения
  необходима теорема Милнора и замечание о том, что декартов квадрат
  @eq:milnor-projective-functor-square является $E$-сюръективным.

  Морфизм декартовых квадратов
  $
    det: #milnor-determinant-square() ->
    #milnor-determinant-square(picard: true)
  $
  в случае коммутативных колец индуцирует морфизм последовательностей Майера —
  Вьеториса, который, как мы знаем из §~@sec:rank-determinant-picard,
  оказывается сюръективным. Наконец, очевидно, что отображение
  $U(A) -> U(A_1) plus.o U(A_2)$ инъективно. Тем самым доказательство закончено.
]

#theorem[
  В ситуации теоремы @th:projective-k-mayer-vietoris естественные гомоморфизмы
  $ K'_0 (h_2) -> K'_0 (f_1) quad "и" quad K'_0 (h_1) -> K'_0 (f_2) $
  являются изоморфизмами. Если рассматриваемые кольца коммутативны, то
  соответствующие изоморфизмы
  $ Pic(h_2) -> Pic(f_1) quad "и" quad Pic(h_1) -> Pic(f_2) $
  также являются изоморфизмами.
] <th:projective-k-pullback-excision>

#proof[
  Эти отображения в точности совпадают с изоморфизмами вырезания из
  гл.~@ch:exact-k-sequences, §~@sec:excision-isomorphisms.
]

Последовательности Майера — Вьеториса оказываются в основном полезными для
получения информации о группе $K_0 (A)$ и о группе $Pic(A)$ в случае
коммутативного кольца $A$. Таким образом, необходимо знать, как можно построить
декартов квадрат, исходя из кольца $A$.

#example(title: [в котором оба отображения $f_1$ и $f_2$ сюръективны])[
  Начнем с двусторонних идеалов $frak(q)_1$ и $frak(q)_2$ кольца $A$,
  пересечение которых $frak(q)_1 inter frak(q)_2$ равно нулю. Тогда квадрат
  $ #milnor-quotient-square() $
  является декартовым. Из результатов о вырезании следует, что
  $
    K_0 (A, frak(q)_1) approx K_0 (A slash frak(q)_2,
      (frak(q)_1 + frak(q)_2) slash frak(q)_2).
  $
  Аналогичное утверждение справедливо и для функтора $Pic$ в коммутативном
  случае. Заметим, что аналог этого утверждения для #source(376)функтора $K_1$
  был доказан в @prop:disjoint-ideal-relative-k-decomposition. Примеры такого
  типа возникают в гл.~@ch:finite-group-induction,
  §~@sec:group-ring-k0-g0-applications.
] <exm:disjoint-ideal-pullback>

#example(title: [в котором отображение $f_1$ инъективно, а отображение $f_2$
  сюръективно])[
  Пусть $A$ — подкольцо кольца $B$ и $frak(c)$ — двусторонний $B$-идеал, лежащий
  в $A$. Тогда получаем декартов квадрат
  $ #milnor-conductor-square() $
  где отображения $j$ и $j'$ — вложения. Назовем возникающую ситуацию «ситуацией
  кондуктора», поскольку она часто встречается тогда, когда $frak(c)$ является
  кондуктором из области целостности $A$ в ее целое замыкание $B$. Примеры этого
  типа встретятся нам в гл.~@ch:arithmetic-finiteness и
  @ch:finite-group-induction. В этом случае изоморфизмы вырезания таковы:
  $
    K'_0 (j) arrow.r.tilde K'_0 (j') quad "и" quad
    K_0 (A, frak(c)) arrow.r.tilde K_0 (B, frak(c)).
  $
  Аналогично в коммутативном случае получаем изоморфизмы
  $
    Pic(j) arrow.r.tilde Pic(j') quad "и" quad
    Pic(A, frak(c)) arrow.r.tilde Pic(B, frak(c)).
  $
] <exm:conductor-pullback>

#example(title: [в котором оба отображения $f_1$ и $f_2$ инъективны])[
  Диаграмма вложений колец
  $ #milnor-intersection-square() $
  является декартовым квадратом, если $A = A_1 inter A_2$. Приведенные выше
  теоремы здесь неприменимы, кроме тривиального случая $A' = A_1$ или
  $A' = A_2$. Тем не менее существует последовательность Майера — Вьеториса для
  декартова квадрата @eq:milnor-projective-fiber-square, где $bold(P)(A)$
  заменяется на $bold(P)(A_1) times_(bold(P)(A')) bold(P)(A_2)$. Эта
  последовательность будет использована в гл.~@ch:polynomial-extensions,
  §~@sec:projective-line-k0, где рассматривается функтор $K_0$ на проективной
  прямой над кольцом $A$.
] <exm:subring-intersection-pullback>

Имеется частный случай изоморфизма вырезания для функтора $K_1$, который будет
применяться далее.

#proposition[
  Пусть $B = product_(1<=i<=n) B_i$ — произведение колец и $A subset B$ —
  подкольцо, все проекции которого в каждое из $B_i$ сюръективны. Пусть
  $frak(c)$ — двусторонний идеал кольца $B$, лежащий в $A$. Тогда естественный
  гомоморфизм $K_1 (A, frak(c)) -> K_1 (B, frak(c))$ является изоморфизмом.
] <prop:subdirect-product-relative-k-one-excision>

#proof[
  #source(377)Группа $GL(B, frak(c))$ состоит из всех матриц $alpha in GL(B)$,
  для которых элементы матриц $alpha - I$ и $alpha^(-1) - I$ лежат в $frak(c)$.
  Из этого следует, что элементы матриц $alpha$ и $alpha^(-1)$ лежат в $A$.
  Поэтому
  $ GL(A, frak(c)) = GL(B, frak(c)). $
  Так как
  $
    (K_1 (A, frak(c)) -> K_1 (B, frak(c)))
    = (GL(A, frak(c)) slash E(A, frak(c)) ->
      GL(B, frak(c)) slash E(B, frak(c))),
  $
  то предложение будет доказано, как только мы покажем, что включение
  $E(A, frak(c)) subset E(B, frak(c))$ является равенством.

  Через $S$ обозначим множество элементарных матриц, сравнимых с $I$ по модулю
  идеала $frak(c)$. Тогда $E(A, frak(c))$ (соответственно $E(B, frak(c))$)
  является _нормальным_ делителем группы $E(A)$ (соответственно группы $E(B)$),
  порожденным $S$ (см. гл.~@ch:mennicke-symbols,
  §~@sec:universal-mennicke-symbols).

  Так как $frak(c)$ является $B$-идеалом, то $frak(c)$ — прямая сумма идеалов
  $frak(c)_i$, которые отображаются мономорфно в кольцо $B_i$ ($1 <= i <= n$) и
  отображаются в нуль кольца $B_j$, если $j != i$. Через $S'$ обозначим
  множество тех элементов $epsilon in S$, таких, что
  $epsilon equiv I mod frak(c)_i$ для некоторого $i$. Группа, порожденная
  элементами из $S'$, очевидно, содержит $S$. Поэтому $E(B, frak(c))$ является
  группой, порожденной всеми матрицами вида $beta epsilon beta^(-1)$, где
  $beta in E(B)$ и $epsilon in S'$. Таким образом, достаточно показать, что
  каждая такая матрица $beta epsilon beta^(-1)$ лежит в $E(A, frak(c))$. В
  $(product B_i)$-координатах можно записать, что
  $beta = (beta_1, beta_2, dots, beta_n)$, $epsilon = (epsilon_1, I, dots, I)$,
  считая $epsilon equiv I mod frak(c)_1$. Так как отображение $A -> B_1$
  сюръективно (в силу предположения), то отображение $E(A) -> E(B_1)$ также
  сюръективно (см. @prop:elementary-matrices-quotient-surjection). Таким
  образом, поскольку $beta_1 in E(B_1)$, можно найти
  $alpha = (beta_1, alpha_2, dots, alpha_n) in E(A)$. Тогда
  $beta epsilon beta^(-1) = (beta_1 epsilon_1 beta_1^(-1), I, dots, I)
  = alpha epsilon alpha^(-1) in E(A, frak(c))$, что завершает доказательство.
]

Сейчас мы получим слабый вариант утверждения типа теорем Майера — Вьеториса для
функторов $G_i$.

#proposition[
  Пусть диаграмма
  $ #milnor-ring-square() $
  является декартовым квадратом нётеровых справа колец, которые являются также
  конечно порожденными правыми $A$-модулями. Допустим, что отображение $f_1$
  (или $f_2$) сюръективно. Тогда гомоморфизмы ограничения индуцируют эпиморфизмы
  $ G_i (A_1) plus.o G_i (A_2) -> G_i (A) quad (i = 0, 1). $
] <prop:abelian-k-pullback-generation>

#proof[
  #source(378)Указанные гомоморфизмы индуцируются функтором «ограничения» из
  $bold(M)(A_1 times A_2)$ в $bold(M)(A)$. Пусть $B = A_1 times A_2$ и
  $frak(c)_1 = Ker(h_1)$. Допустим, что, например, отображение $f_2$
  сюръективно. Тогда $A slash frak(c)_1 = A_1$, а $frak(c)_1$ является
  $B$-идеалом, содержащимся в $A$.

  Для $M in bold(M)(A)$ положим $N = M tensor_A B$ и рассмотрим естественное
  отображение $eta:M -> N$. Если $c in frak(c)_1$, то формула
  $m tensor b arrow.r.bar m(b c)$ определяет аддитивное отображение $N -> M$,
  поскольку $B frak(c)_1 subset A$. Его композиция с $eta$ есть умножение на
  $c$. Поэтому $Ker(eta) dot frak(c)_1 = 0$. Равенство
  $(m tensor b)c = m(b c) tensor 1$ показывает также, что
  $"Coker"(eta) dot frak(c)_1 = 0$.

  Таким образом, $K = Ker(eta)$ и $C = "Coker"(eta)$ — конечно порожденные
  $A_1$-модули, а $N$ — конечно порожденный $B$-модуль. Из двух коротких точных
  последовательностей, связанных с $eta$, получаем
  $ [M] = [K] + [N] - [C] quad "в" G_0 (A). $
  Каждый автоморфизм $alpha$ модуля $M$ индуцирует автоморфизмы $alpha_K$,
  $alpha tensor 1$ и $alpha_C$ этих модулей. Из тех же точных
  последовательностей получаем
  $
    [M, alpha] = [K, alpha_K] + [N, alpha tensor 1] - [C, alpha_C]
    quad "в" G_1 (A).
  $
  Следовательно, указанные гомоморфизмы сюръективны при $i = 0, 1$.#ed-note[
    В исходном доказательстве предполагается структура $A_2$-модуля на
    $M frak(c)_1$, которая может не существовать. Например, для поля $k$,
    $A = k + x^2 k[x]$, $A_2 = k[x]$, $frak(c)_1 = x^2 k[x]$ и
    $M = A slash (x^4 A)$ пространство $M frak(c)_1$ имеет базис $x^2$, $x^3$,
    $x^5$. Действие $x^2$ на $x^2$ нулевое, а действие $x^3$ ненулевое, что
    исключает продолжение действия до $k[x]$. О соотношениях Гротендика и точном
    ограничении скаляров см. #cite(<Weibel2013>, form: "full"), гл.~II, §~6
    (6.1.1, 6.2).
  ]
]

#corollary[
  Пусть $B = product_(1<=i<=n) B_i$ — произведение колец и $A subset B$ —
  подкольцо, проектирующееся сюръективно на каждый сомножитель $B_i$. Тогда
  гомоморфизмы $G_i (B) = union.sq.big G_i (B_j) -> G_i (A)$ ($i = 0, 1$)
  сюръективны.
] <cor:subdirect-product-g-restriction-surjection>

#proof[
  Пусть $A'_1$ — проекция $A$ в $B_2 times dots times B_n$. Тогда имеется
  расслоенное произведение
  $ #milnor-product-induction-square() $
  к которому можно применить @prop:abelian-k-pullback-generation и показать, что
  отображения $G_i (B_1) plus.o G_i (A'_1) -> G_i (A)$ сюръективны ($i = 0, 1$).
  Проводя индукцию по $n$, делаем вывод, что отображение
  $G_i (B_2) plus.o dots plus.o G_i (B_n) -> G_i (A'_1)$ сюръективно.
  Доказательство закончено.
]

Мы завершим этот параграф описанием поведения функтора $H_0$ на расслоенном
произведении. Эта информация потребуется нам в некоторых вычислениях гл.
@ch:finite-group-induction.

#proposition[
  Пусть диаграмма @eq:milnor-ring-pullback-square является декартовым квадратом
  гомоморфизмов коммутативных колец, в котором отображение $f_1$ (или $f_2$)
  сюръективно. Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[квадрат #source(379)#numbered-condition[
        $ #milnor-spectrum-square() $
      ] <eq:milnor-spectrum-pushout>
      является кодекартовым в категории топологических пространств;]
    <cond:milnor-spectrum-topological-pushout>
    #condition-item(format: "cyrillic")[последовательность #numbered-condition[
        $
          0 -> H_0 (A) arrow.r^(binom(H_0 (h_1), -H_0 (h_2)))
          H_0 (A_1) plus.o H_0 (A_2)
          arrow.r^((H_0 (f_1), H_0 (f_2))) H_0 (A')
        $
      ] <eq:milnor-rank-functions-exact-sequence>
      точна и $coker(H_0 (f_1), H_0 (f_2))$ — абелева группа без кручения.]
    <cond:milnor-rank-functions-torsion-free-cokernel>
  ]
] <prop:milnor-spectrum-rank-pushout>

#proof[
  @cond:milnor-spectrum-topological-pushout Пусть, скажем, отображение $f_2$
  сюръективно. Тогда разложим $f_1$ в произведение эпиморфизма, за которым
  следует мономорфизм. В любой категории, если два квадрата прямоугольника
  $ #milnor-two-squares() $
  являются (ко)декартовыми, то этим же свойством обладает и прямоугольник.
  Следовательно, достаточно рассмотреть отдельно такие случаи:
  #condition-list[
    #condition-item(format: "(1°)")[отображение $f_1$ также сюръективно;]
    <cond:milnor-pushout-both-surjective>
    #condition-item(format: "(1°)")[отображение $f_1$ инъективно.]
    <cond:milnor-pushout-conductor-case>
  ]

  @cond:milnor-pushout-both-surjective В первом случае можно записать
  $A_i = A slash frak(a)_i$ ($i = 1, 2$) и
  $A' = A slash (frak(a)_1 + frak(a)_2)$, где пересечение идеалов $frak(a)_1$ и
  $frak(a)_2$ равно нулю. (См. пример @exm:disjoint-ideal-pullback.) Тогда все
  встречающиеся пространства $spec$ можно отождествить с замкнутыми
  подмножествами в $spec(A)$, используя вложения в диаграмме
  @eq:milnor-spectrum-pushout. С этими отождествлениями получаем
  $
    spec(A_1) union spec(A_2) = V(frak(a)_1) union V(frak(a)_2)
    = V(frak(a)_1 inter frak(a)_2) = spec(A),
  $
  $
    spec(A_1) inter spec(A_2) = V(frak(a)_1) inter V(frak(a)_2)
    = V(frak(a)_1 + frak(a)_2) = spec(A').
  $
  Эти соотношения показывают, что квадрат @eq:milnor-spectrum-pushout является
  кодекартовым.

  @cond:milnor-pushout-conductor-case Во втором случае можно отождествить $A$ с
  подкольцом кольца $A_2$, при этом $A_1 = A slash frak(c)$ и
  $A' = A_2 slash frak(c)$ для некоторого $A_2$-идеала $frak(c) subset A$. (См.
  пример @exm:conductor-pullback.) Тогда можно отождествить
  $spec(A_1) = V_A (frak(c)) subset spec(A)$ и
  $spec(A') = V_(A_2) (frak(c)) subset spec(A_2)$. Кроме того, при отображении
  $spec(A_2) -> spec(A)$ идеал $frak(p)$ переходит в $frak(p) inter A$. Нам надо
  доказать, что $spec(A)$ является объединением #source(380)$V_A (frak(c))$ и
  образа пространства $spec(A_2)$ и что если $frak(p) in spec(A_2)$ и при этом
  $frak(p) inter A in V_A (frak(c))$, то $frak(p) in V_(A_2) (frak(c))$.
  Последнее утверждение в точности совпадает с импликацией
  «$frak(p) inter A supset frak(c) => frak(p) supset frak(c)$», которая
  очевидна. Остается показать, что если $frak(p) in spec(A)$ и
  $frak(p) supset.not frak(c)$, то $frak(p)$ является ограничением простого
  идеала из $A_2$. Выберем $t in frak(c)$, $t in.not frak(p)$. Тогда элемент $t$
  обратим в $A_frak(p)$. С другой стороны, $t A_2 subset frak(c) subset A$.
  Поэтому $A_frak(p) = (A_2)_frak(p)$. Пусть идеал $frak(q) in spec(A_2)$
  соответствует максимальному идеалу кольца $(A_2)_frak(p)$. Тогда
  $frak(q) inter A = frak(p)$, что и требовалось доказать.

  @cond:milnor-rank-functions-torsion-free-cokernel Так как квадрат
  @eq:milnor-spectrum-pushout кодекартов, то по определению из этого следует,
  что $ContMaps(#[ @eq:milnor-spectrum-pushout], G)$ является декартовым
  квадратом множеств для любого топологического пространства $G$. Если $G$ —
  абелева группа с дискретной топологией, то $ContMaps(
    #[
      @eq:milnor-spectrum-pushout], G
  )$ является диаграммой абелевых групп; при этом, будучи декартовым квадратом
  как диаграмма множеств, квадрат также является декартовым как диаграмма
  абелевых групп. Возьмем $G = ZZ$. Таким образом, приходим к точной
  последовательности @eq:milnor-rank-functions-exact-sequence для функтора
  $H_0$. В силу квазикомпактности пространства $spec(A)$
  $ ContMaps(spec(A), G) = H_0 (A) tensor G $
  #symbol-idx($ContMaps$, sort: "Cont. maps", group: "operators", order: 38)
  для любой дискретной абелевой группы $G$. Таким образом, последовательность
  @eq:milnor-rank-functions-exact-sequence является точной последовательностью
  групп вида #numbered-condition[
    $ 0 -> M_0 -> M_1 arrow.r^h M_2, $
  ] <eq:milnor-rank-pure-sequence>
  причем последовательность $#[ @eq:milnor-rank-functions-exact-sequence]
  tensor G$ остается точной для всех абелевых групп $G$. Возьмем
  $G = ZZ slash n ZZ$. Тогда легко показать, что
  $n M_2 inter Im(h) = n dot Im(h)$. В нашем примере группа $M_2 = H_0 (A')$ без
  кручения. Поэтому из равенства $n M_2 inter Im(h) = n dot Im(h)$ для всех
  $n in ZZ$ следует, что группа $coker(h)$ без кручения. Доказательство
  закончено.
]

#corollary[
  В ситуации предложения @prop:milnor-spectrum-rank-pushout мы получаем
  коммутативную диаграмму с точными строками и столбцами:
  $ #milnor-reduced-determinant-sequences() $
  #source(381)Отображения из средней строки в нижнюю строку являются
  определителями. Обозначение $SK_0 (C) = Ker(det_0 (C))$ было введено ранее для
  коммутативного кольца $C$.
] <cor:milnor-reduced-determinant-sequences>

#proof[
  Если мы заменим $Rk_0$ на $K_0$, то средняя строка превращается в
  $K$-последовательность Майера — Вьеториса декартова квадрата
  @eq:milnor-ring-pullback-square из @prop:milnor-spectrum-rank-pushout. Точная
  последовательность @eq:milnor-rank-functions-exact-sequence из
  @prop:milnor-spectrum-rank-pushout говорит нам о том, что образ связывающего
  гомоморфизма $K_1 (A') -> K_0 (A)$ в последовательности Майера — Вьеториса на
  самом деле лежит в $Rk_0 (A)$, а получающаяся в итоге последовательность с
  $Rk_0$ вместо $K_0$ точна. Нижняя строка является $Pic$-последовательностью
  Майера — Вьеториса. Верхняя строка является ядром гомоморфизма-определителя из
  средней строки в нижнюю. Из точности гомологической последовательности
  получаем, что верхняя строка точна. Это завершает доказательство.
]

#corollary[
  Допустим, что в ситуации предложения @prop:milnor-spectrum-rank-pushout
  отображения $det_0 (A_1)$, $det_0 (A_2)$ и $det_1 (A')$ являются изоморфизмами
  (т. е. что $SK_0 (A_i) = 0 = SK_1 (A')$ ($i = 1, 2$)). Тогда отображение
  $det_0 (A)$ также является изоморфизмом.
] <cor:milnor-determinant-isomorphism>
