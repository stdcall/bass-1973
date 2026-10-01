#import "main-defs.typ": (
  Aut, E, FP, GL, H, K, Ker, PGL, Pic, PicCat, Rk, SK, U, det, directLim,
  moduleCategory, ob, rad, rk, source, spec, supp, symbol-idx, systemLimit,
  tensor,
)
#import "statements.typ": (
  condition-item, condition-list, lemma, numbered-condition, proof, proposition,
  theorem,
)
#import "diagrams/projective-k-theory-fp.typ": (
  fp-exponential-isomorphism, fp-transition-square,
)

== Приложение: категория $FP$ <sec:finite-projective-resolutions-k-theory>

#source(393)Зафиксируем коммутативное кольцо $A$. Объектами категории
$FP = FP(A)$ являются строго проективные $A$-модули, а ее морфизмами —
$A$-изоморфизмы этих модулей.#symbol-idx(
  $FP$,
  sort: "FP",
  group: "categories",
  order: 6,
) В $FP$ мы рассматриваем $tensor_A$ в качестве произведения (в смысле
гл.~@ch:exact-k-sequences). Заметим, что вложение
$ PicCat(A) subset FP(A) $
является сохраняющим произведение функтором (хотя и некофинальным). В силу
@prop:strict-projective-free-tensor-complement модуль $P in moduleCategory-A$
принадлежит категории $FP$ тогда и только тогда, когда
$P tensor_A Q tilde.eq A^n$ для некоторого $Q in moduleCategory-A$ и некоторого
$n > 0$. В частности, из этого факта следует, что свободные модули кофинальны в
категории $FP$. Отсюда также следует, что гомоморфизм $A -> B$ коммутативных
колец индуцирует кофинальный функтор $tensor_A B: FP(A) -> FP(B)$, сохраняющий
произведение.

Цель этого параграфа — вычислить группы $K_i FP$ в терминах групп $K_i bold(P)$.

Напомним, что имеет место (расщепляющаяся) точная последовательность
$ 0 -> Rk_0 (A) -> K_0 (A) arrow.r^rk H_0 (A) -> 0, $
которая индуцирует последовательность
$
  0 -> QQ tensor Rk_0 (A) -> QQ tensor K_0 (A) arrow.r^rk QQ tensor H_0 (A) ->
  0,
$
где все тензорные произведения берутся над кольцом $ZZ$. Напомним, что $H_0 (A)$
(т. е. кольцо всех непрерывных функций из $spec(A)$ в $ZZ$) порождается
аддитивно характеристическими функциями подмножеств $supp(e A)$, где
$e = e^2 in A$. (Это следует из квазикомпактности.) Таким образом, можно
отождествить $QQ tensor H_0 (A)$ с кольцом непрерывных функций из $spec(A)$ в
$QQ$. Тогда можно определить
$ U^+ (QQ tensor K_0 (A)) $
как множество элементов $x in QQ tensor K_0 (A)$, для которых $rk(x)$ принимает
лишь строго положительные значения. Обозначая через $U^+ (QQ tensor H_0 (A))$
множество функций из $spec(A)$ в положительные рациональные числа, мы видим, что
$U^+ (QQ tensor H_0 (A))$ является подгруппой группы единиц кольца
$QQ tensor H_0 (A)$. Так как $Rk_0 (A)$ — нильидеал (см.
@prop:strict-projective-free-tensor-complement), то $QQ tensor Rk_0 (A)$ также
является нильидеалом и, следовательно, лежит в $rad(QQ tensor K_0 (A))$. Таким
образом, элемент из $QQ tensor K_0 (A)$ обратим тогда и только тогда, #source(
  394,
)когда обратим его ранг. Следовательно, получаем расщепляющуюся точную
последовательность групп (единиц): #numbered-condition[
  $
    0 -> 1 + (QQ tensor Rk_0 (A)) -> U^+ (QQ tensor K_0 (A)) arrow.r^rk U^+ (QQ
      tensor H_0 (A)) -> 0.
  $
] <eq:fp-positive-unit-exact-sequence>
Если $x in QQ tensor Rk_0 (A)$, то элемент $x$ нильпотентен; поэтому можно
рассмотреть многочлены
$
  exp(x) = sum_(n >= 0) x^n slash n!, quad log(1 + x) = -sum_(n > 0) (-x)^n
  slash n.
$
Они осуществляют взаимно обратные изоморфизмы групп:
#numbered-condition[$ #fp-exponential-isomorphism() $]
<eq:fp-exponential-isomorphism>
Соединяя @eq:fp-positive-unit-exact-sequence и @eq:fp-exponential-isomorphism,
получаем #numbered-condition[
  $
    U^+ (QQ tensor K_0 (A)) tilde.eq U^+ (QQ tensor H_0 (A)) plus.o (QQ tensor
      Rk_0 (A)).
  $
] <eq:fp-positive-unit-decomposition>
Наш интерес к этому изоморфизму объясняется следующим утверждением:

#theorem[
  Отображение $P |-> 1 tensor [P]_(bold(P))$ из $ob FP(A)$ в $QQ tensor K_0 (A)$
  индуцирует изоморфизм
  $ K_0 FP(A) tilde.eq U^+ (QQ tensor K_0 (A)). $
] <th:strict-projective-category-k0>
#proof[
  Если $P in FP$, то функция $[P: A]$ всюду положительна (в силу
  @prop:strict-projective-free-tensor-complement). Поэтому
  $h P = 1 tensor [P]_(bold(P)) in U^+ (QQ tensor K_0 (A))$. Очевидно, что
  $h(P tensor_A Q) = h(P) h(Q)$ для $P, Q in FP$. Поэтому $h$ индуцирует
  гомоморфизм
  $ h: K_0 FP(A) -> U^+ (QQ tensor K_0 (A)). $
  Предположим, что $[P]_(FP) - [Q]_(FP) in Ker(h)$, т. е. что
  $1 tensor [P]_(bold(P)) = 1 tensor [Q]_(bold(P))$. Тогда порядок элемента
  $[P]_(bold(P)) - [Q]_(bold(P))$ конечен в аддитивной группе $K_0 (A)$. Пусть
  $n [P]_(bold(P)) = n [Q]_(bold(P))$ для некоторого $n > 0$. Это означает, что
  модули $A^n tensor_A P$ и $A^n tensor_A Q$ стабильно изоморфны. Умножая $n$ на
  достаточно большой множитель, если это необходимо, можно считать (см.
  @prop:k0-multiple-stability), что $A^n tensor P tilde.eq A^n tensor Q$. Но
  тогда $[P]_(FP) = [Q]_(FP)$. Таким образом, отображение $h$ инъективно.

  Наконец, предположим, что $1 slash n tensor x in U^+ (QQ tensor K_0 (A))$, где
  $n > 0$ и $x in K_0 (A)$. Тогда функция $rk(x)$ всюду положительна на
  $spec(A)$. Поэтому из @prop:k0-multiple-stability следует, что существует
  $m > 0$, #source(395)для которого $m x = [P]_(bold(P))$ для некоторого
  $P in bold(P)$. Так как функция $[P: A]$ всюду положительна, то $P in FP$.
  Таким образом,
  $
    1 slash n tensor x = 1 slash (n m) tensor m x = (1 tensor n m)^(-1) (1
      tensor [P]_(bold(P))) = h(A^(n m))^(-1) h(P).
  $
  Это показывает, что отображение $h$ сюръективно, что и завершает
  доказательство.
]

Для того чтобы вычислить группу $K_1 FP$, нам потребуется лемма о прямых
пределах.

Пусть $L = (W_n; f_(n, n m): W_n -> W_(n m))$ $(n, m in NN)$ — направленная
система абелевых групп, занумерованная натуральными числами, упорядоченными по
делимости. Тогда определим новую направленную систему
$
  L' = (W_n; f'_(n, n m): W_n -> W_(n m)), quad "где" f'_(n, n m) = m f_(n, n
  m),
$
и морфизм $(n 1_(W_n))_(n in NN): L -> L'$ направленных систем. Легко
проверяются нужные условия коммутативности:
$ #fp-transition-square() $
$L'$ является функтором от $L$, а $L -> L'$ — естественное преобразование,
коядро которого мы обозначим через $L'' = (W_n slash (n W_n); f'_(n, n m))$, так
что получаем точную последовательность
$ L -> L' -> L'' -> 0. $

#lemma[
  Пусть $L$ — приведенная выше направленная система. Тогда последовательности
  $ systemLimit(L) -> systemLimit(L') -> systemLimit(L'') -> 0 $
  и
  $ systemLimit(L) tensor (ZZ -> QQ -> QQ slash ZZ -> 0) $
  естественно изоморфны.
] <lem:scaled-transition-system-rationalization>
#proof[
  Пусть $E = (ZZ_n; e_(n, n m))$ — система, состоящая из $ZZ_n = ZZ$ и
  $e_(n, n m) = 1_(ZZ)$ для всех $n, m in NN$. Очевидно, что точные
  последовательности направленных систем
  $ L -> L' -> L'' -> 0 $
  #source(396)и
  $ L tensor (E -> E' -> E'' -> 0) $
  изоморфны. (Здесь
  $L tensor E = (W_n tensor ZZ_n; f_(n, n m) tensor e_(n, n m))$ и т. д.) Так
  как $L |-> systemLimit(L)$ — точный функтор, то утверждение леммы будет
  доказано, как только мы покажем, что отображения
  $systemLimit(E) -> systemLimit(E')$ и $ZZ -> QQ$ естественно изоморфны.
  Поскольку все $e_(n, n m)$ являются изоморфизмами, то $systemLimit(E) = ZZ$.
  Кроме того, отображение $systemLimit(E') -> QQ tensor systemLimit(E')$
  является мономорфизмом, а мономорфизмы в системе $QQ tensor E'$ являются
  изоморфизмами. Поэтому $systemLimit((QQ tensor E')) = QQ$. Однако очевидно,
  что группа $systemLimit(E')$ делимая. Поэтому $systemLimit(E') = QQ$, что и
  требовалось доказать.
]

Так как свободные модули кофинальны в категории $FP(A)$, то из
@cor:whitehead-sequential-group-colimit следует, что можно вычислить группу
$K_1 FP(A)$ как прямой предел факторгрупп по коммутанту $W_n$ групп
$Aut_A (A^n) = GL_n (A)$, т. е. групп
$ W_n = GL_n (A) slash [GL_n (A), GL_n (A)]. $
Конечно, предел берется по гомоморфизмам
$ g_(n, n m): W_n -> W_(n m), $
индуцированным отображениями
$
  alpha |-> alpha tensor I_m = mat(alpha, , 0; , dots.down, ; 0, , alpha) quad
  (alpha in GL_n (A)).
$
Рассмотрим также гомоморфизм
$ f_(n, n m): W_n -> W_(n m), $
индуцированный отображением
$
  alpha |-> alpha plus.o I_(n(m-1)) = mat(
    alpha, , , 0; , I_n, , ; , ,
    dots.down, ; 0, , , I_n
  ).
$
В силу леммы Уайтхеда @prop:whitehead-lemma
$
  mat(alpha, , 0; , dots.down, ; 0, , alpha) equiv mat(
    alpha^m, , , 0; , I_n, ,
    ; , , dots.down, ; 0, , , I_n
  ) quad mod E_(n m) (A).
$
#source(397)Из теоремы @cor:relative-elementary-commutators получаем, что
$E_n (A) subset [GL_n (A), GL_n (A)]$ для $n >= 3$. Если $n, m > 1$, то
$n m > 3$ и поэтому $g_(n, n m) = m f_(n, n m)$, т. е.
$g_(n, n m) = f'_(n, n m)$ (в обозначениях леммы
@lem:scaled-transition-system-rationalization). Так как
$directLim(n) (W_n; f_(n, n m)) = K_1 (A)$, то из леммы
@lem:scaled-transition-system-rationalization вытекает

#theorem[
  Существует естественный изоморфизм
  $
    K_1 FP(A) tilde.eq QQ tensor K_1 (A) tilde.eq (QQ tensor U(A)) plus.o (QQ
      tensor SK_1 (A)).
  $
] <th:strict-projective-category-k1>

Можно даже перейти к пределу:
$
  GL^tensor (A) = directLim(n) (GL_n (A); alpha |-> alpha tensor I_m) quad (n, m
    in NN).
$
В силу @cor:whitehead-sequential-group-colimit
$ K_1 FP(A) = GL^tensor (A) slash [GL^tensor (A), GL^tensor (A)]. $
Элементы группы $GL^tensor (A)$ можно представлять себе как бесконечные матрицы
вида #numbered-condition[
  $
    overline(alpha) = mat(
      alpha, , , , 0; , alpha, , , ; , , dots.down, , ; , ,
      , alpha, ; 0, , , , dots.down
    ) quad (alpha in GL_n (A) "для некоторого" n >
      0).
  $
] <eq:tensor-stable-infinite-matrix>
Пусть $det(overline(alpha)) = 1 slash n tensor det(alpha) in QQ tensor U(A)$.
Тогда легко видеть, что это определение не зависит от выбора представителя
$alpha$ элемента $overline(alpha)$ (отметим, например, что
$overline((alpha tensor I_m)) = overline(alpha)$ для всех $m > 0$). Получающийся
гомоморфизм
$ det: GL^tensor (A) -> QQ tensor U(A) $
в точности совпадает с проекцией на первое слагаемое в разложении из теоремы
@th:strict-projective-category-k1.

Вложение $PicCat(A) subset FP(A)$ индуцирует гомоморфизмы #numbered-condition[$
  Pic(A) -> K_0 FP(A)
$] <eq:picard-to-strict-projective-k0>
и #numbered-condition[$ U(A) -> K_1 FP(A). $] <eq:units-to-strict-projective-k1>

#proposition[
  #condition-list(start: 0)[
    #condition-item[Ядро отображения @eq:picard-to-strict-projective-k0 является
      периодической подгруппой группы $Pic(A)$, а его образ лежит в подгруппе,
      соответствующей $QQ tensor Rk_0 (A)$ (см.
      @th:strict-projective-category-k0).]
    <cond:strict-projective-picard-torsion-kernel>
    #condition-item[Ядро отображения @eq:units-to-strict-projective-k1 является
      периодической подгруппой группы $U(A)$, а его образ соответствует
      подгруппе $1 tensor U(A) subset QQ tensor U(A)$ из теоремы
      @th:strict-projective-category-k1. Таким образом, #source(398)коядро
      отображения @eq:units-to-strict-projective-k1 равно
      $ (QQ slash ZZ tensor U(A)) plus.o (QQ tensor SK_1 (A)). $]
    <cond:strict-projective-units-torsion-kernel>
  ]
] <prop:picard-units-strict-projective-k-kernels>
#proof[
  @cond:strict-projective-picard-torsion-kernel Если $P in PicCat(A)$, то
  $[P: A] = 1$. Поэтому $[P]_(bold(P)) in 1 + Rk_0 (A)$. Последнее утверждение
  следует из этого замечания, поскольку $QQ tensor Rk_0 (A)$ соответствует
  подгруппе $1 + (QQ tensor Rk_0 (A)) subset U^+ (QQ tensor K_0 (A))$ из
  @th:strict-projective-category-k0.

  Если $[P]_(FP) = [A]_(FP)$, то $P tensor_A Q tilde.eq A tensor_A Q$ для
  некоторого $Q in FP$. Можно даже считать, что $Q = A^n$ для некоторого
  $n > 0$, поскольку свободные модули кофинальны. Тогда $P^n tilde.eq A^n$.
  Поэтому $A = Lambda^n (A^n) tilde.eq Lambda^n (P^n) tilde.eq P^n$.
  Следовательно, порядок элемента $[P]_(Pic)$ делит $n$.

  Обратно, предположим, что порядок элемента $[P]_(Pic)$ конечен и равен
  $n > 0$. Тогда $P^n tilde.eq A$. Положим
  $Q = A plus.o P plus.o P^2 plus.o dots.c plus.o P^(n-1)$. Очевидно, что
  $P tensor_A Q tilde.eq Q tilde.eq A tensor_A Q$ и $Q in FP$. Следовательно,
  $[P]_(FP) = [A]_(FP)$, что и требовалось доказать.

  @cond:strict-projective-units-torsion-kernel Если $u in U(A) = GL_1 (A)$, то
  $
    overline(u) = mat(u, , , 0; , u, , ; , , dots.down, ; 0, , , dots.down) in
    GL^tensor (A)
  $
  и гомоморфизм @eq:units-to-strict-projective-k1 $U(A) -> K_1 FP(A)$
  индуцируется вложением $U(A) subset GL^tensor (A)$. На самом деле мы видим,
  что это позволяет отождествить группу $U(A)$ с центром группы $GL^tensor (A)$.
  Так как разложение $K_1 (A) = U(A) plus.o SK_1 (A)$ индуцировано расщеплением
  $U(A) = GL_1 (A) subset GL_n (A) arrow.r^det U(A)$, то в силу способа
  построения изоморфизма в теореме @th:strict-projective-category-k1 получаем,
  что отображение @eq:units-to-strict-projective-k1 соответствует отображению
  $
    U(A) -> (QQ tensor U(A)) plus.o (QQ tensor SK_1 (A)), quad u |-> (1 tensor
      u) = det(overline(u)).
  $
  Утверждение @cond:strict-projective-units-torsion-kernel уже немедленно
  следует отсюда. Тем самым предложение доказано.
]

Если положить
$ PGL(A) = GL^tensor (A) slash U(A) = directLim(n) (PGL_n (A), h_(n, n m)), $
#symbol-idx($PGL$, sort: "PGL", group: "groups", order: 115)
где $PGL_n (A) = GL_n (A) slash ("скаляры")$ и $h_(n, n m)$ индуцированы
отображением $alpha |-> alpha tensor I_m$ $(alpha in GL_n (A))$, то из
предложения @prop:picard-units-strict-projective-k-kernels
@cond:strict-projective-units-torsion-kernel #source(399)получаем, что
$
  PGL(A) slash [PGL(A), PGL(A)] tilde.eq (QQ slash ZZ tensor U(A)) plus.o (QQ
    tensor SK_1 (A)),
$
где проекция на первое слагаемое совпадает с отображением, индуцированным
определителем (на группе $GL^tensor (A)$).
