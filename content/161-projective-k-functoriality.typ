#import "main-defs.typ": (
  Aut, E, GL, HCat, K, Ker, U, det, moduleCategory, rad, res, source, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, item-record, numbered-condition, proof,
  proposition, theorem,
)
#import "diagrams/projective-k-theory-introduction.typ": (
  projective-quotient-triangle, projective-restriction-square,
)

#heading(level: 2)[Определения и свойства функториальности групп $K_i A$
  $(i = 0, 1)$] <sec:projective-k-functoriality>

Основное внимание в этом параграфе мы уделяем функторам
$ K_i A = K_i bold(P)(A) quad (i = 0, 1). $
Здесь через $A$ обозначено кольцо, а через $bold(P)(A)$ (напоминаем) — категория
конечно порожденных проективных правых $A$-модулей. Можно рассматривать
категорию $bold(P)(A)$ как категорию с произведением $plus.o$ (как в
гл.~@ch:exact-k-sequences) или как допустимую подкатегорию в абелевой категории
$moduleCategory-A$ (как в гл.~@ch:abelian-k-theory). Возникающие в связи с этим
два возможных определения группы $K_i bold(P)(A)$ на самом деле совпадают,
поскольку категория $bold(P)(A)$ полупроста в смысле гл.~@ch:abelian-k-theory,
§~@sec:cofinal-exact-k-sequence, т. е. все короткие точные последовательности
расщепляются. (См. теорему @th:semisimple-exact-k-sequence.)

Кольцевой гомоморфизм $f: A -> B$ индуцирует аддитивный функтор
$bold(P)(f) = (dot tensor_A B): bold(P)(A) -> bold(P)(B)$. Так как свободные
#source(349)модули образуют кофинальную подкатегорию в $bold(P)$ и так как наш
функтор переводит свободные модули в свободные, то мы получаем точную
последовательность (см. @th:cofinal-functor-exact-sequence). Появляющуюся в ней
относительную группу $K'_0 (bold(P)(f))$ мы будем обозначать просто через
$K'_0 (f)$. Сформулируем теперь утверждение о точной последовательности:

#theorem[
  Функторы $K_i$ $(i = 0, 1)$ являются функторами из категории колец в категорию
  абелевых групп. Кольцевой гомоморфизм $f: A -> B$ индуцирует точную
  последовательность
  $ K_1 (A) -> K_1 (B) -> K'_0 (f) -> K_0 (A) -> K_0 (B). $
] <th:ring-k-functor-exact-sequence>

Конечно, эта последовательность естественна (в очевидном смысле) относительно
коммутативных квадратных диаграмм гомоморфизмов колец.

Если $frak(q)$ — идеал кольца $A$ и $f$ — отображение на кольцо
$B = A slash frak(q)$, то иногда мы будем употреблять обозначение
$K_0 (A, frak(q))$ для группы $K'_0 (f)$. Через $K_1 (A, frak(q))$ обозначим
группу $K_1 (bold(P)(A), bold(P)(f))$ (см. гл.~@ch:exact-k-sequences,
§~@sec:cofinal-functors). Напомним, что это группа Уайтхеда, построенная по
парам $(P, alpha)$ из $Sigma bold(P)(A)$ (т. е. $P in bold(P)(A)$ и
$alpha in Aut_A (P)$), для которых
$alpha tensor_A (A slash frak(q)) = 1_(P slash (P frak(q)))$. В этой ситуации
можно усилить теорему @th:ring-k-functor-exact-sequence следующим образом:

#theorem[
  Пусть $frak(q)$ — двусторонний идеал кольца $A$. Тогда имеет место точная
  последовательность #numbered-condition[
    $
      K_1 (A, frak(q)) -> K_1 (A) -> K_1 (A slash frak(q)) ->
      K_0 (A, frak(q)) -> K_0 (A) -> K_0 (A slash frak(q)),
    $
  ] <eq:ideal-k-exact-sequence>
  расширяющая последовательность из теоремы @th:ring-k-functor-exact-sequence.
  При этом трехчленная последовательность с функтором $K_1$ естественно
  изоморфна последовательности
  $
    GL(A, frak(q)) slash E(A, frak(q)) -> GL(A) slash E(A) ->
    GL(A slash frak(q)) slash E(A slash frak(q)).
  $
  Если идеал $frak(q)'$ содержит идеал $frak(q)$, то точна последовательность
  #numbered-condition[
    $
      K_1 (A, frak(q)) -> K_1 (A, frak(q)') ->
      K_1 (A slash frak(q), frak(q)' slash frak(q)) -> K_0 (A, frak(q)) ->
      K_0 (A, frak(q)') -> K_0 (A slash frak(q), frak(q)' slash frak(q)).
    $
  ] <eq:nested-ideal-k-exact-sequence>
] <th:ideal-relative-k-exact-sequences>
#proof[
  Рассмотрим коммутативную треугольную диаграмму функторов
  $ #projective-quotient-triangle() $
  Точная последовательность @eq:ideal-k-exact-sequence получается из утверждения
  @th:cofinal-functor-exact-sequence, а последовательность
  @eq:nested-ideal-k-exact-sequence — из @th:exact-k-functor-triangle-sequence и
  @prop:exact-k-triangle-middle-criterion, как #source(350)только мы проверим
  выполнение условий «Е-сюръективности», входящих в эти теоремы. Начнем с
  проверки условия предложения @prop:exact-k-triangle-middle-criterion. Оно
  требует по $P in bold(P)(A)$ и $alpha in Aut_A (P)$, для которых
  $
    alpha tensor (A slash frak(q)) in
    [Aut_(A slash frak(q)) (P slash (P frak(q))),
      Aut_(A slash frak(q)) (P slash (P frak(q)), frak(q)' slash frak(q))],
  $
  найти $Q = P plus.o P' in bold(P)(A)$ и автоморфизм
  $epsilon in [Aut_A (Q), Aut_A (Q, frak(q)')]$, такие, что
  $epsilon tensor (A slash frak(q)) = (alpha tensor (A slash frak(q))) plus.o
  1_(P' slash (P' frak(q)))$. Здесь $Aut_A (Q, frak(q)) = Ker(
    Aut_A (Q) ->
    Aut_(A slash frak(q)) (Q slash (Q frak(q)))
  )$. Группа
  $Aut_(A slash frak(q)) (P slash (P frak(q)), frak(q)' slash frak(q))$
  определяется аналогично.

  Так как свободные модули в категории $bold(P)$ образуют кофинальную
  подкатегорию, то достаточно это условие проверить для свободных модулей $P$,
  $P'$ и т. д. В этом случае оно означает: для матрицы $alpha in GL_n (A)$,
  образ которой по модулю идеала $frak(q)$ лежит в
  $[GL_n (A slash frak(q)), GL_n (A slash frak(q), frak(q)' slash frak(q))]$,
  можно найти $m >= 0$ и $epsilon in [GL_(n+m) (A), GL_(n+m) (A, frak(q)')]$,
  для которых $epsilon equiv alpha plus.o I_m mod frak(q)$. Переходя к пределу
  по $n$, мы видим, что достаточно доказать сюръективность отображения
  $
    [GL(A), GL(A, frak(q)')] ->
    [GL(A slash frak(q)), GL(A slash frak(q), frak(q)' slash frak(q))].
  $
  В силу @th:stable-linear-normal-subgroups
  $[GL(A), GL(A, frak(q)')] = E(A, frak(q)')$ и отображение
  $E(A, frak(q)') -> E(A slash frak(q), frak(q)' slash frak(q))$
  действительно сюръективно.

  Если $frak(q)' = A$, то приведенные выше рассуждения показывают, что функтор
  $bold(P)(A) -> bold(P)(A slash frak(q))$ является Е-сюръективным. Таким
  образом, все функторы, входящие в треугольник, Е-сюръективны, и поэтому мы
  получаем две точные последовательности.

  Так как свободные модули образуют кофинальную подкатегорию, то из утверждения
  @cor:whitehead-sequential-group-colimit следует, что гомоморфизмы
  $GL_n (A, frak(q)) -> K_1 (A, frak(q))$ индуцируют в пределе (по $n$)
  изоморфизм
  $ GL(A, frak(q)) slash [GL(A), GL(A, frak(q))] -> K_1 (A, frak(q)). $
  Это приводит нас к изоморфизму
  $ GL(A, frak(q)) slash E(A, frak(q)) -> K_1 (A, frak(q)), $
  а в случае когда $frak(q) = A$, — к изоморфизму $GL(A) slash E(A) -> K_1 (A)$.
  Очевидно, что эти изоморфизмы естественны, и, таким образом, мы установили все
  утверждения теоремы.
]

Опишем теперь поведение групп $K_i (A, frak(q))$ в некоторых конкретных
ситуациях.

#proposition[
  Допустим, что $frak(q) subset rad A$. Тогда
  #condition-list(start: 0)[
    #condition-item[Отображение $K_0 (A) -> K_0 (A slash frak(q))$ является
      мономорфизмом, который оказывается изоморфизмом, если кольцо $A$
      $frak(q)$-адически полно. Кроме того, $K_0 (A, frak(q)) = 0$.]
    <cond:k-zero-radical-quotient-injection>
    #condition-item[#source(351)Далее, $GL_1 (A, frak(q)) = 1 + frak(q)$, и
      отображение $GL_1 (A, frak(q)) -> K_1 (A, frak(q))$ является эпиморфизмом,
      который оказывается изоморфизмом, если кольцо $A$ коммутативно. Кроме
      того, отображение $K_1 (A) -> K_1 (A slash frak(q))$ — эпиморфизм.]
    <cond:k-one-radical-quotient-surjection>
  ]
] <prop:k-radical-ideal-comparison>
#proof[
  В силу @prop:projective-reduction-mod-radical функтор
  $bold(P)(A) -> bold(P)(A slash frak(q))$ инъективен на классах изоморфных
  объектов и биективен на них, если кольцо $A$ $frak(q)$-адически полно. Первое
  утверждение непосредственно следует из этого. Так как
  $frak(q) M_n (A) subset rad M_n (A)$ (см. @prop:radical-morita-invariance), то
  матрица над кольцом $A$, обратимая по модулю идеала $frak(q)$, обратима. В
  частности, отображение $GL_n (A) -> GL_n (A slash frak(q))$ сюръективно для
  всех $n$, а включение $GL_1 (A, frak(q)) subset 1 + frak(q)$ является
  равенством. Из первого утверждения в этой ситуации получаем, что отображение
  $K_1 (A) -> K_1 (A slash frak(q))$ сюръективно. Поэтому рассмотрение точной
  последовательности @eq:ideal-k-exact-sequence показывает, что
  $K_0 (A, frak(q)) = 0$. В @th:semilocal-relative-k1 как раз и было показано,
  что отображение
  $GL_1 (A, frak(q)) -> K_1 (A, frak(q)) = GL(A, frak(q)) slash E(A, frak(q))$
  сюръективно. Если кольцо $A$ коммутативно, то отображение перехода к
  определителю $GL(A, frak(q)) -> GL_1 (A, frak(q))$ индуцирует обратное к нему
  отображение.
]

#proposition[
  Предположим, что кольцо $A$ полулокально. Тогда
  #condition-list(start: 0)[
    #condition-item[$K_0 (A)$ — свободная абелева группа конечного ранга.]
    <cond:semilocal-k-zero-free-finite-rank>
    #condition-item[Отображение $K_1 (A) -> K_1 (A slash frak(q))$ сюръективно
      для любого двустороннего идеала $frak(q)$. Кроме того, отображение
      $GL_1 (A, frak(q)) -> K_1 (A, frak(q))$ является эпиморфизмом, который
      оказывается изоморфизмом, если кольцо $A$ коммутативно.]
    <cond:semilocal-k-one-units-surjection>
  ]
] <prop:semilocal-k-groups>
#proof[
  @cond:semilocal-k-zero-free-finite-rank В силу
  @prop:k-radical-ideal-comparison, @cond:k-zero-radical-quotient-injection
  отображение $K_0 (A) -> K_0 (A slash rad A)$ является мономорфизмом. Так как
  кольцо $A slash rad A$ полупросто, то $K_0 (A slash rad A)$ — свободная
  абелева группа, базис которой образуют классы простых модулей. Так как
  подгруппа свободной абелевой группы свободна и ранг ее не превосходит ранга
  всей группы, то это доказывает утверждение
  @cond:semilocal-k-zero-free-finite-rank.

  @cond:semilocal-k-one-units-surjection Если элемент $a in A$ обратим по модулю
  идеала $frak(q)$, то $frak(q) + a A = A$. Поэтому в силу
  @prop:semilocal-unit-in-coset множество $frak(q) + a$ содержит обратимый
  элемент. Таким образом, отображение $U(A) -> U(A slash frak(q))$ сюръективно,
  где $U$ обозначает группу обратимых элементов. Применяя это к алгебрам матриц
  над кольцом $A$, получаем, что отображения
  $GL_n (A) -> GL_n (A slash frak(q))$ сюръективны для всех $n$. Поэтому
  отображение $K_1 (A) -> K_1 (A slash frak(q))$ также сюръективно. В силу
  @th:semilocal-relative-k1 имеем
  $GL_n (A, frak(q)) = GL_1 (A, frak(q)) E_n (A, frak(q))$ для всех $n$. Значит,
  отображение $GL_1 (A, frak(q)) -> K_1 (A, frak(q))$ является эпиморфизмом.
  Если кольцо $A$ коммутативно, то отображение
  $det: K_1 (A, frak(q)) -> GL_1 (A, frak(q))$ является обратным к нему.
]

#source(352)
#proposition[
  Пусть $frak(q)_1$ и $frak(q)_2$ — двусторонние идеалы кольца $A$, для которых
  $frak(q)_1 inter frak(q)_2 = 0$. Тогда
  $
    K_1 (A, frak(q)_1 + frak(q)_2) =
    K_1 (A, frak(q)_1) plus.o K_1 (A, frak(q)_2)
  $
  и отображение
  $K_1 (A, frak(q)_1) ->
  K_1 (A slash frak(q)_2, (frak(q)_1 + frak(q)_2) slash frak(q)_2)$
  является изоморфизмом.
] <prop:disjoint-ideal-relative-k-decomposition>
#proof[
  Так как $frak(q)_1 inter frak(q)_2 = 0$, то
  $frak(q)_1 frak(q)_2 = 0 = frak(q)_2 frak(q)_1$. Поэтому
  $GL(A, frak(q)_1 + frak(q)_2) = GL(A, frak(q)_1) times GL(A, frak(q)_2)$
  (прямое произведение). Аналогичное разложение имеет место для группы
  $E(A, frak(q)_1 + frak(q)_2)$, поскольку прямое произведение
  $E(A, frak(q)_1) times E(A, frak(q)_2)$ является нормальным делителем в группе
  $GL(A)$ и содержит все $(frak(q)_1 + frak(q)_2)$-элементарные матрицы. Так как
  $K_1 (A, frak(q)_1 + frak(q)_2) =
  GL(A, frak(q)_1 + frak(q)_2) slash E(A, frak(q)_1 + frak(q)_2)$, то теперь оба
  утверждения предложения очевидны.
]

Иногда группы $K_i$ ведут себя как контравариантные функторы. Например, если
отображение $f: A -> B$ превращает $B$ в конечно порожденный проективный правый
$A$-модуль, то ограничение скаляров из категории $moduleCategory-B$ в категорию
$moduleCategory-A$ индуцирует функтор $res: bold(P)(B) -> bold(P)(A)$.
Рассмотрим более общую ситуацию.

Пусть $HCat(A)$ — категория модулей с конечными $bold(P)(A)$-резольвентами (см.
гл.~@ch:rings-modules, §~@sec:homological-dimension). В силу
@th:projective-resolution-k-isomorphisms вложение $bold(P)(A) subset HCat(A)$
индуцирует изоморфизм #item-record[
  $ K_i (A) = K_i (bold(P)(A)) arrow.r^tilde K_i (HCat(A)) quad (i = 0, 1). $
] <ss:projective-resolution-k-isomorphism>
Предположим теперь, что в рассмотренной выше ситуации $B in HCat(A)$ как правый
$A$-модуль. Тогда из @cor:resolvable-subcategories следует, что ограничение
скаляров индуцирует функтор $res: HCat(B) -> HCat(A)$. Следовательно, можно
определить отображение $res: K_i (B) -> K_i (A)$, для которого диаграмма
#item-record[$ #projective-restriction-square() $] <ss:projective-k-restriction>
коммутативна.

Пусть $R$ — коммутативное кольцо, $A$ и $B$ — $R$-алгебры. Тогда $tensor_R$
определяет аддитивный бифунктор
$ tensor_R: bold(P)(A) times bold(P)(B) -> bold(P)(A tensor_R B). $
С его помощью можно превратить $K_0 (R)$ в коммутативное кольцо (при этом
$A = R = B$). Далее можно превратить $K_0 (A)$ и $K_1 (A)$ в $K_0 (R)$-модули.
Кроме того, мы получаем спаривания
$
  K_i (A) times K_j (B) -> K_(i+j) (A tensor_R B)
  quad (i = 0, j = 0 "или" j = 1),
$
являющиеся $K_0 (R)$-билинейными отображениями.

#source(353)Для иллюстрации этих структур предположим, что $P in bold(P)(R)$,
$Q in bold(P)(A)$ и $alpha in Aut_A (Q)$. Тогда
$ [P]_R [Q]_A = [P tensor_R Q]_A in K_0 (A), $
$ [P]_R [Q; alpha]_A = [P tensor_R Q, 1_P tensor alpha]_A in K_1 (A). $
Аналогично если $frak(q)$ — двусторонний $A$-идеал и
$alpha in Aut_A (Q, frak(q))$, то группа $K_1 (A, frak(q))$ превращается в
$K_0 (R)$-модуль. Если $f: A -> B$ — гомоморфизм $R$-алгебр, то $K'_0 (f)$
превращается в $K_0 (R)$-модуль при $[P]_R [Q_1, alpha, Q_2]' =
[P tensor_R Q_1, 1_P tensor_R alpha, P tensor_R Q_2]'$, где $Q_i in bold(P)(A)$
и $alpha: Q_1 tensor_A B -> Q_2 tensor_A B$ — изоморфизм. Кроме того, точная
последовательность @th:ring-k-functor-exact-sequence (или
@th:ideal-relative-k-exact-sequences) является точной последовательностью
$K_0 (R)$-модулей. Гомоморфизмы ограничения @ss:projective-k-restriction также
являются $K_0 (R)$-линейными отображениями (если они определены).

Пусть $R -> S$ — гомоморфизм коммутативных колец. Тогда функтор
$tensor_R S: bold(P)(A) -> bold(P)(A tensor_R S)$ естественно изоморфен функтору
$tensor_A (A tensor_R S)$. Если $S$ — конечно порожденный проективный
$R$-модуль, то мы получаем гомоморфизм ограничения
$res: K_i (A tensor_R S) -> K_i (A)$. Следующее предложение очевидно:

#proposition[
  Пусть $A$ и $S$ — $R$-алгебры, при этом алгебра $S$ коммутативна и является
  конечно порожденным проективным $R$-модулем. Тогда композиция отображений
  $ K_i (A) -> K_i (A tensor_R S) arrow.r^res K_i (A) $
  совпадает с умножением на элемент $[S]_R in K_0 (R)$. Следовательно,
  $Ker(K_i (A) -> K_i (A tensor_R S))$ является $K_0 (R)$-модулем, аннулируемым
  элементом $[S]_R$.
] <prop:projective-k-transfer-scalar-multiplication>
