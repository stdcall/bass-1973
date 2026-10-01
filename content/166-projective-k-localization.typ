#import "main-defs.typ": (
  Coker, End, G, GL, HCat, Ht, Im, K, Ker, Pic, Rk, SK, U, ann, det, divisor,
  idx, maxSpec, moduleCategory, rank, rk, source, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, numbered-condition, proof,
  proposition, theorem,
)
#import "diagrams/projective-k-theory-localization.typ": (
  localization-cartan-sequences, localization-dedekind-determinant-diagram,
  localization-dedekind-kernel-sequence, localization-determinant-square,
  localization-devissage-sequence, localization-divisor-sequence,
  localization-divisor-square, localization-injective-square,
  localization-picard-identification, localization-picard-sequences,
  localization-regular-sequence,
)

== Точная последовательность функтора локализации
<sec:projective-k-localization>

В этом параграфе зафиксируем коммутативное кольцо $R$ и мультипликативную
систему $S$ в $R$. Если $A$ является $R$-алгеброй, то получаем локализацию
$ S^(-1): moduleCategory(A) -> moduleCategory(S^(-1)A). $
С точностью до эквивалентности можно рассматривать локализацию как функтор
факторизации в смысле гл.~@ch:abelian-k-theory, §~@sec:quotient-categories (см.
пример @exm:module-serre-localization). Следовательно, можно применить
результаты из гл.~@ch:abelian-k-theory, §~@sec:quotient-categories. Это и
является целью данного параграфа.

Начнем с изучения функторов $G_i$. Поэтому допустим сначала, что кольцо $A$
_нётерово справа_. Тогда можно рассмотреть #numbered-condition[
  $ bold(M)_S (A) subset bold(M)(A) arrow.r^(S^(-1)) bold(M)(S^(-1)A) $
] <eq:g-localization-categories>
как факторфунктор, где $bold(M)_S (A)$ — полная подкатегория $S$-периодических
модулей $M$ (т.~е. $S^(-1)M = 0$). Кроме того, положим
$ G_i (A, S) = K_i bold(M)_S (A) quad (i = 0, 1). $
В частном случае, когда $S = {t^n | n >= 0}$ состоит из степеней одного
элемента, получаем, что $bold(M)(A slash t A) subset bold(M)_S (A)$ (как
подкатегория модулей, аннулируемых элементом $t$). Если $M in bold(M)_S (A)$, то
$M t^n = 0$ для некоторого $n$. Поэтому
$ 0 = M t^n subset M t^(n-1) subset dots subset M t^0 = M $
#source(382)является конечной характеристической фильтрацией с факторами из
$bold(M)(A slash t A)$. Таким образом, из @th:devissage-k-isomorphisms следует,
что
$ G_i (A, {t^n}) approx G_i (A slash t A) quad (i = 0, 1). $
В следующем предложении суммированы некоторые из результатов
@prop:exact-k-triangle-middle-criterion.

#proposition[
  Последовательность
  $ G_0 (A, S) -> G_0 (A) -> G_0 (S^(-1)A) -> 0, $
  индуцированная диаграммой @eq:g-localization-categories, является точной.
  Кроме того, существует единственный гомоморфизм
  $partial:G_1 (S^(-1)A) -> G_0 (A, S)$, для которого
  $partial[S^(-1)M, S^(-1)alpha] = [Coker alpha] - [Ker alpha]$, где
  $M in bold(M)(A)$ и $alpha in End_A (M)$ таковы, что $S^(-1)alpha$ является
  автоморфизмом.
] <prop:g-localization-boundary>

#theorem(title: [Хеллер, Райнер @bib:Heller1964])[
  Пусть, как и выше, $A$ — нётерова справа $R$-алгебра. Допустим, что существует
  нильпотентный идеал $J subset S^(-1)A$, для которого $B = (S^(-1)A) slash J$
  является регулярным справа кольцом. (Например, это так, если $S^(-1)A$ —
  артиново справа кольцо.) Тогда последовательность
  $ G_1 (S^(-1)A) arrow.r^partial G_0 (A, S) -> G_0 (A) -> G_0 (S^(-1)A) -> 0 $
  точна.
] <th:g-localization-exact-sequence>
#idx("теорема Хеллера — Райнера")

#proof[
  Начнем с замечания о том, что можно поднимать конечные фильтрации и
  резольвенты с помощью функтора
  $ S^(-1):bold(M)(A) -> bold(M)(S^(-1)A). $
  Именно:
  #condition-list[
    #condition-item(format: "(1°)")[Если $M in bold(M)(A)$ и
      $0 = N_0 subset N_1 subset dots subset N_n = S^(-1)M$ — конечная
      фильтрация в $bold(M)(S^(-1)A)$, то она является локализацией фильтрации
      $0 = M_0 subset M_1 subset dots subset M_n = M$ из $bold(M)(A)$.]
    <cond:g-localization-filtration-lifting>
    #condition-item(format: "(1°)")[Если
      $0 -> N_n -> dots -> N_0 -> S^(-1)M -> 0$ — точная последовательность в
      категории $bold(M)(S^(-1)A)$, то она является (с точностью до изоморфизма)
      локализацией точной последовательности
      $ 0 -> M_n -> dots -> M_0 -> M -> 0 quad "из" bold(M)(A). $]
    <cond:g-localization-resolution-lifting>
  ]
  Эти утверждения вытекают из @prop:localization-hom-finite-presentation.

  Рассмотрим теперь подкатегории
  $ C'_0 = bold(P)(B) subset C' = bold(M)(B) subset bold(M)(S^(-1)A), $
  где второе включение является отождествлением $B$-модулей с
  $S^(-1)A$-модулями, аннулируемыми идеалом $J$. Далее введем
  $ C_0 subset C subset bold(M)(A), $
  #source(383)где $C$ (соответственно $C_0$) — полная подкатегория, объектами
  которой являются те $M$, для которых $S^(-1)M in C'$ (соответственно
  $S^(-1)M in C'_0$). Если $N in bold(M)(S^(-1)A)$, то
  $N supset N J supset N J^2 supset dots$ является конечной характеристической
  $C'$-фильтрацией, поскольку идеал $J$ нильпотентен.

  Из приведенного утверждения @cond:g-localization-filtration-lifting следует,
  что каждый объект категории $bold(M)(A)$ обладает конечной $C$-фильтрацией.
  Таким образом, можно применить @th:devissage-k-isomorphisms и показать, что
  вертикальные отображения в коммутативной диаграмме
  $ #localization-devissage-sequence() $
  являются изоморфизмами. Следовательно, достаточно показать, что нижняя строка
  точна в члене $G_0 (A, S)$ (точность в других членах обеспечивается
  предложением @prop:g-localization-boundary).

  Предположение о регулярности кольца $B$ означает, что каждый объект категории
  $C' = bold(M)(B)$ обладает конечной резольвентой из объектов категории
  $C'_0 = bold(P)(B)$. Свойство @cond:g-localization-resolution-lifting
  позволяет нам далее считать, что каждый объект категории $C$ обладает конечной
  $C_0$-резольвентой. Таким образом, можно применить
  @th:grothendieck-resolution-k0 и @th:projective-resolution-k-isomorphisms и
  показать, что вертикальные отображения в коммутативной диаграмме
  $ #localization-devissage-sequence(resolution: true) $
  являются изоморфизмами. Таким образом, мы свели задачу к доказательству
  точности нижней строки. Но это уже вытекает из
  @prop:exact-k-triangle-middle-criterion, поскольку категория
  $C'_0 = bold(P)(B)$ полупроста. Этим завершается доказательство.
]

_Теперь при рассмотрении функторов $K_i$ мы уже более не предполагаем, что
кольцо $A$ нётерово справа._ Используем обозначения #numbered-condition[
  $ HCat_S (A) subset HCat(A) arrow.r^(S^(-1)) HCat(S^(-1)A), $
] <eq:k-localization-categories>
где $HCat_S (A)$ — полная подкатегория, объектами которой являются
$S$-периодические модули категории $HCat(A)$ (см. гл.~@ch:rings-modules,
§~@sec:homological-dimension). Кроме того, положим
$ K_i (A, S) = K_i HCat_S (A) quad (i = 0, 1). $

#theorem[
  Пусть $A$ является $R$-алгеброй, на которой умножение на любой элемент
  $s in S$ является инъективным отображением. Тогда существует единственный
  гомоморфизм $partial:K_1 (S^(-1)A) -> K_0 (A, S)$, для которого
  $partial[S^(-1)P, S^(-1)alpha] = [Coker(alpha)]$, #source(384)как только
  $P in bold(P)(A)$ и $alpha in End_A (P)$ таковы, что $S^(-1)alpha$ является
  автоморфизмом. Последовательность
  $
    K_1 (A) -> K_1 (S^(-1)A) arrow.r^partial K_0 (A, S) -> K_0 (A) -> K_0
    (S^(-1)A),
  $
  получающаяся в результате из @eq:k-localization-categories, точна.
] <th:k-localization-boundary>

#proof[
  Утверждения этой теоремы непосредственно следуют из теоремы
  @th:projective-localization-exact-sequence. Поэтому нам надо лишь проверить
  выполнение трех предположений этой теоремы. Справедливость первого очевидна.
  Второе гласит: если морфизм $f:P -> Q$ категории $bold(P)(A)$ таков, что
  $S^(-1)f$ — мономорфизм, то $f$ — также мономорфизм. Выполнение этого условия
  вытекает из коммутативной диаграммы
  $ #localization-injective-square() $
  и замечания о том, что $h_P$ — мономорфизм. Последнее условие на отображение
  $h_P$ в свою очередь следует из проективности модуля $P$, поскольку элементы
  $s in S$ не являются делителями нуля кольца $A$. Третье предположение из
  @th:projective-localization-exact-sequence требует, чтобы выполнялось
  следующее условие: если $Q subset P in bold(P)(A)$ и $S^(-1)(P slash Q) = 0$,
  то существует $P' subset Q$, для которого $P' in bold(P)(A)$ и
  $S^(-1)(P slash P') = 0$. Так как модуль $P$ конечно порожден, то существует
  элемент $s in S$, для которого $(P slash Q)s = 0$. Таким образом, модуль
  $P' = P s approx P$ подходит для наших целей. Это завершает доказательство.
]

Если кольцо $A$ к тому же нётерово справа, то в ситуации теоремы
@th:k-localization-boundary мы получаем «гомоморфизмы Картана» между двумя
последовательностями:
$ #localization-cartan-sequences() $
Если кольцо $A$ регулярно справа, то регулярно справа и кольцо $S^(-1)A$, а
вертикальные отображения являются изоморфизмами. Таким образом, в этом случае мы
можем срастить две последовательности.

#corollary[
  В ситуации теоремы @th:k-localization-boundary будем предполагать, что кольцо
  $A$ регулярно справа. Тогда существует изоморфизм точных последовательностей:
  #source(385)$ #localization-cartan-sequences(complete: true) $
] <cor:regular-localization-cartan-sequences>

Было бы интересно суметь продолжить приведенную последовательность до группы
$K_1 (A, S)$ слева. Сейчас мы можем осуществить это лишь в некоторых частных
случаях; затем мы проделаем это в общем случае, используя весьма тонкую технику
(см. главу @ch:reciprocity-finiteness).

Пусть $A$ — нётерова справа $R$-алгебра. Напомним (см. гл.~@ch:rings-modules,
§~@sec:homological-dimension), что система $S$ называется _регулярной
относительно $A$_, если включение $HCat_S (A) subset bold(M)_S (A)$ является
равенством, другими словами, если гомологическая размерность каждого конечно
порожденного правого $A$-модуля $M$, для которого $S^(-1)M = 0$, конечна.
Очевидно, в этом случае
$ K_i (A, S) = G_i (A, S) quad (i = 0, 1). $
Кроме того, из @th:localization-finite-resolution-sequence мы непосредственно
получаем следующее утверждение.

#theorem[
  Пусть $A$ — нётерова справа алгебра. Допустим, что система $S$ регулярна
  относительно $A$ и что умножение на каждый элемент $s in S$ задает на кольце
  $A$ инъективное отображение. Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[Если $M in bold(M)(A)$, то
      $[M in HCat(A)] <=> [S^(-1)M in HCat(S^(-1)A)]$.]
    <cond:regular-localization-finite-resolution>
    #condition-item(format: "cyrillic")[Точна последовательность
      $ #localization-regular-sequence() $]
    <cond:regular-localization-projective-k-sequence>
  ]
] <th:regular-projective-k-localization>

Пусть $A$ — область целостности с полем частных $L = S^(-1)A$
($S = A without {0}$). Если $M in bold(M)(A)$, то определим его _ранг_ так:
$ rank_A (M) = [M tensor_A L:L]. $
Ясно, что получаем аддитивную функцию, индуцирующую гомоморфизм
$ G_0 (A) -> G_0 (L) approx ZZ. $
Отметим, что эта терминология согласована с употреблением термина ранг в случае
проективных модулей $P in bold(P)(A)$. Положим
$ tilde(G)_0 (A) = Ker(G_0 (A) arrow.r^rank ZZ). $
Так как $rank(A) = 1$, то получаем разложение
$ G_0 (A) = ZZ dot [A] plus.o tilde(G)_0 (A). $

#source(386)Допустим теперь, что $A$ — кольцо Крулля (см. гл.~@ch:rings-modules,
§~@sec:rank-picard-krull). Если $M in moduleCategory(A)$ и
$frak(p) in Ht_1 (A)$, то через $l_frak(p) (M)$ обозначим длину (возможно,
бесконечную!) $A_frak(p)$-модуля $M_frak(p)$. Определим полную подкатегорию $C$,
объектами которой являются все модули $M in moduleCategory(A)$, для которых:
#condition-list[
  #condition-item(format: "(1°)")[длина $l_frak(p) (M)$ конечна для всех
    $frak(p) in Ht_1 (A)$;] <cond:divisor-characteristic-finite-length>
  #condition-item(format: "(1°)")[$l_frak(p) (M) = 0$ для всех, кроме конечного
    числа, $frak(p) in Ht_1 (A)$.]
  <cond:divisor-characteristic-finite-support>
]
Тогда для модуля $M in C$ можно определить элемент группы дивизоров
$ chi(M) = sum_(frak(p) in Ht_1 (A)) l_frak(p) (M)frak(p) in D(A). $
Так как локализация — точный функтор, то $C$ является абелевой категорией, а
$chi$ есть аддитивная функция на $C$, индуцирующая, таким образом, отображение
$ chi:K_0 (C) -> D(A). $
Очевидно, что категория $bold(M)_S (A)$ конечно порожденных периодических
$A$-модулей содержится в $C$. Вложения
$HCat_S (A) subset bold(M)_S (A) subset C$ индуцируют, таким образом,
гомоморфизмы, которые мы также обозначим буквой $chi$:
$ chi:G_0 (A, S) = K_0 (bold(M)_S (A)) -> D(A) $
и
$ chi:K_0 (A, S) = K_0 (HCat_S (A)) -> D(A). $

#proposition[
  Пусть $A$ — коммутативное кольцо, $alpha in End_A (A^n)$ и $M = Coker(alpha)$.
  Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[$M dot det(alpha) = 0$.]
    <cond:determinant-annihilates-cokernel>
    #condition-item(format: "cyrillic")[Если $A$ — кольцо Крулля и
      $det(alpha) != 0$, то $chi(M) = divisor(det(alpha))$.]
    <cond:determinant-divisor-characteristic>
    #condition-item(format: "cyrillic")[Если $A$ — нётерово кольцо Крулля с
      полем частных $L = S^(-1)A$ ($S = A without {0}$), то существует
      единственный гомоморфизм $"cl":G_0 (A) -> C(A)$ (т.~е. в группу классов
      дивизоров), такой, что $"cl"[A] = 0$ и диаграмма
      $ #localization-divisor-sequence() $
      коммутативна. Здесь верхняя строка совпадает с точной последовательностью
      из @th:g-localization-exact-sequence, а нижняя строка является точной
      последовательностью дивизоров и классов дивизоров из
      гл.~@ch:rings-modules, §~@sec:rank-picard-krull,
      @eq:divisor-class-diagram. Кроме того, вертикальные отображения являются
      эпиморфизмами.]
    <cond:grothendieck-divisor-class-homomorphism>
  ]
] <prop:determinant-divisor-characteristic>

#proof[
  #source(387)@cond:determinant-annihilates-cokernel Легко заметить (правило
  Крамера), что существует матрица $beta in End_A (A^n)$, для которой
  $alpha beta = beta alpha = det(alpha) 1_(A^n)$. Таким образом,
  $A^n dot det(alpha) subset Im(alpha)$, что доказывает
  @cond:determinant-annihilates-cokernel.

  @cond:determinant-divisor-characteristic Покажем, что диаграмма
  $ #localization-determinant-square() $
  где $partial$ — отображение из @th:k-localization-boundary, коммутативна. Если
  мы рассмотрим $alpha$ как элемент группы $GL_n (L)$, то он определяет элемент
  $[alpha] in K_1 (L)$. В силу @th:k-localization-boundary
  $partial[alpha] = [Coker(alpha)]$. Следовательно,
  @cond:determinant-divisor-characteristic будет вытекать из коммутативности
  этого квадрата. Так как $det$ является изоморфизмом, то достаточно показать,
  что $chi(partial[u]) = divisor(u)$ для $u in U(L)$, где
  $[u] = [L, u dot 1_L] in K_1 (L)$. Полагая $u = a slash b$, где $a, b != 0$
  элементы из $A$, мы сводим задачу к случаю, когда $u = a in A$. Тогда, как мы
  уже видели, $chi(partial[a]) = chi(A slash a A)$. Если $frak(p) in Ht_1 (A)$ и
  $a A_frak(p) = (frak(p) A_frak(p))^n$, то очевидно, что длина
  $A_frak(p)$-модуля $(A slash a A)_frak(p)$ равна $n$, поскольку $A_frak(p)$ —
  кольцо дискретного нормирования. Итак, $chi(A slash a A) = divisor(a)$, что и
  требовалось доказать.

  @cond:grothendieck-divisor-class-homomorphism Заметим, что
  $G_0 (A) = ZZ dot [A] plus.o tilde(G)_0 (A)$, где
  $tilde(G)_0 (A) = Ker(G_0 (A) -> G_0 (L))
  = Im(G_0 (A, S) -> G_0 (A)) = Coker(partial)$. Из части
  @cond:determinant-divisor-characteristic доказательства следует, что диаграмма
  $ #localization-determinant-square(grothendieck: true) $
  коммутативна. Поэтому она индуцирует гомоморфизм $"cl":tilde(G)_0 (A) -> C(A)$
  на коядрах. Таким образом, гомоморфизм $"cl"$ построен. Его единственность
  следует из коммутативности диаграммы и замечания о том, что $"cl"[A] = 0$.

  Как мы уже отмечали, $det$ является изоморфизмом. Так как
  $chi[A slash frak(p)] = frak(p)$ для $frak(p) in Ht_1 (A)$, то $chi$ —
  эпиморфизм. Рассматривая диаграмму, убеждаемся в том, что отображение $"cl"$
  также эпиморфно. Тем самым доказательство закончено.
]

#proposition[
  Пусть кольцо $A$ такое же, как и в предложении
  @prop:determinant-divisor-characteristic
  @cond:grothendieck-divisor-class-homomorphism. Пусть $T$ — мультипликативная
  система ($0 in.not T$), для которой кольцо $B = T^(-1)A$ регулярно. Тогда
  существует эпиморфизм #source(388)точных последовательностей
  $ #localization-divisor-sequence(restricted: true) $
] <prop:regular-localization-divisor-class-sequence>

#proof[
  Верхняя строка взята из @th:g-localization-exact-sequence. Отображение $chi_T$
  определяется коммутативной диаграммой
  $ #localization-divisor-square() $
  где $S = A without {0}$ и верхнее отображение индуцировано вложением
  $bold(M)_T (A) subset bold(M)_S (A)$. Нам надо лишь отметить, что если
  $M in bold(M)_T (A)$, то $chi(M) in D(A, T)$. Но $M t = 0$ для некоторого
  $t in T$. Таким образом, если $M_frak(p) != 0$ для $frak(p) in Ht_1 (A)$, то
  $frak(p) supset ann_A (M)$ и, следовательно, $frak(p) inter T != emptyset$.
  Так как группа $D(A, T)$ порождается элементами $frak(p) in Ht_1 (A)$,
  пересекающимися с $T$, то это показывает, что отображение $chi_T$ существует.
  Нижняя точная последовательность взята из гл.~@ch:rings-modules,
  §~@sec:rank-picard-krull (диаграмма @eq:localized-divisor-class-diagram). В
  силу
  @prop:determinant-divisor-characteristic
  @cond:grothendieck-divisor-class-homomorphism коммутативность нашей диаграммы
  устанавливается непосредственно, если учесть способ введения этих отображений.
]

Рассмотрим теперь последовательность функтора локализации для функтора $Pic$.
Пусть кольцо $A$ коммутативно и $f:A -> S^(-1)A$ — локализация. Тогда из
@eq:determinant-exact-sequence-morphism получаем точную последовательность
#numbered-condition[
  $
    U(A) -> U(S^(-1)A) arrow.r^partial Pic(f) arrow.r^d Pic(A) -> Pic(S^(-1)A),
  $
] <eq:picard-localization-functor-sequence>
Если система $S$ не содержит делителей нуля кольца $A$, то можно также
рассмотреть группу $Pic(A, S)$ (см. гл.~@ch:rings-modules,
§~@sec:rank-picard-krull) обратимых идеалов $frak(a) subset S^(-1)A$, для
которых $S^(-1)frak(a) = S^(-1)A$, и точную последовательность
@prop:picard-localization-exact-sequence: #numbered-condition[
  $ U(A) -> U(S^(-1)A) -> Pic(A, S) -> Pic(A) -> Pic(S^(-1)A). $
] <eq:picard-localization-ideal-sequence>
Отождествим эти две последовательности. В силу 5-леммы достаточно построить
гомоморфизм $h:Pic(A, S) -> Pic(f)$, превращающий получающуюся диаграмму $#[
  @eq:picard-localization-ideal-sequence] ->
#[ @eq:picard-localization-functor-sequence]$ в коммутативную. Определим
$h(frak(a)) = [frak(a), alpha, A]$, где $alpha:S^(-1)frak(a) -> S^(-1)A$ —
изоморфизм, индуцированный вложением $frak(a) subset S^(-1)A$. Легко проверить,
что $h$ — гомоморфизм, поскольку отображение
$frak(a) tensor_A frak(b) -> frak(a) frak(b)$ является изоморфизмом для
$frak(a), frak(b) in Pic(A, S)$. Кроме того,
$d[frak(a), alpha, A] = [frak(a)] - [A] = [frak(a)]$ в группе $Pic(A)$. Если
$a in U(S^(-1)A)$, то #source(389)$
  partial(a) = [A, a dot 1_(S^(-1)A), A]
  = [a A, 1_(S^(-1)A), A] = h(a A).
$
Таким образом, диаграмма
$ #localization-picard-identification() $
коммутативна. Следовательно, с этого момента мы можем использовать $h$ для
отождествления групп $Pic(f)$ и $Pic(A, S)$. Более общим образом обозначим через
$Pic(A, S)$ группу $Pic(f)$ для любой мультипликативной системы (возможно, уже
содержащей делители нуля). В этих обозначениях можно записать гомоморфизм $det$
как эпиморфизм точных последовательностей: #numbered-condition[
  $ #localization-picard-sequences() $
] <eq:localization-determinant-sequences>
Если при отображении $A -> S^(-1)A$ ни один из ненулевых идемпотентов не
отображается в нуль (например, если система $S$ не содержит делителей нуля), то
можно заменить в диаграмме $K_0$ на $Rk_0$.

#theorem[
  Пусть $A$ — коммутативное нётерово кольцо и $S$ — мультипликативная система,
  не содержащая делителей нуля и регулярная относительно кольца $A$. Тогда
  существует эпиморфизм точных последовательностей
  $ #localization-picard-sequences(regular: true) $
  где $Pic(A, S)$ — свободная абелева группа с базисом из простых идеалов высоты
  1, пересекающихся с $S$.
] <th:regular-localization-picard-sequence>

#proof[
  Диаграмма совпадает с диаграммой @prop:reduced-determinant-exact-sequence
  всюду, кроме нулевых членов справа и члена $G_0 (A, S)$. Дополнительные члены
  в верхней строке возникают из @th:regular-projective-k-localization. В силу
  @th:regular-system-factorial система $S$ факториальна относительно кольца $A$.
  Поэтому указанные свойства нижней строки вытекают из
  @prop:factorial-localization-picard-surjection.
]

Применим теперь некоторые из этих результатов к алгебрам над _дедекиндовыми
кольцами_.

#proposition[
  #source(390)Пусть $R$ — дедекиндово кольцо с полем частных $L = S^(-1)R$
  ($S = R without {0}$). Пусть $X = maxSpec(R)$. Допустим, что $A$ — нётерова
  справа $R$-алгебра, являющаяся $R$-модулем без кручения. Положим
  $B = A tensor_R L = S^(-1)A$. Допустим, что алгебра $B$ удовлетворяет условиям
  теоремы @th:g-localization-exact-sequence. Тогда существует естественный
  изоморфизм #numbered-condition[
    $
      union.sq.big_(frak(p) in X) G_i (A slash (frak(p) A)) -> G_i (A, S)
      quad (i = 0, 1).
    $
  ] <eq:dedekind-g-localization-decomposition>
  Следовательно, последовательность
  $
    G_1 (B) -> union.sq.big_(frak(p) in X) G_0 (A slash (frak(p) A))
    -> G_0 (A) -> G_0 (B) -> 0
  $
  точна. Кроме того, если алгебра $A$ регулярна справа, то последовательность
  $
    K_1 (A) -> K_1 (B) -> union.sq.big_(frak(p) in X) G_0 (A slash (frak(p) A))
    -> K_0 (A) -> K_0 (B) -> 0
  $
  точна.
] <prop:dedekind-g-localization-decomposition>

#proof[
  Как только изоморфизм @eq:dedekind-g-localization-decomposition установлен,
  точность приведенных последовательностей вытекает из теорем
  @th:g-localization-exact-sequence и @cor:regular-localization-cartan-sequences
  соответственно, если использовать @eq:dedekind-g-localization-decomposition
  для замены $union.sq.big_(frak(p) in X) G_0 (A slash (frak(p) A))$ на
  $G_0 (A, S)$ в последней последовательности.

  Если $frak(p) in X$, то через $bold(M)_frak(p) (A)$ обозначим категорию
  модулей $M in bold(M)(A)$, аннулируемых некоторой степенью идеала $frak(p)$.
  Если $M in bold(M)_S (A)$, то $M frak(a) = 0$ для некоторого идеала
  $frak(a) != 0$ кольца $R$. Если
  $frak(a) = frak(p)_1^(n_1) dots frak(p)_r^(n_r)$ — разложение на простые
  множители идеала $frak(a)$ кольца $R$, то в силу китайской теоремы об остатках
  $R slash frak(a) approx product R slash frak(p)_i^(n_i)$. Таким образом,
  получаем каноническое разложение модуля $M$: $M = M_1 plus.o dots plus.o M_r$,
  где $M_i$ состоят из элементов модуля $M$, аннулируемых некоторой степенью
  идеала $frak(p)_i$. Из этого разложения легко видеть, что
  $
    G_i (A, S) = K_i (bold(M)_S (A))
    = union.sq.big_(frak(p) in X) K_i (bold(M)_frak(p) (A)).
  $
  Далее отметим, что $bold(M)(A slash (frak(p) A)) subset bold(M)_frak(p) (A)$.
  Если $M in bold(M)_frak(p) (A)$, то
  $M supset M frak(p) supset M frak(p)^2 supset dots$ дает нам конечную
  характеристическую фильтрацию с факторами из $bold(M)(A slash (frak(p) A))$.
  Следовательно, из @th:devissage-k-isomorphisms следует, что отображение
  $G_i (A slash (frak(p) A)) = K_i (bold(M)(A slash (frak(p) A)))
  -> K_i (bold(M)_frak(p) (A))$ является изоморфизмом ($i = 0, 1$). Это
  завершает доказательство.
]

#proposition[
  #source(391)Пусть $R$, $L = S^(-1)R$ и $X$ такие же, как и в предложении
  @prop:dedekind-g-localization-decomposition. Пусть $D(R) = ZZ^((X))$ — группа
  дивизоров кольца $R$. Пусть $A$ — коммутативная регулярная область
  целостности, содержащая кольцо $R$ и такая, что в ней идеал $frak(p) A$
  является простым для всех $frak(p) in X$. Положим $B = A tensor_R L$. Тогда
  имеет место коммутативная диаграмма с точными строками и столбцами
  $ #localization-dedekind-determinant-diagram() $
  Если $frak(p) in X$ и $M in bold(M)(A slash (frak(p) A))$, то
  $delta[M] = rk(M)frak(p)$, где $rk(M)$ — ранг модуля $M$ над областью
  целостности $A slash (frak(p) A)$.
] <prop:dedekind-relative-determinant-diagram>

#proof[
  Предложение очевидно, если $R = L$. Поэтому предположим, что $R != L$. Тогда
  $X = Ht_1 (R)$. Если $frak(p) in X$, то
  $frak(p) subset frak(p) A inter R subset R$. Так как идеал $frak(p) A$
  простой, а $frak(p)$ — максимальный, то $frak(p) = frak(p) A inter R$. Таким
  образом, выполнены предположения предложения
  @cor:factorial-base-extension-relative-picard, поскольку система $S$
  факториальна в $R$ и в $A$ (в силу регулярности колец $R$ и $A$ (см.
  @th:regular-system-factorial)). Следовательно, из
  @cor:factorial-base-extension-relative-picard и из
  @prop:factorial-localization-picard-surjection вытекает, что
  $ D(R) = Pic(R, S) approx Pic(A, S) approx D(A, S). $
  Желая определить нижние две трети диаграммы, начнем с эпиморфизма точных
  последовательностей в теореме @th:regular-localization-picard-sequence.
  Используя полученный изоморфизм $D(R) approx Pic(A, S)$ и изоморфизм
  $union.sq.big_(frak(p) in X) G_0 (A slash (frak(p) A)) -> G_0 (A, S)$ из
  предложения @prop:dedekind-g-localization-decomposition, произведем замену
  $ G_0 (A, S) = K_0 (A, S) arrow.r^(det_0 (A, S)) Pic(A, S). $
  Так как кольцо $A$ регулярно, то можно использовать гомоморфизмы Картана для
  отождествления $det_0 (A, S)$ с $chi_S:G_0 (A, S) -> D(A, S)$ (см.
  @cor:regular-localization-cartan-sequences). Напомним, что
  $chi_S (M) = sum l_(A_frak(p)) (M_frak(p))frak(p)$ для $frak(p) in Ht_1 (A)$,
  $frak(p) inter S != emptyset$ и $M in bold(M)_S (A)$. В силу
  @cor:factorial-base-extension-relative-picard #source(392)соответствие
  $frak(p) arrow.r.bar frak(p) A$ осуществляет биекцию из $X$ на множество
  ${frak(p) in Ht_1 (A) | frak(p) inter S != emptyset}$. В частности, если
  $frak(p) in X$ и $M in bold(M)(A slash (frak(p) A))$, то $M_(frak(q) A) = 0$
  для $frak(q) != frak(p)$ из $X$. Поэтому
  $chi_S (M) = l_(A_(frak(p) A)) (M_(frak(p) A))(frak(p) A)$. Так как
  $M frak(p) = 0$, то $M_(frak(p) A)$ является векторным пространством над полем
  частных кольца $A slash (frak(p) A)$ (совпадающим с полем вычетов кольца
  $A_(frak(p) A)$). Поэтому (см. доказательство
  @prop:determinant-divisor-characteristic
  @cond:determinant-divisor-characteristic) $l_(A_(frak(p) A)) (M_(frak(p) A))$
  совпадает с рангом $M_(frak(p) A)$ как модуля над областью целостности
  $A slash (frak(p) A)$. Это дает нам описание отображения $delta$. Но теперь
  верхняя строка совпадает с ядром морфизма из средней строки в нижнюю (в силу
  определения в случае $tilde(Rk)_0$). Верхняя строка точна ввиду свойств
  длинной гомологической последовательности и расщепляемости эпиморфизмов
  $det_1$. Тем самым предложение доказано.
]

#corollary[
  В ситуации предложения @prop:dedekind-relative-determinant-diagram допустим,
  что кольцо $B$ и все кольца $A slash (frak(p) A)$ ($frak(p) in X$)
  дедекиндовы. Тогда имеет место точная последовательность
  $
    SK_1 (A) -> SK_1 (B) -> union.sq.big_(frak(p) in X) Pic(A slash (frak(p) A))
    -> Rk_0 (A) arrow.r^(det_0 (A)) Pic(A) -> 0.
  $
] <cor:dedekind-quotient-picard-localization>

#proof[
  В диаграмме предложения @prop:dedekind-relative-determinant-diagram можно
  отождествить $G_0 (A slash (frak(p) A))$ и $K_0 (A slash (frak(p) A))$, а
  тогда $tilde(G)_0 (A slash (frak(p) A))
  = Ker(G_0 (A slash (frak(p) A)) arrow.r^rk ZZ)$ отождествляется с
  $Rk_0 (A slash (frak(p) A))$. Кроме того, из
  @cor:dimension-one-reduced-determinant-isomorphism следует, что в случае
  дедекиндовых колец отображение $det_0:Rk_0 -> Pic$ оказывается изоморфизмом.
  Таким образом, $tilde(Rk)_0 (B) = 0$, а из предложения
  @prop:dedekind-relative-determinant-diagram мы получаем диаграмму
  $ #localization-dedekind-kernel-sequence() $
  строки и столбцы которой являются точными последовательностями. Из этих
  замечаний непосредственно вытекает наше утверждение.
]
