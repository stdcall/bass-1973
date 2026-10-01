#import "main-defs.typ": (
  Coker, G, Im, K, Ker, Pic, U, ann, char, dim, hd, idx, maxSpec, rad, source,
  tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, definition, example, proof,
  proposition,
)
#import "diagrams/arithmetic-finiteness-cartan.typ": (
  diagram-cartan-localization, diagram-cartan-order-comparison,
  diagram-conductor-pullback, diagram-regular-cartan-localization,
  diagram-swan-local-cartan, diagram-swan-triangle,
)

== Треугольник Суона и условие Картана <sec:swan-triangle-cartan-condition>
#idx("треугольник Суона")

Мы используем обозначения @eq:arithmetic-finiteness-data. Включение
$A subset Lambda = S^(-1) A$ приводит нас к коммутативной диаграмме с точными
строками

$ #diagram-cartan-localization() $ <eq:arithmetic-cartan-localization-sequences>

Верхняя строка происходит из @th:k-localization-boundary, а нижняя строка — из
@th:g-localization-exact-sequence. Вертикали — это гомоморфизмы Картана (гл.
@ch:projective-k-theory, § @sec:g-groups-cartan-maps). Отождествление нижнего
копроизведения с группой $G_0 (A, S)$ осуществлено в силу
@prop:dedekind-g-localization-decomposition. Многие из результатов этого
параграфа будут сформулированы в терминах диаграммы
@eq:arithmetic-cartan-localization-sequences.

Пусть $bold(italic(M))_0 (A) subset bold(italic(M)) (A)$ — полная подкатегория
($R$-) модулей
#source(405)
без кручения $M in bold(italic(M)) (A)$. Если последовательность
$0 -> N -> P -> M -> 0$ точна в категории $italic("mod") "-" A$, где
$M in bold(italic(M))_0 (A)$, то
$P in bold(italic(M))_0 (A) <=> N in bold(italic(M))_0 (A)$. Кроме того, если
$P in bold(italic(P)) (A)$, то $N in bold(italic(M))_0 (A)$, и поэтому
$bold(italic(M))_0 (A)$ является допустимой подкатегорией категории
$bold(italic(M)) (A)$, а каждый модуль $M in bold(italic(M)) (A)$ может быть
дополнен до точной последовательности рассмотренного типа с
$P in bold(italic(P)) (A)$ и $N in bold(italic(M))_0 (A)$. Таким образом, из
@th:projective-resolution-k-isomorphisms следует, что вложение
$bold(italic(M))_0 (A) subset bold(italic(M)) (A)$ индуцирует изоморфизмы

$
  K_i (bold(italic(M))_0 (A)) -> K_i (bold(italic(M)) (A)) = G_i (A)
  quad (i = 0, 1).
$ <eq:torsion-free-category-k-isomorphisms>

Пусть $frak(a)$ — ненулевой идеал кольца $R$. Тогда функтор
$tensor_R R slash frak(a): bold(italic(M)) (A) ->
bold(italic(M)) (A slash A frak(a))$ при ограничении на $bold(italic(M))_0 (A)$
дает точный функтор, что и является причиной введения категории
$bold(italic(M))_0$. Действительно, если $M in bold(italic(M))_0 (A)$, то
$M in bold(italic(P)) (R)$, и поэтому короткая точная последовательность этих
модулей расщепляется как последовательность $R$-модулей. Итак, получаем
индуцированные гомоморфизмы

$
  K_i (bold(italic(M))_0 (A)) -> G_i (A slash A frak(a))
  quad (i = 0, 1).
$

Сопоставляя их с отображениями @eq:torsion-free-category-k-isomorphisms, получим
гомоморфизмы

$ phi_frak(a): G_i (A) -> G_i (A slash A frak(a)) quad (i = 0, 1). $

#idx("теорема", "о треугольнике Суона")
#proposition(title: [о «треугольнике Суона»])[
  Пусть $frak(a)$ — ненулевой идеал кольца $R$. Существует и притом единственный
  гомоморфизм $delta_frak(a): G_0 (Lambda) ->
  G_0 (A slash A frak(a))$, такой, что коммутативна диаграмма

  $ #diagram-swan-triangle($frak(a)$) $
] <prop:swan-triangle>

#proof[
  Так как отображение $g_0$ сюръективно (см.
  @eq:arithmetic-cartan-localization-sequences), то предложение будет доказано,
  как только мы покажем, что $phi_frak(a) (Ker (g_0)) = 0$. Но
  $Ker (g_0) = Im (G_0 (A, S) -> G_0 (A))$, и группа
  $G_0 (A, S) = K_0 (bold(italic(M))_S (A))$ порождается классами простых
  $A$-модулей $M in bold(italic(M)) (A slash A frak(p))$ по всем
  $frak(p) in maxSpec (R)$.

  Пусть последовательность $0 -> N -> P -> M -> 0$ точна и
  $P in bold(italic(P)) (A)$. Тогда в силу определения
  $phi_frak(a) [M] = [P slash P frak(a)] - [N slash N frak(a)]$. Предположим
  сначала, что идеал $frak(a) = a R$ главный.

  Если $M frak(a) != 0$, то, поскольку модуль $M$ простой, отображение
  $M arrow^a M$ является автоморфизмом. Отсюда следует, что
  $P frak(a) inter N = N frak(a)$, и поэтому последовательность
  $0 -> N slash N frak(a) -> P slash P frak(a) ->
  M slash M frak(a) = 0$ точна. Таким образом, $phi_frak(a) [M] = 0$.

  Если, с другой стороны, $M frak(a) = 0$, то рассмотрение точной
  последовательности $0 -> P frak(a) slash N frak(a) ->
  N slash P frak(a) -> P slash P frak(a) -> M -> 0$ в категории
  #source(406)
  $bold(italic(M)) (A slash A frak(a))$ показывает, что

  $ phi_frak(a) [M] = [M] - [P frak(a) slash N frak(a)] = [M] - [M] = 0. $

  Наконец, если идеал $frak(a)$ не является главным, то положим
  $S = 1 + frak(a)$ и рассмотрим локализацию $R -> S^(-1) R$. Это не изменяет ни
  один из модулей $P slash P frak(a)$, $N slash N frak(a)$ и т. д., которые
  аннулируются идеалом $frak(a)$. С другой стороны,
  $S^(-1) frak(a) subset rad S^(-1) R$. Поэтому $S^(-1) R$ (как дедекиндово
  кольцо с ненулевым радикалом) является полулокальным кольцом и, следовательно,
  кольцом главных идеалов. Таким образом, можно применить предыдущее рассуждение
  к кольцу $S^(-1) R$ и сделать вывод $phi_frak(a) [M] = 0$, что и требовалось
  доказать.
]

#corollary[
  Допустим, что $R$ — локальное кольцо с максимальным идеалом $frak(p)$. Если
  гомоморфизм Картана $c_0 (frak(p)) = c_0 (A slash A frak(p)):
  K_0 (A slash A frak(p)) -> G_0 (A slash A frak(p))$ является мономорфизмом, то
  отображение $k_0: K_0 (A) -> K_0 (Lambda)$ также является мономорфизмом. Кроме
  того, если $P, Q in bold(italic(P)) (A)$, то
  $P tensor_R L tilde.eq Q tensor_R L => P tilde.eq Q$. Если к тому же кольцо
  $A$ регулярно справа, то отображение $k_0$ — изоморфизм.
] <cor:local-cartan-projective-descent>

#proof[
  Рассмотрим коммутативную диаграмму

  $ #diagram-swan-local-cartan() $

  Так как $A frak(p) subset rad A$, то из @prop:k-radical-ideal-comparison
  @cond:k-zero-radical-quotient-injection следует, что отображение $psi_frak(p)$
  является мономорфизмом (фактически изоморфизмом, если кольцо $R$
  $frak(p)$-адически полно). Таким образом, отображение
  $c_0 (frak(p)) psi_frak(p) = delta_frak(p) c_0 (Lambda) k_0$ — мономорфизм и,
  следовательно, $k_0$ — также мономорфизм. Если кольцо $A$ регулярно справа, то
  $c_0 (A)$ — изоморфизм. Поэтому сюръективность отображения $k_0$ следует из
  сюръективности отображения $g_0$.

  Наконец, если $P, Q in bold(italic(P)) (A)$ и
  $P tensor_R L tilde.eq Q tensor_R L$, то $[P] = [Q]$ в группе $K_0 (A)$,
  поскольку $k_0$ — мономорфизм, т. е. $P plus.o A^n tilde.eq Q plus.o A^n$ для
  некоторого $n >= 0$. Так как кольцо $A$ полулокально, то из
  @cor:semilocal-projective-cancellation следует, что $P tilde.eq Q$, что и
  требовалось доказать.
]

#idx("условия Картана")
#definition[
  Следующее условие назовем _условием Картана_: гомоморфизм Картана

  $
    c_0 (frak(p)) = c_0 (A slash A frak(p)):
    K_0 (A slash A frak(p)) -> G_0 (A slash A frak(p))
  $

  #source(407)
  является мономорфизмом. Это эквивалентно тому, что определитель матрицы
  Картана для $A slash A frak(p)$ отличен от нуля.
] <def:cartan-condition>

#corollary[
  Пусть кольцо $A$ удовлетворяет условию Картана. Пусть модуль
  $P in bold(italic(P)) (A)$ таков, что $P tensor_R L tilde.eq Lambda^n$, где
  $n>=1$. Тогда $P_frak(p) tilde.eq A_frak(p)^n$ для всех $frak(p) in X$, и
  модуль $P$ содержит прямое слагаемое, которое изоморфно модулю $A^(n-1)$. Если
  кольцо $R$ полулокально, то $P tilde.eq A^n$.
] <cor:cartan-locally-free-splitting>

#proof[
  Первое утверждение вытекает из @cor:local-cartan-projective-descent (в
  применении к $A_frak(p)$ над $R_frak(p)$). В силу первого утверждения и того,
  что $dim X <= 1$, второе утверждение теперь следует из теоремы Серра
  @cor:serre-free-summand. Если кольцо $R$ полулокально, то аналогично
  получается последнее утверждение, поскольку в этом случае $dim X = 0$.
]

#corollary[
  Пусть кольцо $A$ удовлетворяет условию Картана. Допустим, что $Lambda$ —
  алгебра с делением. Тогда каждый модуль $P in bold(italic(P)) (A)$ является
  прямой суммой свободного модуля и правого идеала кольца $A$.
] <cor:cartan-projectives-ideal-plus-free>

#proof[
  При $P=0$ утверждение тривиально; далее пусть $P!=0$. Очевидно, что
  $P tensor_R L tilde.eq Lambda^n$ для некоторого $n$. Поэтому из следствия
  @cor:cartan-locally-free-splitting вытекает, что
  $P tilde.eq Q plus.o A^(n-1)$. При этом $Q$ обязательно является $A$-решеткой
  в $Q tensor_R L tilde.eq Lambda$. Таким образом, оказывается, что модуль $Q$
  изоморфен некоторому правому $A$-идеалу.
]

#proposition[
  Пусть

  $ C = Coker (K_0 (A,S) arrow^(c_0(A,S)) G_0 (A,S)). $

  Тогда существует естественный эпиморфизм

  $ union.sq.big_(frak(p) in X) Coker (c_0 (frak(p))) -> C. $

  Следовательно, если кольцо $A$ удовлетворяет условию Картана, то группа $C$
  периодическая.
] <prop:cartan-localization-torsion-cokernel>

#proof[
  Заметим, что $G_0 (A,S) = union.sq.big_(frak(p) in X)
  G_0 (A slash frak(p) A)$ и что $K_0 (A,S) = K_0 (bold(italic(H))_S (A))$, где
  $bold(italic(H))_S (A)$ — категория периодических $A$-модулей конечной
  гомологической размерности. Следовательно, предложение будет доказано, как
  только мы покажем, что
  $bold(italic(P)) (A slash frak(p) A) subset bold(italic(H))_S (A)$
  для каждого $frak(p) in X$. Так как любой модуль
  $P in bold(italic(P)) (A slash frak(p) A)$ является прямым слагаемым в
  некотором модуле $(A slash frak(p) A)^n$, то достаточно показать, что
  $hd_A (A slash frak(p) A) < infinity$. Но, поскольку идеал $frak(p)$ обратим,
  $frak(p) A tilde.eq frak(p) tensor_R A in bold(italic(P)) (A)$.
  #source(408)
  Следовательно, последовательность $0 -> frak(p) A -> A ->
  A slash frak(p) A -> 0$ дает нам конечную $bold(italic(P)) (A)$-резольвенту,
  что и требовалось доказать.
]

#example[
  Предположим, что $B = product B_i$ $(1 <= i <= n)$, где каждое из $B_i$ —
  артиново справа кольцо, у которого $B_i slash rad B_i$ — простое кольцо. Тогда
  $c_0 (B) = c_0 (B_1) plus.o dots plus.o c_0 (B_n)$, при этом $c_0 (B_i)$
  представляется ненулевой $(1 times 1)$-матрицей. Следовательно, $c (B)$ —
  мономорфизм. Так как любое коммутативное артиново кольцо является
  произведением локальных колец, то из сделанного замечания вытекает, что

  _Если $A$ — коммутативное кольцо, то $A$ удовлетворяет условию Картана._

  Далее, мы утверждаем, что

  _Если $A$ — максимальный $R$-порядок, то $A$ удовлетворяет условию Картана._

  Действительно, пусть $frak(a)$ — любой двусторонний идеал кольца $A$,
  являющийся $R$-решеткой (например, $A frak(p)$ для некоторого $frak(p) in X$).
  Покажем, что тогда отображение $c (A slash frak(a))$ инъективно.

  Согласно @th:maximal-order-two-sided-lattices, рассмотрим однозначно
  определенное разложение $frak(a) = frak(p)_1^(n_1) dots frak(p)_r^(n_r)$, где
  $frak(p)_i in maxSpec (A)$ (множество максимальных двусторонних идеалов).
  Положим $frak(q)_i = product_(j != i) frak(p)_j^(n_j)$ $(1 <= i <= r)$. В силу
  теоремы об однозначности разложения $frak(q)_i subset.not frak(p)_i$, и
  поэтому $sum_j frak(q)_j subset.not frak(p)_i$ для всех $i$ $(1 <= i <= r)$.
  Таким образом, получаем, что $sum_j frak(q)_j = A$. Аналогично
  $frak(p)_i + frak(q)_i = A$ для каждого $i$. Теперь, как и в доказательстве
  китайской теоремы об остатках @prop:chinese-remainder-modules, получаем, что

  $ A slash frak(a) tilde.eq product A slash frak(p)_i^(n_i). $

  Так как каждый $frak(p)_i in maxSpec (A)$, то $B_i = A slash frak(p)_i^(n_i)$
  удовлетворяет предположениям, сформулированным вначале. Поэтому, учитывая
  сделанное выше первое замечание, можно заключить, что отображение
  $c (A slash frak(a))$ инъективно, что и требовалось доказать.
] <exm:commutative-maximal-orders-cartan-condition>

#example[
  Пусть $pi$ — конечная группа. Тогда отображение $c_0 (L pi)$ инъективно (см.
  @th:finite-group-cartan-injectivity и следующее замечание). Если
  характеристика $char (L)$ не делит $[pi:1]$, то алгебра $L pi = Lambda$
  полупроста (см. @th:maschke), а $R$-порядок $A = R pi$ удовлетворяет условию
  Картана. (Следует применить первое утверждение к полям $R slash frak(p)$.)
] <exm:finite-group-order-cartan-condition>

С учетом теории максимальных порядков (см. гл. @ch:rings-modules, §
@sec:orders-semisimple-algebras) и примера
@exm:commutative-maximal-orders-cartan-condition можно попытаться получить
информацию о кольце $A$, сравнивая $A$ с максимальным $R$-порядком $B$,
содержащим $A$.

Рассмотрим диаграмму, аналогичную диаграмме
@eq:arithmetic-cartan-localization-sequences, для кольца $B$. Будем теперь
использовать обозначение $k_0 (A)$ вместо $k_0$,
#source(409)
чтобы отличить это отображение от аналогичного отображения
$k_0 (B): K_0 (B) -> K_0 (Lambda)$. Подобные соглашения будут применяться и в
обозначениях отображений $k_i$ и $g_i$ $(i = 0, 1)$.

_До конца этого параграфа будем считать, что $B$ — максимальный $R$-порядок,
содержащий $A$, и что $B$ является $R$-решеткой._
Последнее допущение гарантирует, что

$ frak(c)_0 = {a in R bar a B subset A} = ann_R (B slash A) $

является ненулевым $R$-идеалом. Тогда $frak(c)_0 B$ — двусторонний $B$-идеал,
содержащийся в $A$ и являющийся $R$-решеткой в $Lambda$. На самом деле
существует наибольший такой идеал $frak(c)_(B slash A)$, называемый
_кондуктором_:

$
  frak(c)_(B slash A) = {b in Lambda bar B b B subset A}
  = {b in B bar B b B subset A} = {b in A bar B b B subset A}.
$

Пусть $T = R without (union_(frak(p) supset frak(c)_0) frak(p))$. Это
мультипликативная система кольца $R$ и $T^(-1) R$ — полулокальное кольцо,
максимальные идеалы которого имеют вид $T^(-1) frak(p)$, где $frak(p)$ пробегает
все простые идеалы, содержащие идеал $frak(c)_0$.

#proposition[
  Сохраним приведенные выше обозначения. Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[Если $frak(p) in X$ и
      $frak(p) inter T != emptyset$, то $A_frak(p) = B_frak(p)$. Следовательно,
      $T$ — регулярная система относительно $A$ (в смысле
      @prop:finite-algebra-global-dimension-regularity), и поэтому следующая
      диаграмма с точными строками

      $ #diagram-regular-cartan-localization() $

      коммутативна, причем отображение $c_0 (A,T)$ является
      изоморфизмом.] <cond:order-conductor-regular-localization>
    #condition-item(format: "cyrillic")[Группа
      $Coker (c_0(A,S):K_0(A,S)->G_0(A,S))$ является факторгруппой конечно
      порожденной группы
      $union.sq.big_(frak(p) supset frak(c)_0) Coker (c_0(A slash frak(p) A))$.]
    <cond:order-cartan-cokernel-finite-generation>
    #condition-item(format: "cyrillic")[Отображение $K_0(A)->K_0(B)$ индуцирует
      эпиморфизм $Ker (k_0(A))->Ker (k_0(B))$. Если кольцо $A$ удовлетворяет
      условию Картана, то (некоммутативная) диаграмма

      $ #diagram-cartan-order-comparison() $

      #source(410)
      индуцирует коммутативную диаграмму

      $ #diagram-cartan-order-comparison(kernels: true) $

      Следовательно, образы левого и нижнего отображения совпадают.]
    <cond:order-class-kernel-surjection>
  ]
] <prop:order-maximal-order-comparison>

#proof[
  @cond:order-conductor-regular-localization Если $frak(p) inter T != emptyset$,
  то $frak(p) supset.not frak(c)_0$. Значит, $frak(c)_0 R_frak(p) = R_frak(p)$ и
  поэтому $B_frak(p) = frak(c)_0 B_frak(p) subset A_frak(p)$. Это показывает,
  что $A_frak(p) = B_frak(p)$. В силу
  @th:hereditary-maximal-order-characterizations кольцо $B$ — наследственное и
  потому, в частности, регулярное. Таким образом, кольцо $A_frak(p)$ регулярно
  для всех $frak(p) in X$, пересекающихся с $T$. В силу
  @prop:finite-algebra-global-dimension-regularity отсюда вытекает, что система
  $T$ регулярна относительно кольца $A$. Свойства нашей диаграммы следуют теперь
  из @th:g-localization-exact-sequence и @th:regular-projective-k-localization.

  @cond:order-cartan-cokernel-finite-generation Если
  $frak(p) inter T != emptyset$, то
  $bold(italic(M)) (A slash frak(p) A) subset bold(italic(H)) (A)$, поскольку
  система $T$ регулярна относительно кольца $A$. Следовательно, образ
  гомоморфизма

  $
    c_0(A,S): K_0(A,S)->G_0(A,S)
    = union.sq.big_(frak(p) in X) G_0(A slash frak(p) A)
  $

  содержит все члены, для которых $frak(p) inter T != emptyset$. Кроме того, как
  и в доказательстве предложения @prop:cartan-localization-torsion-cokernel,
  образ содержит образ гомоморфизма
  $c_0(A slash frak(p) A):K_0(A slash frak(p) A)->
  G_0(A slash frak(p) A)$ для всех $frak(p) in X$. Так как каждая группа
  $G_0(A slash frak(p) A)$ является свободной абелевой группой конечного ранга,
  то @cond:order-cartan-cokernel-finite-generation следует из этих замечаний.

  @cond:order-class-kernel-surjection Элемент группы $Ker (k_0(B))$ можно
  записать в виде $[P]-[F]$, где $F=B^n$ для некоторого $n>0$ и
  $P tensor_R L tilde.eq Lambda^n$. Так как кольцо $B$ удовлетворяет условию
  Картана (см. @exm:commutative-maximal-orders-cartan-condition), то из
  @cor:cartan-locally-free-splitting следует, что $T^(-1) P tilde.eq T^(-1) F$.
  Таким образом, можно выбрать $B$-гомоморфизм $h:P->F$, для которого $T^(-1) h$
  является изоморфизмом. Отсюда следует, что $h$ — мономорфизм и $T^(-1) M=0$,
  где $M=Coker (h)$. Так как система $T$ регулярна относительно кольца $A$, то
  $hd_A (M)<infinity$. На самом деле $M_frak(p)=0$, если
  $frak(p) inter T=emptyset$, а в противном случае $A_frak(p)$ — наследственное
  кольцо и поэтому $hd_A (M)<=1$ (см. @cor:local-global-projective-dimension).
  Пусть последовательность

  $ 0 -> P' -> F' -> M -> 0 $

  точна и $F' in bold(italic(P)) (A)$. Тогда также $P' in bold(italic(P)) (A)$.

  Мы утверждаем, что:
  #condition-list[
    #condition-item(format: "degree")[$M tensor_A B tilde.eq M$;]
    <cond:order-comparison-cokernel-base-change>
    #condition-item(format: "degree")[последовательность

      $ 0 -> P' tensor_A B -> F' tensor_A B -> M tensor_A B -> 0 $

      #source(411)
      точна.] <cond:order-comparison-resolution-base-change>
  ]
  Как только мы в этом убедимся, из леммы Шанюэля @prop:schanuel-lemma получим,
  что
  $F plus.o (P' tensor_A B) tilde.eq (F' tensor_A B) plus.o P$
  и, следовательно,

  $
    [P]-[F]=[P' tensor_A B]-[F' tensor_A B]
    in Im (Ker (k_0(A))->Ker (k_0(B))),
  $

  что и требуется.

  Для доказательства @cond:order-comparison-cokernel-base-change домножим
  последовательность

  $ 0 -> A -> B -> B slash A -> 0 $

  тензорно на $M$ над $A$. Так как $(B slash A) frak(c)_0 = 0$ и модуль $M$
  аннулируется элементом, который взаимно прост с $frak(c)_0$ (поскольку
  $T^(-1) M = 0$), то $M tensor_A (B slash A) = 0$ и, следовательно, отображение
  $M -> M tensor_A B$ является эпиморфизмом. Это отображение — изоморфизм,
  поскольку его локализации при всех $frak(p) in X$ являются изоморфизмами: если
  $frak(p) inter T=emptyset$, то $M_frak(p)=0$, а иначе $A_frak(p)=B_frak(p)$.

  Для доказательства @cond:order-comparison-resolution-base-change заметим, что
  отображение $P' tensor_A B -> F' tensor_A B$ является гомоморфизмом
  $R$-модулей без кручения (поскольку модуль $P'$ проективен), превращающимся в
  изоморфизм над $L$. Следовательно, это мономорфизм. Точность
  последовательности в других местах доказывается стандартно. Таким образом, мы
  доказали первую часть утверждения @cond:order-class-kernel-surjection.

  В связи со второй частью рассмотрим элемент
  $[P]_(bold(italic(P))(A))-[F]_(bold(italic(P))(A)) in Ker (k_0(A))$, где
  $F=A^n$ и $P tensor_R L tilde.eq Lambda^n$. Утверждение о коммутативности в
  точности и означает, что в группе $G_0(A)$

  $
    [P]_(bold(italic(M))(A))-[F]_(bold(italic(M))(A))
    =[P tensor_A B]_(bold(italic(M))(A))-[F tensor_A B]_(bold(italic(M))(A)).
  $

  Так как теперь мы предполагаем, что кольцо $A$ удовлетворяет условию Картана,
  то можно применить приведенную выше конструкцию и получить точную
  последовательность $0->P->F->M->0$, в которой $T^(-1) M=0$. Тогда утверждения
  @cond:order-comparison-cokernel-base-change и
  @cond:order-comparison-resolution-base-change (с заменой $P'$ и $F'$ там на
  $P$ и $F$ здесь) позволяют сделать вывод о том, что

  $
    [P]_(bold(italic(M))(A))-[F]_(bold(italic(M))(A))
    =-[M]_(bold(italic(M))(A))
    =[P tensor_A B]_(bold(italic(M))(A))-[F tensor_A B]_(bold(italic(M))(A)),
  $

  что и требовалось доказать.
]

#proposition[
  Сохраним обозначения предложения @prop:order-maximal-order-comparison. Пусть
  $frak(c)$ — двусторонний $B$-идеал, содержащийся в $A$ и являющийся
  $R$-решеткой в $Lambda$ (например, $frak(c)=frak(c)_0 B$ или $frak(c)$ есть
  $frak(c)_(B slash A)$, т. е. кондуктор). Тогда длина $R$-модулей
  $A'=A slash frak(c)$ и $B'=B slash frak(c)$ конечна, и мы получаем точную
  последовательность Майера — Вьеториса

  $
    K_1(A)->K_1(A') plus.o K_1(B)->K_1(B')->K_0(A)->
    K_0(A') plus.o K_0(B)->K_0(B').
  $

  Группы $K_0(A')$ и $K_0(B')$ являются свободными абелевыми группами конечного
  ранга, а отображение $U(B')->K_1(B')$ сюръективно.
  #source(412)
  Если кольцо $A$ коммутативно, то $B$ как раз является целым замыканием кольца
  $A$ в $Lambda$, и мы получаем точную последовательность

  $ 0 -> frac(U(B'), U(A') dot U(B)') -> Pic (A) -> Pic (B) -> 0, $

  где $U(B)'=Im (U(B)->U(B'))$.
] <prop:order-conductor-mayer-vietoris>

#proof[
  Так как диаграмма

  $ #diagram-conductor-pullback() $

  является расслоенным произведением (см. @exm:conductor-pullback), то она
  приводит нас к выписанной последовательности Майера — Вьеториса, а также к
  последовательности

  $
    U(A)->U(A') plus.o U(B)->U(B')->Pic (A)->
    Pic (A') plus.o Pic (B)->Pic (B')
  $

  в случае коммутативного кольца $A$ (см. @th:projective-k-mayer-vietoris).
  Заметим, что $A'$ и $B'$ являются конечно порожденными периодическими
  $R$-модулями, и, следовательно, их длины конечны. Таким образом, кольца $A'$ и
  $B'$ полулокальны. Теперь из @prop:semilocal-k-groups следует, что группы
  $K_0(A')$ и $K_0(B')$ являются свободными абелевыми группами конечного ранга,
  а отображение $U(B')->K_1(B')$ сюръективно. Кроме того, если кольцо $A$
  коммутативно, то из @prop:semilocal-picard-trivial вытекает, что
  $Pic (A')=0=Pic (B')$. Последнюю точную последовательность в предложении можно
  получить, учитывая этот факт из приведенной последовательности Майера —
  Вьеториса для групп $Pic$. Предложение доказано.
]
