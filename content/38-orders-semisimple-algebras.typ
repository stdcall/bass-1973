#import "main-defs.typ": (
  End, Hom, Ht, Int, Nr, Nrd, Tr, Trd, U, ann, det, hd, idx, maxSpec,
  moduleCategory, name-idx, source, spec, supp, symbol-idx, tensor,
)
#import "statements.typ": (
  condition-item, condition-list, corollary, numbered-condition, proof,
  proposition, theorem,
)

== Порядки в полупростых алгебрах
<sec:orders-semisimple-algebras>

Зафиксируем область целостности $R$ с полем частных $L$. Наша задача — изучить
некоторые $R$-алгебры, содержащиеся в полупростых $L$-алгебрах. Материал этого
параграфа будет применяться в гл. @ch:finite-group-induction к таким примерам,
как групповые кольца $A = R pi$ конечной группы $pi$.

Пусть $V in bold(M)(L)$. Тогда _$R$-решеткой_ в $V$ назовем $R$-подмодуль
$M subset V$, удовлетворяющий следующим равносильным условиям:
#condition-list[
  #condition-item[$M L = V$ и $M$ содержится в конечно порожденном $R$-модуле
    $N subset V$;] <cond:lattice-spans-bounded>

  #condition-item[существуют свободные $R$-модули $F,F'$ ранга $[V\:L]$, такие,
    что $F subset M subset F' subset V$.] <cond:lattice-free-bounds>
]
#idx("R-решетка")
Так как $L$ — локализация кольца $R$ ($L = R_((0))$), то вложение $M subset V$
индуцирует мономорфизм $M tensor_R L arrow.r V$, образом которого служит $M L$.
Если $F subset V$ — свободный $R$-модуль ранга $[V\:L]$, то из подсчета
размерности ясно, что $F L = V$. Таким образом, $#[
  @cond:lattice-free-bounds] => (1)$. Обратно, если $M L = V$, то пусть $F$ есть
$R$-модуль, #source(129) порожденный $L$-базисом модуля $V$ в $M$. Пусть
$x in V$. Так как $(V slash F) tensor_R L = 0$, то $x a in F$ для некоторого
$a != 0$. Рассматривая произведения, можно найти элемент $a$, обладающий этим же
свойством уже для конечного множества $x$-ов. Следовательно, если
$N in bold(M)(R)$, то $N a subset F$ для некоторого $a != 0$ из $R$. Таким
образом, $F subset M subset a^(-1)F$, что доказывает $#[
  @cond:lattice-free-bounds]$.

Аналогичные рассуждения показывают, что если $M$ есть $R$-решетка в $V$ и $N$ —
некоторый $R$-подмодуль в $V$, то $N$ является $R$-решеткой тогда и только
тогда, когда $a M subset N subset a^(-1)M$ для некоторого $a != 0$ из $R$. Более
общий случай: $N$ является $R$-решеткой, если его можно поместить между двумя
$R$-решетками. Эти замечания, как и следующие предложения, оставляем в качестве
упражнения. Все $L$-модули предполагаются конечномерными.

#proposition(title: [Бурбаки @bib:Bourbaki1971e, § 4, п. 1, предложение 3])[
  #condition-list[
    #condition-item[Если $M_1$ и $M_2$ — две $R$-решетки в $V$, то решетками
      являются $M_1+M_2$ и $M_1 inter M_2$.] <cond:lattice-sum-intersection>

    #condition-item[Если $W subset V$ суть $L$-модули и если $M$ есть
      $R$-решетка в $V$, то $M inter W$ является $R$-решеткой в
      $W$.] <cond:lattice-subspace-intersection>

    #condition-item[Если $f\: V_1 times dots times V_n arrow.r V$ — полилинейное
      отображение $L$-модулей и если $M_i$ есть $R$-решетка в $V_i$
      ($1 <= i <= n$), то $R$-модуль, порожденный $f(M_1 times dots times M_n)$,
      является $R$-решеткой в $L$-модуле, порожденном
      $f(V_1 times dots times V_n)$.] <cond:lattice-multilinear-image>

    #condition-item[Пусть $M subset V$ и $N subset W$ — две $R$-решетки. Тогда
      $(N\:M)$ есть $R$-решетка в $Hom_L (V,W)$, где
      $(N\:M) = {h | h(M) subset N}$ и $Hom_R (M,N)$ канонически
      изоморфны.] <cond:lattice-hom-module>

    #condition-item[Если $S$ — мультипликативная система в $R without {0}$ и
      если $M$ — некоторая $R$-решетка в $V$, то $S^(-1)M$ является
      $S^(-1)R$-решеткой в $V$.] <cond:lattice-localization>
  ]
] <prop:lattice-elementary-properties>
Следующее предложение — основа для построения и расширения решеток.

#proposition[
  Пусть $R$ — кольцо Крулля, и пусть $M$ — произвольная $R$-решетка в $L$-модуле
  $V$. Предположим, что для каждого $frak(p) in Ht_1(R)$ нам задана
  $R_(frak(p))$-решетка $N_(frak(p))$ в $V$. Тогда для существования $R$-решетки
  $N'$ в $V$, такой, что $N'_(frak(p)) = N_(frak(p))$ для всех
  $frak(p) in Ht_1(R)$, необходимо и достаточно, чтобы $N_(frak(p)) =
  M_(frak(p))$ для всех, кроме конечного числа $frak(p) in Ht_1(R)$. В этом
  случае $breve(N) = inter_(frak(p)) N_(frak(p))$ ($frak(p) in Ht_1(R)$)
  является наибольшей такой $R$-решеткой.
] <prop:lattice-height-one-patching>
#proof[
  Покажем сначала, что если $N'$ — произвольная решетка (в $V$), то
  $M_(frak(p)) = N'_(frak(p))$ почти для всех $frak(p)$. Действительно, можно
  выбрать $a != 0$ в $R$ так, что $a M subset N' subset a^(-1)M$ и
  $a in U(R_(frak(p)))$ почти для всех $frak(p)$.

  Предположим далее, что $N_(frak(p)) = M_(frak(p))$ почти для всех $frak(p)$ и
  положим $breve(N) = inter_(frak(p)) N_(frak(p))$ (здесь $frak(p)$ пробегают
  множество $Ht_1(R)$). Если $N'$ — #source(130) такая решетка, что
  $N'_(frak(p)) = N_(frak(p))$ для всех $frak(p)$, то ясно, что
  $N' subset breve(N)$. Таким образом, утверждение предложения будет доказано,
  как только мы покажем, что $breve(N)$ является $R$-решеткой. В силу первой
  части доказательства наши предположения о $N_(frak(p))$ не зависят от решетки
  $M$, с которой мы их сравниваем. Таким образом, не теряя общности рассуждения,
  можно считать, что решетка $M$ является $R$-свободной. Так как
  $R = inter_(frak(p)) R_(frak(p))$, то тогда $M = inter_(frak(p)) M_(frak(p))$.

  Положим $I = {frak(p) | M_(frak(p)) != N_(frak(p))}$ (это конечное множество).
  Для каждого $frak(p) in I$ найдется элемент $a_(frak(p)) != 0$ из
  $R_(frak(p))$, такой, что
  $
    a_(frak(p))M_(frak(p)) subset N_(frak(p)) subset
    a_(frak(p))^(-1)M_(frak(p)).
  $
  Конечно, можно выбрать $a_(frak(p)) in R$ (возможно, изменяя его на обратимый
  элемент из $R_(frak(p))$). Положим
  $a = product_(frak(p) in I) a_(frak(p)) in R$. Тогда
  $a M_(frak(p)) subset N_(frak(p)) subset a^(-1)M_(frak(p))$ для всех
  $frak(p)$. Мы добились этого для $frak(p) in I$, и
  $M_(frak(p)) = N_(frak(p))$, если $frak(p) in.not I$. Переходя к пересечениям,
  получаем, что $a M subset breve(N) subset a^(-1)M$ (поскольку
  $M = inter_(frak(p)) M_(frak(p))$). Таким образом, $breve(N)$ — решетка, что и
  требовалось доказать.
]

Назовем $R$-решетку $M$ в $V$ _дивизориальной_, если
$M = inter_(frak(p)) M_(frak(p))$. #idx("дивизориальная R-решетка")#idx(
  "R-решетка",
  "дивизориальная",
)

#corollary[
  Если $M$ есть $R$-решетка в $V$, то дивизориальные $R$-решетки в $M$
  удовлетворяют условию обрыва возрастающих цепей.
] <cor:divisorial-lattice-ascending-chain>
#proof[
  Пусть $D^1 subset D^2 subset dots$ — цепь дивизориальных $R$-решеток, лежащих
  в $M$. Пусть $I = {frak(p) in Ht_1(R) | D_(frak(p))^1 != M_(frak(p))}$. Если
  $frak(p) in I$, то, поскольку $M_(frak(p))$ является нётеровым
  $R_(frak(p))$-модулем, цепь $D_(frak(p))^1 subset D_(frak(p))^2 subset dots$
  стабилизируется. Так как множество $I$ конечно, то найдется такое $n$, что
  $D_(frak(p))^n = D_(frak(p))^m$ для всех $m >= n$ и всех $frak(p) in I$. Для
  $frak(p) in.not I$ мы знаем, что $D_(frak(p))^1 = M_(frak(p))$. Следовательно,
  $D^m = inter_(frak(p)) D_(frak(p))^m = inter_(frak(p)) D_(frak(p))^n =
  D^n$ для $m >= n$, поскольку решетки $D$ дивизориальные, что и требовалось
  доказать.
]

#corollary[
  Пусть $M$ и $N$ — некоторые $R$-решетки в $V$ и $W$ соответственно. Пусть $S$
  — мультипликативная система в $R$. Допустим, что $N$ — дивизориальная решетка.
  Тогда $S^(-1)(N\:M) = ((S^(-1)N)\:(S^(-1)M))$. Кроме того,
  $ breve((N\:M)) = (N\:M) = (N\:breve(M)). $
] <cor:divisorial-lattice-hom-localization>
#proof[
  Предположим, что $h\: V arrow.r W$ и $h S^(-1)M subset S^(-1)N$. Положим
  $I = {frak(p) in Ht_1(R) | h M_(frak(p)) subset.not N_(frak(p))}$. Это
  конечное #source(131) множество, и если $frak(p) in I$, то
  $frak(p) inter S != emptyset$. Выбирая $a_(frak(p)) in frak(p) inter S$ так,
  что $a_(frak(p)) h M_(frak(p)) subset N_(frak(p))$ для каждого $frak(p) in
  I$, и полагая $s = product_(frak(p) in I) a_(frak(p))$, видим, что
  $s h M_(frak(p)) subset N_(frak(p))$ для всех $frak(p) in I$ и, следовательно,
  для всех $frak(p) in Ht_1(R)$. Тогда
  $s h M subset inter_(frak(p)) N_(frak(p)) = breve(N) = N$, и поэтому
  $h = (s h) slash s in S^(-1)(N\:M)$. Обратное включение
  $S^(-1)(N\:M) subset (S^(-1)N\:S^(-1)M)$ очевидно.

  Используя первую часть этого доказательства и тот факт, что $breve(N) = N$,
  получаем соотношение
  $(N\:breve(M)) subset (N\:M) subset breve((N\:M)) =
  inter_(frak(p))(N\:M)_(frak(p)) =
  inter_(frak(p))(N_(frak(p))\:M_(frak(p))) = {h | h M_(frak(p)) subset
  N_(frak(p))$
  для всех $frak(p)} = (breve(N)\:breve(M)) = (N\:breve(M))$, что и требовалось
  доказать.
]

_До конца этого параграфа будем предполагать, что $R$ — кольцо Крулля._ Если
$Lambda$ — конечномерная $L$-алгебра, то назовем $R$-алгебру $A subset Lambda$
_$R$-порядком_ в $Lambda$, если $A L = Lambda$ и если каждый элемент из $A$
является целым над $R$. #idx("R-порядок")

Пусть $M$ есть $R$-решетка в $Lambda$. Тогда $M dot M$ также является
$R$-решеткой (см. @prop:lattice-elementary-properties
@cond:lattice-multilinear-image), и поэтому $a M dot M subset M$ для некоторого
$a != 0$ из $R$. Полагая $N = a M$, видим, что $N dot N subset N$, и поэтому
$R dot 1 + N$ будет $R$-алгеброй в $Lambda$, которая также является и
$R$-решеткой. В частности, это $R$-порядок в $Lambda$#footnote[Это следует из
  того, что элемент $x in Lambda$ является целым над $R$ в том и только том
  случае, когда он цел над $R_(frak(p))$ для каждого $frak(p) in Ht_1(R)$. —
  _Прим. ред._], и поэтому $R$-порядки существуют. Наша первая цель — показать,
что если алгебра $Lambda$ полупроста, то любой $R$-порядок содержится в
максимальном, а максимальные порядки являются иногда $R$-решетками.

Предположим сначала, что $Lambda$ — простая алгебра с центром $L$. Из теории
центральных простых алгебр (Бурбаки @bib:Bourbaki1966b) вытекает существование
расширения $L'$ поля $L$ и изоморфизма
$alpha\: Lambda tensor_L L' arrow.r M_n (L')$ (где $[Lambda\:L] = n^2$). В этом
случае определим _редуцированный след_ и _редуцированную норму_:
$
  Trd_(Lambda slash L)(x) = Tr(alpha(x tensor 1)), quad Nrd_(Lambda slash
  L)(x) = det(alpha(x tensor 1)).
$
#idx("редуцированный след")#idx("редуцированная норма")#name-idx(
  "Бурбаки (Bourbaki N.)",
)
#symbol-idx($Nr$, sort: "Nr", group: "operators", order: 63)
#symbol-idx($Tr$, sort: "Tr", group: "operators", order: 74)
Поскольку изоморфизмы $alpha$ определены с точностью до внутреннего автоморфизма
алгебры $M_n (L')$, то наши определения не зависят от выбора $alpha$. Легко
видеть, что они не меняются при расширении поля $L'$ и, следовательно, не
зависят от поля $L'$ (в чем можно убедиться, если вложить два расширения в одно
общее). Наконец, известно, что в качестве $L'$ можно выбрать расширение Галуа,
скажем, с группой $G$. Тогда проверяется, что $Trd_(Lambda slash L)(x)$ и
$Nrd_(Lambda slash L)(x)$ для $x in Lambda$ остаются неподвижными при действии
группы $G$ и, следовательно, лежат в $L$. Получаем $L$-линейное отображение
$ Trd_(Lambda slash L)\: Lambda arrow.r L $
#source(132) и мультипликативное отображение
$ Nrd_(Lambda slash L)\: Lambda arrow.r L. $
Кроме того,
$ x in U(Lambda) <=> Nrd_(Lambda slash L)(x) != 0 $
и
$
  Lambda times Lambda arrow.r L, quad (x,y) arrow.r.bar Trd_(Lambda slash
  L)(x y)
$
является невырожденной билинейной формой. Первое утверждение основано на том
замечании, что если $x in U(Lambda)$, то $x^(-1) in L[x]$. Второе следует из
того, что форма следа на $M_n (L')$ невырожденная, а вырожденная форма не может
стать невырожденной при расширении основного поля.

Предположим, что элемент $x in Lambda$ является целым над $R$. Тогда (в
приведенных выше обозначениях) элемент $y = alpha(x tensor 1) in M_n (L')$
является целым над $R$. Из предложения
@prop:integral-matrix-characteristic-polynomial следует, что коэффициенты
многочлена $P(t) = det(t dot 1 - y)$ являются целыми над $R$. В частности,
поскольку кольцо $R$ целозамкнуто: #numbered-condition[_если элемент
$x in Lambda$ является целым над $R$, то $Trd_(Lambda slash L)(x)$ и
$Nrd_(Lambda slash L)(x)$ лежат в $R$._] <eq:reduced-trace-integrality>

Пусть теперь $Lambda$ — произвольная полупростая $L$-алгебра. Пусть
$Lambda = product_i Lambda_i$, где $Lambda_i$ — простая алгебра с центром $C_i$.
Определим тогда
$ Trd_(Lambda_i slash L) = Tr_(C_i slash L) compose Trd_(Lambda_i slash C_i) $
и
$ Trd_(Lambda slash L)((x_i)) = sum_i Trd_(Lambda_i slash L)(x_i). $
Аналогично определим
$Nrd_(Lambda slash L)((x_i)) = product_i Nrd_(Lambda_i slash L)(x_i)$, где
$Nrd_(Lambda_i slash L) = Nr_(C_i slash L) compose Nrd_(Lambda_i slash C_i)$.
Легко видеть, что свойство @eq:reduced-trace-integrality остается справедливым и
в этой более общей ситуации.

Если каждое поле $C_i$ является сепарабельным расширением поля $L$, то назовем
$Lambda$ _сепарабельной $L$-алгеброй_. Это эквивалентно тому, что алгебра
$Lambda tensor_L L'$ полупроста для любого поля $L'$, являющегося расширением
поля $L$. В этом случае отображение $Tr_(C_i slash L)\: C_i arrow.r L$ ненулевое
для каждого $i$, и из этого легко следует, что билинейная форма
$(x,y) arrow.r.bar Trd_(Lambda slash L)(x y)$ невырожденная. #idx(
  "сепарабельная L-алгебра",
)

#theorem[
  Как и раньше, пусть $R$ — кольцо Крулля с полем частных $L$, и пусть $Lambda$
  — полупростая конечномерная $L$-алгебра. Тогда любой $R$-порядок $A$ в
  $Lambda$ содержится в максимальном $R$-порядке. Если $Lambda$ — сепарабельная
  $L$-алгебра или если $R$ — конечно порожденная алгебра над полем, то $A$
  является $R$-решеткой в $Lambda$. Кроме того, в этом случае порядок $A$
  максимален тогда и только тогда, когда $A$ является дивизориальной
  $R$-решеткой и $A_(frak(p))$ — максимальный $R_(frak(p))$-порядок в $Lambda$
  для каждого $frak(p) in Ht_1(R)$.
] <th:maximal-orders-existence>
#proof[
  _Случай 1._ Алгебра $Lambda$ сепарабельна над $L$.

  #source(133) Выберем базис $e_1,dots,e_n in A$ для $Lambda$. Так как
  $Trd_(Lambda slash L)(x y)$ — невырожденная форма, то можно выбрать
  $e'_1,dots,e'_n in Lambda$ так, что
  $Trd_(Lambda slash L)(e_i e'_j) = delta_(i j)$. Если $B$ является
  $R$-порядком, содержащим $A$, то запишем $b = sum_j e'_j a_j$, где $a_j in L$.
  Так как элемент $e_i b in B$ является целым над $R$ для каждого $i$, то в силу
  утверждения @eq:reduced-trace-integrality
  $ Trd_(Lambda slash L)(e_i b) = sum_j Trd(e_i e'_j)a_j = a_i in R. $
  Следовательно, $B subset sum_j e'_j R = F$, и поэтому $B$ является
  $R$-решеткой в $Lambda$. Кроме того, $breve(B) = inter_(frak(p)) B_(frak(p))$
  ($frak(p) in Ht_1(R)$) — дивизориальная $R$-решетка и, следовательно,
  $R$-порядок, содержащий $B$ (см. @prop:lattice-height-one-patching). В силу
  следствия @cor:divisorial-lattice-ascending-chain дивизориальные $R$-решетки в
  $F$ удовлетворяют условию обрыва возрастающих цепей, и поэтому существует
  максимальная такая решетка, содержащая $A$. Из сделанных выше замечаний
  следует, что она является максимальным $R$-порядком.

  Если $A$ — максимальный $R$-порядок, то, как мы видели, он является
  дивизориальной $R$-решеткой. Если $A_(frak(p)_0)$ не является максимальным над
  $R_(frak(p)_0)$ для некоторого $frak(p)_0 in Ht_1(R)$, то, используя
  @prop:lattice-height-one-patching, построим дивизориальный $R$-порядок $B$,
  такой, что $B_(frak(p)) = A_(frak(p))$, если $frak(p) != frak(p)_0$ и
  $B_(frak(p)_0)$ строго содержит $A_(frak(p)_0)$. Это противоречит
  максимальности порядка $A$.

  Обратно, предположим, что $A$ — дивизориальный $R$-порядок и что $A_(frak(p))$
  — максимальный порядок для всех $frak(p) in Ht_1(R)$. Тогда, если $B$ является
  $R$-порядком, содержащим $A$, то $B_(frak(p)) = A_(frak(p))$ для всех
  $frak(p)$, и поэтому $B subset breve(A) = A$.

  Заметим, что в рассуждениях последних двух абзацев было использовано лишь то,
  что каждый $R$-порядок в $Lambda$ является $R$-решеткой.

  _Общий случай._ Запишем $Lambda = product_i Lambda_i$, где $Lambda_i$ —
  простая алгебра с центром $C_i$. Пусть $R'_i$ — целое замыкание кольца $R$ в
  $C_i$. Если $A_i$ — проекция порядка $A$ в $Lambda_i$, то очевидно, что
  $R'_i[A_i]$ является $R$-порядком в $Lambda_i$ (см.
  @cor:integral-closure-transitivity). В силу предложения
  @th:integral-closure-finite-field-extension $R'_i$ — кольцо Крулля, являющееся
  конечномерной $R$-алгеброй в том случае, когда $R$ — конечно порожденная
  алгебра над полем.

  В силу разобранного случая 1 можно вложить $R'_i[A_i]$ в максимальный
  $R'_i$-порядок $B_i$ в $Lambda_i$, и $B_i$ является $R'_i$-решеткой. Очевидно,
  что $B_i$ — максимальный $R$-порядок в $Lambda_i$ и что $B_i$ является
  $R$-решеткой в том случае, когда $R'_i$ — конечномерная $R$-алгебра.

  Легко видеть теперь, что $B = product_i B_i$ является максимальным
  $R$-порядком, содержащим $A$. Действительно, любой порядок, содержащий $B$,
  должен разлагаться в произведение порядков, содержащих $B_i$, которые
  максимальны. Если $R$ — конечно порожденная алгебра над полем, то, как мы
  видели, каждая алгебра $B_i$ и, #source(134) следовательно, также $B$ и $A$
  являются $R$-решетками. В силу замечания, сделанного в конце разбора случая 1,
  это завершает доказательство теоремы.
]

В оставшейся части этого параграфа будем предполагать, что:
#numbered-condition[_$R$ — кольцо Крулля с полем частных $L$; $Lambda$ —
полупростая конечномерная $L$-алгебра; каждый $R$-порядок в $Lambda$ является
$R$-решеткой._] <eq:orders-lattice-standing-assumption>

Пусть $A$ есть $R$-порядок в $Lambda$, и пусть $V in bold(M)(Lambda)$. Будем
говорить, что $R$-решетка в $V$ является _$A$-решеткой_, если она является
$A$-подмодулем в $V$. Такие всегда существуют. Действительно, пусть
$M subset Lambda$ — конечно порожденный $R$-модуль, содержащий $A$ (существующий
в силу предположения @eq:orders-lattice-standing-assumption), и пусть
$(e_i)_(1 <= i <= n)$ есть $L$-базис для $V$. Тогда $sum_i e_i A$ является
$A$-подмодулем в $V$, содержащим базис и лежащим в конечно порожденном
$R$-модуле $sum_i e_i M$.

Применительно к случаю $V = Lambda$ будем говорить о _левых_, _правых_ и
_двусторонних $A$-решетках_ в обычном смысле. #idx("A-решетка")#idx(
  "A-решетка",
  "левая",
)#idx("A-решетка", "двусторонняя")

#theorem[
  Допустим, что $R$ — дедекиндово кольцо и что $A$ — максимальный $R$-порядок в
  $Lambda$. Пусть $maxSpec(A)$ — множество максимальных двусторонних идеалов в
  $A$. Тогда множество двусторонних $A$-решеток в $Lambda$ является относительно
  умножения свободной абелевой группой с базисом $maxSpec(A)$.
] <th:maximal-order-two-sided-lattices>
_Замечания._ Мы используем лишь то соображение, что $R$ — нётерова целозамкнутая
область целостности размерности $<= 1$. Таким образом, в частном случае
$Lambda = L$ из этой теоремы будет следовать, что кольцо $R$ дедекиндово, и тем
самым будет доказана импликация
$#[@cond:dedekind-noetherian-normal-dimension-one] => #[@cond:dedekind-domain]$
из теоремы @th:dedekind-domain-characterizations, которая была отложена до этого
момента.

Назовем $M in moduleCategory hyph R$ _периодическим модулем_ (соответственно
_модулем без кручения_), если отображение $M arrow.r M tensor_R L$ нулевое
(соответственно мономорфизм). Будем применять эти термины, в частности, к
$A$-модулям. Если $M in bold(M)(A)$ — периодический модуль, то $ann_R (M) != 0$,
и поэтому $supp(M)$ является собственным замкнутым подмножеством в $spec(R)$.
Так как последнее пространство неприводимо и его размерность $<= 1$, то
$supp(M)$ должен быть конечным множеством максимальных идеалов. Следовательно,
из @prop:finite-length-support-characterizations можно заключить, что: _если
модуль $M in bold(M)(A)$ периодический, то длина $R$-модуля $M$ конечна_. В силу
предложения @prop:maximal-primitive-finite-algebra, кроме того, убеждаемся, что
$[frak(p) in maxSpec(A)] <=>$ [идеал $frak(p)$ первичный и модуль
$A slash frak(p)$ периодический]. Но если $frak(a) subset A$ идеал, то очевидно,
что [модуль $A slash frak(a)$ периодический]
$<=> [A tensor_R L = frak(a) tensor_R L] <=>$ [$frak(a)$ является $R$-решеткой].
Таким образом, если $frak(p) subset A$ — двусторонняя $A$-решетка, то
$[frak(p) in maxSpec(A)] <=>$ [идеал $frak(p)$ первичный]. Перейдем теперь к
доказательству. #idx("периодический модуль")#idx("модуль без кручения")

#source(135)
#proof(head: [Доказательство теоремы @th:maximal-order-two-sided-lattices.])[
  #condition-list[
    Мы проведем его в несколько шагов. Все рассматриваемые решетки лежат в
    $Lambda$.

    #condition-item[_Если $frak(a)$ — левая $A$-решетка, то
    $A = {x in Lambda | x frak(a) subset frak(a)}$, и аналогичное утверждение
    справедливо для правых решеток._] <cond:maximal-order-lattice-stabilizer>
    #idx("A-решетка", "правая")

    Действительно, ${x in Lambda | x frak(a) subset frak(a)}$, очевидно,
    является $R$-порядком, содержащим $A$, и $A$ максимален.

    #condition-item[_Если $frak(a) subset A$ — двусторонняя $A$-решетка, то
    $frak(a)$ содержит произведение элементов из
    $maxSpec(A)$._] <cond:maximal-order-ideal-contains-product>

    Если $frak(a) in maxSpec(A)$, то утверждение очевидно. В противном случае
    идеал $frak(a)$ не является первичным. Таким образом, найдутся два
    двусторонних идеала $frak(b)$ и $frak(c)$, строго содержащие идеал $frak(a)$
    (и, следовательно, являющиеся решетками) и такие, что
    $frak(b) dot frak(c) subset frak(a)$. Используя нётеровость кольца, мы можем
    считать, что идеалы $frak(b)$ и $frak(c)$ содержат произведения элементов из
    $maxSpec(A)$. Следовательно, это же верно и для идеала $frak(a)$.

    Если $frak(a)$ является двусторонней $A$-решеткой, то положим
    $ overline(frak(a)) = {x in Lambda | x frak(a) subset A}. $
    Так как $(A overline(frak(a)) A)frak(a) =
    A overline(frak(a)) frak(a) subset A A = A$, то мы видим, что
    $overline(frak(a))$ также является двусторонней $A$-решеткой.

    #condition-item[_Если $frak(p) in maxSpec(A)$, то
    $overline(frak(p)) != A$._] <cond:maximal-order-inverse-ideal-nontrivial>

    Выберем элемент $a != 0$ в $R$, такой, что $a A subset frak(p)$, и выберем
    элементы $frak(p)_1,dots,frak(p)_n in maxSpec(A)$, такие, что
    $frak(p)_1 dots frak(p)_n subset a A$ (используя утверждение
    @cond:maximal-order-ideal-contains-product). Предположим также, что $n$
    является наименьшим среди возможных. Так как идеал $frak(p)$ первичный, то
    он содержит один из идеалов $frak(p)_i$ и, следовательно,
    $frak(p) = frak(p)_i$, поскольку идеал $frak(p)_i$ максимальный. Значит,
    можем записать, что $frak(a) frak(p) frak(b) subset a A$, где
    $frak(a) = frak(p)_1 dots frak(p)_(i-1)$ и
    $frak(b) = frak(p)_(i+1) dots frak(p)_n$. Итак,
    $
      a^(-1)frak(a) frak(p)frak(b) subset A => frak(b) a^(-1)frak(a)
      frak(p)frak(b) subset frak(b) => \
      => frak(b) a^(-1)frak(a) frak(p) subset A quad
      ("шаг" #[@cond:maximal-order-lattice-stabilizer]) => \
      => frak(b) a^(-1)frak(a) subset overline(frak(p)).
    $
    Так как $frak(b) frak(a)$ является произведением $n - 1$ простых идеалов, то
    из минимальности числа $n$ следует, что $frak(b) frak(a) subset.not a A$, и
    поэтому $a^(-1)frak(b) frak(a) subset.not A$. Таким образом,
    $overline(frak(p)) != A$, что и требовалось доказать.

    #condition-item[_Если $frak(p) in maxSpec(A)$, то
      $frak(p)overline(frak(p)) = A = overline(frak(p))frak(p)$._
    ] <cond:maximal-order-maximal-ideal-invertible>

    Так как $A subset overline(frak(p))$, то
    $frak(p) subset overline(frak(p))frak(p) subset A$, и поэтому из
    максимальности идеала $frak(p)$ следует, что
    $overline(frak(p))frak(p) = frak(p)$ или $overline(frak(p))frak(p) = A$.
    Если $overline(frak(p))frak(p) = frak(p)$, то из утверждения
    @cond:maximal-order-lattice-stabilizer следует, что
    $overline(frak(p)) subset A$, но это противоречит утверждению
    @cond:maximal-order-inverse-ideal-nontrivial. Таким образом,
    $overline(frak(p))frak(p) = A$. Но
    $frak(p)overline(frak(p))frak(p) = frak(p)A$, и поэтому из
    @cond:maximal-order-lattice-stabilizer следует, что
    $frak(p)overline(frak(p)) subset A$, и очевидно, что
    $frak(p) subset frak(p)overline(frak(p))$. Рассуждая в точности так же, как
    раньше, получим, что $frak(p)overline(frak(p)) = A$.

    #source(136)
    #condition-item[_Если $frak(p)_1,frak(p)_2 in maxSpec(A)$, то
      $frak(p)_1 frak(p)_2 = frak(p)_2 frak(p)_1$._
    ] <cond:maximal-order-maximal-ideals-commute>

    Пусть $frak(a) = overline(frak(p))_1 frak(p)_2 frak(p)_1$. Так как
    $frak(p)_2 frak(p)_1 subset frak(p)_1$, то $frak(a) subset A$. Поскольку
    $frak(p)_1 frak(a) = frak(p)_2 frak(p)_1 subset frak(p)_2$ и так как
    $frak(p)_2$ является первичным идеалом, не содержащим $frak(p)_1$, то
    $frak(a) subset frak(p)_2$. Следовательно,
    $frak(p)_2 frak(p)_1 = frak(p)_1 frak(a) subset frak(p)_1 frak(p)_2$.
    Обратное включение устанавливается симметрично.

    #condition-item[_Двусторонняя $A$-решетка $frak(a) subset A$ разлагается
    однозначно (с точностью до порядка) в произведение элементов из
    $maxSpec(A)$._] <cond:maximal-order-ideal-factorization>

    Можно считать, что $frak(a) != A$, поэтому выберем идеал
    $frak(p) in maxSpec(A)$, содержащий $frak(a)$. Тогда
    $frak(a) subset overline(frak(p))frak(a) subset A$, и из утверждений
    @cond:maximal-order-lattice-stabilizer и
    @cond:maximal-order-inverse-ideal-nontrivial следует, что
    $frak(a) != overline(frak(p))frak(a)$. В силу нётеровости можно считать, что
    идеал $overline(frak(p))frak(a)$ является произведением элементов из
    $maxSpec(A)$ и, следовательно, таким же является идеал
    $frak(a) = frak(p)(overline(frak(p))frak(a))$.

    Предположим, что $frak(p)_1 dots frak(p)_n = frak(q)_1 dots frak(q)_m$, где
    $frak(p)_i$ и $frak(q)_j$ принадлежат $maxSpec(A)$. Так как $frak(p)_1$ —
    первичный идеал и содержит $frak(q)_1 dots frak(q)_m$, то он должен
    содержать некоторый из идеалов $frak(q)_i$. Используя утверждение
    @cond:maximal-order-maximal-ideals-commute для перенумерации сомножителей,
    можно считать, что $frak(p)_1 supset frak(q)_1$. Так как идеал $frak(q)_1$
    максимален, то $frak(p)_1 = frak(q)_1$. Умножим наше равенство на
    $overline(frak(p))_1$ и получим
    $frak(p)_2 dots frak(p)_n = frak(q)_2 dots frak(q)_m$. Единственность
    следует из индукции по $n$ (случай $n = 1$ очевиден).

    Наконец, если $frak(a)$ — произвольная двусторонняя $A$-решетка, то
    $b frak(a) subset A$ для некоторого элемента $b != 0$ в $R$, и поэтому
    $frak(a) = overline((b A))(b frak(a))$ является произведением элементов из
    $maxSpec(A)$ и их обратных. Если бы было справедливо соотношение
    $A = product_(frak(p)) frak(p)^(n_(frak(p)))$ ($frak(p) in maxSpec(A)$,
    $n_(frak(p)) = 0$ почти для всех $frak(p)$), то мы могли бы перенести все
    сомножители с $n_(frak(p)) < 0$ влево и получить соотношение в $A$,
    противоречащее @cond:maximal-order-ideal-factorization. Таким образом,
    $maxSpec(A)$ является свободным базисом группы двусторонних $A$-решеток, что
    и требовалось доказать.
  ]
]

#theorem[
  Пусть $R$ — дедекиндово кольцо, и пусть $A$ есть $R$-порядок в $Lambda$. Тогда

  #condition-list[
    #condition-item(format: "cyrillic")[[Кольцо $A$ наследственно справа (см. §
      @sec:homological-dimension)] $<=>$ [каждый идеал $frak(p) in maxSpec(A)$
      является проективным правым $A$-модулем]. В этом случае
      $hd_A (M) = hd_R (M)$ для всех $M in bold(M)(A)$, и
      $[M in bold(P)(A)] <=>$ [модуль $M$ без кручения]. Кроме того, каждый
      модуль $M in bold(M)(A)$ является прямой суммой своего периодического
      подмодуля и модулей, изоморфных правым
      идеалам.] <cond:hereditary-order-projective-maximal-ideals>

    #condition-item(format: "cyrillic")[[$A$ является максимальным порядком]
      $<=>$ [кольцо $A$ наследственно справа, и каждый точный модуль
      $P in bold(P)(A)$ (т. е. $ann_A (P) = 0$) строго проективен (т. е. в этом
      случае является образующим категории $moduleCategory hyph A$)].
    ] <cond:maximal-order-faithful-projective-generator>
  ]
] <th:hereditary-maximal-order-characterizations>
#proof[
  @cond:hereditary-order-projective-maximal-ideals Если модуль $M in bold(M)(A)$
  без кручения, то $M$ ($= M tensor_R 1$) является $A$-решеткой в
  $M tensor_R L = V$. Так как алгебра $Lambda$ полупроста, то
  $V plus.o W approx.eq Lambda^n$ для некоторого #source(137) $n >= 0$. Пусть
  $N$ есть $A$-решетка в $W$, тогда $M plus.o N$ является $A$-решеткой в
  $Lambda^n$. Так как $A^n subset Lambda^n$ — другая такая $A$-решетка, то можем
  найти элемент $a != 0$ в $R$, для которого $(M plus.o N)a subset A^n$.
  Конечно, $(M plus.o N)a approx.eq M plus.o N$. Таким образом, мы показали, что
  модуль без кручения $M in bold(M)(A)$ изоморфен подмодулю модуля $A^n$ для
  некоторого $n >= 0$. Обратное очевидно. Отсюда следует, что кольцо $A$
  наследственно справа тогда и только тогда, когда все такие модули $M$ являются
  $A$-проективными.

  Предположим теперь, что кольцо $A$ наследственно справа. Так как модуль,
  являющийся проективным над $R$ или $A$, должен быть модулем без кручения, то
  мы видим, что категория $bold(P)(A)$ состоит из модулей без кручения категории
  $bold(M)(A)$ и аналогичный факт имеет место для кольца $R$. Так как возможные
  гомологические размерности исчерпываются размерностями $0$ и $1$ (и $-1$ для
  нулевого модуля), то $hd_A (M) = hd_R (M)$ для $M in bold(M)(A)$. Кроме того,
  если $T$ — периодический подмодуль модуля $M in bold(M)(A)$, то модуль
  $M slash T$ проективен, и поэтому $M approx.eq T plus.o M slash T$. В силу
  предложения @prop:hereditary-ring-ideals модуль $M slash T$ является прямой
  суммой модулей, изоморфных правым идеалам.

  Обратно, допуская, что каждый идеал $frak(p) in maxSpec(A)$ проективен как
  правый $A$-модуль, мы должны показать, что кольцо $A$ наследственно справа, т.
  е. $hd_A (M) <= 1$ для всех $M in bold(M)(A)$.

  Пусть модуль $T in bold(M)(A)$ периодический. Длина его конечна. Кроме того,
  если последовательность
  $ 0 arrow.r T' arrow.r T arrow.r T'' arrow.r 0 $
  точна, то в силу @prop:projective-dimension-sequence
  $hd_A (T) <= sup(hd_A (T'), hd_A (T''))$. Следовательно, проводя индукцию по
  длине, достаточно показать, что $hd_A (T) <= 1$ в случае простого модуля $T$.
  Пусть $frak(p) = ann_A T$. В силу предложения
  @prop:maximal-primitive-finite-algebra $frak(p) in maxSpec(A)$, и поэтому
  кольцо $A slash frak(p)$ простое. Из этого следует, что $T$ выделяется прямым
  слагаемым в $A slash frak(p)$. Кроме того, из точности последовательности
  $0 arrow.r frak(p) arrow.r A arrow.r A slash frak(p) arrow.r 0$ и из наших
  предположений о том, что $frak(p) in bold(P)(A)$, ясно, что
  $hd_A (A slash frak(p)) <= 1$. Следовательно, $hd_A (T) <= 1$.

  Пусть теперь модуль $M in bold(M)(A)$ без кручения. Достаточно доказать, что
  $hd_A (M) <= 0$ для всех таких модулей $M$. Из первой части доказательства
  было ясно, что мы смогли найти вложение $M plus.o N subset A^n$, такое, что
  $M plus.o N$ является решеткой в $Lambda^n$; это приводит к точной
  последовательности $0 arrow.r M plus.o N arrow.r A^n arrow.r T arrow.r 0$, где
  коядро $T$ обязано быть периодическим модулем. Таким образом, мы показали, что
  $hd_A (T) <= 1$, поэтому модуль $M plus.o N$ проективен, что и требовалось
  доказать.

  @cond:maximal-order-faithful-projective-generator Пусть $A$ — максимальный
  порядок. Если $frak(p) in maxSpec(A)$, то
  $frak(p)overline(frak(p)) = A = overline(frak(p))frak(p)$, поэтому можно найти
  элементы $a_i in frak(p)$ и $b_i in overline(frak(p))$, такие, что
  $sum_i a_i b_i = 1$. Определим $h_i\: frak(p) arrow.r A$, полагая
  $h_i x = b_i x$. #source(138) Тогда для $x in frak(p)$ получаем равенство
  $x = sum_i a_i b_i x = sum_i a_i h_i (x)$. Следовательно, в силу предложения
  @prop:projective-dual-basis идеал $frak(p)$ является проективным правым
  $A$-модулем. Из части @cond:hereditary-order-projective-maximal-ideals
  доказательства теперь следует, что кольцо $A$ наследственно справа.

  Предположим, что модуль $P in bold(P)(A)$ точный. Пусть $frak(a) = sum h P$
  ($h in P^* = Hom_A (P,A)$). Так как $P L = P tensor_R L$ — точный
  $Lambda$-модуль и алгебра $Lambda$ полупроста, то $Lambda = sum h P_L$
  ($h in P_L^*$). Поскольку $Hom_Lambda (P L, Lambda) = Hom_A (P,A) tensor_R L$,
  можно заключить, что $frak(a) subset A$ является $R$-решеткой. Кроме того, из
  @prop:projective-dual-basis следует, что $frak(a)$ — идемпотентный
  двусторонний идеал. Но теорема @th:maximal-order-two-sided-lattices утверждает
  однозначную разложимость двусторонних $A$-решеток в $Lambda$. Поэтому
  $frak(a) = A$, т. е. $P$ является образующим. Так как $P in bold(P)(A)$, то из
  предложения @prop:strict-projective-modules следует, что $P$ — строго
  проективный правый $A$-модуль.

  Обратно, предположим, что кольцо $A$ наследственно справа и что каждый точный
  модуль $P in bold(P)(A)$ строго проективен. Пусть $B$ есть $R$-порядок,
  содержащий $A$. Тогда $B$ принадлежит $bold(P)(A)$, поскольку кольцо $A$
  наследственно справа (надо учитывать при этом часть
  @cond:hereditary-order-projective-maximal-ideals доказательства), и очевидно,
  что модуль $B$ точен. Рассматривая $B$ как правый $A$-модуль, можно
  отождествить $Hom_A (B,A)$ и $overline(B) = {x in Lambda | x B subset A}$. Из
  наших предположений вытекает, что $B$ — строго проективный правый $A$-модуль,
  поэтому $overline(B)B = A$. Но тогда
  $A = overline(B)B = overline(B)(B B) = (overline(B)B)B = A B = B$. Это
  показывает, что $A$ — максимальный порядок, и завершает доказательство теоремы
  @th:hereditary-maximal-order-characterizations.
]

#theorem[
  Сохраняется сделанное выше предположение
  @eq:orders-lattice-standing-assumption. Пусть $A$ — максимальный $R$-порядок в
  $Lambda$, $V$ — точный конечно порожденный левый $Lambda$-модуль и $P$ —
  дивизориальная $A$-решетка в $V$. Тогда $A' = End_A (P)$ является максимальным
  $R$-порядком в $Lambda' = End_Lambda (V)$ и $A = End_(A')(P)$.
] <th:maximal-order-endomorphism-centralizer>
#proof[
  Так как модуль $V$ точен, то можно рассматривать $Lambda$ как подалгебру в
  $E = End_L (V)$. Тогда $Lambda'$ совпадает с централизатором множества
  $Lambda$ в $E$. Кроме того,
  $A subset (P\:P) = {h in E | h P subset P} approx.eq End_R (P)$ и
  $A' = Lambda' inter (P\:P)$, поскольку $h in E$ коммутирует с $A$ тогда и
  только тогда, когда элемент $h$ перестановочен с $Lambda$. (Напомним, что
  $Lambda = A dot L$.) Так как решетка $P$ дивизориальна, то из
  @cor:divisorial-lattice-hom-localization следует, что $(P\:P)$ является
  дивизориальной $R$-решеткой в $E$ и, следовательно, $A'$ — дивизориальный
  $R$-порядок в $Lambda'$.

  Из наших предположений следует, что $V$ — строго проективный $Lambda$-модуль
  и, значит, $Lambda = End_(Lambda')(V)$, т. е. $Lambda$ — централизатор в $E$
  множества $Lambda'$. Рассуждая, как и выше, видим, что
  $Lambda inter (P\:P) = End_(A')(P)$ и что $Lambda inter (P\:P)$ является
  $R$-порядком в $Lambda$, содержащим $A$. Так как порядок $A$ максимальный, то
  $A = End_(A')(P)$.

  #source(139) Остается лишь показать, что $A'$ — максимальный $R$-порядок в
  $Lambda'$. Как мы убедились, $A'$ — дивизориальная $R$-решетка, поэтому в силу
  @th:maximal-orders-existence достаточно показать, что $A'_(frak(p))$ является
  максимальным $R_(frak(p))$-порядком для каждого $frak(p) in Ht_1(R)$. Еще раз
  используя @cor:divisorial-lattice-hom-localization, получаем, что
  $
    A'_(frak(p)) = Lambda' inter (P\:P)_(frak(p)) = Lambda' inter
    (P_(frak(p))\:P_(frak(p))) = End_(A_(frak(p)))(P_(frak(p))).
  $
  Так как $A_(frak(p))$ — максимальный $R_(frak(p))$-порядок и так как
  $R_(frak(p))$ — дедекиндово кольцо (фактически кольцо дискретного
  нормирования), то из @th:hereditary-maximal-order-characterizations следует,
  что $P_(frak(p))$ — строго проективный $A_(frak(p))$-модуль. Следовательно,
  функтор
  $
    Hom_(A_(frak(p)))(P_(frak(p)),dot)\: A_(frak(p)) hyph moduleCategory arrow.r
    A'_(frak(p)) hyph moduleCategory
  $
  является $R$-эквивалентностью $R$-категорий (см. @ch:module-categories, §
  @sec:module-category-characterization–@sec:right-continuous-functors). Так как
  кольцо $A_(frak(p))$ наследственно (см.
  @th:hereditary-maximal-order-characterizations), то кольцо $A'_(frak(p))$
  также наследственно. Кроме того, каждый объект из $bold(P)(A'_(frak(p)))$
  изоморфен $Hom_(A_(frak(p)))(P_(frak(p)),Q)$ для некоторого
  $Q in bold(P)(A_(frak(p)))$. Если $Hom_(A_(frak(p)))(P_(frak(p)),Q)$ — точный
  $A'_(frak(p))$-модуль, то в силу утверждения @th:morita-equivalence-properties
  @cond:morita-left-module-equivalence $Q$ — точный $A_(frak(p))$-модуль.
  Следовательно, в этом случае $Q$ является, согласно теореме
  @th:hereditary-maximal-order-characterizations, строго проективным
  $A_(frak(p))$-модулем. Итак, мы установили справедливость критерия из
  @th:hereditary-maximal-order-characterizations
  @cond:maximal-order-faithful-projective-generator, откуда следует, что
  $A'_(frak(p))$ — максимальный $R_(frak(p))$-порядок в $Lambda'$. Этим
  заканчивается доказательство теоремы
  @th:maximal-order-endomorphism-centralizer.
]

#corollary[
  Сохраняется предположение @eq:orders-lattice-standing-assumption. Пусть $A$ —
  максимальный $R$-порядок в $Lambda$. Тогда
  $A approx.eq product_i End_(A'_i)(P_i)$, где каждая алгебра $A'_i$ является
  максимальным порядком в некотором теле $D_i$ и где $P_i$ — дивизориальная
  $A'_i$-решетка в конечномерном $D_i$-модуле.
] <cor:maximal-orders-division-algebra-endomorphisms>
#proof[
  Пусть $S_1,dots,S_n$ — различные простые левые $Lambda$-модули, и пусть
  $D_i = End_Lambda (S_i)$, $P_i$ — дивизориальная $A$-решетка в $S_i$ и
  $P = product.co_i P_i subset V = product.co_i S_i$. Тогда $D_i$ — тело (лемма
  Шура), $Lambda' = product_i D_i$ и $A' = product_i A'_i$, где
  $A'_i = End_A (P_i)$ (в обозначениях из
  @th:maximal-order-endomorphism-centralizer). Теперь следствие вытекает из
  @th:maximal-order-endomorphism-centralizer.
]

Закончим этот параграф, приведя предложение, содержащее метод сведения некоторых
вопросов для произвольных конечномерных $R$-алгебр к случаю порядков в
полупростых алгебрах.

#proposition[
  Пусть $R$ — дедекиндово кольцо и $B$ — конечномерная $R$-алгебра. Тогда
  существует наибольший двусторонний нильпотентный идеал $N$ в $B$. Если $T$ —
  подмодуль ($R$-) #source(140) кручения в $B slash N$, то $T$ — полупростое
  кольцо (длина которого как $R$-модуля конечна) и
  $B slash N approx.eq T times A$, где $A$ есть $R$-порядок в полупростой
  $L$-алгебре.
] <prop:finite-algebra-semisimple-order-reduction>
#proof[
  Если $N_1^(n_1) = 0 = N_2^(n_2)$ для двусторонних идеалов $N_1$ и $N_2$, то
  очевидно, что $(N_1+N_2)^(n_1+n_2) = 0$. Так как $R$-модуль $B$ нётеров, то
  существует наибольший нильпотентный двусторонний идеал. Очевидно, что в
  факторкольце $B slash N$ уже нет нильпотентных идеалов. Так как длина
  $R$-модуля $T$ конечна, то можно применить @prop:artinian-ideal-semisimple и
  заключить, что $B slash N approx.eq T times A$ для некоторого $A$, при этом
  кольцо $T$ полупросто. Отсюда следует, что $A$ — модуль без кручения и в $A$
  нет ненулевых нильпотентных идеалов. Следовательно, $A$ является $R$-порядком
  в $A tensor_R L$ и в нем отсутствуют ненулевые нильпотентные идеалы (они
  пересекались бы с $A$). Из @th:semisimple-ring-characterizations вытекает, что
  $L$-алгебра $A tensor_R L$ полупроста, что и требовалось доказать.
]
