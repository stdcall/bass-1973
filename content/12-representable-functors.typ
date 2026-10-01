#import "main-defs.typ": idx, name-idx, symbol-idx
#import "main-defs.typ": (
  Coim, Coker, Im, Ker, NatTran, coker, colim, ker, mor, ob, source,
)
#import "statements.typ": corollary, exercise, proof, proposition
#import "diagrams/category-algebra-representable.typ": (
  image-coimage, kernel-cokernel, pullback-square, pushout-square,
  yoneda-naturality,
)

== Представимые функторы <sec:representable-functors>

Фиксируя одну переменную, можно рассматривать функции от двух переменных как
функции от одной переменной, значениями которых являются функции от другой
переменной. В применении к функторам это дает следующее:
$ bold(C)^(bold(A) times bold(B)) = (bold(C)^bold(A))^bold(B), $
где $bold(A)$, $bold(B)$ и $bold(C)$~— категории. Для любой категории $bold(A)$
#symbol-idx(
  $italic("Sets")$,
  sort: "Sets",
  group: "categories",
  order: 24,
)рассмотрим «функтор морфизмов»:
$
  bold(A)(,): bold(A)^degree times bold(A) -> italic("Sets")#footnote[
    $italic("Sets")$ обозначает категорию множеств.~— _Прим. ред._
  ].
$
В силу отмеченного выше формализма это соответствует функтору
$
  bold(A)^degree -> italic("Sets")^bold(A), quad
  A & arrow.r.bar overline(A) \
  a & arrow.r.bar overline(a),
$
который называется #idx("функтор представления")_функтором представления_. Более
подробно,
$
  overline(A)(B) = bold(A)(A, B) quad "и" quad
  overline(A)(b) = bold(A)(A, b): c arrow.r.bar b c.
$
Если $a: A -> A'$ (в $bold(A)^degree$), то $overline(a): overline(A) ->
overline(A')$ определяется так:
$
  overline(a)_B: overline(A)(B) -> overline(A')(B), quad overline(a)_B (b) = b
  a.
$

#idx("теорема Йонеды")#proposition(title: [Йонеда])[
  Пусть $A in bold(A)$ и $F in italic("Sets")^bold(A)$. Определим
  $ phi: NatTran(overline(A), F) -> F(A), $
  полагая $phi(alpha) = alpha_A (1_A)$. Тогда отображение $phi$ биективно.
] <prop:yoneda>

#proof[
  Если $a in F(A)$, то определим $a': overline(A) -> F$, полагая
  $a'_B (h) = (F h)(a)$ для $h: A -> B$. Тогда
  $phi(a') = (a')_A (1_A) = (F 1_A)(a) = a$. Таким образом, отображение $phi$
  сюръективно. Кроме того,
  $phi(alpha)'_A (1_A) = (F 1_A)(phi(alpha)) = phi(alpha) = alpha_A (1_A)$.
  Следовательно, $alpha$ и $beta = phi(alpha)'$ совпадают на $1_A$. В #source(
    21,
  )общем случае, если $h: A -> B$, то из коммутативности диаграммы
  $ #yoneda-naturality() $
  следует, что $alpha_B (h) = alpha_B (overline(A)(h)(1_A)) = F(h)(alpha_A
    (1_A)) =
  F(h)(beta_A (1_A)) = beta_B (overline(A)(h)(1_A))$. Итак, $phi$~— биективное
  отображение, что и требовалось доказать.
]

#corollary[
  Функтор представления
  $ bold(A)^degree -> italic("Sets")^bold(A) $
  является строгим и полным. В частности, любой изоморфизм функторов
  $bold(A)(A, dot) -> bold(A)(B, dot)$ индуцируется изоморфизмом $A -> B$ (в
  $bold(A)^degree$).
] <cor:yoneda-embedding>

#proof[
  Отображение
  $
    overline(B)(A) = bold(A)^(degree)(A, B)
    arrow.r^"функтор представления" NatTran(overline(A), overline(B))
  $
  совпадает с отображением $a arrow.r.bar a'$, построенным выше.
]

Функтор $F: bold(A) -> italic("Sets")$ называется #idx(
  "представимый функтор",
)#idx("функтор представимый")_представимым_, если он изоморфен объекту
$overline(A)$ для некоторого $A in bold(A)$. Если $alpha: overline(A) -> F$~—
данный изоморфизм, то в силу приведенных выше результатов пара $(A, alpha)$
определена однозначно с точностью до единственного изоморфизма. Таким образом,
об объекте все известно, если мы знаем его морфизмы в другие объекты.
Аналогичное утверждение для функторов $bold(A)(dot, A)$ можно получить, заменяя
$bold(A)$ на $bold(A)^degree$.

Определим теперь некоторые типы объектов в категориях, описывая представляемые
ими функторы. При этом, естественно, остается открытым вопрос об их
существовании.

#idx("инициальный объект")#idx("объект инициальный")_Инициальный_ (или
_начальный_) _объект_ представляет функтор $A arrow.r.bar
{A}$, т. е. он обладает единственным морфизмом в любой объект. Двойственно,
#idx("финальный объект")#idx("объект финальный")_финальный_ объект допускает
единственный морфизм из любого объекта. Объект, одновременно инициальный и
финальный, называется #idx("нулевой объект")#idx("объект нулевой")_нулевым
объектом_. Символ $0$ всегда будет использоваться для обозначения нулевого
объекта. Если в категории $bold(A)$ имеется нулевой объект, то в $bold(A)(A, B)$
существует единственный морфизм, разлагающийся в произведение $A -> 0 -> B$.
Этот морфизм мы будем тоже обозначать через $0$! Очевидно, $0 a = 0$ и $a 0 = 0$
для любого морфизма $a$.

#source(22)Пусть $X_1 arrow.r^(f_1) X' arrow.l^(f_2) X_2$~— пара отображений
множеств. Тогда определим
$
  X_1 product_(X') X_2 = {(x_1, x_2) in X_1 times X_2 | f_1(x_1) = f_2(x_2)}.
$
Если задана диаграмма $A_1 arrow.r^(f_1) A' arrow.l^(f_2) A_2$ в категории
$bold(A)$, то определим _расслоенное произведение_ $A_1 product_(A') A_2$:
$bold(A)(B, A_1 product_(A') A_2) = bold(A)(B, A_1)
product_(bold(A)(B, A')) bold(A)(B, A_2)$ $(B in bold(A))$. Более подробно,
$A_1 product_(A') A_2$ снабжено «проекциями» $p_1$, $p_2$, для которых диаграмма
$ #pullback-square() $ <eq:pullback-square>
коммутативна. Кроме того, если дан другой коммутативный квадрат
$ #pullback-square(object: $B$, upper: $h_2$, left: $h_1$) $
то существует единственный морфизм $t: B -> A_1 product_(A') A_2$, такой, что
$h_i = p_i t$ $(i = 1, 2)$. Квадрат типа~@eq:pullback-square будем называть
#idx("декартов квадрат")#idx("коуниверсальный квадрат")_декартовым_#footnote[
  В оригинале «Cartesian»; в литературе на английском языке принят термин
  «pullback diagram». В русской литературе используется часто термин
  «коуниверсальный квадрат».~— _Прим. перев._
]. Дуальное понятие сопоставляет диаграмме
$A_1 arrow.l^(f_1) A' arrow.r^(f_2) A_2$ #idx("универсальный квадрат")#idx(
  "расслоенное копроизведение",
)_кодекартов_ квадрат#footnote[
  В оригинале «co-Cartesian»; соответствующие альтернативные термины (см.
  предыдущее примечание): «push out diagram», «универсальный квадрат».~—
  _Прим. ред._
]
$ #pushout-square() $
т. е. квадрат, являющийся начальным объектом в категории всех таких
коммутативных квадратов. Это определяет _расслоенное копроизведение_ данной
диаграммы.

Пусть $a: A -> B$~— морфизм в категории $bold(A)$ с нулевым объектом. Тогда
#symbol-idx($Ker$, sort: "Ker", group: "operators", order: 57)#symbol-idx(
  $Coker$,
  sort: "Coker",
  group: "operators",
  order: 37,
)определим $Ker(a) = A product_B 0$, $Coker(a) = 0 product.co_A B$. Прописные
буквы будем сейчас использовать для обозначения объектов, #source(23)а строчные
буквы~— для обозначения соответствующих морфизмов:
$ #kernel-cokernel(). $
Если задан морфизм $a': A' -> A$, такой, что $a a' = 0$, то существует
единственный морфизм $alpha: A' -> Ker(a)$, такой, что $a' = ker(a) alpha$.
Аналогичное свойство характеризует коядро. Далее, определим #symbol-idx(
  $Im$,
  sort: "Im",
  group: "operators",
  order: 55,
)#symbol-idx($Coim$, sort: "Coim", group: "operators", order: 35)$
  Im(a) = Ker(coker(a))
$
и
$ Coim(a) = Coker(ker(a)). $
Нетрудно проверить, что существует канонический морфизм
$ i: Coim(a) -> Im(a), $
для которого диаграмма
$ #image-coimage() $
коммутативна.

Теперь введем понятие _предела_ (и _копредела_) функтора. Пусть $bold(L)$ и
$bold(A)$~— категории. С любым объектом $A in bold(A)$ связан _постоянный
функтор_:
$
  c(A): bold(L) -> bold(A), quad
  L & arrow.r.bar A quad (L in ob bold(L)) \
  f & arrow.r.bar 1_A quad (f in mor bold(L)).
$
Морфизм $a: A -> B$ определяет очевидным образом естественное преобразование
$c(a): c(A) -> c(B)$. Таким образом, мы получаем функтор
$ c: bold(A) -> bold(A)^bold(L), $
который при непустой связной категории $bold(L)$ является полным и строгим.
Теперь, если $F: bold(L) -> bold(A)$~— произвольный функтор, то определим его
#idx(
  "предел функтора",
)#symbol-idx($lim$, sort: "lim", group: "operators", order: 58)#symbol-idx(
  $F_(arrow.l)$,
  sort: "subscript ←",
  group: "subscripts",
  order: 155,
)_предел_
$ F_(arrow.l) = lim F in bold(A), $
полагая
$ bold(A)(A, F_(arrow.l)) = bold(A)^bold(L)(c(A), F) quad (A in bold(A)). $
Двойственно, #idx("копредел функтора")#symbol-idx(
  $colim$,
  sort: "colim",
  group: "operators",
  order: 36,
)#symbol-idx(
  $F_(arrow.r)$,
  sort: "subscript →",
  group: "subscripts",
  order: 154,
)_копредел_ функтора $F$,
$ F_(arrow.r) = colim F in bold(A) $
#source(24)определяется как
$ bold(A)(F_(arrow.r), A) = bold(A)^bold(L)(F, c(A)) quad (A in bold(A)). $
Если пределы всегда существуют, то легко видеть, что они определяют функтор
$ lim: bold(A)^bold(L) -> bold(A). $
Аналогичное утверждение имеет место для копределов.

Дальнейшие замечания о пределах будут сделаны в §~@sec:direct-limits. Сейчас мы
рассмотрим лишь следующий случай: пусть $L$~— множество, $bold(L)$~— категория с
$ob bold(L) = L$ и лишь с тождественными морфизмами. Функтор
$F: bold(L) -> bold(A)$ в этом случае является семейством $(F(i))_(i in L)$
объектов категории $bold(A)$, занумерованных множеством $L$. В этом случае
предел функтора $F$ называется #idx("произведение")#symbol-idx(
  $product$,
  sort: "∏",
  group: "symbols",
  order: 143,
)_произведением_ семейства $(F(i))_(i in L)$ и обозначается так:
$ product_(i in L) F(i). $
Копредел называется #idx("копроизведение")#symbol-idx(
  $product.co$,
  sort: "∐",
  group: "symbols",
  order: 144,
)_копроизведением_ и обозначается через
$ product.co_(i in L) F(i). $
Если все объекты $F(i)$ совпадают с одним и тем же объектом $A$ (т. е. если
$F = c(A)$), то будем использовать символы
$ A^L quad "и" quad A^((L)) $
для произведения и копроизведения соответственно. В частности, если
$L = {1, dots, n}$, то часто будем писать
$ A^n = A product dots product A quad (n "сомножителей") $
и #symbol-idx(
  $A^((n))$,
  sort: "superscript (n)",
  group: "superscripts",
  order: 150,
)$ A^((n)) = A product.co dots product.co A quad (n "сомножителей"). $

#exercise(numbered: false)[
  Пусть $bold(L)$~— категория с объектами ${0, 1, 2}$, в которой всего лишь два
  нетождественных морфизма: $1 -> 0$ и $2 -> 0$. Пусть $F: bold(L) -> bold(A)$~—
  функтор. Дайте интерпретацию функторов $lim F$ и $colim F$.
] <exc:span-limits>
