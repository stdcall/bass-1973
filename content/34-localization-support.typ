#import "main-defs.typ": (
  Coker, End, Hom, Im, Int, Ker, U, idx, maxSpec, moduleCategory, source, spec,
  supp, symbol-idx, tensor,
)
#import "statements.typ": (
  assertion, condition-item, condition-list, numbered-condition, proof,
  proposition,
)
#import "diagrams/rings-modules-diagrams.typ": (
  localization-hom-square, localization-pullback-square,
  localization-submodule-square, localization-tensor-square,
)

== Локализация, носитель
<sec:localization-support>
#idx("носитель")

Большая часть материала этого параграфа вполне стандартна, поэтому многие
элементарные факты будут оставлены для проверки читателю.

Пусть $S$ — мультипликативная система (т. е. $s, t in S => s t in S$) в
коммутативном кольце $R$. Если $M in moduleCategory hyph R$, то «локализация»
модуля $M$ определяется как
$ S^(-1) M = (M times S) slash tilde, $
#idx("локализация модуля")
#symbol-idx($S^(-1)$, sort: "S^-1", group: "groups", order: 118)
где $tilde$ — отношение эквивалентности: $(x_1,s_1) tilde (x_2,s_2)$, если
$(x_1 s_2 - x_2 s_1)t = 0$ для некоторого $t in S$. Класс эквивалентности,
#source(97) содержащий пару $(x,s)$, обозначим через $x slash s$. Превратим
$S^(-1)M$ в аддитивную группу, полагая
$ (x slash s) + (y slash t) = (x t + y s) slash (s t). $
В частности, #numbered-condition[$x slash s = 0 <=> x t = 0$ для некоторого
  $t in S$.] <eq:localization-zero>

Если $x slash s in S^(-1)M$ и $a slash t in S^(-1)R$, то положим
$(x slash s)(a slash t) = (x a) slash (s t)$. Эти структуры определены корректно
и превращают $S^(-1)R$ в коммутативное кольцо, а $S^(-1)M$ — в $S^(-1)R$-модуль.
Кроме того, имеет место каноническое отображение
$ h_M\: M arrow.r S^(-1)M quad (h_M (x) = (x s) slash s "для любого" s in S). $
Ясно, что $h_R$ — гомоморфизм колец (для которого $h_R (S) subset U(S^(-1)R)$),
и что $h_M$ есть $h_R$-полулинейное отображение, т. е.
$h_M (x a) = h_M (x)h_R (a)$, где $x in M$ и $a in R$. Следовательно, можно
рассмотреть индуцированный канонический $S^(-1)R$-гомоморфизм
$ h'_M\: M tensor_R S^(-1)R arrow.r S^(-1)M quad (M in moduleCategory hyph R), $
при котором
$ h'_M (x tensor (a slash s)) = (x a) slash s. $

Если $f\: M arrow.r N$ является $R$-линейным отображением, то оно индуцирует
$S^(-1)R$-гомоморфизм
$ S^(-1)f\: S^(-1)M arrow.r S^(-1)N, quad S^(-1)f(x slash s) = f(x) slash s, $
превращая
$ S^(-1)\: moduleCategory hyph R arrow.r moduleCategory hyph S^(-1)R $
в аддитивный функтор.

Основным результатом является #proposition[
  Функтор $S^(-1)$ точен и
  $
    h'_M\: M tensor_R S^(-1)R arrow.r S^(-1)M quad (M in moduleCategory hyph R)
  $
  является естественным изоморфизмом функторов.
] <prop:localization-exact-tensor>
#proof[
  Если последовательность $M' limits(arrow.r)^g M limits(arrow.r)^f M''$ точна,
  то очевидно, что $(S^(-1)f)(S^(-1)g) = 0$. Поэтому нам надо показать, что,
  если $x slash s in Ker(S^(-1)f)$, то $x slash s in Im(S^(-1)g)$. Так как
  $f(x) slash s = 0$, то $f(x)t = 0$ для некоторого $t in S$ (в силу утверждения
  @eq:localization-zero). Следовательно, $x t in Ker f = Im(g)$, скажем,
  $x t = g(y)$. Тогда
  $x slash s = (x t) slash (s t) = g(y) slash (s t) = (S^(-1)g)(y slash (s t))$.

  Нетрудно проверить, что функтор $S^(-1)$ сохраняет любые копроизведения.
  Следовательно, $h' = (h'_M)$ является естественным преобразованием непрерывных
  справа функторов (см. @ch:module-categories, §
  @sec:right-continuous-functors). Так как очевидно, что $h'_R$ — изоморфизм, то
  $h'_M$ является изоморфизмом #source(98) для любого модуля $M$ вида
  $Coker(R^((I)) arrow.r R^((J)))$, т. е. для всех $M in moduleCategory hyph R$,
  что и требовалось доказать.
]

Гомоморфизм колец $f\: R arrow.r R'$, такой, что $f(S) subset U(R')$, можно
записать в виде $f = f' h_R$, где гомоморфизм $f'\: S^(-1)R arrow.r R'$
определен однозначно, $f'(a slash s) = f(a)f(s)^(-1)$. В частности, на
$R$-модуле $M$, на котором умножение на элементы из $S$ биективно, определена
каноническая структура $S^(-1)R$-модуля (следует рассмотреть
$R' = End_Int (M)$). В этом случае $h_M\: M arrow.r S^(-1)M$ является
изоморфизмом.

Если $frak(a)$ — идеал в кольце $R$, то можно канонически отождествить
$S^(-1)(R slash frak(a))$ с локализацией кольца $R slash frak(a)$ по образу
системы $S$ в $R slash frak(a)$.

Пусть $M in moduleCategory hyph R$. Так как функтор $S^(-1)$ точен,
$R$-подмодуль $N$ в $M$ определяет $S^(-1)R$-подмодуль $S^(-1)N$ в $S^(-1)M$. С
другой стороны, если $H$ является $S^(-1)R$-подмодулем в $S^(-1)M$, то обозначим
(для краткости)
$ H inter M = h_M^(-1)(H). $
Так как функтор $S^(-1)$ точен, то функция $N arrow.r.bar S^(-1)N$ сохраняет
операции (сумму и пересечение) на подмодулях. Кроме того,
$
  N subset S^(-1)N inter M quad (N subset M), \
  H = S^(-1)(H inter M) quad (H subset S^(-1)M).
$ <eq:localized-submodule-contraction>

#proposition[
  Отображение $spec(S^(-1)R) arrow.r spec(R)$ индуцирует гомеоморфизм
  пространства $spec(S^(-1)R)$ на пространство всех $frak(p) in spec(R)$, таких,
  что $frak(p) inter S = emptyset$, при этом $frak(p) arrow.r.bar S^(-1)frak(p)$
  является обратным отображением. Если $S = {s^n | n >= 0}$ для некоторого
  $s in R$, то это позволяет отождествить $spec(S^(-1)R)$ с (открытым)
  дополнением подмножества $V(s) subset spec(R)$.
] <prop:localization-prime-correspondence>
#proof[
  Отображение $spec(S^(-1)R) arrow.r spec(R)$ действует следующим образом:
  $frak(q) arrow.r.bar h_R^(-1)(frak(q)) = frak(q) inter R$. Так как
  $frak(q) = S^(-1)(frak(q) inter R)$, то это отображение инъективно. Поскольку
  $h_R (S)$ состоит из обратимых элементов,
  $(frak(q) inter R) inter S = emptyset$ для любого собственного идеала
  $frak(q)$.

  Предположим, что $frak(p) in spec R$ и $frak(p) inter S = emptyset$.
  Рассмотрим точную последовательность
  $
    0 arrow.r S^(-1)frak(p) arrow.r S^(-1)R arrow.r S^(-1)(R slash frak(p))
    arrow.r 0.
  $
  Образ множества $S$ является мультипликативной системой ненулевых элементов
  области целостности $R slash frak(p)$, поэтому $S^(-1)(R slash frak(p))$ лежит
  в поле частных кольца $R slash frak(p)$. Отсюда следует, что идеал
  $S^(-1)frak(p)$ прост и что отображение $h_(R slash frak(p))$ инъективно, а
  поэтому, как легко видеть, $frak(p) = S^(-1)frak(p) inter R$. Таким образом,
  для доказательства первого утверждения предложения остается лишь показать, что
  отображение $frak(p) arrow.r.bar S^(-1)frak(p)$ непрерывно (где
  $frak(p) in spec(R)$, $frak(p) inter S = #source(99) emptyset$). Но полный
  прообраз множества $V(frak(a)) subset spec(S^(-1)R)$, где $frak(a)$ — идеал в
  $S^(-1)R$, совпадает с множеством
  ${frak(p) in spec(R) | frak(p) inter S = emptyset,
    frak(a) subset S^(-1)frak(p)}$. Это последнее, как нетрудно заметить,
  является множеством тех $frak(p) in spec(R)$, для которых
  $frak(p) inter S = emptyset$ и $(frak(a) inter R) subset frak(p)$, и поэтому
  замкнуто.

  Наконец, если $S = {s^n}$, то
  $frak(p) inter S = emptyset <=> s in.not frak(p)$, где $frak(p) in.not V(s)$.
  Утверждение доказано.
]

Если $frak(p) in spec(R)$, то $S_(frak(p)) = R without frak(p)$ является
мультипликативной системой. Локализацию $S_(frak(p))^(-1)M$ обычно принято
обозначать через $M_(frak(p))$. В этом случае $R_(frak(p))$ — локальное кольцо с
максимальным идеалом $frak(p)R_(frak(p))$. Если $M in moduleCategory hyph R$, то
введем обозначение
$ supp(M) = {frak(p) in spec(R) | M_(frak(p)) != 0}, $
это множество называется _носителем_ модуля $M$. #idx(
  "носитель модуля",
)#symbol-idx($supp$, sort: "supp", group: "operators", order: 73) Иногда мы
будем рассматривать носитель модуля $M$ в $maxSpec(R)$, который определяется
аналогично. Существенная информация о модуле $M$ не теряется, если вместо него
рассмотреть все его локализации, точнее: #assertion[
  Если $x in M$, то $x = 0 <=> x slash 1 = 0$ в $M_(frak(m))$ для всех
  $frak(m) in maxSpec(R)$. В частности, $M = 0 <=> M_(frak(m)) = 0$ для всех
  $frak(m) in maxSpec(R)$.
] <ss:local-vanishing-detection>
Это замечание и точность локализации позволяют сводить многие вопросы к
рассмотрению их над локальными кольцами, например вопрос о том, является ли
$R$-гомоморфизм изоморфизмом.

Рассмотрим теперь поведение функторов $tensor$ и $Hom$ при локализации. Если
$M, N in moduleCategory hyph R$, то имеет место коммутативный квадрат
#localization-tensor-square()
где $f(x tensor_R y) = x tensor_(S^(-1)R) y$ и где отображение $g$ существует,
поскольку $f(h_M tensor_R h_N) = h_M tensor_(S^(-1)R) h_N$ является
$h_R$-полулинейным отображением. Тот факт, что локализация сохраняет тензорное
произведение, можно выразить следующим образом: #assertion[
  Отображения $f$ и $g_M$ являются изоморфизмами.
] <ss:localization-tensor-preservation>
Рассмотрение отображения $f$ оставим в качестве упражнения. Поскольку $g$
является естественным преобразованием непрерывных справа функторов (см.
@ch:module-categories, § @sec:right-continuous-functors) и очевидно, что $g_R$ —
изоморфизм, то стандартные рассуждения показывают теперь, что $g_M$ — изоморфизм
для любого модуля $M$ вида $Coker(R^((I)) arrow.r R^((J)))$, т. е. для всех
модулей $M$.

#source(100) Прежде чем рассматривать функтор $Hom$, обобщим нашу конструкцию на
случай $R$-алгебры $A$. Если $M in moduleCategory hyph A$, то легко заметить,
что $S^(-1)A$ есть $S^(-1)R$-алгебра и
$S^(-1)\: moduleCategory hyph A arrow.r moduleCategory hyph S^(-1)A$ является
точным функтором, который изоморфен функтору $tensor_R S^(-1)R$ или, что
эквивалентно, функтору $tensor_A S^(-1)A$. Если $M, N in moduleCategory hyph A$,
то следующая диаграмма
#numbered-condition[#localization-hom-square()] <eq:localization-hom-diagram>
коммутативна, где $f$ — вложение, а $g_M$ существует, поскольку отображение
$S^(-1)$ является $h_R$-полулинейным.

#proposition[
  В диаграмме @eq:localization-hom-diagram отображение $f$ — изоморфизм и
  естественное преобразование
  $ g_M\: S^(-1)Hom_A (M,N) arrow.r Hom_(S^(-1)A)(S^(-1)M,S^(-1)N) $
  является изоморфизмом для конечно представимого $A$-модуля $M$ (т. е. для
  модуля $M$, который имеет вид $Coker(A^n arrow.r A^m)$ для некоторых
  $n,m > 0$).
] <prop:localization-hom-finite-presentation>
#proof[
  Утверждение относительно $f$ является несложным упражнением, которое мы
  оставляем читателю.

  Очевидно, что $g_A$ — изоморфизм, поэтому $g_(A^n)$ — изоморфизм для всех
  $n > 0$. Так как функтор $S^(-1)$ точен, то оба рассмотренных выше
  контравариантных функтора модуля $M$ переводят коядра в ядра, и поэтому лемма
  о последовательности из пяти членов показывает, что $g_M$ — изоморфизм, если
  найдется точная последовательность $P_1 arrow.r P_0 arrow.r M arrow.r 0$,
  такая, что каждое отображение $g_(P_i)$ — изоморфизм. Рассматривая
  $P_i = A^(n_i)$, мы получим на этом пути все конечно представимые модули $M$.
]

#proposition[
  #condition-list[
    #condition-item(format: "cyrillic")[Пусть $M in moduleCategory hyph A$ и $H$
      есть $S^(-1)A$-подмодуль модуля $S^(-1)M$. Тогда $H = S^(-1)(H inter M)$,
      и поэтому $H arrow.r.bar H inter M$ — инъективное отображение структуры
      $S^(-1)A$-подмодулей модуля $S^(-1)M$ в структуру $A$-подмодулей модуля
      $M$. В частности, если $M$ — нётеров (соответственно артинов) $A$-модуль,
      то $S^(-1)M$ — нётеров (соответственно артинов)
      $S^(-1)A$-модуль.] <cond:localization-submodule-lattice>

    #condition-item(format: "cyrillic")[Допустим, что кольцо $A$ нётерово справа
      и что $M in bold(M)(A)$ и
      $
        E = (0 arrow.r H_n arrow.r dots arrow.r H_0 limits(arrow.r)^d S^(-1)M
          arrow.r 0)
      $
      точная последовательность в $bold(M)(S^(-1)A)$. Тогда существуют точная
      последовательность
      $
        E' = (0 arrow.r M_n arrow.r dots arrow.r M_0 limits(arrow.r)^(d_0) M
          arrow.r 0)
      $
      #source(101) в $bold(M)(A)$ и изоморфизм $S^(-1)E' approx.eq E$,
      индуцирующий тождественный изоморфизм на
      $S^(-1)M$.] <cond:localization-finite-exact-sequence-descent>
  ]
] <prop:localization-chain-descent>
#proof[
  @cond:localization-submodule-lattice Первое утверждение следует из формул
  @eq:localized-submodule-contraction, а из него вытекает остальное.

  @cond:localization-finite-exact-sequence-descent Разбивая $E$ на короткие
  точные последовательности и проводя очевидную индукцию, можно свести все к
  рассмотрению случая $n = 1$. Нам дана последовательность
  $0 arrow.r H_1 arrow.r H_0 limits(arrow.r)^d S^(-1)M arrow.r 0$. Если мы
  сможем найти эпиморфизм $d_0\: M_0 arrow.r M$ в $bold(M)(A)$ и изоморфизм
  $S^(-1)d_0 approx.eq d$, индуцирующий $1_(S^(-1)M)$, то в силу точности
  функтора $S^(-1)$ этот изоморфизм индуцирует изоморфизм
  $S^(-1)M_1 approx.eq H_1$, где $M_1 = Ker(d_0)$. Кроме того,
  $M_1 in bold(M)(A)$, так как кольцо $A$ нётерово справа. Поэтому задача будет
  решена, как только мы построим эпиморфизм $d_0$.

  Пусть $X$ — конечное множество $S^(-1)A$-образующих модуля $H_0$. Умножая,
  если это необходимо, элементы из $X$ на элементы из $S$, можно считать, что
  $d(X)$ лежит в образе отображения $h_M\: M arrow.r S^(-1)M$. Выберем теперь
  конечное множество $Y subset H_0$, такое, что $d(Y)$ порождает $A$-модуль
  $Im(h_M)$. Пусть $N subset H_0$ есть $A$-подмодуль, порожденный множествами
  $X$ и $Y$. Тогда $d$ индуцирует эпиморфизм $d'\: N arrow.r Im(h_M)$ в
  $bold(M)(A)$. Кроме того, вложение $i\: N arrow.r H_0$ индуцирует
  коммутативный квадрат
  #localization-submodule-square()
  в котором отображение $S^(-1)i$ сюръективно (в силу построения) и инъективно
  (поскольку функтор $S^(-1)$ точен).

  Образуем декартов квадрат
  #localization-pullback-square()
  Так как кольцо $A$ нётерово справа, то категория $bold(M)(A)$ абелева, и
  поскольку $M,N in bold(M)(A)$, то $M_0 in bold(M)(A)$. (Фактически,
  $M_0 subset M plus.o N$.) Кроме того, так как $d'$ — эпиморфизм, то $d_0$
  также эпиморфизм. Наконец, поскольку $S^(-1)h_M$ — изоморфизм и функтор
  $S^(-1)$ точен, отображение $S^(-1)f$ также является изоморфизмом.
  Следовательно, отображение
  $
    (S^(-1)(f),1_(S^(-1)M))\: S^(-1)(M_0 limits(arrow.r)^(d_0) M) arrow.r
    (H_0 limits(arrow.r)^d S^(-1)M)
  $
  является искомым изоморфизмом.
]

#source(102)
#proposition[
  Пусть $A$ есть $R$-алгебра.

  #condition-list[
    #condition-item(format: "cyrillic")[Если $M in bold(M)(A)$ и $frak(a)$ —
      аннулятор $R$-модуля $M$, то $supp(M)$ совпадает с $V(frak(a))$ и является
      замкнутым множеством в
      $spec(R)$.] <cond:finite-module-support-annihilator>

    #condition-item(format: "cyrillic")[Пусть
      $P = (0 arrow.r P_n limits(arrow.r)^(d_n) dots limits(arrow.r)^(d_1) P_0
        arrow.r 0)$
      — конечный комплекс в $bold(P)(A)$. Тогда $supp(H(P))$ — замкнутое
      множество в $spec(R)$.] <cond:finite-projective-complex-closed-support>
  ]
] <prop:closed-support-finite-complex>
#proof[
  @cond:finite-module-support-annihilator Если $s in a$, $s in.not frak(p)$, то
  очевидно, что $M_(frak(p)) = 0$. Обратно, если $M_(frak(p)) = 0$ и элементы
  $x_1, dots, x_n$ порождают $M$ (как $A$-модуль), то для каждого $i$ найдется
  элемент $s_i in.not frak(p)$, такой, что $x_i s_i = 0$. Следовательно,
  $s = s_1 dots s_n in a$ и $s in.not frak(p)$.

  @cond:finite-projective-complex-closed-support Проведем индукцию по $n$.
  Случай $n = 0$, когда $H(P) = P_0$, следует из п.
  @cond:finite-module-support-annihilator.

  Если $frak(p) in.not supp(H(P))$, то попробуем найти окрестность точки
  $frak(p)$ в дополнении к $supp(H(P))$. Пусть $M = Coker(d_1) in bold(M)(A)$.
  Тогда $M = H_0(P)$, и поэтому $M_(frak(p)) = 0$. Выберем элемент
  $s in.not frak(p)$, такой, что $M_s = 0$ (используя
  @cond:finite-module-support-annihilator), и рассмотрим $S = {s^n | n >= 0}$.
  Перейдем к комплексу $S^(-1)P$ над $S^(-1)R$-алгеброй $S^(-1)A$. В силу
  предложения @prop:localization-prime-correspondence можно отождествить
  $spec(S^(-1)R)$ с $spec(R) without V(s)$, который является открытой
  окрестностью точки $frak(p)$. Следовательно, достаточно показать, что
  $supp(H(S^(-1)P))$ — замкнутое множество в $spec(S^(-1)R)$.

  В силу построения отображение $S^(-1)d_1$ сюръективно и поэтому расщепляется
  (так как $S^(-1)P_0 in bold(P)(S^(-1)A)$). Следовательно, комплекс $S^(-1)P$
  изоморфен прямой сумме комплекса
  $
    (dots 0 arrow.r S^(-1)P_0 limits(arrow.r)^(1_(S^(-1)P_0)) S^(-1)P_0
      arrow.r 0 dots)
  $
  и подкомплекса
  $
    Q = (dots 0 arrow.r S^(-1)P_n arrow.r dots arrow.r S^(-1)P_2 arrow.r
      Ker(S^(-1)d_1) arrow.r 0 dots)
  $
  комплекса $S^(-1)P$. Таким образом, $H(S^(-1)P) = H(Q)$. Так как длина
  комплекса $Q$ меньше, чем $n$, то из предположения индукции следует, что
  $supp(H(Q))$ — замкнутое множество.
]
