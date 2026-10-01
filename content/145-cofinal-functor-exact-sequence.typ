#import "main-defs.typ": Aut, Im, K, Ker, idx, source, symbol-idx
#import "statements.typ": proof, proposition, theorem
#import "diagrams/exact-k-sequences-squares.typ": (
  automorphism-fiber-square, diagonal-fiber-square, exact-functor-triangle,
  exact-k-quotient-diagram, exact-k-triangle-diagram,
  natural-exact-functor-square, natural-k-sequence-diagram,
)

== Точная последовательность для кофинального функтора
<sec:cofinal-functor-exact-sequence>

В этом параграфе мы покажем, что кофинальный функтор $F: bold(A) -> bold(A)'$,
сохраняющий произведение, индуцирует точную последовательность вида
$ K_1 bold(A) -> K_1 bold(A)' -> K'_0 (F) -> K_0 bold(A) -> K_0 bold(A)'. $

#source(297)Желая определить группу $K'_0 (F)$, введем сначала диаграмму
расслоенного произведения
$ #diagonal-fiber-square() quad alpha: F G_1 -> F G_2. $
<eq:cofinal-functor-diagonal-square>
Так как функтор $F$ кофинален, то очевидно, что $(F, F)$~— кофинальная пара (см.
@def:cofinal-functor-pair). Кроме того, если функтор $F$ Е-сюръективен (см.
@def:e-surjective-functor), то из @prop:fiber-square-cofinality
@cond:fiber-square-e-surjectivity следует, что диаграмма
@eq:cofinal-functor-diagonal-square является Е-сюръективной (см.
@def:e-surjective-functor-square).

Тождественный функтор из категории $bold(A)$ в два ее экземпляра в
диаграмме~@eq:cofinal-functor-diagonal-square индуцирует #idx(
  "диагональный функтор",
)_диагональный функтор_
#symbol-idx($Delta$, sort: "Δ", group: "symbols", order: 130)
$
  Delta: bold(A) -> italic("co")(F), quad G_i Delta = 1_(bold(A))
  quad (i = 1, 2).
$ <eq:diagonal-cofinal-functor>
Определим теперь группы $K_i (F)$ как коядра в коротких точных
последовательностях
$
  0 -> K_i bold(A) arrow.r^Delta K_i (italic("co")(F)) -> K_i (F) -> 0
  quad (i = 0, 1).
$
Так как отображение $Delta$ расщепляется с помощью $G_1$ и $G_2$, то
$
  K_i (F) tilde.eq Ker(K_i (italic("co")(F)) arrow.r^(G_j) K_i bold(A))
  quad (i = 0, 1; j = 1, 2),
$
$ K_i (italic("co")(F)) tilde.eq K_i bold(A) xor K_i (F) quad (i = 0, 1). $
Так как $italic("co")(F)$ является расслоенным произведением, то рассмотрим
факторгруппу $K'_0 (italic("co")(F))
= K_0 (italic("co")(F)) slash M$ группы $K_0 (italic("co")(F))$, встречающуюся в
последовательности Майера~— Вьеториса
@eq:mayer-vietoris-cartesian-square
(см. @def:mayer-vietoris-grothendieck-quotient). Определим
$ K'_0 (F) = K_0 (italic("co")(F)) slash (M + Im(Delta)) $
как соответствующую факторгруппу группы $K_0 (F)$. Таким образом, получаем
точную последовательность
#symbol-idx($d$, sort: "d", group: "letters", order: 80)
$ K_0 bold(A) arrow.r^d K'_0 (italic("co")(F)) -> K'_0 (F) -> 0, $
где $d = ("естественная проекция") compose Delta$. Напомним (см.
@def:mayer-vietoris-grothendieck-quotient), что подгруппа $M$ порождается
элементами
$
  chevron.l A, alpha_1, alpha_2 chevron.r
  = [A alpha_1 alpha_2] + [A] - [A alpha_1] - [A alpha_2],
$
где $A = (A_1, alpha_A, A_2) in italic("co")(F)$,
$alpha_i in Aut_(bold(A)') (F A_1)$ ($i = 1, 2$) и
$A beta = (A_1, alpha_A beta, A_2)$ для $beta in Aut_(bold(A)') (F A_1)$. Так
как $G_i A = A_i$ ($i = 1, 2$), то рассмотренный элемент
$chevron.l A, alpha_1, alpha_2 chevron.r$ лежит в ядре отображения
$K'_0 (italic("co")(F)) -> K_0 bold(A)$, индуцированного функторами $G_i$. Таким
образом, каждый функтор $G_i$ индуцирует отображение $K'_0 (italic("co")(F)) ->$
#source(298)$K_0 bold(A)$, причем эти отображения расщепляют приведенный выше
гомоморфизм $d$. Это доказывает первое утверждение следующего предложения.

Если $(A, alpha, B) in italic("co")(F)$, то через $[A, alpha, B]'$ обозначим его
класс в группе $K'_0 (F)$, а через $[A, alpha, B]''$~— его класс в
$K'_0 (italic("co")(F))$.

#proposition[
  Диагональный функтор $Delta: bold(A) -> italic("co")(F)$ индуцирует
  расщепляющуюся короткую точную последовательность
  $ 0 -> K_0 bold(A) -> K'_0 (italic("co")(F)) -> K'_0 (F) -> 0. $
  Кроме того, $K'_0 (F) = K_0 (italic("co")(F)) slash N$, где $N$~— подгруппа,
  порожденная всеми элементами вида
  $ [A, beta alpha, C] - [A, alpha, B] - [B, beta, C] $
  группы $K_0 (italic("co")(F))$. Каждый элемент группы $K'_0 (F)$ можно
  записать в виде $[A, alpha, B]'$.
] <prop:relative-grothendieck-composition-presentation>

#proof[
  Первое утверждение уже показано. Для доказательства второго обозначим через
  $[[A, alpha, B]]$ смежный класс элемента $[A, alpha, B]$ по подгруппе $N$. Для
  доказательства включения $M subset N$ надо показать, что
  $[[A alpha_1 alpha_2]] + [[A]] = [[A alpha_1]] + [[A alpha_2]]$ для каждого
  элемента $chevron.l A, alpha_1, alpha_2 chevron.r$, приведенного выше. В свою
  очередь это немедленно следует из того, что
  $[[A beta]] = [[A]] + [[A_1, beta, A_1]]$ для любого
  $beta in Aut_(bold(A)') (F A_1)$. Но последнее утверждение сразу же вытекает
  из определения подгруппы $N$. Включение $Im(Delta) subset N$ следует из
  образующих при $A = B = C$ и $alpha = beta = 1_(F A)$.

  Для доказательства включения $N subset M + Im(Delta)$ надо показать, что
  $ [A, beta alpha, C]' = [A, alpha, B]' + [B, beta, C]' $
  в группе $K'_0 (F)$. Пусть $A in bold(A)$ и
  $alpha, beta in Aut_(bold(A)') (F A)$. Тогда $Delta A = (A, 1_(F A), A)$ и
  $[Delta A]' = 0$ (в силу определения группы $K'_0 (F)$). Из определения $M$
  далее следует, что $[Delta A alpha beta]' = [Delta A alpha beta]' + [Delta A]'
  = [Delta A alpha]' + [Delta A beta]'$. Таким образом, отображение
  $alpha |-> [Delta A alpha]'$ является гомоморфизмом, и поэтому
  $[Delta A alpha]' = 0$ для элемента $alpha$ из коммутанта.

  Пусть теперь элементы $A, alpha, B, beta, C$ выбраны, как и ранее. Тогда
  объекты $(A perp B perp C, s(alpha perp beta perp (beta alpha)^(-1)),
    A perp B perp C)$ и
  $(A perp B perp C, alpha perp beta perp (beta alpha)^(-1),
    B perp C perp A)$ изоморфны в $italic("co")(F)$ (здесь $s$~— подходящий цикл
  длины 3). Из леммы Уайтхеда~@lem:abstract-whitehead следует, что существует
  изоморфизм $F(A perp B perp C)$ на $F(A perp A perp A)$, переводящий
  $s(alpha perp beta perp (beta alpha)^(-1))$ в $t$ (т. е. в соответствующий
  цикл длины три на $A perp A perp A$). Так как цикл длины три лежит в
  коммутанте симметрической группы трех элементов, то
  $s(alpha perp beta perp (beta alpha)^(-1))$ лежит в коммутанте группы
  $Aut_(bold(A)') (F(A perp$ #source(299)$B perp C))$. Из утверждения
  предыдущего абзаца вытекает, что
  $
    0 = [A perp B perp C, s(alpha perp beta perp (beta alpha)^(-1)),
      A perp B perp C]'
  $
  $
    = [A perp B perp C, alpha perp beta perp (beta alpha)^(-1), B perp C perp
      A]'
  $
  $ = [A, alpha, B]' + [B, beta, C]' + [C, (beta alpha)^(-1), A]'. $
  Совершенно аналогичные рассуждения показывают, что также
  $[A, alpha, B]' + [B, alpha^(-1), A]' = 0$. Из этих утверждений следует, как и
  предполагалось,
  $ [A, beta alpha, C]' = [A, alpha, B]' + [B, beta, C]'. $

  Любой элемент группы $K'_0 (F)$ можно записать в виде
  $[A_1, alpha_1, B_1]' - [A_2, alpha_2, B_2]'$, а это можно выразить как
  $[A_1 perp B_2, alpha_1 perp alpha_2^(-1), A_2 perp B_1]'$, что завершает
  доказательство предложения.
]

Рассмотрим теперь группу $K_1 (F)$ и, в частности, сравним ее с группой
$K_1 (bold(A), F)$, определенной в @def:whitehead-group. Напомним, что
$Ker Sigma F$~— полная подкатегория категории $Sigma bold(A)$, объекты которой~—
$(A, alpha)$, для которых $F alpha = 1_(F A)$. Объект категории
$Sigma italic("co")(F)$ имеет вид $((A, gamma, B), (alpha, beta))$, где
$(alpha, beta)$~— автоморфизм объекта $(A, gamma, B)$ из $italic("co")(F)$. Это
означает, что $alpha in Aut_(bold(A)) (A)$, $beta in Aut_(bold(A)) (B)$ и
диаграмма
$ #automorphism-fiber-square() $
коммутативна. Диагональный функтор
$Sigma Delta: Sigma bold(A) -> Sigma italic("co")(F)$ определяется так:
$Sigma Delta(A, alpha) = (Delta A, Delta alpha)
= ((A, 1_(F A), A), (alpha, alpha))$. Он индуцирует расщепляющуюся точную
последовательность
$ 0 -> K_1 bold(A) -> K_1 (italic("co")(F)) -> K_1 (F) -> 0, $
определяющую группу $K_1 (F)$. Из @prop:fiber-square-cofinality
@cond:fiber-square-cofinality и @prop:fiber-square-cofinality
@cond:fiber-square-e-surjectivity следует, что _функтор $Delta$ кофинальный,
если функтор $F$ является Е-сюръективным_.

Рассмотрим естественный функтор
$ H: Ker Sigma F -> Sigma italic("co")(F), $ <eq:relative-whitehead-h-functor>
определенный так: $H(A, alpha) = (Delta A, (alpha, 1_A))$. Так как
$F alpha = 1_(F A)$, то $(alpha, 1_A)$ действительно является автоморфизмом
объекта $Delta A = (A, 1_(F A), A)$. Кроме того, этот функтор, очевидно,
сохраняет произведение. Если $(beta, gamma)$~— любой автоморфизм объекта
$Delta A$, то $(beta, gamma) = (alpha, 1_A)(gamma, gamma)$, где
$alpha = beta gamma^(-1)$, при этом $F alpha = 1_(F A)$. Это каноническое
разложение показывает, что группа $Aut_(italic("co")(F)) (Delta A)$ является
полупрямым произведением $Delta (Aut_(bold(A)) (A))$ и нормального #source(
  300,
)делителя $H(Aut_(bold(A)) (A, F))$. При переходе к факторгруппе по коммутанту
получаем, что $G((Delta A)) = G((A), F) xor G((A))$ (в обозначениях
§~@sec:cofinal-functors; см. лемму~@lem:split-extension-abelianization). Здесь
первое слагаемое получается из $H$, а второе~— из $Delta$. Если теперь взять
предел прямого спектра этих групп над объектами $Delta A$ ($A in bold(A)$), как
в §~@sec:cofinal-functors, то мы получим, что сумма
$K_1 (bold(A), F) + K_1 (bold(A))$ прямая. Если функтор $F$ Е-сюръективен, то,
как было замечено ранее, функтор $Delta$ кофинален. Из
@prop:relative-whitehead-image-kernel следует теперь, что рассмотренный предел
канонически изоморфен группе $K_1 (italic("co")(F))$. Таким образом,
сформулируем

#proposition[
  Функторы
  $
    Sigma bold(A) arrow.r^(Sigma Delta) Sigma italic("co")(F)
    arrow.l^H Ker Sigma F
  $
  (см. @eq:diagonal-cofinal-functor и @eq:relative-whitehead-h-functor)
  индуцируют гомоморфизм
  $ K_1 (bold(A), F) xor K_1 (bold(A)) -> K_1 (italic("co")(F)), $
  являющийся изоморфизмом, если функтор $F$ Е-сюръективен. Следовательно, в этом
  случае функтор $H$ индуцирует изоморфизм $K_1 (bold(A), F) -> K_1 (F)$.
] <prop:relative-whitehead-diagonal-comparison>

Точная последовательность, ассоциированная с функтором $F$, будет построена как
нижняя строка следующей диаграммы:
$ #exact-k-quotient-diagram() $ <eq:cofinal-functor-quotient-sequence-diagram>
Средняя строка диаграммы является последовательностью Майера~— Вьеториса
@th:mayer-vietoris-exact-sequence для @eq:cofinal-functor-diagonal-square.
Отображения $d_i$ и $s_i$ таковы: $d_i (x) = (x, -x)$; $s_i (x, y) = x + y$
($i = 0, 1$). Вертикаль, содержащая $Delta_0$, является расщепляющейся точной
последовательностью~@prop:relative-grothendieck-composition-presentation.
Вертикаль, содержащая $Delta_1$, является короткой точной последовательностью,
определяющей группу $K_1 (F)$. Так как члены нижней строки являются коядрами
соответствующих вертикальных точных последовательностей и так как верхняя
половина диаграммы коммутативна, то горизонтальные стрелки нижней строки
определены однозначно с помощью коммутативности диаграммы.

Из @prop:relative-whitehead-diagonal-comparison вытекает, что слева мы имеем
отображение $H: K_1 (bold(A), F) -> K_1 (italic("co")(F))$. Определим
$h: K_1 (bold(A), F) -> K_1 (F)$ так, чтобы соответствующий треугольник был
коммутативным. #source(301)Композиция отображений
$K_1 (bold(A), F) -> K_1 (F) -> K_1 (bold(A))$ переводит класс объекта
$(A, alpha) in Ker Sigma F$ в элемент
$s_1 (g_1 ([H(A, alpha)])) = s_1 g_1 [Delta A, (alpha, 1_A)]_(italic("co")(F))
= s_1 ([A, alpha]_(bold(A)), [A, 1_A]_(bold(A))) = [A, alpha]_(bold(A))$, так
как $[A, 1_A]_(bold(A)) = 0$. Таким образом, она совпадает с отображением
$K_1 (bold(A), F) -> K_1 (bold(A))$, индуцированным вложением
$Ker Sigma F subset Sigma bold(A)$ (@ss:relative-whitehead-functor-sequence).

Так как верхняя строка ациклична, а средняя строка является комплексом, то
нижняя строка~— комплекс, группы гомологий которого совпадают с группами
гомологий средней строки (в силу теоремы о длинной гомологической
последовательности, @prop:long-homology-sequence). Таким образом,
последовательность в нижней строке точна всюду, где точна последовательность
Майера~— Вьеториса. Учитывая теорему~@th:mayer-vietoris-exact-sequence, мы
получаем такой результат.

#theorem[
  Пусть $F: bold(A) -> bold(A)'$~— кофинальный функтор, сохраняющий
  произведение. Пусть
  $
    K_1 (F) arrow.r^f K_1 (bold(A)) arrow.r^i K_1 (bold(A)')
    arrow.r^(partial') K'_0 (F) -> K_0 (bold(A)) -> K_0 (bold(A)')
  $
  <eq:cofinal-functor-exact-sequence>
  ~— последовательность, которая была построена в
  @eq:cofinal-functor-quotient-sequence-diagram. Тогда
  последовательность~@eq:cofinal-functor-exact-sequence точна всюду, кроме,
  возможно, члена $K_1 (bold(A))$. Композиция гомоморфизмов
  $h: K_1 (bold(A), F) -> K_1 (F)$ из
  @eq:cofinal-functor-quotient-sequence-diagram и $f$ дает отображение
  $K_1 (bold(A), F) -> K_1 (bold(A))$, индуцированное вложением
  $Ker Sigma F subset Sigma bold(A)$. Если функтор $F$ Е-сюръективен, то
  естественная проекция $K_0 (F) -> K'_0 (F)$ оказывается изоморфизмом, $h$~—
  изоморфизм, а последовательность~@eq:cofinal-functor-exact-sequence точна.
] <th:cofinal-functor-exact-sequence>

Отметим естественность последовательности~@eq:cofinal-functor-exact-sequence.
Пусть нам дана диаграмма
$ #natural-exact-functor-square() quad alpha: F J arrow.r.tilde J' G, $
<eq:natural-exact-functor-square>
сохраняющих произведение функторов. Предположим, кроме того, что функторы $F$ и
$G$ кофинальны. Тогда диаграмма~@eq:natural-exact-functor-square индуцирует
морфизм последовательностей:
$ #natural-k-sequence-diagram() $ <eq:natural-k-exact-sequences>
Отображение $j_0$ определено так:
$
  j_0 [B_1, beta, B_2]' = [J B_1, alpha_(B_2)^(-1)(J' beta)alpha_(B_1), J B_2]'.
$
#source(302)Здесь, конечно, $beta: G B_1 -> G B_2$ и
$alpha_(B_i): F J B_i -> J' G B_i$ ($i = 1, 2$). Используя естественное
преобразование $alpha$, можно аналогично определить отображение $j'_1$.

Если $(G B, beta) in Sigma bold(B)'$, то
$j_0 partial' [G B, beta] = j_0 [B, beta, B]'
= [J B, alpha_B^(-1)(J' beta)alpha_B, J B]'
= partial' [F J B, alpha_B^(-1)(J' beta)alpha_B]
= partial' [J' G B, J' beta] = partial' J' [G B, beta]$, т. е.
$j_0 partial' = partial' J'$. Эта выкладка иллюстрирует поведение
диаграммы~@eq:natural-k-exact-sequences. В следующем параграфе мы рассмотрим
отображение $j_0$ специального типа в «теореме о вырезании».

Закончим этот параграф описанием «точной последовательности для треугольника».
Пусть нам дана коммутативная треугольная диаграмма
$ #exact-functor-triangle() $
кофинальных функторов, сохраняющих произведение. Тогда получаем функторы,
сохраняющие произведение:
$
  partial: italic("co")(F) -> italic("co")(H), quad
  partial(A_1, beta, A_2) = (A_1, G beta, A_2)
$
и
$
  delta: italic("co")(H) -> italic("co")(G), quad
  delta(A_1, gamma, A_2) = (F A_1, gamma, F A_2).
$
Они индуцируют гомоморфизмы
$ K'_0 (F) arrow.r^partial K'_0 (H) arrow.r^delta K'_0 (G) $
и
$ K_1 (F) arrow.r^partial K_1 (H) arrow.r^delta K_1 (G), $
при этом в каждом случае $delta partial = 0$. Рассмотрим теперь коммутативную
диаграмму
$ #exact-k-triangle-diagram() $ <eq:exact-k-functor-triangle-diagram>
Отображение $Delta$ определено условием коммутативности диаграммы.
Коммутативность в других случаях следует непосредственно из определений.

#theorem[
  В последовательности
  $
    K_1 (F) arrow.r^partial K_1 (H) arrow.r^delta K_1 (G)
    arrow.r^Delta K'_0 (F) arrow.r^partial K'_0 (H) arrow.r^delta K'_0 (G)
  $
  <eq:exact-k-functor-triangle-sequence>
  #source(303)композиции всех отображений равны нулю.
  Последовательность~@eq:exact-k-functor-triangle-sequence точна в $K'_0 (H)$.
  Если функтор $G$ к тому же Е-сюръективен, то
  последовательность~@eq:exact-k-functor-triangle-sequence точна и в $K'_0 (F)$.
  Если функтор $F$ также Е-сюръективен, то она точна и в $K_1 (G)$.
] <th:exact-k-functor-triangle-sequence>

#proof[
  $K$-последовательности~@eq:cofinal-functor-exact-sequence для функторов $F$,
  $G$ и $H$ вложим в диаграмму~@eq:exact-k-functor-triangle-diagram. В каждой из
  них все композиции отображений нулевые. Из коммутативности следует тогда, что
  $Delta delta = 0$ и $partial Delta = 0$ в
  @eq:exact-k-functor-triangle-sequence. Как мы заметили ранее, в каждом из
  случаев $delta partial = 0$.

  _Точность в $K'_0 (H)$_. Устанавливается с помощью диаграммного поиска,
  использующего точность $K$-последовательностей для функторов $F$, $G$ и $H$.
  Проверку этого факта мы предоставляем читателю в качестве упражнения.

  _Точность в $K'_0 (F)$, если функтор $G$ Е-сюръективен_. Пусть $x in K'_0 (F)$
  и $partial x = 0$. Надо показать, что $x in Im(Delta)$. Так как $d_F x = 0$,
  то $x = delta_F y$ для $y in K_1 (bold(B))$. Так как
  $delta_H G_1 (y) = partial delta_F y = partial x = 0$, то $G_1 (y) = H_1 (z)$
  для некоторого $z in K_1 (bold(A))$, поскольку функтор $G$ Е-сюръективен. Но
  $G_1 F_1 (z) = G_1 (y)$, и поэтому $y - F_1 (z) = d_G (u)$ для некоторого
  $u in K_1 (G)$. Далее, $Delta u = delta_F d_G (u) = delta_F (y - F_1 (z))
  = delta_F (y) - delta_F F_1 (z) = delta_F (y) = x$.

  _Точность в $K_1 (G)$, если функторы $G$ и $F$ Е-сюръективны_. Пусть
  $x in K_1 (G)$ и $Delta x = 0$. Надо показать, что $x in Im(delta)$. Так как
  $0 = Delta x = delta_F d_G (x)$, то $d_G (x) = F_1 (y)$ для некоторого
  $y in K_1 (bold(A))$. Так как $H_1 (y) = 0$ и функтор $H$ Е-сюръективен
  (поскольку таковы функторы $F$ и $G$), то $y = d_H (z)$ для некоторого
  $z in K_1 (H)$. Тогда $d_G delta(z) = F_1 d_H (z) = F_1 (y) = d_G (x)$, и
  поэтому $d_G (u) = 0$, где $u = x - delta z$. Так как функтор $G$
  Е-сюръективен, то $K_1 (G) tilde.eq K_1 (bold(B), G)$, и поэтому
  $u = [B, beta]$ для некоторых $B in bold(B)$ и $beta in Aut_(bold(B)) (B)$,
  для которых $G beta = 1_(G B)$. Поскольку функтор $F$ кофинален, то можно
  далее считать, что $B = F A$ для некоторого $A in bold(A)$. Из равенства
  $d_G (u) = 0$ следует в силу @prop:whitehead-commutator-stabilization, что
  $beta perp 1_(B')$ лежит в коммутанте группы $Aut_(bold(B)) (F A perp B')$ для
  некоторого $B'$. Так как функтор $F$ кофинален, то можно считать, что
  $B' = F A'$. Так как функтор $F$ Е-сюръективен, то, изменяя при необходимости
  $A'$, можно считать, что $beta perp 1_(F A') = F alpha$ для некоторого $alpha$
  из коммутанта группы $Aut_(bold(A)) (A perp A')$. Тогда
  $H alpha = G F alpha = G(beta perp 1_(F A')) = G beta perp 1_(H A')
  = 1_(H(A perp A'))$. Но элемент
  $v = [A perp A', alpha] in K_1 (bold(A), H) tilde.eq K_1 (H)$ таков, что
  $delta(v) = [F(A perp A'), F alpha] = u = x - delta(z)$. Следовательно,
  $x = delta(v + z)$, что и требовалось доказать.

  Это доказывает сформулированную выше теорему
  @th:exact-k-functor-triangle-sequence. Приведем критерий точности в $K_1 (H)$.
]

#proposition[
  Допустим, что в теореме~@th:exact-k-functor-triangle-sequence функторы $F$ и
  $G$ Е-сюръективны и что выполнено следующее условие: #source(304)Если объект
  $A in bold(A)$ и автоморфизм $alpha in Aut_(bold(A)) (A)$ таковы, что
  $F alpha in [Aut_(bold(B)) (F A), Aut_(bold(B)) (F A, G)]$, то найдутся
  $B = A perp A'$ и $epsilon in [Aut_(bold(A)) (B), Aut_(bold(A)) (B, H)]$, для
  которых $F epsilon = F alpha perp 1_(F A')$. В этом случае
  последовательность~@eq:exact-k-functor-triangle-sequence точна в $K_1 (H)$.
] <prop:exact-k-triangle-middle-criterion>

#proof[
  Если $x in K_1 (H)$ и $delta(x) = 0$, то надо показать, что
  $x in Im(partial)$. Так как функтор $H$ Е-сюръективен, то $x = [A, alpha]$,
  где $A in bold(A)$ и $alpha in Aut_(bold(A)) (A, H)$. Так как
  $0 = delta(x) = [F A, F alpha]$, то в силу @prop:whitehead-translation-colimit
  найдем объект $C' = F A perp B'$, для которого
  $F alpha perp 1_(B') in [Aut_(bold(B)) (C'), Aut_(bold(B)) (C', G)]$. Так как
  функтор $F$ кофинален, то можно считать, что $B'$ имеет вид $F A'$. Поэтому
  $C' = F C$, где $C = A perp A'$. В силу нашего предположения можно, изменяя
  далее при необходимости $C$, найти
  $epsilon in [Aut_(bold(A)) (C), Aut_(bold(A)) (C, H)]$, для которого
  $F epsilon = F(alpha perp 1_(A'))$. Но
  $y = [C, epsilon^(-1)(alpha perp 1_(A'))]_F in K_1 (bold(A), F) = K_1 (F)$.
  Так как $[C, epsilon]_H = 0$, то
  $partial(y) = [C, epsilon^(-1)]_H + [C, alpha perp 1_(A')]_H
  = [A, alpha] = x$, что и требовалось доказать.
]
