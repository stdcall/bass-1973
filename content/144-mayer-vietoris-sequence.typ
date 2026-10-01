#import "main-defs.typ": Aut, Im, K, Ker, idx, source, symbol-idx
#import "statements.typ": (
  condition-item, condition-list, definition, lemma, proof, theorem,
)
#import "diagrams/exact-k-sequences-squares.typ": category-fiber-square

== Последовательность Майера — Вьеториса расслоенного произведения
<sec:mayer-vietoris-sequence>

#source(292)В этом параграфе мы собираемся сопоставить декартову квадрату (см.
§~@sec:fiber-product-categories)
$ #category-fiber-square() quad alpha: F_1 G_1 -> F_2 G_2, $
<eq:mayer-vietoris-cartesian-square>
точную последовательность. Это осуществляется в приводимой ниже
теореме~@th:mayer-vietoris-exact-sequence.

Если $A = (A_1, alpha, A_2) in bold(A)$, $beta in Aut_(bold(A)') (F_1 A_1)$ и
$gamma in Aut_(bold(A)') (F_2 A_2)$, то обозначим (как в
@def:e-surjective-functor-square)
$ gamma A beta = (A_1, gamma alpha beta, A_2). $
Кроме того, если $alpha_1, alpha_2 in Aut_(bold(A)') (F_1 A_1)$, то положим
$
  chevron.l A, alpha_1, alpha_2 chevron.r
  = [A alpha_1 alpha_2] + [A] - [A alpha_1] - [A alpha_2] in K_0 bold(A).
$

#definition(word: [Определение группы $K'_0 bold(A)$], upright: true)[
  Положим
  $ K'_0 bold(A) = K_0 bold(A) slash M, $
  где $M$~— группа, порожденная всеми
  $chevron.l A, alpha_1, alpha_2 chevron.r$
  ($A = (A_1, alpha, A_2) in bold(A)$;
  $alpha_1, alpha_2 in Aut_(bold(A)') (F_1 A_1)$). Обозначим класс объекта $A$ в
  группе $K'_0 bold(A)$ через $[A]'$.
] <def:mayer-vietoris-grothendieck-quotient>

Заметим, что если $chevron.l B, beta_1, beta_2 chevron.r$~— другой такой
элемент, то
$
  chevron.l A, alpha_1, alpha_2 chevron.r + chevron.l B, beta_1, beta_2
  chevron.r
  = chevron.l A perp B, alpha_1 perp beta_1, alpha_2 perp beta_2 chevron.r.
$
Из этого следует, что любой элемент группы $M$ представим в виде
$chevron.l A, alpha_1, alpha_2 chevron.r - chevron.l B, beta_1, beta_2
chevron.r$.

#lemma[
  Каждый элемент группы $K'_0 bold(A)$ можно записать в виде $[A]' - [B]'$. Если
  $[A]' = [B]'$, то существуют элементы
  $chevron.l C, gamma_1, gamma_2 chevron.r$ и
  $chevron.l D, delta_1, delta_2 chevron.r$, а также объект $E in bold(A)$, для
  которых объекты
  $ A perp C gamma_1 perp C gamma_2 perp D delta_1 delta_2 perp D perp E $
  и
  $ B perp C gamma_1 gamma_2 perp C perp D delta_1 perp D delta_2 perp E $
  изоморфны в $bold(A)$. Если декартов квадрат
  @eq:mayer-vietoris-cartesian-square Е-сюръективен (см.
  @def:e-surjective-functor-square), то естественная проекция
  $K_0 bold(A) -> K'_0 bold(A)$ оказывается изоморфизмом.
] <lem:mayer-vietoris-stable-relations>

#proof[
  Первое утверждение очевидно, поскольку $K'_0 bold(A)$ является факторгруппой
  группы $K_0 bold(A)$. Если $[A]' =$ #source(293)$[B]'$, то $[A] - [B] in M$, и
  поэтому, как было замечено выше,
  $[A] - [B] = chevron.l C, gamma_1, gamma_2 chevron.r
  - chevron.l D, delta_1, delta_2 chevron.r$. Перепишем это равенство так, чтобы
  все члены в обоих его частях входили с коэффициентом $+1$. Затем применим
  @cond:grothendieck-stable-isomorphism для получения объекта $E$, приводящего к
  желаемому изоморфизму.

  Что касается последнего утверждения, то надо показать, что все элементы
  $chevron.l A, alpha_1, alpha_2 chevron.r$ нулевые. В силу
  @lem:whitehead-diagonal-commutator, $epsilon = alpha_2^(-1) perp alpha_2$~—
  коммутатор в группе $Aut_(bold(A)') (F_1 (A_1 perp A_1))$. Кроме того,
  $(A alpha_1 alpha_2 perp A)epsilon = A alpha_1 perp A alpha_2$. Из определения
  Е-сюръективности следует, что
  $A alpha_1 alpha_2 perp A perp B tilde.eq A alpha_1 perp A alpha_2 perp B$
  для некоторого $B in bold(A)$. Таким образом, как и требовалось,
  $[A alpha_1 alpha_2] + [A] - [A alpha_1] - [A alpha_2] = 0$.
]

Пусть @eq:mayer-vietoris-cartesian-square~— декартов квадрат. Построим при
некоторых предположениях #idx(
  "последовательность Майера — Вьеториса",
)последовательность Майера~— Вьеториса:
#symbol-idx($partial$, sort: "∂", group: "letters", order: 77)
$
  K_1 bold(A) arrow.r^(g_1) K_1 bold(A)_1 xor K_1 bold(A)_2
  arrow.r^(f_1) K_1 bold(A)' arrow.r^partial \
  arrow.r^partial K'_0 bold(A) arrow.r^(g_0) K_0 bold(A)_1 xor K_0 bold(A)_2
  arrow.r^(f_0) K_0 bold(A)'.
$ <eq:mayer-vietoris-sequence>
Через $(T)_i$ обозначим гомоморфизм на $K_i$, индуцированный функтором $T$.
Положим
$ f_i (x_1, x_2) = (F_1)_i (x_1) + (F_2)_i (x_2), quad i = 0, 1, $
$ g_1 (x) = ((G_1)_1 (x), -(G_2)_1 (x)), $
$ g_0 (x) = ((G_1)'_0 (x), -(G_2)'_0 (x)). $
В последнем обозначении $(G_j)'_0$ является гомоморфизмом на группе
$K'_0 (bold(A)) = K_0 (bold(A)) slash M$, индуцированным функтором $(G_j)_0$.
Его существование обеспечено тем, что при $(G_j)_0$ образующие
$chevron.l A, alpha_1, alpha_2 chevron.r$ группы $M$ (см.
@def:mayer-vietoris-grothendieck-quotient) отображаются в нуль. Из самого
определения и коммутативности диаграммы @eq:mayer-vietoris-cartesian-square (с
точностью до изоморфизма) ясно, что
$ f_i g_i = 0 quad (i = 0, 1). $ <eq:mayer-vietoris-zero-composites>

#theorem(title: [«последовательность Майера — Вьеториса»])[
  Пусть @eq:mayer-vietoris-cartesian-square~— декартов квадрат, в котором
  $(F_1, F_2)$~— кофинальная пара функторов (см. @def:cofinal-functor-pair).
  Тогда существует единственный гомоморфизм
  $partial: K_1 bold(A)' -> K'_0 bold(A)$, для которого
  $ partial [F_1 G_1 A, alpha] = [A alpha]' - [A]' $
  ($A in bold(A)$, $alpha in Aut_(bold(A)') (F_1 G_1 A)$). Получающаяся
  последовательность~@eq:mayer-vietoris-sequence является точной, за
  исключением, возможно, члена $K_1 bold(A)_1 xor K_1 bold(A)_2$. Если
  квадрат~@eq:mayer-vietoris-cartesian-square Е-сюръективен (см.
  @def:e-surjective-functor-square), то последовательность
  @eq:mayer-vietoris-sequence точна, а естественный гомоморфизм
  $K_0 (bold(A)) -> K'_0 (bold(A))$ является изоморфизмом. В частности, это так,
  если один из функторов $F_i$ Е-сюръективен (см. @def:e-surjective-functor).
  Наконец, эта последовательность оказывается естественной относительно
  функторов между декартовыми квадратами.
] <th:mayer-vietoris-exact-sequence>

#proof[
  #source(294)Последнее утверждение, точную формулировку которого мы
  предоставляем читателю, будет следовать из определений отображений $partial$,
  $f_i$ и $g_i$. Утверждение о том, что диаграмма
  @eq:mayer-vietoris-cartesian-square Е-сюръективна, если один из функторов
  $F_i$ Е-сюръективен, как раз содержится в @prop:fiber-square-cofinality
  @cond:fiber-square-e-surjectivity. Если
  квадрат~@eq:mayer-vietoris-cartesian-square Е-сюръективен, то гомоморфизм
  $K_0 (bold(A)) -> K'_0 (bold(A))$ является изоморфизмом (это показано в
  @lem:mayer-vietoris-stable-relations).

  Нам остается только построить отображение $partial$ и доказать утверждения
  относительно точности последовательности @eq:mayer-vietoris-sequence. Как мы
  уже показали в @eq:mayer-vietoris-zero-composites, $f_i g_i = 0$ ($i = 0, 1$).
  Заметим, что в силу @prop:fiber-square-cofinality
  @cond:fiber-square-projection-cofinality из предположения о том, что
  $(F_1, F_2)$~— кофинальная пара, следует, что функторы $G_i$ и $F_i G_i$
  ($i = 1, 2$) кофинальны.

  #condition-list[
    #condition-item(format: "cyrillic")[_Существование и единственность
      отображения $partial$_. Пусть $A = (A_1, alpha_A, A_2) in bold(A)$ и
      $alpha in G(F_1 A_1) = Aut_(bold(A)') (F_1 A_1)$. Положим
      $d(A, alpha) = [A alpha]' - [A]' in K'_0 bold(A)$. Если
      $alpha_1, alpha_2 in G(F_1 A_1)$, то, как видно непосредственно из
      определения~@def:mayer-vietoris-grothendieck-quotient,
      $
        d(A, alpha_1 alpha_2) = [A alpha_1 alpha_2]' - [A]'
        = d(A, alpha_1) + d(A, alpha_2).
      $
      Таким образом, отображение $d(A, -): G(F_1 A_1) -> K'_0 bold(A)$ является
      гомоморфизмом в абелеву группу и поэтому может быть пропущено через
      факторгруппу по коммутанту $G((F_1 A_1))$ группы $G(F_1 A_1)$. Если
      $(h_1, h_2): A -> B$~— изоморфизм в $bold(A)$, то $(h_1, h_2)$ индуцирует
      изоморфизм
      $(F_1 A_1, alpha) tilde.eq (F_1 B_1, (F_1 h_1)alpha(F_1 h_1)^(-1))$
      в $Sigma bold(A)'$, а поэтому $alpha_B = (F_2 h_2)alpha_A (F_1 h_1)^(-1)$.
      Из этого следует, что $h$ индуцирует изоморфизм
      $ A alpha -> B(F_1 h_1)alpha(F_1 h_1)^(-1) quad "в" bold(A). $
      Следовательно, $d(B, (F_1 h_1)alpha(F_1 h_1)^(-1))
      = [B(F_1 h_1)alpha(F_1 h_1)^(-1)]' - [B]'
      = [A alpha]' - [A]' = d(A, alpha)$. Это показывает, что $d$ не
      чувствительно к изоморфизму $A -> B$ в $bold(A)$, и поэтому зависит лишь
      от класса $(A)$ изоморфных с $A$ объектов в $bold(A)$. Наконец, если
      $A, B in bold(A)$ и $alpha in G(F_1 A_1)$, то
      $d(A perp B, alpha perp 1_(F_1 B_1))
      = [(A perp B)(alpha perp 1_(F_1 B_1))]' - [A perp B]'
      = [A alpha perp B]' - [A]' - [B]' = [A alpha]' - [A]' = d(A, alpha)$.
      Таким образом, $d$ определяет морфизм в $K'_0 bold(A)$ из направленной
      системы групп, индексы которых являются классами $(A)$ изоморфных с
      $A in bold(A)$ объектов, а отображения
      $G((F_1 G_1 A)) -> G((F_1 G_1 (A perp B)))$
      индуцированы отображением $alpha |-> alpha perp 1_(F_1 G_1 B)$. Так как мы
      знаем, что функтор $F_1 G_1$ кофинален, то из
      @prop:relative-whitehead-image-kernel следует, что группа $K_1 bold(A)'$
      является пределом прямого спектра указанной системы групп. Поэтому
      установлены существование и единственность отображения $partial$ как
      гомоморфизма, индуцированного отображением $d$.
    ] <cond:mayer-vietoris-boundary-existence>

    #condition-item(format: "cyrillic")[Покажем, что $g_0 partial = 0$ и
      $partial f_1 = 0$. Если $A = (A_1, alpha_A, A_2) in bold(A)$ и
      $alpha in G(F_1 A_1)$ определены, как и ранее, то
      $
        g_0 partial [F_1 A_1, alpha] = g_0 ([A alpha]' - [A]')
        = ([A_1] - [A_1], [A_2] - [A_2]) = 0.
      $
      #source(295)Если $alpha = F_1 beta$, $beta in Aut_(bold(A)_1) (A_1)$, то
      $(beta, 1_(A_2)): A alpha -> A$ является изоморфизмом в $bold(A)$ и
      поэтому $0 = partial [F_1 A_1, F_1 beta]
      = partial f_1 ([A_1, beta], 0)$. Так как функтор
      $G_1: bold(A) -> bold(A)_1$ кофинален, то из
      @cor:whitehead-cofinal-full-subcategory следует, что каждый элемент группы
      $K_1 bold(A)_1$ имеет вид $[A_1, beta] = [G_1 A, beta]$ для некоторого
      $A in bold(A)$. Рассуждая аналогично по отношению ко второй координате на
      $K_1 bold(A)_1 xor K_1 bold(A)_2$, заключаем, что, как и требовалось,
      $partial f_1 = 0$.
    ] <cond:mayer-vietoris-boundary-zero-composites>

    #condition-item(format: "cyrillic")[Покажем, что $Ker f_0 subset Im g_0$.
      Пусть $(x_1, x_2) in Ker f_0$. Так как функторы $G_i$ кофинальны, то можно
      записать, что $x_1 = [B_1]_(bold(A)_1) - [G_1 A]_(bold(A)_1)$ и
      $-x_2 = [B_2]_(bold(A)_2) - [G_2 A']_(bold(A)_2)$, где $A, A' in bold(A)$.
      Если заменить $A$ и $A'$ на $A perp A'$ и соответственно допустить сдвиг в
      $B_1$ и $B_2$, то можно добиться того, чтобы $A = A'$. Далее, применим
      $f_0$ и убедимся в том, что $[F_1 B_1]_(bold(A)') = [F_2 B_2]_(bold(A)')$.
      Так как функтор $F_1$ кофинален, то отсюда следует существование
      изоморфизма $gamma: F_1 B_1 perp F_1 B'_1 -> F_2 B_2 perp F_1 B'_1$ для
      некоторого $B'_1 in bold(A)_1$. Так как функтор $F_2$ кофинален
      относительно $F_1$, то существует изоморфизм
      $beta: F_1 B'_1 perp F_1 B''_1 -> F_2 B'_2$ для некоторых
      $B''_1 in bold(A)_1$ и $B'_2 in bold(A)_2$. Теперь мы видим, что
      $(x_1, x_2)$ является результатом применения $g_0$ к
      $
        [B_1 perp B'_1 perp B''_1, alpha, B_2 perp B'_2]
        - [B'_1 perp B''_1, beta, B'_2] - [A],
      $
      где $alpha = (1_(F_2 B_2) perp beta)(gamma perp 1_(F_1 B''_1))$.
    ] <cond:mayer-vietoris-exact-k-zero-sum>

    #condition-item(format: "cyrillic")[Покажем, что
      $Ker g_0 subset Im partial$. Пусть $[B]' - [A]' in Ker g_0$. Это означает,
      что $[B_i]_(bold(A)_i) = [A_i]_(bold(A)_i)$ ($i = 1, 2$) и, следовательно,
      что $B_i perp A'_i tilde.eq A_i perp A'_i$ для подходящих
      $A'_i in bold(A)_i$ ($i = 1, 2$). Так как $(F_1, F_2)$~— кофинальная пара,
      то из @prop:fiber-square-cofinality
      @cond:fiber-square-projection-cofinality следует, что существует
      $C = (C_1, alpha_C, C_2) in bold(A)$ и $A''_i in bold(A)_i$, для которых
      $A'_i perp A''_i tilde.eq C_i$ ($i = 1, 2$). Положим $D = A perp C$. Тогда
      $
        D_i = A_i perp A'_i perp A''_i tilde.eq B_i perp A'_i perp A''_i
        quad (i = 1, 2).
      $
      Используя эти изоморфизмы, видим, что $B perp C tilde.eq D delta$ для
      некоторого $delta in Aut_(bold(A)') (F_1 D_1)$. Наконец,
      $
        [B]' - [A]' = [B perp C]' - [A perp C]' = [D delta]' - [D]'
        = partial [F_1 D_1, delta].
      $
    ] <cond:mayer-vietoris-exact-boundary-image>

    #condition-item(format: "cyrillic")[Покажем, что
      $Ker partial subset Im f_1$. Пусть $x in Ker partial$. Так как функтор
      $F_1 G_1$ кофинален, то можно записать $x = [F_1 G_1 A, alpha]$ для
      некоторых $A in bold(A)$ и $alpha in Aut_(bold(A)') (F_1 G_1 A)$. Так как
      $[A alpha]' - [A]' = partial x = 0$, то из доказанной
      леммы~@lem:mayer-vietoris-stable-relations следует существование
      изоморфизма $(h_1, h_2): U -> V$ в категории $bold(A)$, где
      $U = A alpha perp C gamma_1 perp C gamma_2 perp D delta_1 delta_2
      perp D perp E$ и $V = A perp C gamma_1 gamma_2 perp C perp D delta_1
      perp D delta_2 perp E$ (как в @lem:mayer-vietoris-stable-relations).
      Полагая $U = (U_1, alpha_U, U_2)$ и $V = (V_1, alpha_V, V_2)$, получаем,
      что $U_1 = A_1 perp W_1 = V_1$ и $U_2 = A_2 perp W_2 = V_2$, где
      $W_i = C_i perp C_i perp D_i perp D_i perp E_i$ ($i = 1, 2$). Кроме того,
      $alpha_U = alpha_V beta$, где
      $beta = alpha perp gamma_2^(-1) perp gamma_2 perp delta_2
      perp delta_2^(-1) perp 1_(F_1 E_1)$. Так как $(h_1, h_2)$~— изоморфизм, то
      $alpha_V = (F_2 h_2)alpha_U (F_1 h_1)^(-1)$. Таким образом,
      $beta = alpha_V^(-1)(F_2 h_2)^(-1)alpha_V (F_1 h_1)$ в группе
      $Aut_(bold(A)') (F_1 (A_1 perp W_1))$. Следовательно,
      $[alpha] = [beta] = [F_1 h_1]
      + [alpha_V^(-1)(F_2 h_2)^(-1)alpha_V]
      = [F_1 h_1] - [F_2 h_2] = f_1 ([h_1], -[h_2])$
      в группе $K_1 bold(A)'$.
    ] <cond:mayer-vietoris-exact-k-one-prime>

    #condition-item(format: "cyrillic")[#source(296)Покажем, что если
      диаграмма~@eq:mayer-vietoris-cartesian-square Е-сюръективна, то
      $Ker f_1 subset Im g_1$. Пусть
      $x = ([A_1, alpha_1], -[A_2, alpha_2]) in Ker f_1$. В силу
      предложения~@prop:fiber-square-cofinality
      @cond:fiber-square-projection-cofinality найдутся
      $B = (B_1, alpha_B, B_2) in bold(A)$ и $A'_i in bold(A)_i$ ($i = 1, 2$),
      для которых $B_i tilde.eq A_i perp A'_i$ ($i = 1, 2$). Тогда
      $(A_i perp A'_i, alpha_i perp 1_(A'_i)) tilde.eq (B_i, beta_i)$ для
      некоторых $beta_i$ ($i = 1, 2$), и поэтому, очевидно,
      $x = ([B_1, beta_1], -[B_2, beta_2])$. Применяя $f_1$, убеждаемся в том,
      что
      $
        0 = f_1 (x) = [F_1 beta_1] - [F_2 beta_2]
        = [alpha_B^(-1)(F_2 beta_2)^(-1)alpha_B (F_1 beta_1)].
      $
      Из @prop:relative-whitehead-image-kernel и кофинальности функтора
      $F_1 G_1$ теперь следует существование
      $B' = (B'_1, alpha_(B'), B'_2) in bold(A)$ такого, что элемент
      $epsilon = alpha_B^(-1)(F_2 beta_2)^(-1)alpha_B (F_1 beta_1)
      perp 1_(F_1 B'_1)$ лежит в коммутанте группы
      $Aut_(bold(A)') (F_1 (B_1 perp B'_1))$. Таким образом,
      $(F_2 beta_2)^(-1) B (F_1 beta_1) perp B' = (B perp B')epsilon$. Из
      предположения о Е-сюръективности следует существование
      $B'' = (B''_1, alpha_(B''), B''_2) in bold(A)$ и $epsilon_i$ из коммутанта
      группы $Aut_(bold(A)_i) (B_i perp B'_i perp B''_i)$ ($i = 1, 2$), для
      которых $(epsilon_1, epsilon_2): (B perp B')epsilon perp B''
      -> B perp B' perp B''$~— изоморфизм. Это означает, что
      $
        F_2 epsilon_2^(-1)(alpha_B perp alpha_(B') perp alpha_(B''))F_1
        epsilon_1
        = (alpha_B perp alpha_(B') perp alpha_(B''))epsilon perp 1_(F_1 B''_1)
      $
      $
        = (F_2 beta_2)^(-1)alpha_B (F_1 beta_1) perp alpha_(B') perp alpha_(B'')
      $
      $
        = (F_2 gamma_2)^(-1)(alpha_B perp alpha_(B') perp alpha_(B''))(F_1
          gamma_1),
      $
      где $gamma_i = beta_i perp 1_(B'_i perp B''_i)$ ($i = 1, 2$). Положим
      $C = B perp B' perp B''$ и $delta_i = gamma_i epsilon_i^(-1)$
      ($i = 1, 2$). Тогда из приведенных выше равенств следует, что
      $(F_2 delta_2)^(-1)alpha_C (F_1 delta_1) = alpha_C$, т. е., другими
      словами, что $(delta_1, delta_2)$~— автоморфизм объекта $C$.

      Мы закончим доказательство, убедившись, что
      $x = g_1 ([C, (delta_1, delta_2)]) = ([C_1, delta_1], -[C_2, delta_2])$.
      Например, в группе $K_1 bold(A)_1$:
      $[delta_1] = [gamma_1 epsilon_1^(-1)] = [gamma_1] + [epsilon_1^(-1)]
      = [gamma_1]$ (поскольку $epsilon_1$ лежит в коммутанте)
      $= [beta_1 perp 1_(B'_1 perp B''_1)] = [beta_1]$. Аналогично
      $[delta_2] = [beta_2]$ в группе $K_1 bold(A)_2$. Так как
      $x = ([beta_1], -[beta_2])$, то доказательство
      части~@cond:mayer-vietoris-exact-k-one-sum, а следовательно, и
      теоремы~@th:mayer-vietoris-exact-sequence завершено.
    ] <cond:mayer-vietoris-exact-k-one-sum>
  ]
]
