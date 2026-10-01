#import "main-defs.typ": (
  Aut, AzCat, End, Int, K, Ker, Pic, PicCat, Quad, idx, name-idx, ob, source,
  symbol-idx, tensor,
)
#import "statements.typ": (
  assertion, condition-item, condition-list, corollary, definition, example,
  lemma, named-axiom, proof, proposition,
)
#import "diagrams/exact-k-sequences-squares.typ": permuted-morphism-square

== Группы Гротендика и Уайтхеда категории с произведением
<sec:product-category-k-groups>

#source(277)_Произведением_ на категории $bold(A)$ называется функтор
$ perp: bold(A) times bold(A) -> bold(A), $
который «когерентно ассоциативен и коммутативен» в смысле #name-idx(
  "Маклейн (MacLane S.)",
)Маклейна~@bib:MacLane1963a. Это означает, что функтор #symbol-idx(
  $perp$,
  sort: "⊥",
  group: "symbols",
  order: 141,
)$perp$ снабжается естественными изоморфизмами
$
  perp compose (1_(bold(A)) times perp) tilde.eq
  perp compose (perp times 1_(bold(A))):
  bold(A) times bold(A) times bold(A) -> bold(A)
$
и
$ perp compose t tilde.eq perp: bold(A) times bold(A) -> bold(A), $
где $t$ переставляет сомножители в $bold(A) times bold(A)$. «Когерентность» этих
изоморфизмов означает, что изоморфизмы произведений нескольких множителей,
полученные из приведенных выше путем применения последовательности тройных
ассоциативностей и двойных перестановок, совпадают. Это позволяет нам писать
(однозначно определенные с точностью до канонического изоморфизма) выражения
вида $A_1 perp dots perp A_n = perp_(i = 1)^n A_i$. Будем также употреблять
обозначение $A^n = A perp dots perp A$ ($n$ членов), где $A in bold(A)$,
$n > 0$. Наконец, предполагается наличие нейтрального объекта $0 in bold(A)$
вместе с естественными изоморфизмами $0 perp A -> A$ $(A in bold(A))$,
согласованными с приведенными выше изоморфизмами.

#idx("сохраняющий произведение функтор")#idx(
  "функтор сохраняющий произведение",
)_Функтором, сохраняющим произведение_, из $(bold(A), perp)$ в
$(bold(A)', perp')$ называется функтор $F: bold(A) -> bold(A)'$, сохраняющий $0$
и снабженный естественным изоморфизмом
$
  F compose perp tilde.eq perp' compose (F times F):
  bold(A) times bold(A) -> bold(A)'.
$ <eq:product-preserving-functor>
Требуется, чтобы этот изоморфизм был согласован в обычном смысле с изоморфизмами
ассоциативности, коммутативности и нейтральности в категориях $bold(A)$ и
$bold(A)'$. Кроме того, будем предполагать, что естественные преобразования
сохраняющих произведение функторов согласованы с изоморфизмами
@eq:product-preserving-functor для обоих функторов.

Практически мы будем обозначать все произведения одним и тем же символом $perp$,
за исключением лишь тех примеров, где известны стандартные обозначения. Мы
позволим себе употреблять следующие выражения: «$F: bold(A) -> bold(A)'$
является сохраняющим произведение функтором категорий с произведением». В этой
ситуации мы обычно будем (неявно) использовать естественный изоморфизм для
отождествления $F(A perp B)$ ($A, B in bold(A)$) и $F A perp F B in bold(A)'$.
Будем говорить, что функтор $F$ #idx("кофинальный функтор")#idx(
  "функтор кофинальный",
)_кофинален_, если для $A' in bold(A)'$ существуют объекты $A in bold(A)$ и
$B' in bold(A)'$, такие, что $A' perp B' tilde.eq F A$.

Классы изоморфных объектов категории $bold(A)$ образуют полугруппу #source(
  278,
)$M(bold(A))$, при этом функтор $F$ индуцирует гомоморфизм $M(F)$ из
$M(bold(A))$ в $M(bold(A)')$. Очевидно, что функтор $F$ кофинален тогда и только
тогда, когда $M(F)$~— кофинальный гомоморфизм в смысле
предложения~@prop:cofinal-translation-category.

#example(plural: true)[
  Пусть $R$~— коммутативное кольцо и $A$ есть $R$-алгебра. Тогда рассмотрим:

  + Категорию $bold(P)(A)$ конечно порожденных проективных правых $A$-модулей и
    $A$-гомоморфизмов с $perp = xor$. Можно также использовать и другие
    категории модулей.
  + Категорию $bold(italic("FP"))(R)$ (строго проективных $R$-модулей и
    $R$-гомоморфизмов) с $perp = tensor_R$ (см. §~@sec:semisimplicity-wedderburn
    гл.~@ch:rings-modules).
  + Категорию $PicCat_R (A)$ обратимых левых $A tensor_R A^degree$-модулей с
    $perp = tensor_A$ (см. §~@sec:picard-group гл.~@ch:module-categories).
    Заметим, что $PicCat_R (R)$~— подкатегория в $bold(italic("FP"))(R)$.
  + Категорию $Quad(R)$ пар $(P, q)$, где $P in bold(P)(R)$ и $q$~—
    несингулярная квадратичная форма на $P$. В качестве морфизмов берутся
    изометрии, а $perp$~— ортогональная прямая сумма. Можно получать аналогичные
    категории и с помощью других форм (альтернирующих, эрмитовых, …).
  + Назовем $A$ #idx("R-алгебра Адзумаи")_$R$-алгеброй Адзумаи_, если существует
    другая $R$-алгебра $B$, для которой $A tensor_R B$ совпадает с полной
    алгеброй матриц над $R$. Алгебры Адзумаи и их изоморфизмы алгебр образуют
    категорию $AzCat(R)$ с произведением $perp = tensor_R$.
  + В категории $bold(P)(A)$ свободные модули являются объектами кофинальной
    подкатегории. Это же верно, но менее очевидно, в категории
    $bold(italic("FP"))(R)$ (см.
    предложение~@prop:strict-projective-free-tensor-complement
    гл.~@ch:projective-k-theory). Если в $bold(italic("FP"))(R)$ в качестве
    морфизмов брать лишь изоморфизмы, то соответствие $P -> End_R (P)$
    определяет сохраняющий произведение функтор
    $bold(italic("FP"))(R) -> AzCat(R)$, и, из последнего замечания вытекает,
    что этот функтор кофинален.
  + Если $bold(A)(R)$~— любая из категорий примеров 2–5 и $R -> S$ гомоморфизм
    коммутативных колец, то $tensor_R S: bold(A)(R) -> bold(A)(S)$ является
    кофинальным функтором, сохраняющим произведение. В примере 1 этот функтор
    индуцирует функтор $bold(P)(A) -> bold(P)(A tensor_R S)$.
] <exm:product-categories>

#definition(word: [Определение функтора $K_0$], upright: true)[
  Пусть $bold(A)$~— категория с произведением. Ее #idx(
    "группа Гротендика",
  )_группой Гротендика_ называется абелева группа $K_0 bold(A)$ вместе с
  отображением
  #symbol-idx($[ ]_(bold(A))$, sort: "[ ]_A", group: "delimiters", order: 163)
  $ [ ]_(bold(A)): ob bold(A) -> K_0 bold(A), $
  которое универсально относительно отображений в абелевы группы,
  удовлетворяющих условиям:

  #named-axiom[если $A tilde.eq B$, то $[A]_(bold(A)) = [B]_(bold(A))$;]
  <ax:grothendieck-isomorphism>
  #named-axiom[$[A perp B]_(bold(A)) = [A]_(bold(A)) + [B]_(bold(A))$
    $(A, B in bold(A))$.] <ax:grothendieck-product>

  Это означает, что любое отображение $f: ob bold(A) -> G$ (где $G$~— абелева
  группа), удовлетворяющее условиям, аналогичным @ax:grothendieck-isomorphism и
  @ax:grothendieck-product, #source(279)можно записать в виде
  $f A = f_0 [A]_(bold(A))$ для однозначно определенного гомоморфизма
  $f_0: K_0 bold(A) -> G$. Для построения группы $K_0 bold(A)$ возьмем свободную
  абелеву группу, базис которой~— классы изоморфных объектов категории
  $bold(A)$, и рассмотрим факторгруппу по подгруппе, порожденной соотношениями,
  соответствующими @ax:grothendieck-product.
]
<def:grothendieck-group>

Непосредственно из определения вытекает, что $K_0 bold(A)$ является функтором от
$bold(A)$ относительно сохраняющих произведение функторов
$F: bold(A) -> bold(A)'$. Таким образом, отображение
$K_0 bold(A) -> K_0 bold(A)'$ определено тем, что
$[A]_(bold(A)) -> [F A]_(bold(A)')$. Мы не будем обозначать это отображение
символом $K_0 (F)$, поскольку $K_0 (F)$ будет использовано для обозначения
«относительной» группы, которая будет введена в
§~@sec:cofinal-functor-exact-sequence.

Если задание категории с произведением $bold(A)$ ясно из контекста, то в
обозначении $[A]_(bold(A))$ мы часто будем опускать нижний индекс.

#proposition[
  Пусть $bold(A)$~— категория с произведением и $bold(B)$~— кофинальная
  подкатегория. Тогда:

  #condition-list[
    #condition-item(format: "cyrillic")[каждый элемент группы $K_0 bold(A)$
      имеет вид $[A]_(bold(A)) - [B]_(bold(A))$, где $A in bold(A)$ и
      $B in bold(B)$;] <cond:grothendieck-cofinal-difference>

    #condition-item(format: "cyrillic")[если $A_1, A_2 in bold(A)$, то
      $[A_1]_(bold(A)) = [A_2]_(bold(A))$ в том и только том случае, когда
      $A_1 perp B tilde.eq A_2 perp B$ для некоторого $B in bold(B)$.]
    <cond:grothendieck-stable-isomorphism>
  ]
] <prop:grothendieck-cofinal-stabilization>

#proof[
  Пусть $F$~— свободная абелева группа, порожденная классами изоморфных объектов
  $(A)$, где $A in bold(A)$, и пусть $R$~— подгруппа, порожденная всеми
  элементами вида $(A, A') = (A perp A') - (A) - (A')$. Тогда отображение
  $(A) -> [A]$ индуцирует изоморфизм $F slash R tilde.eq K_0 bold(A)$.

  Так как элементы $[A]$ порождают группу $K_0 bold(A)$, то любой элемент в ней
  можно записать в виде
  $
    sum_i [A_i] - sum_j [A'_j] = [A] - [A'],
    quad "где" quad A = perp_i A_i quad "и" quad A' = perp_j A'_j .
  $
  Так как подкатегория $bold(B)$ кофинальна, то $A' perp A'' tilde.eq B$ для
  $A'' in bold(A)$ и $B in bold(B)$. Следовательно,
  $[A] - [A'] = [A perp A''] - [A' perp A'']
  = [A perp A''] - [B]$, что доказывает @cond:grothendieck-cofinal-difference.

  В @cond:grothendieck-stable-isomorphism импликация $<=$ тривиальна. Обратно,
  пусть $[A_1] = [A_2]$. Тогда в группе $F$ можно записать равенство
  $(A_1) - (A_2) = sum_i (C_i, C'_i) - sum_j (D_j, D'_j)$, и поэтому
  $
    (A_1) + sum_i ((C_i) + (C'_i)) + sum_j (D_j perp D'_j)
    = (A_2) + sum_i (C_i perp C'_i) + sum_j ((D_j) + (D'_j)).
  $
  Так как в группе $F$ классы изоморфных объектов образуют базис, то из этого
  равенства следует, что
  $ A_1 perp E tilde.eq A_2 perp E, $
  #source(280)где $E = perp_i (C_i perp C'_i) perp perp_j (D_j perp D'_j)$.
  Находя $E' in bold(A)$ и $B in bold(B)$, для которых $E perp E' tilde.eq B$,
  получим, что, как и утверждалось, $A_1 perp B tilde.eq A_2 perp B$.
]

_Примеры_ (см. @exm:product-categories). Группа $K_0 bold(A) = K_0 bold(P)(A)$
для $R$-алгебры $A$ будет детально рассмотрена в гл.~@ch:projective-k-theory.
#idx("группа Пикара")_Группа Пикара_ $Pic_R (A) = K_0 PicCat_R (A)$ уже была
введена в §~@sec:picard-group гл.~@ch:module-categories. Группу #symbol-idx(
  $Quad$,
  sort: "Quad",
  group: "categories",
  order: 21,
)$K_0 Quad(R)$, используя $tensor_R$, можно наделить структурой коммутативного
кольца, естественное факторкольцо которого обычно называется #idx(
  "кольцо Витта",
)_кольцом Витта_ квадратичных форм. Функтор
$End_R: bold(italic("FP"))(R) -> AzCat(R)$ индуцирует гомоморфизм
$K_0 bold(italic("FP"))(R) -> K_0 AzCat(R)$, коядро которого называется #idx(
  "группа Брауэра",
)_группой Брауэра_ кольца $R$.

#definition(word: [Определение: группы $K_1 (bold(A), F)$], upright: true)[
  Пусть $F: bold(A) -> bold(A)'$~— сохраняющий произведение функтор. Тогда можно
  рассмотреть индуцированный функтор
  $ Sigma F: Sigma bold(A) -> Sigma bold(A)', $
  где $Sigma bold(A) = bold(A)^Int$~— категория автоморфизмов объектов категории
  $bold(A)$ (см. §~@sec:categories-functors гл.~@ch:category-algebra), в которой
  произведение определено следующим образом:
  $ (A, alpha) perp (B, beta) = (A perp B, alpha perp beta). $
  Кроме того, функтор $Sigma F$ сохраняет это произведение. Через
  #symbol-idx($Ker$, sort: "Ker", group: "operators", order: 57)
  $ Ker Sigma F subset Sigma bold(A) $
  обозначим полную подкатегорию объектов $(A, alpha)$, таких, что
  $F alpha = 1_(F A)$. #idx("группа Уайтхеда")_Группой Уайтхеда_ категории
  $bold(A)$ относительно функтора $F$ назовем группу
  #symbol-idx($K_1 (bold(A))$, sort: "K_1(A)", group: "groups", order: 106)
  $K_1 (bold(A), F)$ вместе с отображением
  #symbol-idx(
    $[ ]_(bold(A), F)$,
    sort: "[ ]_(A,F)",
    group: "delimiters",
    order: 164,
  )
  $ [ ]_(bold(A), F): ob Ker Sigma F -> K_1 (bold(A), F), $
  которое универсально относительно отображений в абелевы группы,
  удовлетворяющих условиям:

  #named-axiom[если $(A, alpha) tilde.eq (B, beta)$, то
    $[A, alpha]_(bold(A), F) = [B, beta]_(bold(A), F)$;]
  <ax:whitehead-isomorphism>
  #named-axiom[$[A perp B, alpha perp beta]_(bold(A), F)
    = [A, alpha]_(bold(A), F) + [B, beta]_(bold(A), F)$;]
  <ax:whitehead-product>
  #named-axiom[$[A, alpha alpha']_(bold(A), F)
  = [A, alpha]_(bold(A), F) + [A, alpha']_(bold(A), F)$]
  <ax:whitehead-composition>

  (здесь $A, B in bold(A)$, $alpha, alpha' in Aut_(bold(A)) (A, F)$ и
  $beta in Aut_(bold(A)) (B, F)$, где
  $Aut_(bold(A)) (A, F) = Ker(Aut_(bold(A)) (A) -> Aut_(bold(A)') (F A))$).

  Если $F$~— постоянный функтор, то $Ker Sigma F = Sigma bold(A)$, и в этом
  случае мы будем употреблять обозначение
  $K_1 (bold(A))$
  #source(281)вместо $K_1 (bold(A), "постоянный функтор")$.
] <def:whitehead-group>

Функторы $Ker Sigma F subset Sigma bold(A) arrow.r^(Sigma F) Sigma bold(A)'$
индуцируют гомоморфизмы

#assertion(italic: false)[
  $ K_1 (bold(A), F) arrow.r^j K_1 (bold(A)) -> K_1 (bold(A)'), $
  композиция которых, очевидно, равна нулю. В предложении
  @prop:relative-whitehead-image-kernel будет дан критерий точности этой
  последовательности.
] <ss:relative-whitehead-functor-sequence>

В §~@sec:cofinal-functor-exact-sequence мы построим последовательность вида
$
  K_1 (F) arrow.r^j K_1 (bold(A)) -> K_1 (bold(A)') -> K_0 (F) -> K_0 (bold(A))
  -> K_0 (bold(A)')
$
для кофинального функтора $F: bold(A) -> bold(A)'$, сохраняющего произведение.
Мы убедимся, что гомоморфизм $j$ можно пропустить через гомоморфизм
$h: K_1 (bold(A), F) -> K_1 (F)$, который в ряде случаев является изоморфизмом.

#proposition[
  Пусть $F: bold(A) -> bold(A)'$~— сохраняющий произведение функтор. Если
  $(A, alpha) in Ker Sigma F$, то через $[alpha]$ обозначим
  $[A, alpha]_(bold(A), F)$ группы $K_1 (bold(A), F)$.

  #condition-list[
    #condition-item(format: "cyrillic")[Каждый элемент группы $K_1 (bold(A), F)$
      имеет вид $[alpha]$ для некоторого объекта
      $(A, alpha) in Ker Sigma F$.] <cond:whitehead-single-automorphism>

    #condition-item(format: "cyrillic")[$[alpha] = [beta]$ в $K_1 (bold(A), F)$
      тогда и только тогда, когда существуют элементы $gamma$, $delta_0$,
      $delta_1$, $epsilon_0$, $epsilon_1$, такие, что произведения
      $delta_0 delta_1$ и $epsilon_0 epsilon_1$ определены и имеет место
      изоморфизм объектов категории $Ker Sigma F$:
      $
        alpha perp gamma perp delta_0 perp delta_1 perp epsilon_0 epsilon_1
        tilde.eq beta perp gamma perp delta_0 delta_1 perp epsilon_0 perp
        epsilon_1.
      $] <cond:whitehead-equality-stabilization>
  ]
] <prop:whitehead-stabilization-relations>

#proof[
  Так как группа $K_1 (bold(A), F)$ является факторгруппой, скажем,
  $K_0 (Ker Sigma F) slash M$ группы $K_0 (Ker Sigma F)$, то из
  предложения~@prop:grothendieck-cofinal-stabilization следует, что каждый ее
  элемент можно записать в виде $[alpha] - [beta]$. Из аксиомы
  @ax:whitehead-composition вытекает, что
  $0 = [1] = [beta beta^(-1)] = [beta] + [beta^(-1)]$, и поэтому
  $[alpha] - [beta] = [alpha perp beta^(-1)]$. Это доказывает
  @cond:whitehead-single-automorphism.

  Для доказательства @cond:whitehead-equality-stabilization заметим сначала, что
  приведенная выше подгруппа $M$ порождается элементами вида
  $chevron.l alpha, beta chevron.r = [alpha beta]' - [alpha]' - [beta]'$, где
  через $[ ]'$ обозначен класс элемента в $K_0 (Ker Sigma F)$. Если
  $chevron.l alpha', beta' chevron.r$~— другой такой элемент, то
  $chevron.l alpha, beta chevron.r + chevron.l alpha', beta' chevron.r
  = chevron.l alpha perp alpha', beta perp beta' chevron.r$, поскольку
  $(alpha perp alpha')(beta perp beta') = alpha beta perp alpha' beta'$
  ($perp$~— функтор двух переменных). Из этого следует, что любой элемент
  подгруппы $M$ является разностью
  $chevron.l delta_0, delta_1 chevron.r - chevron.l epsilon_0, epsilon_1
  chevron.r$. Далее, если $[alpha] = [beta]$ в $K_1 (bold(A), F)$, то
  $[alpha]' - [beta]' in M$ и, следовательно, разность имеет указанный выше вид.
  Таким образом,
  $
    [alpha]' + [delta_0]' + [delta_1]' + [epsilon_0 epsilon_1]'
    = [beta]' + [delta_0 delta_1]' + [epsilon_0]' + [epsilon_1]'
  $
  в группе $K_0 (Ker Sigma F)$. Применяя @cond:grothendieck-stable-isomorphism к
  этому уравнению, получим элемент $gamma$, удовлетворяющий утверждению
  предложения, что и требовалось доказать.
]

#source(282)Из коммутативности функтора $perp$ следует, что для любой
перестановки $s$ элементов $\{1, dots, n\}$ и для любых объектов
$A_1, dots, A_n in bold(A)$ имеет место изоморфизм
$ A_1 perp dots.c perp A_n arrow.r^s A_(s(1)) perp dots.c perp A_(s(n)). $
Если $alpha_i: A_i -> B_i$~— морфизмы категории $bold(A)$, то следующая
диаграмма
#permuted-morphism-square()
коммутативна, т. е.
$
  s(alpha_1 perp dots.c perp alpha_n)s^(-1)
  = alpha_(s(1)) perp dots.c perp alpha_(s(n)).
$

Предположим далее, что нам даны изоморфизмы $alpha_i: A_i -> A_(i+1)$,
$1 <= i < n$, и $alpha_n: A_n -> A_1$. Пусть
$ s(i) = i - 1 quad (mod n). $ <eq:whitehead-cyclic-permutation>
Положим $alpha = alpha_1 perp dots.c perp alpha_n$. Тогда
$(A_1 perp dots.c perp A_n, s alpha) in Sigma bold(A)$. Пусть
$
  beta = (1_(A_1) perp alpha_1^(-1) perp dots.c perp
    (alpha_(n-1) dots.c alpha_1)^(-1)):
  A_1 perp A_2 perp dots.c perp A_n -> A_1 perp A_1 perp dots.c perp A_1.
$ <eq:whitehead-conjugating-isomorphism>
Тогда $beta: (A_1 perp dots.c perp A_n, s alpha)
-> (A_1 perp dots.c perp A_1, beta(s alpha)beta^(-1))$ является изоморфизмом в
категории $Sigma bold(A)$. В силу приведенной ранее формулы
$alpha beta^(-1) = alpha_1 perp alpha_2 alpha_1 perp dots.c perp
(alpha_n dots.c alpha_1)$ и $beta s = s(alpha_1^(-1) perp
  (alpha_2 alpha_1)^(-1) perp dots.c perp 1_(A_1))$. Следовательно,
$
  beta s alpha beta^(-1) = s(1_(A_1) perp dots.c perp 1_(A_1)
    perp (alpha_n dots.c alpha_1)).
$ <eq:whitehead-cyclic-conjugation>
Это доказывает следующее утверждение:

#lemma(title: [абстрактная лемма Уайтхеда])[
  #idx("абстрактная лемма Уайтхеда")Пусть $bold(A)$~— категория с произведением,
  $alpha_i: A_i -> A_(i+1)$, $1 <= i < n$, и $alpha_n: A_n -> A_1$~— изоморфизмы
  в $bold(A)$. Пусть $s$~— циклическая перестановка $s(i) = i - 1 quad (mod n)$.
  Тогда в категории $Sigma bold(A)$ имеет место изоморфизм
  $(A_1 perp dots.c perp A_n, s(alpha_1 perp dots.c perp alpha_n))
  tilde.eq (A_1 perp dots.c perp A_1,
    s(1_(A_1) perp dots.c perp 1_(A_1) perp (alpha_n dots.c alpha_1)))$. В
  частности, если $alpha: A -> B$ и $beta: B -> C$~— изоморфизмы, то
  $ (A perp B, t(alpha perp alpha^(-1))) tilde.eq (A perp A, t) $
  и
  $
    (A perp B perp C, s(alpha perp beta perp (beta alpha)^(-1)))
    tilde.eq (A perp A perp A, s)
  $
  в $Sigma bold(A)$, где $t$ и $s$~— транспозиция и цикл длины три
  соответственно.
] <lem:abstract-whitehead>

#source(283)Предположим, что все рассматриваемые $A_i$ являются одним и тем же
объектом $A$, и допустим, что $alpha_n dots.c alpha_1 = 1_A$. Тогда из
равенства~@eq:whitehead-cyclic-conjugation следует, что
$alpha = s^(-1) beta^(-1) s beta$. Таким образом, имеет место

#lemma[
  Пусть $alpha_1, dots, alpha_n in Aut_(bold(A)) (A)$ таковы, что
  $alpha_n dots.c alpha_1 = 1_A$. Тогда
  $ alpha_1 perp dots.c perp alpha_n = s^(-1) beta^(-1) s beta, $
  где $s$ и $beta$ такие же, как в формулах @eq:whitehead-cyclic-permutation и
  @eq:whitehead-conjugating-isomorphism выше.
] <lem:whitehead-diagonal-commutator>

#proposition[
  Пусть $[A, alpha] = 0$ в $K_1 bold(A)$. Тогда найдется объект
  $(F, phi) in Sigma bold(A)$, для которого $alpha perp phi perp phi^(-1)$
  является коммутатором в группе $Aut_(bold(A)) (A perp F perp F)$. Кроме того,
  $alpha perp 1_(F perp F)$~— произведение двух коммутаторов.
] <prop:whitehead-commutator-stabilization>

#proof[
  Так как $[alpha] = [1_A]$, то
  $
    alpha perp gamma perp delta_0 perp delta_1 perp epsilon_0 epsilon_1
    tilde.eq 1_A perp gamma perp delta_0 delta_1 perp epsilon_0 perp epsilon_1,
  $
  <eq:whitehead-null-stabilization>
  как в @prop:whitehead-stabilization-relations
  @cond:whitehead-equality-stabilization. Обозначая область определения каждого
  из автоморфизмов соответствующей латинской буквой, получаем, в частности, что
  $A perp C perp D perp D' perp E tilde.eq A perp C perp D perp E perp E'$.
  Пусть $X = A perp C perp D perp E$. Тогда $D' perp X tilde.eq E' perp X$.
  Кроме того, указанный изоморфизм @eq:whitehead-null-stabilization сохраняется,
  если мы заменим $delta_i$ на $delta_i perp 1_X$ и $epsilon_i$ на
  $epsilon_i perp 1_X$ ($i = 0, 1$), поскольку это равносильно добавлению трех
  автоморфизмов $1_X$ к каждой стороне. Таким образом, изменяя обозначения,
  можно считать, что $D = E$. Если добавить $1_D$ к каждой стороне, то получим
  изоморфизм объектов
  $
    alpha_1 = alpha perp gamma perp delta_0 perp delta_1 perp 1_D
    perp epsilon_0 epsilon_1,
  $
  $
    alpha_2 = 1_A perp gamma perp 1_D perp delta_0 delta_1 perp epsilon_0
    perp epsilon_1,
  $
  где $alpha_1, alpha_2 in Aut_(bold(A)) (A perp C perp D^4)$. Существование
  этого изоморфизма как раз и означает, что автоморфизмы $alpha_1$ и $alpha_2$
  сопряжены, и поэтому $alpha_1 alpha_2^(-1)$~— коммутатор. Таким образом,
  $
    alpha_1 alpha_2^(-1) = alpha perp 1_C perp delta_0 perp delta_0^(-1)
    perp epsilon_0^(-1) perp epsilon_0.
  $
  Положим $F = C perp D perp D$ и $phi = 1_C perp delta_0 perp epsilon_0$. Тогда
  $ alpha_1 alpha_2^(-1) perp 1_C tilde.eq alpha perp phi perp phi^(-1), $
  и очевидно, что этот автоморфизм также является коммутатором. Наконец, из
  леммы~@lem:whitehead-diagonal-commutator вытекает, что
  $1_A perp phi^(-1) perp phi$~— коммутатор, и поэтому
  $
    alpha perp 1_(F perp F) = (alpha perp phi perp phi^(-1))
    (1_A perp phi^(-1) perp phi)
  $
  является произведением двух коммутаторов, что и требовалось доказать.
]

#corollary[
  #source(284)Предположим, что $alpha$~— элемент коммутанта группы
  $Aut_(bold(A)) (A)$. Тогда найдется $phi in Aut_(bold(A)) (A^n)$ при некотором
  $n >= 0$, для которого $alpha perp phi perp phi^(-1)$~— коммутатор, а
  $alpha perp 1_(A^(2n))$~— произведение двух коммутаторов.
] <cor:whitehead-stabilized-commutator>

#proof[
  Пусть $bold(B)$~— полная подкатегория в категории $bold(A)$, объекты которой
  $A^n = A perp dots.c perp A$ ($n$ членов). Тогда $[alpha]_B = 0$ в
  $K_1 bold(B)$, поскольку отображение $Aut_(bold(A)) (A) -> K_1 bold(B)$
  является гомоморфизмом в абелеву группу. Следствие вытекает, таким образом, из
  предложения~@prop:whitehead-commutator-stabilization.
]
