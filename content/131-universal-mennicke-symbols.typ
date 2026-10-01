#import "main-defs.typ": (
  E, GL, Ker, SK, SL, U, idx, mennicke, mennickeRelation, name-idx, source,
  symbol-idx,
)
#import "statements.typ": (
  condition-item, condition-list, definition, named-axiom, named-axiom-group,
  proof, proposition,
)
#import "diagrams/mennicke-symbols-diagrams.typ": (
  first-row-arrow, first-row-factorization,
)

== Символы Меннике $mennicke(b, a)$ <sec:universal-mennicke-symbols>

_Зафиксируем коммутативное кольцо $A$ и идеал $frak(q)$ в нем._ Через
$W_frak(q)$#symbol-idx($W_frak(q)$, sort: "W_q", group: "groups", order: 127)
обозначим множество $frak(q)$-унимодулярных элементов из $A^2$. Именно,

$
  W_frak(q) = {(a, b) in A^2 | (a, b) equiv (1, 0) mod frak(q);
    a A + b A = A}.
$

Предмет изучения в этом параграфе описывается следующим образом.

#definition[
  Пусть $C$ — группа. Функция
  $ [ ]: W_frak(q) -> C, quad (a, b) arrow.r.bar mennicke(b, a), $
  называется _символом Меннике_,#idx("символ Меннике")#symbol-idx(
    $mennicke(a, b)$,
    sort: "[a/b]",
    group: "delimiters",
    order: 161,
  ) если она удовлетворяет условиям @ax:mennicke-invariance и
  @ax:mennicke-multiplicativity, приводимым ниже:

  #named-axiom-group(
    [#named-axiom[
      $mennicke(b + t a, a) = mennicke(b, a)$, если $(a, b) in W_frak(q)$ и
      $t in frak(q)$.
    ] <ax:mennicke-upper-transvection>],
    [#named-axiom[
      $mennicke(b, a + t b) = mennicke(b, a)$, если $(a, b) in W_frak(q)$ и
      $t in A$.
    ] <ax:mennicke-lower-transvection>],
  ) <ax:mennicke-invariance>

  (Отметим #source(230)несимметричность этих условий.)

  #named-axiom-group(
    [#named-axiom[
      $mennicke(b_1, a) mennicke(b_2, a) = mennicke(b_1 b_2, a)$, если
      $(a, b_1), (a, b_2) in W_frak(q)$.
    ] <ax:mennicke-first-multiplicativity>],
    [#named-axiom[
      $mennicke(b, a_1) mennicke(b, a_2) = mennicke(b, a_1 a_2)$, если
      $(a_1, b), (a_2, b) in W_frak(q)$.
    ] <ax:mennicke-second-multiplicativity>],
  ) <ax:mennicke-multiplicativity>
] <def:mennicke-symbol>

Из этого определения ясно, что существует _универсальный символ Меннике_#idx(
  "универсальный символ Меннике",
) $[ ]_frak(q): W_frak(q) -> C_frak(q)$, характеризуемый тем свойством, что
любой другой символ Меннике $[ ]$ может быть представлен в виде
$h compose [ ]_frak(q)$, где $h$ — однозначно определенный гомоморфизм
$C_frak(q) -> C$. Кроме того, группа $C_frak(q)$ тем самым определена с
точностью до единственного изоморфизма. Ее можно построить, например, как группу
с образующими из $W_frak(q)$ и соотношениями @ax:mennicke-invariance и
@ax:mennicke-multiplicativity. (Далее мы убедимся, что эти аксиомы не являются
независимыми, а потому это задание группы $C_frak(q)$ не является самым
экономным.) Основная теорема этой главы утверждает, что _если $A$ — дедекиндово
кольцо_, то $C_frak(q) tilde.eq SK_1 (A, frak(q))$. Это объясняет наш интерес к
символам Меннике. Следствие из этого результата: для любой группы $C$ задание
гомоморфизма $SK_1 (A, frak(q)) -> C$ равносильно заданию символа Меннике
$W_frak(q) -> C$. В последнем параграфе будут приведены примеры, в которых
группы $SK_1 (A, frak(q))$ можно вычислить с помощью символов Меннике. Начнем с
установления некоторых элементарных свойств символов Меннике.

#proposition[
  #condition-list[
    #condition-item(format: "cyrillic")[
      Если $alpha = mat(a, b; c, d) in GL_2 (A, frak(q))$, то
      $(a, b) in W_frak(q)$. Возникающее отображение
      $ GL_2 (A, frak(q)) #first-row-arrow() W_frak(q) $
      индуцирует биективное отображение
      $ S N without SL_2 (A, frak(q)) -> N without GL_2 (A, frak(q)), $
      где левая и правая части обозначают множества смежных классов по
      подгруппам для $S N = {I + t e_(2 1) | t in frak(q)}$ и
      $N = {mat(1, 0; c, d) in GL_2 (A, frak(q))}$ соответственно.
    ] <cond:mennicke-first-row-cosets>

    #condition-item(format: "cyrillic")[
      Пусть $k: SL_2 (A, frak(q)) -> C$ — гомоморфизм, такой, что $Ker(k)$
      содержит $E_2 (A, frak(q))$ и $[E_2 (A), SL_2 (A, frak(q))]$. Тогда
      гомоморфизм $k$ допускает разложение
      $ #first-row-factorization() $ <eq:homomorphism-first-row-factorization>
      и функция $[ ]$ удовлетворяет условию @ax:mennicke-invariance.
    ] <cond:mennicke-first-row-factorization>
  ]
] <prop:mennicke-first-row-factorization>

#source(231)В § @sec:mennicke-main-theorems мы выясним, при каких дополнительных
условиях на $k$ функция $[ ]$ является символом Меннике.

#proof[
  @cond:mennicke-first-row-cosets Очевидно, что
  $(a, b) equiv (1, 0) mod frak(q)$. Кроме того, $a d - b c in U(A)$. Таким
  образом, $(a, b) in W_frak(q)$, и мы получаем отображение
  $GL_2 (A, frak(q)) #first-row-arrow() W_frak(q)$. Предположим, что первые
  строки матриц $alpha = mat(a, b; c, d)$ и $alpha' = mat(a, b; c', d')$
  одинаковы, т.~е. что $epsilon alpha = epsilon alpha'$, где $epsilon = (1, 0)$.
  Тогда $epsilon alpha' alpha^(-1) = epsilon$, т.~е. $alpha' alpha^(-1) in N$.
  Так как $N inter SL_2 (A, frak(q)) = S N$, то отображение одного множества
  смежных классов в другое корректно определено и инъективно. Его биективность
  следует из @prop:semilocal-commutative-stable-rank
  @cond:commutative-rank-two-transitivity, но мы напомним доказательство. Пусть
  $(a, b) in W_frak(q)$. Запишем $1 = a x + b y$. Положим
  $c = -b y^2 in frak(q)$, $d = x + b x y$. Получим
  $a d - b c = a(x + b x y) + b^2 y^2 = a x + b y(a x + b y) = 1$. Это
  показывает, что $d equiv 1 mod frak(q)$ и, таким образом,
  $mat(a, b; c, d) in SL_2 (A, frak(q))$.

  @cond:mennicke-first-row-factorization Так как
  $S N subset E_2 (A, frak(q)) subset Ker(k)$, то из части
  @cond:mennicke-first-row-cosets следует, что $k$ можно пропустить через
  $W_frak(q) (= S N without SL_2 (A, frak(q)))$ и получить, таким образом,
  диаграмму @eq:homomorphism-first-row-factorization. Пусть
  $alpha = mat(a, b; c, d) in SL_2 (A, frak(q))$. Если $epsilon = I + t e_(1 2)$
  ($t in frak(q)$), то $epsilon in E_2 (A, frak(q)) subset Ker(k)$ и поэтому
  $k(alpha epsilon) = k(alpha)$. Но $alpha epsilon = mat(a, b + t a; ast, ast)$
  и, значит, $mennicke(b + t a, a) = mennicke(b, a)$ для $t in frak(q)$. Если
  $epsilon = I + t e_(2 1)$ ($t in A$), то
  $[alpha, epsilon] = alpha^(-1) alpha^epsilon in Ker(k)$, следовательно,
  $k(alpha^epsilon) = k(alpha)$. Но
  $
    alpha^epsilon = mat(1, 0; -t, 1) mat(a, b; c, d) mat(1, 0; t, 1)
    = mat(a + t b, b; ast, ast),
  $
  и поэтому $mennicke(b, a + t b) = mennicke(b, a)$ для $t in A$. Итак, мы
  проверили справедливость свойств @ax:mennicke-upper-transvection и
  @ax:mennicke-lower-transvection для $[ ]$.
]

Обозначим через $H$ подгруппу группы $SL_2 (A)$, порожденную всеми элементами
$tau_(1 2) (t) = I + t e_(1 2)$ ($t in frak(q)$) и всеми
$tau_(2 1) (t) = I + t e_(2 1)$ ($t in A$). Если $(a, b) in A^2$, то
$(a, b) tau_(1 2) (t) = (a, b + t a)$, в то время как
$(a, b) tau_(2 1) (t) = (a + t b, b)$. Если $(a_1, b_1), (a_2, b_2) in A^2$, то
будем писать

$ (a_1, b_1) mennickeRelation(frak(q)) (a_2, b_2), $
#symbol-idx(
  $mennickeRelation(frak(q))$,
  sort: "~_q",
  group: "symbols",
  order: 145,
)

если существует элемент $tau in H$, такой, что $(a_2, b_2) = (a_1, b_1) tau$.
Это — отношение эквивалентности, порожденное отношениями
$(a, b + t a) mennickeRelation(frak(q)) (a, b)$ при всех $t in frak(q)$ и
$(a + t b, b) mennickeRelation(frak(q)) (a, b)$ при всех #source(232)$t in A$.
Заметим, что если $(a_1, b_1) in W_frak(q)$, то также $(a_2, b_2) in W_frak(q)$.
Кроме того, в этих обозначениях можно переформулировать аксиому
@ax:mennicke-invariance для символа Меннике следующим образом:

#named-axiom[
  $mennicke(b', a') = mennicke(b, a)$, если $(a, b) in W_frak(q)$ и
  $(a', b') mennickeRelation(frak(q)) (a, b)$.
] <ax:mennicke-orbit-invariance>

#proposition[
  Пусть $(a, b) in W_frak(q)$ и $u in U(A)$. Тогда
  $(a, b) mennickeRelation(frak(q)) (a, (1 - a) b)$ и
  $(a, b) mennickeRelation(frak(q)) (1, 0)$, если $a equiv u mod b$ или
  $b equiv u mod a$.
] <prop:mennicke-unit-orbits>

#proof[
  Заметим, что $(a, b) mennickeRelation(frak(q)) (a, b - a b) = (a, (1 - a) b)$.
  Если $a = u - t b$, то
  $
    (a, b) mennickeRelation(frak(q)) (a + t b, b) = (u, b)
    mennickeRelation(frak(q)) (u, b + u dot u^(-1) (1 - u - b))
    = (u, 1 - u) mennickeRelation(frak(q)) (1, 1 - u)
    mennickeRelation(frak(q)) (1, 0).
  $
  Предположим, наконец, что $b = u + t a$. Положим $q = 1 - a$. Тогда
  $
    (a, b) mennickeRelation(frak(q)) (a, q b)
    mennickeRelation(frak(q)) (a, q b - q t a)
    = (a, q u) mennickeRelation(frak(q)) (a + u^(-1) u q, u q)
    = (1, u q) mennickeRelation(frak(q)) (1, 0),
  $
  что и требовалось доказать.
]

#proposition[
  Пусть $frak(q)'$ — идеал, содержащий идеал $frak(q)$. Допустим, что кольцо
  $frac(A, frak(q))$ полулокально. Тогда, если $(a', b') in W_(frak(q)')$, то
  существует элемент $(a, b) in W_frak(q)$, такой, что
  $(a, b) mennickeRelation(frak(q)') (a', b')$.
] <prop:mennicke-semilocal-lifting>

#proof[
  Переходя к $frac(A, frak(q))$ и $frac(frak(q)', frak(q))$, можно считать, что
  $frak(q) = 0$ и что кольцо $A$ полулокально. Тогда в силу
  @prop:semilocal-unit-in-coset можно выбрать $t in A$ таким образом, чтобы
  $a' + t b' in U(A)$. Применяя @prop:mennicke-unit-orbits, получаем, что
  $
    (a', b') mennickeRelation(frak(q)') (a' + t b', b')
    mennickeRelation(frak(q)') (1, 0).
  $
  Предложение доказано.
]

Это предложение особенно полезно в том случае, когда $A$ — нётерова область
целостности размерности $<= 1$. Действительно, тогда кольцо $frac(A, frak(q))$
полулокально (фактически оно артиново) для каждого ненулевого идеала $frak(q)$.

#proposition[
  Пусть $A$ — нётерова область целостности размерности $<= 1$ (например,
  дедекиндово кольцо).
  #condition-list[
    #condition-item(format: "cyrillic")[
      Пусть $frak(q)$ — ненулевой идеал кольца $A$ и $t$ — ненулевой элемент из
      $frak(q)$. Если $(a_1, b_1), dots, (a_n, b_n) in W_frak(q)$, то найдутся
      элементы $(a, c_1 t), dots, (a, c_n t) in W_t (= W_(t A))$, такие, что
      $(a_i, b_i) mennickeRelation(frak(q)) (a, c_i t)$ ($1 <= i <= n$).
    ] <cond:mennicke-common-denominator>
    #condition-item(format: "cyrillic")[
      Пусть $S$ — мультипликативная система кольца $A$, $frak(q)'$ — идеал
      кольца $A' = S^(-1) A$ и $frak(q) = frak(q)' inter A$. Если
      $(a', b') in W_(frak(q)')$, то существует элемент $(a, b) in W_frak(q)$,
      такой, что $(a, b) mennickeRelation(frak(q)') (a', b')$.
    ] <cond:mennicke-localization-lifting>
  ]
] <prop:localized-special-linear-generation>

_Замечание._ Из @prop:localized-special-linear-generation
@cond:mennicke-localization-lifting легко следует, что для всех $n >= 1$ группа
$SL_n (A', frak(q)')$ порождается $E_n (A', frak(q)')$ и $SL_n (A, frak(q))$. В
частности, отображение $SK_1 (A, frak(q)) -> SK_1 (A', frak(q)')$ сюръективно.

#proof[
  @cond:mennicke-common-denominator Так как кольцо $frac(A, t A)$ полулокально,
  то можно использовать @prop:mennicke-semilocal-lifting для нахождения
  элементов #source(233)$(a'_i, b'_i t) in W_t$, таких, что
  $(a'_i, b'_i t) mennickeRelation(frak(q)) (a_i, b_i)$ ($1 <= i <= n$). Проводя
  индукцию по $n$, допустим, что мы нашли $(a', c_i t) in W_t$, для которых
  $(a', c_i t) mennickeRelation(t) (a'_i, c_i t)$ ($1 <= i < n$). Конечно, можно
  добиться того, чтобы каждый элемент $c_i != 0$. Пусть
  $c = c_1 dots c_(n - 1) != 0$. Так как $b'_n$ и $a'_n A$ комаксимальны, то в
  силу @prop:semilocal-unit-in-coset можно подобрать $c_n equiv b'_n mod a'_n$
  так, чтобы элемент $c_n$ переходил в обратимый элемент (полулокального кольца)
  $frac(A, c A)$. Тогда очевидно, что
  $(a'_n, b'_n t) mennickeRelation(t) (a'_n, c_n t)$. Кроме того, если записать
  $a' - a'_n = d t$, то можно выразить $d = r c_n - s c$. Тогда
  $a' - a'_n = r c_n t - s c t$ и поэтому $a'_n + r c_n t = a' + s c t$
  (обозначим этот элемент через $a$). Имеем
  $(a'_n, c_n t) mennickeRelation(t) (a, c_n t)$, и так как
  $c = c_1 dots c_(n - 1)$, то $(a', c_i t) mennickeRelation(t) (a, c_i t)$
  ($1 <= i < n$).

  @cond:mennicke-localization-lifting Пусть $frak(a) != 0$ — идеал кольца $A$.
  Тогда кольцо $frac(A, frak(a))$ артиново, и поэтому
  $frac(A, frak(a)) = product frac(A, frak(q)_i)$, где каждое из колец
  $frac(A, frak(q)_i)$ — локальное с максимальным идеалом
  $frac(frak(p)_i, frak(q)_i)$. Кроме того, $frak(p)_i^(n_i) subset frak(q)_i$
  для некоторого $n_i > 0$, и поэтому $frak(q)_i$ комаксимальны и
  $frak(a) = inter frak(q)_i = product frak(q)_i$ (см. китайскую теорему об
  остатках @prop:chinese-remainder-modules). Кроме того,
  $
    S^(-1) frak(a) = inter S^(-1) frak(q)_i quad (frak(p)_i inter S = emptyset)
    quad "и" quad
    frac(A', S^(-1) frak(a)) = product frac(A, frak(q)_i)
    quad (frak(p)_i inter S = emptyset).
  $
  Эти утверждения следуют из стандартных свойств локализации (см.
  @ch:rings-modules, § @sec:localization-support) и того, что идеалы $frak(p)_i$
  максимальны. Так как любой идеал $frak(a)'$ кольца $A'$ имеет вид
  $frak(a)' = S^(-1) frak(a)$ ($frak(a) = frak(a)' inter A$), то, в частности,
  композиция отображений $A subset A' -> frac(A', frak(a)')$ является
  сюръективным отображением для $frak(a)' != 0$.

  Нам дан элемент $(a', b') in W_(frak(q)')$, и мы хотели бы найти
  $(a, b) in W_frak(q)$, для которого
  $(a, b) mennickeRelation(frak(q)') (a', b')$. Если элемент $a'$ или $b'$ равен
  нулю, то другой элемент обратим, и из @prop:mennicke-unit-orbits следует, что
  $(a', b') mennickeRelation(frak(q)') (1, 0)$. В противном случае в силу
  рассуждения предыдущего абзаца можно найти элемент $b != 0$ в $A$, для
  которого $b equiv b' mod a' frak(q)'$. Кроме того, в этом же абзаце показано,
  что $b A = frak(b)_1 frak(b)_2$, где $frak(b)_1 = b A' inter A$ (и значит,
  $b A' = frak(b)_1 A'$) и где идеалы $frak(b)_2$ и $frak(b)_1$ комаксимальны.
  Выберем элемент $a_1 in A$ так, чтобы $a_1 equiv a' mod b A'$, а затем выберем
  элемент $a in A$ так, чтобы
  $ a equiv a_1 mod frak(b)_1, quad a equiv 1 mod frak(b)_2. $
  Из первого сравнения вытекает, что $a equiv a_1 equiv a' mod b A'$, поэтому
  $
    (a', b') mennickeRelation(frak(q)') (a', b)
    mennickeRelation(frak(q)') (a, b).
  $
  Следовательно, $(a, b) equiv (1, 0) mod frak(q)' inter A (= frak(q))$. Чтобы
  убедиться в том, что $(a, b) in W_frak(q)$, остается показать, что идеал
  $frak(a) = a A + b A$ совпадает с $A$. Конечно, $frak(a) A' = A'$ и
  $frak(a) supset b A = frak(b)_1 frak(b)_2$. Если $s in S inter frak(a)$, то
  $s$ не лежит ни в одном из максимальных идеалов, содержащих $frak(b)_1$. Кроме
  того, $a in frak(a)$ и $a equiv 1 mod frak(b)_2$. Таким образом,
  $A = s A + a A + frak(b)_1 frak(b)_2 subset frak(a)$. Доказательство
  завершено.
]

#source(234)
#proposition[
  Пусть $frak(q)$ — идеал в коммутативном кольце $A$, $C$ — группа и
  $[ ]: W_frak(q) -> C$ — функция, удовлетворяющая условию
  @ax:mennicke-invariance и такая, что $mennicke(0, 1) = 1$. Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[
      если $(a, b) in W_frak(q)$ и если существует элемент $u in U(A)$, для
      которого $a equiv u mod b$ или $b equiv u mod a$, то $mennicke(b, a) = 1$;
    ] <cond:mennicke-unit-symbol>
    #condition-item(format: "cyrillic")[
      если $t in frak(q)$ и $a equiv 1 mod t$, то отображение
      $b arrow.r.bar mennicke(b t, a)$, где $b in A$, $b A + a A = A$,
      индуцирует отображение
      $ U(frac(A, a A)) -> C, $ <eq:mennicke-residue-unit-map>
      композиция которого с отображением $U(A) -> U(frac(A, a A))$ равна
      тождественному отображению $1$;
    ] <cond:mennicke-residue-unit-map>
    #condition-item(format: "cyrillic")[
      если $A$ — нётерова область целостности размерности $<= 1$, то для данных
      элементов $(a_1, b_1), dots, (a_n, b_n) in W_frak(q)$ найдутся элементы
      $t$ и $a$, удовлетворяющие приведенным выше условиям и такие, что все
      $mennicke(b_i, a_i)$ ($1 <= i <= n$) лежат в образе отображения
      @eq:mennicke-residue-unit-map.
    ] <cond:mennicke-finite-common-image>
    Предположим теперь, что отображение $[ ]$ удовлетворяет также и условию
    @ax:mennicke-multiplicativity (откуда следует, что $mennicke(0, 1) = 1$).
    Тогда #condition-item(format: "cyrillic")[
      отображение @eq:mennicke-residue-unit-map является гомоморфизмом; если
      кольцо $A$ удовлетворяет предположениям части
      @cond:mennicke-finite-common-image, то $[W_frak(q)]$ — абелева подгруппа
      группы $C$; кроме того, если $0 != frak(q)' subset frak(q)$, то
      $[W_(frak(q)')] = [W_frak(q)]$;
    ] <cond:mennicke-abelian-image>
    #condition-item(format: "cyrillic")[
      (Кервер)#name-idx("Кервер (Kervaire M.)") если $t in frak(q)$ и элементы
      $a, d in A$ таковы, что $a equiv 1 equiv d mod t$ и $a A + d A = A$, то
      $ mennicke(d t, a) = mennicke(a t, d). $
    ] <cond:kervaire-symbol-transfer>
  ]
] <prop:mennicke-symbol-elementary-properties>

#proof[
  @cond:mennicke-unit-symbol следует из @prop:mennicke-unit-orbits.

  @cond:mennicke-residue-unit-map Пусть $(a, b_1 t), (a, b_2 t) in W_frak(q)$.
  Если $b_2 = b_1 - x a$, то
  $ mennicke(b_2 t, a) = mennicke(b_2 t + x t a, a) = mennicke(b_1 t, a). $
  Таким образом, $mennicke(b t, a)$ зависит лишь от класса элемента $b$ в
  $U(frac(A, a A))$. Если $b in U(A)$, то $a equiv 1 mod t A (= b t A)$, и
  поэтому из @cond:mennicke-unit-symbol следует, что $mennicke(b t, a) = 1$.

  @cond:mennicke-finite-common-image следует из
  @prop:localized-special-linear-generation @cond:mennicke-common-denominator.

  #source(235)@cond:mennicke-abelian-image В силу @cond:mennicke-unit-symbol
  $mennicke(t, a) = 1$; используя @ax:mennicke-first-multiplicativity, мы
  убеждаемся в том, что
  $
    mennicke(b_1 b_2 t, a) = mennicke(b_1 b_2 t, a) mennicke(t, a)
    = mennicke(b_1 t b_2 t, a)
    = mennicke(b_1 t, a) mennicke(b_2 t, a).
  $
  Следовательно, отображение @eq:mennicke-residue-unit-map — гомоморфизм. В
  частности, образ отображения @eq:mennicke-residue-unit-map — абелева подгруппа
  группы $C$. Если кольцо $A$ выбрано, как в @cond:mennicke-finite-common-image,
  то из нашего рассуждения следует, что $[W_frak(q)]$ является объединением
  образов отображений @eq:mennicke-residue-unit-map при различных $t$ и $a$.
  Следовательно, $[W_frak(q)]$ — абелева подгруппа группы $C$. Если
  $0 != frak(q)' subset frak(q)$, то кольцо $frac(A, frak(q)')$ полулокально, и
  поэтому из @prop:mennicke-semilocal-lifting вытекает, что
  $[W_(frak(q)')] = [W_frak(q)]$.

  @cond:kervaire-symbol-transfer Пусть $d - a = x t$. Тогда
  $
    mennicke(d t, a) = mennicke(d t - a t, a) = mennicke(x t^2, a)
    = mennicke(x t, a) = mennicke(x t, d) = mennicke(-x t^2, d)
    = mennicke(a t - d t, d) = mennicke(a t, d),
  $
  что и требовалось доказать.
]

#proposition(title: [Лэм])[
  #name-idx("Лэм (Lam T.-Y.)")Пусть $A$, $frak(q)$ и $C$ выбраны так же, как и в
  @prop:mennicke-symbol-elementary-properties, и пусть функция
  $[ ]: W_frak(q) -> C$ удовлетворяет условию @ax:mennicke-invariance. Тогда
  #condition-list[
    #condition-item(format: "cyrillic")[
      @ax:mennicke-second-multiplicativity $==>$
      @ax:mennicke-first-multiplicativity;
    ] <cond:mennicke-denominator-implies-numerator>
    #condition-item(format: "cyrillic")[
      если $A$ — нётерова область целостности размерности $<= 1$ и $frak(q)$ —
      обратимый идеал, то @ax:mennicke-first-multiplicativity $==>$
      @ax:mennicke-second-multiplicativity.
    ] <cond:mennicke-numerator-implies-denominator>
  ]
] <prop:mennicke-axiom-redundancy>

#proof[
  @cond:mennicke-denominator-implies-numerator Предположим, что выполнено
  @ax:mennicke-second-multiplicativity. Допустим, что $t in frak(q)$,
  $a equiv 1 mod t$ и $(a, b t) in W_frak(q)$. Пусть $a = 1 + s t$. Тогда
  $ mennicke(b t^2, a) = mennicke(-a t, a + b t). $
  <eq:mennicke-square-transfer>
  Действительно,
  $
    mennicke(b t^2, 1 + b t)
    = mennicke(b t^2 - t(1 + b t), 1 + b t)
    = mennicke(-t, 1 + b t) = 1
  $
  и, следовательно,
  $
    mennicke(b t^2, a) = mennicke(b t^2, a) mennicke(b t^2, 1 + b t)
    = mennicke(b t^2, (1 + s t)(1 + b t))
    = mennicke(b t^2, 1 + s t + b t + s b t^2)
    = mennicke(b t^2, a + b t)
    = mennicke(b t^2 - t(a + b t), a + b t)
    = mennicke(-a t, a + b t).
  $
  #source(236)Предположим теперь, что $b = b_1 b_2$. Тогда
  $
    mennicke(b_1 t^2, a) mennicke(b_2 t^2, a)
    = mennicke(-a t, a + b_1 t) mennicke(-a t, a + b_2 t)
    = mennicke(-t a, a^2 + a t(b_1 + b_2) + b_1 b_2 t^2)
    = mennicke(-t a, a(1 + s t) + b_1 b_2 t^2)
    = mennicke(-t a, a + b_1 b_2 t^2)
    = mennicke((b_1 b_2 t) t^2, a)
  $
  (с учетом @eq:mennicke-square-transfer в первом и последнем равенствах).
  Наконец, допустим, что $(a, b_1), (a, b_2) in W_frak(q)$. Покажем, что
  $mennicke(b_1 b_2, a) = mennicke(b_1, a) mennicke(b_2, a)$. Положим
  $t = 1 - a$. Тогда если $(a, b) in W_frak(q)$, то
  $mennicke(b, a) = mennicke(b t, a) = mennicke(b t^n, a)$ для всех $n >= 0$.
  Следовательно, используя проведенные выше вычисления, получаем, что
  $
    mennicke(b_1, a) mennicke(b_2, a)
    = mennicke(b_1 t^2, a) mennicke(b_2 t^2, a)
    = mennicke(b_1 b_2 t^3, a) = mennicke(b_1 b_2, a),
  $
  @cond:mennicke-numerator-implies-denominator Допустим теперь, что $A$ —
  нётерова область целостности размерности $<= 1$, $frak(q)$ — обратимый идеал и
  что выполнено условие @ax:mennicke-first-multiplicativity. Покажем, что если
  $(a_1, b), (a_2, b) in W_frak(q)$, то
  $ mennicke(b, a_1 a_2) = mennicke(b, a_1) mennicke(b, a_2). $
  <eq:mennicke-denominator-multiplicativity>
  _Частный случай._ Существует элемент $t in frak(q)$, для которого
  $a_1 equiv 1 equiv a_2 mod t$. Тогда
  $mennicke(t, a_1 a_2) = 1 = mennicke(t, a_i)$ ($i = 1, 2$), и поэтому
  достаточно доказать, что
  $ mennicke(b t, a_1 a_2) = mennicke(b t, a_1) mennicke(b t, a_2). $
  Никакая из частей этого равенства не меняется при изменении $b$ в одном и том
  же классе по модулю $a_1 a_2$. Если $a_1 a_2 = 0$, то $b in U(A)$, и из
  @prop:mennicke-symbol-elementary-properties @cond:mennicke-residue-unit-map
  следует, что все эти символы равны $1$. В противном случае можно, изменяя $b$
  по модулю $a_1 a_2$, добиться того, что элементы $b$ и $t$ будут
  комаксимальны. (Можно допустить, что $t != 0$, поскольку иначе задача
  тривиальна.) Затем можно найти элемент $b' in A$, для которого
  $b' equiv 1 mod a_1 a_2$ и $b_1 equiv 1 mod t$, где $b_1 = b' b$. Далее,
  используя @prop:mennicke-symbol-elementary-properties
  @cond:mennicke-abelian-image, получаем, что
  $
    mennicke(b_1 t, a_1 a_2)
    = mennicke(b' t, a_1 a_2) mennicke(b t, a_1 a_2)
    = mennicke(b t, a_1 a_2)
  $
  #source(237)и
  $
    mennicke(b_1 t, a_i) = mennicke(b' t, a_i) mennicke(b t, a_i)
    = mennicke(b t, a_i) quad (i = 1, 2).
  $
  Наконец, применяя @prop:mennicke-symbol-elementary-properties
  @cond:kervaire-symbol-transfer, получаем, что
  $
    mennicke(b_1 t, a_1 a_2) = mennicke(a_1 a_2 t, b_1)
    = mennicke(a_1 t, b_1) mennicke(a_2 t, b_1)
    = mennicke(b_1 t, a_1) mennicke(b_1 t, a_2),
  $
  и это завершает разбор частного случая.

  _Общий случай._ Пусть $a_1 = 1 - t$. Если $t = 0$, то мы находимся в рамках
  частного случая. Поэтому допустим, что $t != 0$. Если заменить $b$ на
  $b_1 = b + s a_1 a_2$, где $s in frak(q)$, то ни одна из сторон равенства
  @eq:mennicke-denominator-multiplicativity не изменится. Покажем, что можно так
  подобрать элемент $s$, что элементы $t$ и $b_1$ будут порождать идеал
  $frak(q)$. Действительно, достаточно так выбрать $s$, чтобы это имело место
  для каждого из (конечного числа) максимальных идеалов, содержащих $t$. В силу
  китайской теоремы об остатках достаточно осуществить это локально. Но тогда
  обратимый идеал $frak(q)$ является главным и либо $a_1 a_2$, либо $b$ —
  обратимый элемент. Следовательно, такой элемент $s$ существует.

  Так как $frak(q) = A t + A b_1$, то $a_2 = 1 + x t + y b_1$. Ни одна из сторон
  желаемого равенства
  $ mennicke(b_1, a_1 a_2) = mennicke(b_1, a_1) mennicke(b_1, a_2). $
  не изменится, если заменить $a_2$ на $a'_2 = a_2 - y b_1$. Но $(a_1, b_1)$ и
  $(a'_2, b_1)$ удовлетворяют условиям первого случая, что и завершает
  доказательство.
]
