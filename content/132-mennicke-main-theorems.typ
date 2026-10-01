#import "main-defs.typ": (
  E, GE, GL, Ker, SK, SL, dim, idx, mennicke, name-idx, source,
)
#import "statements.typ": (
  assertion, condition-item, condition-list, corollary, proof, theorem,
)
#import "diagrams/mennicke-symbols-diagrams.typ": (
  first-row-arrow, first-row-factorization, universal-first-row-factorization,
)

== Основные теоремы <sec:mennicke-main-theorems>

Пусть $frak(q)$ — идеал коммутативного кольца $A$, $k: SL_2 (A, frak(q)) -> C$ —
такой гомоморфизм групп, что $Ker k$ содержит $E_2 (A, frak(q))$ и
$[E_2 (A), SL_2 (A, frak(q))]$. Тогда в силу
@prop:mennicke-first-row-factorization @cond:mennicke-first-row-factorization
гомоморфизм $k$ допускает следующее разложение:

$ #first-row-factorization() $ <eq:mennicke-main-first-row-factorization>

и отображение $[ ]$ удовлетворяет условию @ax:mennicke-invariance. Очевидно, что
$mennicke(0, 1) = 1$.

#source(238)
#theorem[
  #condition-list[
    #condition-item(format: "cyrillic")[
      Отображение $[ ]$ удовлетворяет условию
      @ax:mennicke-first-multiplicativity тогда и только тогда, когда
      гомоморфизм $k$ удовлетворяет следующему условию:
      $
        "если элементы" quad alpha, alpha' in SL_2 (A, frak(q))
        quad "имеют вид" quad
        alpha = mat(1 + t a, b; t c, d) quad "и" quad
        alpha' = mat(1 + t a, t b; c, d), quad "где" quad a, t in frak(q),
        quad "то" quad k(alpha) = k(alpha').
      $ <eq:mennicke-matrix-transfer-condition>
    ] <cond:mennicke-matrix-transfer-criterion>
    #condition-item(format: "cyrillic")[
      (Меннике).#name-idx("Меннике (Mennicke)")#idx("теорема", "Меннике") Если
      гомоморфизм $k$ является ограничением такого гомоморфизма
      $k': SL_3 (A, frak(q)) -> C$, что
      $[E_3 (A), SL_3 (A, frak(q))] subset Ker(k')$, то отображение $[ ]$ —
      символ Меннике.
    ] <cond:mennicke-stable-restriction-symbol>
  ]
] <th:mennicke-symbol-homomorphism-criterion>

Через $M S (A, frak(q))$ обозначим нормальный делитель в $SL_2 (A, frak(q))$,
порожденный $E_2 (A, frak(q))$, $[E_2 (A), SL_2 (A, frak(q))]$ и всеми
элементами $alpha^(-1) alpha'$, где $alpha$, $alpha'$ — описанные в
@eq:mennicke-matrix-transfer-condition матрицы.

#corollary[
  В предположениях теоремы @th:mennicke-symbol-homomorphism-criterion допустим,
  что $A$ — нётерова область целостности размерности $<= 1$ и что $frak(q)$ —
  обратимый идеал. Тогда $[ ]$ — символ Меннике в том и только в том случае,
  когда $M S (A, frak(q)) subset Ker(k)$.
] <cor:mennicke-normal-subgroup-criterion>

#proof[
  Утверждение немедленно следует из @th:mennicke-symbol-homomorphism-criterion
  @cond:mennicke-matrix-transfer-criterion и @prop:mennicke-axiom-redundancy
  @cond:mennicke-numerator-implies-denominator.
]

#proof(head: [Доказательство @th:mennicke-symbol-homomorphism-criterion
  @cond:mennicke-matrix-transfer-criterion.])[
  Если $alpha = mat(a, b; c, d) in SL_2 (A, frak(q))$, то
  $mennicke(b, a) = k(alpha)$.

  @ax:mennicke-first-multiplicativity $==>$
  @eq:mennicke-matrix-transfer-condition. Если элементы $alpha$ и $alpha'$
  удовлетворяют условию @eq:mennicke-matrix-transfer-condition, то
  $
    k(alpha') = k(mat(1 + a t, b t; c, d)) = mennicke(b t, 1 + a t)
    = mennicke(b, 1 + a t) mennicke(t, 1 + a t)
    = mennicke(b, 1 + a t) = k(alpha).
  $
  @eq:mennicke-matrix-transfer-condition $==>$
  @ax:mennicke-first-multiplicativity. Отметим сначала непосредственное
  следствие условия @eq:mennicke-matrix-transfer-condition: если
  $(a, b) in W_frak(q)$ и $a = 1 + x t$, где $x, t in frak(q)$, то
  $ mennicke(b t, a) = mennicke(b, a). $
  <eq:mennicke-small-transvection-invariance>
  Сейчас мы должны доказать, что если $(a, b_0), (a, b_1) in W_frak(q)$, то
  $mennicke(b_0 b_1, a) = mennicke(b_0, a) mennicke(b_1, a)$. Пусть $a = 1 + q$,
  и поэтому $q in frak(q)$; выберем #source(239)элемент $c in A$ таким образом,
  чтобы
  $ c equiv 1 mod q, quad b_0 b_1 c equiv -1 mod a $
  (скажем, $1 + b_0 b_1 c = a d$). Тогда
  $alpha_i = mat(a, b_i; b_(1 - i) c, d) in SL_2 (A, frak(q))$ и
  $mennicke(b_i, a) = k(alpha_i)$ ($i = 0, 1$). Пусть
  $pi = mat(0, -1; 1, 0) in E_2 (A)$. Тогда в силу предположения
  $k(alpha^pi) = k(alpha)$ для $alpha in SL_2 (A, frak(q))$. Следовательно,
  $
    mennicke(b_0, a) mennicke(b_1, a) = k(alpha_0) k(alpha_1^pi)
    = k(alpha_0 alpha_1^pi),
  $
  где
  $
    alpha_0 alpha_1^pi = mat(a, b_0; b_1 c, d) mat(d, -b_0 c; -b_1, a)
    = mat(a d - b_0 b_1, a b_0 - a b_0 c; ast, ast)
    = mat(1 - b_0 b_1 (1 - c), a b_0 (1 - c); ast, ast).
  $
  Так как $c equiv 1 mod q$ (напомним, что $q = a - 1$), то $1 - c = t q$ и
  $
    mennicke(b_0, a) mennicke(b_1, a)
    = mennicke(a b_0 t q, 1 - b_0 b_1 t q)
    = mennicke(a q, 1 - b_0 b_1 t q)
    = mennicke(a q, a - q(1 + b_0 b_1 t))
    = mennicke(a q - q(a - q(1 + b_0 b_1 t)), a - q(1 + b_0 b_1 t))
    = mennicke(q^2(1 + b_0 b_1 t), a - q(1 + b_0 b_1 t))
    = mennicke(q(1 + b_0 b_1 t), a - q(1 + b_0 b_1 t))
    = mennicke(q(1 + b_0 b_1 t), a)
    = mennicke(q + b_0 b_1 (1 - c), a).
  $
  Во втором равенстве применено @eq:mennicke-small-transvection-invariance с
  $b_0 t$ вместо $t$, третье равенство следует из $a = 1 + q$; в шестом
  равенстве применено @eq:mennicke-small-transvection-invariance с
  $t = q (= a - 1)$; последнее равенство использует $1 - c = q t$.
  #source(240)
  $
    mennicke(q + b_0 b_1 (1 - c), a)
    = mennicke(b_0 b_1 + q - b_0 b_1 c, a)
    = mennicke(b_0 b_1 + q + 1 - a d, a)
    = mennicke(b_0 b_1 + a(1 - d), a) = mennicke(b_0 b_1, a)
  $
  (так как $a d - b_0 b_1 c = 1$).
]

#proof(head: [Доказательство @th:mennicke-symbol-homomorphism-criterion
  @cond:mennicke-stable-restriction-symbol.])[
  В силу @prop:mennicke-axiom-redundancy
  @cond:mennicke-denominator-implies-numerator, для того чтобы убедиться в том,
  что отображение $[ ]$ является символом Меннике, достаточно проверить
  выполнение условия @ax:mennicke-second-multiplicativity. Пусть
  $(a_1, b), (a_2, b) in W_frak(q)$. Достаточно показать, что
  $mennicke(b, a_1 a_2) = mennicke(b, a_1) mennicke(b, a_2)$, в предположении,
  что $k$ можно продолжить до гомоморфизма $k'$, определенного на
  $SL_3 (A, frak(q))$ и содержащего в своем ядре подгруппу $E_3 (A, frak(q))$.

  Выберем $alpha_i = mat(a_i, b; c_i, d_i) in SL_2 (A, frak(q))$. Пусть
  $
    overline(alpha)_i = mat(alpha_i, 0; 0, 1) quad (i = 1, 2),
    quad "и пусть" quad overline(pi) = mat(-1, 0; 0, pi) in E_3 (A),
  $
  где $pi = mat(0, 1; 1, 0)$. Тогда
  $
    mennicke(b, a_1) mennicke(b, a_2) = k(alpha_1) k(alpha_2)
    = k'(overline(alpha)_1) k'(overline(alpha)_2^overline(pi)) = k'(alpha),
  $
  где
  $
    alpha = overline(alpha)_1 overline(alpha)_2^overline(pi)
    = mat(a_1, b, 0; c_1, d_1, 0; 0, 0, 1)
    mat(a_2, 0, -b; 0, 1, 0; -c_2, 0, d_2)
    = mat(a_1 a_2, b, -a_1 b; c_1 a_2, d_1, -c_1 b; -c_2, 0, d_2).
  $
  Пусть $epsilon_1 = I + a_1 e_(2 3) in E_3 (A)$. Тогда
  $
    alpha^(epsilon_1)
    = mat(
      a_1 a_2, b, 0;
      c_1 a_2 - c_2 a_1, d_1, a_1 d_1 - a_1 d_2 - c_1 b;
      -c_2, 0, d_2
    )
    = mat(a_1 a_2, b, 0; x, d_1, 1 - a_1 d_2; -c_2, 0, d_2).
  $
  #source(241)Пусть $epsilon_2 = I + (a_1 - 1) e_(2 3)$. Тогда
  $
    epsilon_2 alpha^(epsilon_1)
    = mat(a_1 a_2, b, 0; y, d_1, 1 - d_2; -c_2, 0, d_2).
  $
  Пусть $epsilon_3 = I - e_(3 2) in E_3 (A)$. Тогда
  $
    (epsilon_2 alpha^(epsilon_1))^(epsilon_3)
    = mat(
      a_1 a_2, b, 0; y, d_1 + d_2 - 1, 1 - d_2;
      y - c_2, d_1 - 1, 1
    ).
  $
  Пусть $epsilon_4 = I + (d_2 - 1) e_(2 3) in E_3 (A, frak(q))$. Тогда
  $
    epsilon_4 (epsilon_2 alpha^(epsilon_1))^(epsilon_3)
    = mat(a_1 a_2, b, 0; z, d_1 d_2, 0; y - c_2, d_1 - 1, 1).
  $
  Пусть $beta = mat(a_1 a_2, b; z, d_1 d_2)$ и
  $overline(beta) = mat(beta, 0; 0, 1)$. Тогда
  $epsilon_4 (epsilon_2 alpha^(epsilon_1))^(epsilon_3)
  = epsilon_5 overline(beta)$, где $epsilon_5 in E_3 (A, frak(q))$. Так как
  $E_3 (A, frak(q)) subset [E_3 (A), SL_3 (A, frak(q))]
  subset Ker(k')$, то
  $
    mennicke(b, a_1) mennicke(b, a_2) = k'(alpha)
    = k'(epsilon_4 (epsilon_2 alpha^(epsilon_1))^(epsilon_3))
    = k'(epsilon_5 overline(beta)) = k'(overline(beta)) = k(beta)
    = mennicke(b, a_1 a_2),
  $
  чем и завершается доказательство.
]

Основным результатом этой главы является следующая теорема, в некотором смысле
обращающая теорему @th:mennicke-symbol-homomorphism-criterion. В следующих
параграфах мы воспользуемся некоторыми ее следствиями.

#theorem[
  Пусть $A$ — нётерова область целостности#footnote[
    Л.~Н.~Васерштейн сообщил, что условие об отсутствии делителей нуля в кольце
    $A$ излишне. — _Прим. ред._
  ] размерности $<= 1$, и пусть $frak(q)$ — идеал кольца $A$. Естественный
  гомоморфизм $k_frak(q): SL_2 (A, frak(q)) -> SK_1 (A, frak(q))$ допускает
  разложение
  $ #universal-first-row-factorization() $
  аналогичное разложению @eq:mennicke-main-first-row-factorization, и
  отображение $[ ]_frak(q)$ является универсальным символом Меннике.
] <th:universal-mennicke-symbol-sk1>

Эта теорема будет выведена из следующего более точного утверждения (являющегося
в свою очередь следствием этой теоремы).

#source(242)
#assertion(italic: false)[
  I (Кубота).#idx("теорема", "Куботы") _Пусть $[ ]: W_frak(q) -> C$ — символ
  Меннике, и отображение $k: GL_2 (A, frak(q)) -> C$ является композицией
  отображений $GL_2 (A, frak(q)) #first-row-arrow() W_frak(q) arrow.r^[ ] C$.
  Тогда $k$ — гомоморфизм, ядро которого содержит $GE_2 (A, frak(q))$,
  $[GE_2 (A), GL_2 (A, frak(q))]$ и все элементы $alpha^(-1) alpha'$, где
  матрицы $alpha$, $alpha' in GL_2 (A, frak(q))$ имеют вид
  $alpha = mat(1 + a t, b; c t, d)$ и $alpha' = mat(1 + a t, t b; c, d)$ с
  $a, t in frak(q)$._
] <ss:kubota-mennicke-homomorphism>

#assertion(italic: false)[
  II. _Гомоморфизм $k$ из @ss:kubota-mennicke-homomorphism можно продолжить до
  гомоморфизма $k': GL_3 (A, frak(q)) -> C$, такого, что
  $E_3 (A, frak(q)) subset Ker(k')$._
] <ss:mennicke-homomorphism-extension>

#proof(head: [Доказательство того, что из I и II следует
  @th:universal-mennicke-symbol-sk1.])[
  Заметим сначала, что из @th:mennicke-symbol-homomorphism-criterion
  @cond:mennicke-stable-restriction-symbol следует, что $[ ]_frak(q)$ — символ
  Меннике (без всяких предположений о кольце $A$). Докажем его универсальность.
  Пусть $[ ]: W_frak(q) -> C$ — универсальный символ Меннике. Тогда
  $[ ]_frak(q) = h compose [ ]$ для однозначно определенного гомоморфизма
  $h: C -> SK_1 (A, frak(q))$. Нам надо показать, что $h$ — изоморфизм. Пусть
  $k$ и $k'$ — гомоморфизмы, существование которых обеспечивается соответственно
  утверждениями I и II. Пусть
  $f': frac(SL_3 (A, frak(q)), E_3 (A, frak(q))) -> C$ — гомоморфизм,
  индуцированный отображением $k'$. Так как $dim A <= 1$, то из
  @cor:linear-stability-dimension-bound следует, что естественный гомоморфизм
  $frac(SL_3 (A, frak(q)), E_3 (A, frak(q))) -> SK_1 (A, frak(q))$ оказывается
  изоморфизмом. Таким образом, $f'$ индуцирует отображение
  $f: SK_1 (A, frak(q)) -> C$. Если $alpha = mat(a, b; c, d)
  in SL_2 (A, frak(q))$, то
  $
    mennicke(b, a)
    = f("смежный класс элемента" quad mat(alpha, 0; 0, 1)
      quad "в" quad SK_1 (A, frak(q)))
    = f mennicke(b, a)_frak(q) = f h mennicke(b, a).
  $
  Так как, опять же в силу @cor:linear-stability-dimension-bound, отображение
  $SL_2 (A, frak(q)) -> SK_1 (A, frak(q))$ сюръективно, то $h$ — эпиморфизм. Как
  мы только что убедились, $f h = 1_C$ и, следовательно, $h$ — изоморфизм, а
  обратное к нему отображение есть $f$, чем и завершается доказательство.
]
